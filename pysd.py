#!/usr/bin/env python
#
#  pysd - a small Python script for automatic TV show subtitles downloading
#  which can also be used as a separate Python module.
#
#  Copyright (C) 2010, Dmitry Konishchev
#  http://konishchevdmitry.blogspot.com/
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 3 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#  GNU General Public License for more details.
#

"""
pysd - a small Python script which allows you to automatically download TV show
subtitles from www.TVsubtitles.net and www.opensubtitles.org and which also can
be used as a separate Python module.
"""


import sys

if sys.version_info < (2, 6):
    if __name__ == "__main__":
        sys.exit("Error: pysd needs python >= 2.6.")
    else:
        raise Exception("pysd needs python >= 2.6")

import getopt
import gzip
import httplib
import os
import re
import signal
import stat
import StringIO
import struct
import time
import urllib
import urllib2
import urlparse
import xmlrpclib
import zipfile


__all__ = [ "Tv_show_tools", "Opensubtitles_org", "Tvsubtitles_net", "NETWORK_TIMEOUT" ]


# Network timeout in seconds.
NETWORK_TIMEOUT = 30


class Tv_show_tools:
    """Provides a set of tools for working with TV show video files."""

    # Objects that downloads subtitles.
    __downloaders = None

    # TV show file name exceptions.
    __file_name_exceptions = {
        "house":     "house m.d.",
        "house.m.d": "house m.d."
    }

    # Known TV show translation releasers.
    __translation_releasers = frozenset((
        "lostfilm.tv", "novafilm.tv" ))


    def __init__(self, use_opensubtitles = False):
        self.__downloaders = []

        if use_opensubtitles:
            self.__downloaders += [( "www.opensubtitles.org", Opensubtitles_org() )]
        self.__downloaders += [( "www.tvsubtitles.net", Tvsubtitles_net() )]


    def get_info_from_filename(self, filename):
        """
        Returns a TV show possible names, season and episode numbers, extra
        info delimiter and extra info gotten from video or subtitles filename.
        For subtitles language returned instead of extra info.
        """

        try:
            filename, extension = os.path.splitext(filename.lower())
            is_subtitles = ( extension == ".srt" )
            name = None

            if not name:
                match = re.match(r"""^(.+)\.s(\d+)\.{0,1}e(\d+)(\..*){0,1}$""", filename)
                if match:
                    name = self.__file_name_exceptions.get(match.group(1), match.group(1).replace(".", " "))
                    season = int(match.group(2))
                    episode = int(match.group(3))
                    delimiter = "."
                    extra_info = (match.group(4) or "")
                    extra_info = [ info.strip() for info in extra_info[1:].split(".") if info.strip() ]

            if not name:
                match = re.match(r"""^(.+)\s+-\s+(\d+)x(\d+)(\..*|\s+-.*){0,1}$""", filename)
                if match:
                    name = self.__file_name_exceptions.get(match.group(1), match.group(1))
                    season = int(match.group(2))
                    episode = int(match.group(3))
                    delimiter = "."
                    extra_info = (match.group(4) or "")
                    if extra_info[0:1] == ".":
                        extra_info = extra_info[1:]
                    else:
                        extra_info = extra_info[extra_info.find('-') + 1:]
                    extra_info = [ info.strip() for info in extra_info.split(".") if info.strip() ]

            if not name:
                match = re.match(r"""^(.+)_s(\d+)e(\d+)(_.*){0,1}$""", filename, re.IGNORECASE)
                if match:
                    name = self.__file_name_exceptions.get(match.group(1), match.group(1).replace("_", " "))
                    season = int(match.group(2))
                    episode = int(match.group(3))
                    extra_info = (match.group(4) or "")
                    delimiter = "_"
                    if extra_info[0:1] == ".":
                        delimiter = "."
                    extra_info = [ info.strip() for info in extra_info[1:].split(delimiter) if info.strip() ]

            if not name:
                raise Not_found()

            # Universalizing the TV show name
            name = re.sub("\s+", " ", name.replace("_", " ")).strip()

            # Searching for possible aliases -->
            names = [ name ]

            # "The Mentalist" == "Mentalist"
            if name.startswith("the "):
                names.append(name[4:])

            # Sometimes releasers include in the show name a year when TV show was
            # started. For example, "V" TV show files was named as
            # V.2009.S01E10.HDTV.XviD-2HD.avi.
            match = re.match(r"""^(.+) \d{4}$""", name)
            if match:
                names.append(match.group(1))
            # Searching for possible aliases <--

            # Checking gotten data -->
            for name in names:
                if not re.search("[a-z0-9]", name):
                    raise Not_found()

                if not season or not episode:
                    raise Not_found()
            # Checking gotten data <--
        except Not_found:
            raise Not_found("This is not a TV show {0} file or it has non-standard file name.",
                "subtitles" if is_subtitles else "video" )

        if is_subtitles:
            if extra_info and (
                len(extra_info[-1]) == 2 and extra_info[-1] in LANGUAGES or
                len(extra_info[-1]) == 3 and extra_info[-1] in LANGUAGES.values()
            ):
                language = extra_info[-1]
            else:
                language = "en"

            return ( names, season, episode, delimiter, language )
        else:
            return ( names, season, episode, delimiter, extra_info )


    def get_subtitles(self, tv_show_paths, languages, recursive = False):
        """
        Gets a list of paths to a TV show video file or to a directories with
        TV show video file(s) and downloads subtitles for this TV shows for the
        specified languages, if they are not downloaded yet.

        Returns the number of errors happened.
        """

        errors = 0
        tasks = []
        subdirectories = []
        files_to_process = []
        media_extensions = ("*.avi", "*.mkv", "*.mp4", "*.wmv")

        # Gathering file list that we are going to process -->
        for tv_show_path in tv_show_paths:
            try:
                try:
                    is_directory = stat.S_ISDIR(os.stat(tv_show_path)[stat.ST_MODE])
                except Exception, e:
                    raise Error("Unable to find '{0}': {1}.", tv_show_path, e)

                tv_show_path = os.path.abspath(tv_show_path)
                media_dir = ( tv_show_path if is_directory else os.path.dirname(tv_show_path) )

                if (not is_directory and
                    os.path.splitext(tv_show_path)[1].lower() not in (ext[1:] for ext in media_extensions)
                ):
                    raise Error("'{0}' is not a media {1} file.", tv_show_path, media_extensions)

                try:
                    available_subtitles = [
                        file_name
                            for file_name in os.listdir(media_dir)
                                if (
                                    os.path.splitext(file_name)[1].lower() == ".srt" and
                                    os.path.isfile(os.path.join(media_dir, file_name))
                                )
                    ]

                    if is_directory:
                        media_files = [
                            file_name
                                for file_name in os.listdir(media_dir)
                                    if (
                                        os.path.splitext(file_name)[1].lower() in (ext[1:] for ext in media_extensions) and
                                        os.path.isfile(os.path.join(media_dir, file_name))
                                    )
                        ]

                        if recursive:
                            subdirectories = [
                                file_path
                                    for file_path in ( os.path.join(media_dir, file_name) for file_name in os.listdir(media_dir) )
                                        if os.path.isdir(file_path)
                            ]
                        else:
                            if not media_files:
                                raise Error("There are no media {0} files in the directory '{1}'.", media_extensions, media_dir)
                    else:
                        media_files = [ os.path.basename(tv_show_path) ]
                except Error:
                    raise
                except Exception, e:
                    raise Error("Error while reading directory '{0}': {1}.", media_dir, e)

                media_files.sort(cmp = self.__cmp_media_files)
                files_to_process += [ os.path.join(media_dir, file_name) for file_name in media_files ]

                tasks.append( (media_dir, media_files, available_subtitles, languages) )
            except Exception, e:
                self.log_error(e)
                errors += 1
        # Gathering file list that we are going to process <--

        # Caching subtitles info if it is possible
        if files_to_process:
            for downloader_name, downloader in self.__downloaders:
                if hasattr(downloader, "will_be_requested"):
                    for e in downloader.will_be_requested(files_to_process, languages):
                        self.log_error(e)

        # Getting the subtitles
        for task in tasks:
            errors += self.__get_subtitles(*task)

        # Processing the subdirectories if needed
        if recursive and subdirectories:
            subdirectories.sort(cmp = lambda a, b: cmp(a.lower(), b.lower()))
            errors += self.get_subtitles(subdirectories, languages, True)

        return errors


    def log_error(self, message, *args):
        """Logs an error message (may be overriden in the derived classes)."""

        E(message, *args)


    def log_info(self, message, *args):
        """Logs an info message (may be overriden in the derived classes)."""

        I(message, *args)


    def __cmp_media_files(self, a, b):
        """
        When we process media files, we have to process original media files
        before any translated media files (if exists). This is needed because
        we don't download more than one subtitles file per language for a
        particular episode, but www.opensubtitles.org search engine uses a file
        hash which is unlikely can be found for translated media files. So if
        we don't sort media files so, subtitles will be downloaded for
        translation version only from www.TVsubtitles.net and
        www.opensubtitles.org will be ignored.
        """

        try:
            cmp_info = []

            for file_name in (a, b):
                name, season, episode, delimiter, extra_info = self.get_info_from_filename(file_name)

                if extra_info and (
                    extra_info[-1] in self.__translation_releasers or
                    delimiter.join(extra_info[-2:]) in self.__translation_releasers
                ):
                    translated = True
                else:
                    translated = False

                cmp_info.append(( name, season, episode, translated ))

            return (0
                or cmp(cmp_info[0][0], cmp_info[1][0])
                or cmp(cmp_info[0][1], cmp_info[1][1])
                or cmp(cmp_info[0][2], cmp_info[1][2])
                or cmp(cmp_info[0][3], cmp_info[1][3])
            )
        except Not_found:
            return cmp(a.lower(), b.lower())


    def __get_subtitles(self, media_dir, media_files, available_subtitles, languages):
        """Downloads subtitles that we have not yet.
        Returns the number of errors happened.
        """

        errors = 0

        # Getting available subtitles info -->
        subtitles = set()

        for file_name in available_subtitles:
            try:
                names, season, episode, delimiter, language = self.get_info_from_filename(file_name)
            except Not_found, e:
                self.log_error("{0}: {1}", os.path.join(media_dir, file_name), e)
            else:
                for name in names:
                    subtitles.add( (name, season, episode, language) )
        # Getting available subtitles info <--

        # Downloading the subtitles that is not downloaded yet -->
        for file_name in media_files:
            file_path = os.path.join(media_dir, file_name)

            try:
                names, season, episode, delimiter, language = self.get_info_from_filename(file_name)
            except Not_found, e:
                self.log_error("{0}: {1}", file_path, e)
                continue

            self.log_info("Processing {0}...", file_path)

            for language in languages:
                for name in names:
                    if (name, season, episode, language) in subtitles:
                        break
                else:
                    for name, (downloader_name, downloader) in ( (n, d) for d in self.__downloaders for n in names ):
                        try:
                            subtitles_data = downloader.get(file_path, name, season, episode, language)
                        except Not_found:
                            pass
                        else:
                            subtitles.add( (name, season, episode, language) )

                            subtitles_file_path = os.path.join(media_dir, "{0}{1}{2}.srt".format(
                                os.path.splitext(file_name)[0], delimiter, language ))

                            try:
                                subtitles_file = open(subtitles_file_path, "w")

                                try:
                                    subtitles_file.write(subtitles_data)
                                except:
                                    os.unlink(subtitles_file_path)
                                    raise
                            except Exception, e:
                                self.log_error("Error while writting subtitles file '{0}': {1}.", subtitles_file_path, e)
                                errors += 1

                            break
                    else:
                        self.log_error("Subtitles for '{0}' TV show for '{1}' language is not found.", file_path, language)
                        errors += 1
        # Downloading the subtitles that is not downloaded yet <--

        return errors



class Opensubtitles_org:
    """
    Gives a facility to download subtitles from www.opensubtitles.org.
    """

    # www.opensubtitles.org domain name.
    __domain_name = "www.opensubtitles.org"

    # www.opensubtitles.org XML-RPC server has limits for maximum number of
    # items retuned per query.
    __max_reply_items = 500

    # Connection with the www.opensubtitles.org XML-RPC server
    __connection = None

    # The www.opensubtitles.org XML-RPC server token.
    __token = None

    # Request cache.
    __cache = None


    def __init__(self):
        self.__cache = {}


    def __del__(self):
        try:
            if self.__token:
                self.__call("LogOut", self.__token)
        except:
            pass


    def get(self, file_path, show_name, season, episode, language):
        """Gets a TV show subtitles and returns the subtitles file contents."""

        if file_path not in self.__cache or language not in self.__cache[file_path]:
            self.will_be_requested([file_path], [language])

        url = self.__cache[file_path][language]
        if url:
            try:
                url_file = StringIO.StringIO(get_url_contents(url))
            except Exception, e:
                raise Fatal_error("Unable to download the subtitles: {0}.", e)

            try:
                return gzip.GzipFile(fileobj = url_file).read()
            except Exception, e:
                raise Error("Unable to gunzip the subtitles file: {0}.", e)
        else:
            raise Not_found()


    def will_be_requested(self, requested_paths, languages):
        """
        Gets a list of files that will likely requested in the nearest time, so
        we can send one request for all of them and cache gotten data to save the
        time in the future.

        Returns a list with errors per file if happened.
        """

        # Checking the gotten data
        for language in languages:
            if language not in LANGUAGES:
                raise Error("invalid language ({0})", language)

        errors = []
        movies_per_request = self.__max_reply_items // (len(languages) * 5) or 1

        while requested_paths:
            movies = []
            hashes = {}

            # Hashing the files -->
            for movie_path in requested_paths[0 : movies_per_request]:
                try:
                    movie_size, movie_hash = self.__get_file_hash(movie_path)
                    movies.append({
                        "moviebytesize": movie_size,
                        "moviehash": movie_hash,
                        "sublanguageid": ",".join([ LANGUAGES[language] for language in languages ])
                    })

                    if movie_hash not in hashes:
                        hashes[movie_hash] = []
                    hashes[movie_hash].append(movie_path)
                except Exception, e:
                    if movie_path not in self.__cache:
                        self.__cache[movie_path] = {}

                    for language in languages:
                        self.__cache[movie_path][language] = None

                    errors.append(str(e))
            # Hashing the files <--

            # Getting available subtitles -->
            if movies:
                self.__connect()

                try:
                    subtitles_list = self.__call("SearchSubtitles", self.__token, movies)["data"]
                except Exception, e:
                    raise Fatal_error("Unable to get a list of subtitles from {0}: {1}.", self.__domain_name, e)

                subtitles_dict = {}

                # Filtering the subtitles with the most downloads count -->
                if subtitles_list:
                    subtitles_list.sort(cmp = lambda a, b: (
                        cmp(a["MovieHash"],       b["MovieHash"]) or
                        cmp(a["ISO639"],          b["ISO639"]) or
                        cmp(a["SubDownloadsCnt"], b["SubDownloadsCnt"])
                    ), reverse = True)

                    for subtitles in subtitles_list:
                        movie_hash = subtitles["MovieHash"]
                        language = subtitles["ISO639"]

                        if movie_hash not in subtitles_dict:
                            subtitles_dict[movie_hash] = {}
                        movie_subtitles = subtitles_dict[movie_hash]

                        if language not in movie_subtitles:
                            movie_subtitles[language] = subtitles["SubDownloadLink"]
                # Filtering the subtitles with the most downloads count <--
            # Getting available subtitles <--

            # Mapping movie names to subtitles -->
            for movie_hash, movie_paths in hashes.iteritems():
                for movie_path in movie_paths:
                    if movie_path not in self.__cache:
                        self.__cache[movie_path] = {}

                    for language in languages:
                        self.__cache[movie_path][language] = subtitles_dict.get(movie_hash, {}).get(language, self.__cache[movie_path].get(language))
            # Mapping movie names to subtitles <--

            requested_paths = requested_paths[movies_per_request:]

        return errors


    def __call(self, method, *args):
        """Calls XML-RPC method and checks its return code."""

        reply = getattr(self.__connection, method)(*args)

        if "status" not in reply:
            raise Error("server returned an invalid response")

        if reply["status"].split(" ")[0] != "200":
            raise Error("server returned error '{0}'", reply["status"])

        return reply


    def __connect(self):
        """Ensures that we are connected to the XML-RPC server."""

        try:
            if self.__connection == None or not self.__token:
                self.__connection = xmlrpclib.ServerProxy(
                    "http://api.opensubtitles.org/xml-rpc", transport = Xml_rpc_proxy(), allow_none = True )
                self.__token = self.__call("LogIn", "", "", "en", "pysd 0.1")["token"]
        except Exception, e:
            raise Fatal_error("Unable to connect to {0} XML-RPC server: {1}.", self.__domain_name, e)


    def __get_file_hash(self, path):
        """
        Calculates file hash sutable for www.opensubtitles.org XML-RPC query
        calls. Returns file size and hash.
        """

        try:
            hashing_file = open(path, "rb")
            buf_size = struct.calcsize("=q")

            file_size = os.path.getsize(path)
            file_hash = file_size

            if file_size < 65536 * 2:
                raise Error("file too small")

            for pos in (0, file_size - 65536):
                hashing_file.seek(pos)

                for i in xrange(65536 / buf_size):
                    buf = ""
                    data = " "

                    while len(buf) != buf_size:
                        data = hashing_file.read(buf_size - len(buf))
                        if data:
                            buf += data
                        else:
                            raise Error("end of file error")

                    file_hash += struct.unpack("=q", buf)[0]
                    file_hash &= 0xFFFFFFFFFFFFFFFF

            return (file_size, "{0:016x}".format(file_hash))
        except IOError, e:
            raise Error("Unable to hash file '{0}': {1}.", path, e)
        except Exception, e:
            raise Fatal_error("Error while hashing file '{0}': {1}.", path, e)



class Tvsubtitles_net:
    """
    Gives a facility to download subtitles from www.tvsubtitles.net.
    """

    # www.tvsubtitles.net domain name.
    __domain_name = "www.tvsubtitles.net"

    # URL prefix for all www.tvsubtitles.net URLs.
    __url_prefix = "http://" + __domain_name + "/"

    # Regular expression that matches a HTML tag.
    __tag_re = re.compile("<[^>]+>")

    # Downloaded data cache.
    __cache = None


    def __init__(self):
        self.__cache = {}


    def get(self, file_path, show_name, season, episode, language):
        """Gets a TV show subtitles and returns the subtitles file contents."""

        subtitles = self.__get_episode_subtitles(show_name, season, episode)

        if language not in subtitles:
            raise Not_found()

        try:
            zipfile_data = get_url_contents( self.__url_prefix + "download-{0}.html".format(subtitles[language]) )
        except Exception, e:
            raise Fatal_error("Unable to download the subtitles: {0}.", e)

        try:
            subtitles_zip = zipfile.ZipFile(StringIO.StringIO(zipfile_data))
            if len(subtitles_zip.namelist()) != 1:
                raise Error("zip file contains {0} files instead of 1", len(subtitles_zip.namelist()))

            return subtitles_zip.open(subtitles_zip.namelist()[0]).read()
        except Exception, e:
            raise Error("Unable to unzip the subtitles file: {0}.", e)


    def __get_episodes(self, show_name, season):
        """Returns a list of episodes for which we have subtitles."""

        shows = self.__get_shows()

        if show_name in shows:
            show = shows[show_name]
        else:
            raise Not_found()

        try:
            if season not in show["seasons"]:
                episodes = {}

                episode_list_html = get_url_contents(self.__url_prefix + "tvshow-{0}-{1}.html".format(show["id"], season))

                all_episodes_regex = re.compile(r"""
                    <td(\s[^>]*){0,1}>\s*</td>\s*
                    <td(\s[^>]*){0,1}>\s*
                    <a(\s[^>]*){0,1}\s+
                        href\s*=\s*["']{0,1}
                            /{0,1}episode-""" + str(show["id"]) + "-" + str(season) + r"""\.html
                        ["']{0,1}
                    (\s[^>]*){0,1}>
                """, re.IGNORECASE | re.VERBOSE)

                if len( [ x for x in all_episodes_regex.finditer(episode_list_html) ] ) != 1:
                    raise Error("failed to parse a server response")

                episode_regex = re.compile(r"""
                    <td(\s[^>]*){0,1}>\s*""" +
                        str(season) + r"""x0*(\d+)\s*
                    </td>\s*
                    <td(\s[^>]*){0,1}>\s*
                    <a(\s[^>]*){0,1}\s+
                        href\s*=\s*["']{0,1}
                            /{0,1}episode-(\d+)\.html
                        ["']{0,1}
                    (\s[^>]*){0,1}>
                """, re.IGNORECASE | re.VERBOSE)

                for match in episode_regex.finditer(episode_list_html):
                    episodes[int(match.group(2))] = { "id": match.group(5) }

                show["seasons"][season] = episodes

            return show["seasons"][season]
        except Exception, e:
            raise Fatal_error("Unable to get episode list for the TV show from {1}: {2}.", self.__domain_name, e)


    def __get_episode_subtitles(self, show_name, season, episode_number):
        """
        Returns a list of subtitles which we have for the episode specified by
        the arguments.
        """

        episodes = self.__get_episodes(show_name, season)

        if episode_number in episodes:
            episode = episodes[episode_number]
        else:
            raise Not_found()

        try:
            if "subtitles" not in episode:
                subtitles_dict = {}
                subtitles_list = []

                subtitles_list_html = get_url_contents(self.__url_prefix + "episode-{0}.html".format(episode["id"]))

                subtitles_regex = re.compile(r"""
                    <a(\s[^>]*){0,1}\s+
                        href\s*=\s*["']{0,1}
                            /{0,1}subtitle-(\d+)\.html
                        ["']{0,1}
                    (\s[^>]*){0,1}>
                        (.+?)
                    </a>
                """, re.IGNORECASE | re.DOTALL | re.VERBOSE)

                subtitles_info_regex = re.compile(r"""
                    <img(\s[^>]*){0,1}\s+
                        src\s*=\s*["']{0,1}
                            [^'"]*flags/([a-z]{2})\.[a-z]+
                        ["']{0,1}
                    (\s[^>]*){0,1}>
                    .*
                    <p(\s[^>]*){0,1}\s+
                        (
                            title\s*=\s*["']{0,1}
                                downloaded
                            ["']{0,1}
                        |
                            alt\s*=\s*["']{0,1}
                                downloaded
                            ["']{0,1}
                        )
                    (\s[^>]*){0,1}>
                        (.*?)
                    </p>
                """, re.IGNORECASE | re.DOTALL | re.VERBOSE)

                for match in subtitles_regex.finditer(subtitles_list_html):
                    subtitles = { "id": match.group(2) }
                    subtitles_info_html = match.group(4)

                    info_match = subtitles_info_regex.search(subtitles_info_html)
                    if not info_match:
                        raise Exception("failed to parse a server response")

                    downloads = self.__tag_re.sub("", info_match.group(7)).replace("&nbsp;", " ").strip()
                    try:
                        downloads = int(downloads)
                    except ValueError:
                        raise Exception("failed to parse a server response")

                    subtitles["language"] = info_match.group(2)
                    subtitles["downloads"] = downloads

                    subtitles_list.append(subtitles)

                # Getting only one subtitle with the most downloads per
                # language.
                # -->
                subtitles_list.sort(lambda a, b: (
                    cmp(a["language"], b["language"]) or cmp(a["downloads"], b["downloads"])
                ), reverse = True)

                for subtitles in subtitles_list:
                    if subtitles["language"] not in subtitles_dict:
                        subtitles_dict[subtitles["language"]] = subtitles["id"]
                # <--

                episode["subtitles"] = subtitles_dict

            return episode["subtitles"]
        except Exception, e:
            raise Fatal_error("Unable to get subtitles list from {0}: {1}.", self.__domain_name, e)


    def __get_shows(self):
        """Returns a list of all www.tvsubtitles.net shows."""

        try:
            if not self.__cache:
                shows = {}

                tv_show_list_html = get_url_contents(self.__url_prefix + "tvshows.html")

                tv_show_regex = re.compile(r"""
                    <a(\s[^>]*){0,1}\s+
                        href\s*=\s*["']{0,1}
                            /{0,1}tvshow-(\d+)-\d+\.html
                        ["']{0,1}
                    (\s[^>]*){0,1}>
                        (.+?)
                    </a>
                """, re.IGNORECASE | re.VERBOSE)

                for match in tv_show_regex.finditer(tv_show_list_html):
                    show_name = self.__tag_re.sub("", match.group(4)).replace("&nbsp;", " ").strip().lower()
                    shows[show_name] = { "id": match.group(2), "seasons": {} }

                if not shows:
                    raise Exception("failed to parse a server response")

                self.__cache = shows

            return self.__cache
        except Exception, e:
            raise Fatal_error("Unable to get TV show list from {0}: {1}.", self.__domain_name, e)



class Xml_rpc_proxy(xmlrpclib.Transport):
    """HTTP proxy for xmlrpclib."""

    # Proxy host (if exists).
    proxy = None


    def __init__(self, use_datetime = 0):
        xmlrpclib.Transport.__init__(self, use_datetime)

        proxy = urllib.getproxies().get("http", "").strip()

        if proxy:
            if proxy.startswith("http://") and urlparse.urlparse(proxy).netloc:
                self.proxy = urlparse.urlparse(proxy).netloc
            else:
                raise Fatal_error("invalid HTTP proxy specified ({0})", proxy)


    def make_connection(self, host):
        connection = httplib.HTTP(self.proxy if self.proxy else host)

        if hasattr(connection, "real_host"):
            raise Fatal_error("logical error")

        connection.real_host = host

        return connection


    def send_request(self, connection, handler, request_body):
        connection.putrequest("POST", "http://{0}{1}".format(connection.real_host, handler))


    def send_host(self, connection, host):
        connection.putheader("Host", connection.real_host)



class Pysd:
    """The pysd script worker."""


    def __init__(self):
        try:
            signal.signal(signal.SIGINT,  self.__signal_handler)
            signal.siginterrupt(signal.SIGINT, False)

            signal.signal(signal.SIGQUIT, self.__signal_handler)
            signal.siginterrupt(signal.SIGQUIT, False)

            signal.signal(signal.SIGTERM, self.__signal_handler)
            signal.siginterrupt(signal.SIGTERM, False)

            signal.siginterrupt(signal.SIGPIPE, False)


            languages, use_opensubtitles, paths, recursive = self.__get_cmd_options()
            tools = Tv_show_tools(use_opensubtitles)

            errors = tools.get_subtitles(paths, languages, recursive)
        except (End_work_exception, Fatal_error), e:
            E(e)
        except BaseException, e:
            if e.__class__ != SystemExit:
                E("pysd crashed: {0}.", e)
        else:
            sys.exit(1 if errors else 0)

        sys.exit(1)


    def __get_cmd_options(self):
        """
        Parses the command line options and returns a tuple that contains a
        list of video files and directories with video files, a list of
        subtitles languages to download and a flag - whether we should download
        subtitles from www.opensubtitles.org.
        """

        try:
            cmd_options, cmd_args = getopt.gnu_getopt(
                sys.argv[1:], "hl:ro", [ "lang=", "recursive", "opensubtitles" ] )

            languages = set()
            recursive = False
            use_opensubtitles = False

            for option, value in cmd_options:
                if option in ("-h", "--help"):
                    print (
                        """{0} [OPTIONS] -l LANGUAGE (DIRECTORY|FILE)...\n\n"""
                        """Options:\n"""
                        """ -l, --lang          a comma separated list of subtitles languages to download ("en,ru")\n"""
                        """ -r, --recursive     process subdirectories recursively\n"""
                        """ -o, --opensubtitles download subtitles also from www.opensubtitles.org (enhances the result,\n"""
                        """                     but significantly increases the script work time + www.opensubtitles.org\n"""
                        """                     servers are often down)\n"""
                        """ -h, --help          show this help"""
                                                .format(sys.argv[0])
                    )
                    sys.exit(0)
                elif option in ("-l", "--lang"):
                    for lang in value.split(","):
                        lang = lang.strip()

                        if lang not in LANGUAGES:
                            raise Error("invalid language '{0}'", lang)

                        languages.add(lang)
                elif option in ("-r", "--recursive"):
                    recursive = True
                elif option in ("-o", "--opensubtitles"):
                    use_opensubtitles = True
                else:
                    raise Error("invalid option '{0}'", option)

            if not cmd_args:
                raise Error("there is no TV show video file or TV show directory specified")

            if not languages:
                raise Error("there is no subtitles languages specified")

            return (languages, use_opensubtitles, cmd_args, recursive)
        except Exception, e:
            raise Fatal_error("Command line options parsing error: {0}. See `{1} -h` for more information.", e, sys.argv[0])


    def __signal_handler(self, signum, frame):
        """Handler for the UNIX signals."""

        raise End_work_exception()



class End_work_exception(BaseException):
    """Raised in the UNIX signal handlers."""

    def __init__(self):
        BaseException.__init__(self, "Program was interrupted by a signal.")


class Error(Exception):
    """The base class for all pysd exceptions."""

    def __init__(self, error, *args):
        Exception.__init__(self, error.format(*args) if len(args) else str(error))


class Fatal_error(Error):
    """
    Raised on logical errors and errors that likely will repeat in the future,
    so it's reasonably to end program work when you get this error.
    """

    def __init__(self, error, *args):
        Error.__init__(self, error, *args)


class Not_found(Error):
    """Raised when we failed to find any object."""

    def __init__(self, error = "not found", *args):
        Error.__init__(self, error, *args)



def get_url_contents(url):
    """Downloads a url and returns the gotten data."""

    max_data_size = 1024 * 1024

    for tries_available in xrange(2, -1, -1):
        try:
            url_file = urllib2.urlopen(url, timeout = NETWORK_TIMEOUT)
            contents = ""
            data = "non empy"

            while data and len(contents) < max_data_size + 1:
                data = url_file.read(max_data_size + 1 - len(contents))
                contents += data
        except Exception:
            if tries_available:
                time.sleep(3)
            else:
                raise
        else:
            if len(data) > max_data_size:
                raise Error("gotten too big data size (> {0})", max_data_size)
            else:
                return contents

    raise Error("logical error")


def E(message, *args):
    """Prints an error message."""

    print >> sys.stderr, message.format(*args) if len(args) else message


def I(message, *args):
    """Prints an info message."""

    print message.format(*args) if len(args) else message



# ISO 639-1 -> 639-2/B language codes.
LANGUAGES = {
    "ab": "abk",
    "aa": "aar",
    "af": "afr",
    "ak": "aka",
    "sq": "alb",
    "am": "amh",
    "ar": "ara",
    "an": "arg",
    "hy": "arm",
    "as": "asm",
    "av": "ava",
    "ae": "ave",
    "ay": "aym",
    "az": "aze",
    "bm": "bam",
    "ba": "bak",
    "eu": "baq",
    "be": "bel",
    "bn": "ben",
    "bh": "bih",
    "bi": "bis",
    "bs": "bos",
    "br": "bre",
    "bg": "bul",
    "my": "bur",
    "ca": "cat",
    "ch": "cha",
    "ce": "che",
    "ny": "nya",
    "zh": "chi",
    "cv": "chv",
    "kw": "cor",
    "co": "cos",
    "cr": "cre",
    "hr": "hrv",
    "cs": "cze",
    "da": "dan",
    "dv": "div",
    "nl": "dut",
    "dz": "dzo",
    "en": "eng",
    "eo": "epo",
    "et": "est",
    "ee": "ewe",
    "fo": "fao",
    "fj": "fij",
    "fi": "fin",
    "fr": "fre",
    "ff": "ful",
    "gl": "glg",
    "ka": "geo",
    "de": "ger",
    "el": "gre",
    "gn": "grn",
    "gu": "guj",
    "ht": "hat",
    "ha": "hau",
    "he": "heb",
    "hz": "her",
    "hi": "hin",
    "ho": "hmo",
    "hu": "hun",
    "ia": "ina",
    "id": "ind",
    "ie": "ile",
    "ga": "gle",
    "ig": "ibo",
    "ik": "ipk",
    "io": "ido",
    "is": "ice",
    "it": "ita",
    "iu": "iku",
    "ja": "jpn",
    "jv": "jav",
    "kl": "kal",
    "kn": "kan",
    "kr": "kau",
    "ks": "kas",
    "kk": "kaz",
    "km": "khm",
    "ki": "kik",
    "rw": "kin",
    "ky": "kir",
    "kv": "kom",
    "kg": "kon",
    "ko": "kor",
    "ku": "kur",
    "kj": "kua",
    "la": "lat",
    "lb": "ltz",
    "lg": "lug",
    "li": "lim",
    "ln": "lin",
    "lo": "lao",
    "lt": "lit",
    "lu": "lub",
    "lv": "lav",
    "gv": "glv",
    "mk": "mac",
    "mg": "mlg",
    "ms": "may",
    "ml": "mal",
    "mt": "mlt",
    "mi": "mao",
    "mr": "mar",
    "mh": "mah",
    "mn": "mon",
    "na": "nau",
    "nv": "nav",
    "nb": "nob",
    "nd": "nde",
    "ne": "nep",
    "ng": "ndo",
    "nn": "nno",
    "no": "nor",
    "ii": "iii",
    "nr": "nbl",
    "oc": "oci",
    "oj": "oji",
    "cu": "chu",
    "om": "orm",
    "or": "ori",
    "os": "oss",
    "pa": "pan",
    "pi": "pli",
    "fa": "per",
    "pl": "pol",
    "ps": "pus",
    "pt": "por",
    "qu": "que",
    "rm": "roh",
    "rn": "run",
    "ro": "rum",
    "ru": "rus",
    "sa": "san",
    "sc": "srd",
    "sd": "snd",
    "se": "sme",
    "sm": "smo",
    "sg": "sag",
    "sr": "srp",
    "gd": "gla",
    "sn": "sna",
    "si": "sin",
    "sk": "slo",
    "sl": "slv",
    "so": "som",
    "st": "sot",
    "es": "spa",
    "su": "sun",
    "sw": "swa",
    "ss": "ssw",
    "sv": "swe",
    "ta": "tam",
    "te": "tel",
    "tg": "tgk",
    "th": "tha",
    "ti": "tir",
    "bo": "tib",
    "tk": "tuk",
    "tl": "tgl",
    "tn": "tsn",
    "to": "ton",
    "tr": "tur",
    "ts": "tso",
    "tt": "tat",
    "tw": "twi",
    "ty": "tah",
    "ug": "uig",
    "uk": "ukr",
    "ur": "urd",
    "uz": "uzb",
    "ve": "ven",
    "vi": "vie",
    "vo": "vol",
    "wa": "wln",
    "cy": "wel",
    "wo": "wol",
    "fy": "fry",
    "xh": "xho",
    "yi": "yid",
    "yo": "yor",
    "za": "zha",
    "zu": "zul"
}



if __name__ == "__main__":
    pysd = Pysd()

