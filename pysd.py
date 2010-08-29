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

import sys

if sys.version_info < (2, 6):
    if __name__ == "__main__":
        sys.exit("Error: pysd needs python >= 2.6.")
    else:
        raise Exception("pysd needs python >= 2.6")

import getopt
import glob
import os
import re
import signal
import stat
import StringIO
import time
import urllib2
import zipfile


__all__ = [ "Tv_show_tools", "Tvsubtitles_net", "NETWORK_TIMEOUT" ]


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


    def __init__(self):
        self.__downloaders = [ Tvsubtitles_net() ]


    def get_info_from_filename(self, filename):
        """
        Returns a TV show possible names, season and episode numbers gotten
        from vidio or subtitles filename. For subtitles language is also
        returned.
        """

        try:
            filename, extension = os.path.splitext(filename)
            is_subtitles = ( extension == ".srt" )
            name = None

            if not name:
                match = re.match(r"""^(.+)\.s(\d+)e(\d+)(\..*){0,1}$""", filename, re.IGNORECASE)
                if match:
                    name = self.__file_name_exceptions.get(match.group(1).lower(), match.group(1).replace(".", " "))
                    season = int(match.group(2))
                    episode = int(match.group(3))
                    extra_info = [
                        info.strip().lower()
                            for info in match.group(4)[1:].split(".")
                    ]

            if not name:
                match = re.match(r"""^(.+)\s+-\s+(\d+)x(\d+)(\s+-.*){0,1}$""", filename, re.IGNORECASE)
                if match:
                    name = self.__file_name_exceptions.get(match.group(1).lower(), match.group(1))
                    season = int(match.group(2))
                    episode = int(match.group(3))
                    extra_info = [
                        info.strip().lower()
                            for info in match.group(4)[match.group(4).find('-') + 1:].split(".")
                    ]

            if not name:
                match = re.match(r"""^(.+)_s(\d+)e(\d+)(_.*){0,1}$""", filename, re.IGNORECASE)
                if match:
                    name = self.__file_name_exceptions.get(match.group(1).lower(), match.group(1).replace("_", " "))
                    season = int(match.group(2))
                    episode = int(match.group(3))
                    extra_info = [
                        info.strip().lower()
                            for info in match.group(4)[1:].split("_")
                    ]

            if not name:
                raise Not_found()

            # Searching for possible aliases -->
            name = re.sub("\s+", " ", name).strip().lower()
            names = [ name ]

            # "The Mentalist" == "Mentalist"
            if name.startswith("the "):
                names.append(name[4:])

            # Sometimes releasers include in the show name a year when TV show was
            # started. For example, "V" TV show files was named as
            # V.2009.S01E10.HDTV.XviD-2HD.avi.
            match = re.match(r"""^(.+) \d{4}$""", name, re.IGNORECASE)
            if match:
                names.append(match.group(1))
            # Searching for possible aliases <--

            # Checking gotten data -->
            for name in names:
                if not re.search("[a-z0-9]", name, re.IGNORECASE):
                    raise Not_found()

                if not season or not episode:
                    raise Not_found()
            # Checking gotten data <--
        except Not_found:
            raise Not_found("This is not a TV show {0} file or it has non-standard file name.",
                "subtitles" if is_subtitles else "video" )

        if is_subtitles:
            if extra_info and len(extra_info[-1]) == 2:
                language = extra_info[-1]
            else:
                language = "en"
        else:
            language = None

        return ( names, season, episode, language )


    def get_subtitles(self, tv_show_path, languages):
        """
        Gets a path to a TV show video file or to a directory with TV show
        video file(s) and downloads subtitles for this TV shows for the
        specified languages, that is not downloaded yet.

        Returns the number of subtitles that had not been found.
        """

        try:
            is_directory = stat.S_ISDIR(os.stat(tv_show_path)[stat.ST_MODE])
        except Exception, e:
            raise Error("Unable to find '{0}': {1}.", tv_show_path, e)

        tv_show_path = os.path.abspath(tv_show_path)
        media_dir = ( tv_show_path if is_directory else os.path.dirname(tv_show_path) )

        try:
            media_files = []
            available_subtitles = [
                os.path.basename(path)
                    for path in glob.glob(os.path.join(media_dir, "*.srt"))
            ]

            if is_directory:
                media_extensions = ("*.avi", "*.mkv", "*.mp4", "*.wmv")

                for extension in media_extensions:
                    media_files += glob.glob(os.path.join(media_dir, extension))

                if not media_files:
                    raise Error("There are no media {0} files in the directory '{1}'.", media_extensions, media_dir)
            else:
                media_files.append(tv_show_path)

            media_files = [
                os.path.basename(path)
                    for path in media_files
            ]
            media_files.sort(cmp = lambda a, b: cmp(a.lower(), b.lower()))
        except Error:
            raise
        except Exception, e:
            raise Error("Error while reading the directory '{0}': {1}.", media_dir, e)

        return self.__get_subtitles(media_dir, media_files, available_subtitles, languages)


    def __get_subtitles(self, media_dir, media_files, available_subtitles, languages):
        """Downloads subtitles that we have not yet.
        Returns the number of subtitles that had not been found.
        """

        not_found = 0

        # Getting available subtitles info -->
        subtitles = set()

        for filename in available_subtitles:
            try:
                names, season, episode, language = self.get_info_from_filename(filename)
            except Not_found, e:
                self.__log_error("{0}: {1}", os.path.join(media_dir, filename), e)
            else:
                for name in names:
                    subtitles.add( (name, season, episode, language) )
        # Getting available subtitles info <--

        # Downloading the subtitles that is not downloaded yet -->
        for filename in media_files:
            try:
                names, season, episode, language = self.get_info_from_filename(filename)
            except Not_found, e:
                self.__log_error("{0}: {1}", os.path.join(media_dir, filename), e)
                continue

            self.__log_info("Processing {0}...", os.path.join(media_dir, filename))

            for language in languages:
                for name in names:
                    if (name, season, episode, language) in subtitles:
                        break
                else:
                    for name, downloader in ( (n, d) for n in names for d in self.__downloaders ):
                        try:
                            subtitles_data = downloader.get(name, season, episode, language)
                        except Not_found:
                            pass
                        else:
                            subtitles.add( (name, season, episode, language) )

                            subtitles_file_path = os.path.join(media_dir, "{0}.{1}.srt".format(
                                os.path.splitext(filename)[0], language ))

                            try:
                                subtitles_file = open(subtitles_file_path, "w")

                                try:
                                    subtitles_file.write(subtitles_data)
                                except:
                                    os.unlink(subtitles_file_path)
                                    raise
                            except Exception, e:
                                E("Error while writting subtitles file '{0}': {1}.", subtitles_file_path, e)
                                not_found += 1

                            break
                    else:
                        self.__log_error("Subtitles for '{0}' TV show for '{1}' language is not found.", os.path.join(media_dir, filename), language)
                        not_found += 1
        # Downloading the subtitles that is not downloaded yet <--

        return not_found


    def __log_error(self, message, *args):
        """Logs an error message (may be overriden in the derived classes)."""

        E(message, *args)


    def __log_info(self, message, *args):
        """Logs an info message (may be overriden in the derived classes)."""

        I(message, *args)



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


    def get(self, show_name, season, episode, language):
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


    def __compare_subtitles(self, a, b):
        """Subtitle compare function (for the sorting)."""

        return cmp(a["language"], b["language"]) or cmp(a["downloads"], b["downloads"])


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
                subtitles_list.sort(self.__compare_subtitles, reverse = True)
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


            paths, languages = self.__get_cmd_options()
            tools = Tv_show_tools()

            not_found = 0
            for path in paths:
                try:
                    not_found += tools.get_subtitles(path, languages)
                except Fatal_error:
                    raise
                except Error, e:
                    not_found += 1
                    E(e)
        except Fatal_error, e:
            E(e)
        except End_work_exception, e:
            E(e)
        except BaseException, e:
            E("pysd crashed: {0}.", e)
        else:
            sys.exit(1 if not_found else 0)

        sys.exit(1)


    def __get_cmd_options(self):
        """
        Parses the command line options and returns a tuple that contains a list of
        video files and directories with video files and a list of subtitles
        languages to download.
        """

        try:
            cmd_options, cmd_args = getopt.gnu_getopt(
                sys.argv[1:], "hl:", [ "lang=" ] )

            languages = set()

            for option, value in cmd_options:
                if option in ("-h", "--help"):
                    print (
                        """{0} [OPTIONS] -l LANGUAGE (DIRECTORY|FILE)...\n\n"""
                        """Options:\n"""
                        """ -l, --lang  a comma separated list of subtitles languages to download ("en,ru")\n"""
                        """ -h, --help  show this help"""
                        .format(sys.argv[0])
                    )
                    sys.exit(0)
                elif option in ("-l", "--lang"):
                    for lang in value.split(","):
                        lang = lang.strip()

                        if len(lang) != 2:
                            raise Error("invalid language '{0}'", lang)

                        languages.add(lang)
                else:
                    raise Error("invalid option '{0}'", option)

            if not cmd_args:
                raise Error("there is no TV show video file or TV show directory specified")

            if not languages:
                raise Error("there is no subtitles languages specified")

            return (cmd_args, languages)
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
        Exception.__init__(self, error.format(*args) if len(args) else error)


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
        except Exception, e:
            if tries_available:
                E("Error while downloading '{0}': {1}. Trying again...", url, e)
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



if __name__ == "__main__":
    pysd = Pysd()

