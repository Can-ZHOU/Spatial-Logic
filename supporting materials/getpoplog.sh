#!/bin/bash
#
# getpoplog.sh -- by A.Sloman, with help from Waldek Hebisch
# Download and install pplog
#
## NB NB NB Search below for information about the '-nopie' parameter, required by
## some recent versions of linux.
#
## Still a draft: Installed 31 Dec 2019
## Last updated 21 Aug 2020
##
## https://www.cs.bham.ac.uk/research/projects/poplog/V16/getpoplog.sh
## Script to download and setup Version 16 of Poplog for 64-bit linux.
##
## UPDATES
## 1 Jan 2020: moved all tar-balls to the downloads subdirectory
## https://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/

# Use this to fetch and install Poplog V16 in the directory where this is run.
# Run with parameter '-nopie' to prevent Position Independent Execution mode.
#     E.g. getpoplog.sh -nopie
#     N.B. This requires the linux 'param' package to have been installed.
# '-nopie' is needed for recent versions of Debian and Ubuntu (e.g. 18.04), and for Arch linux.
# It will prevent proper installation if used with some older versions of linux.
# It is not required for Fedora 31 but seems to do no harm if used.

# INTRODUCTION
## This package was created on 1 Jan 2020, after a series of earlier experimental
## versions had been made available.
## It is written by Aaron Sloman http://www.cs.bham.ac.uk/~axs but mainly
## based on work by Waldek Hebisch http://www.math.uni.wroc.pl/~hebisch
## who produced a new 64 bit port of the core of Poplog in 2019, available on github, at
##     https://github.com/hebisch/poplog

# BACKGROUND INFORMATION
# For information about Poplog, its four languages (Pop-11, Prolog, Common Lisp and
# Standard ML) its history, its uses in teaching, research and development, its
# main contributors see this file, which provides more detailed information and
# additional links:
# https://www.cs.bham.ac.uk/research/projects/poplog/V16/AREADME.html
## Wikipedia information:
#   https://en.wikipedia.org/wiki/Poplog
#   https://en.wikipedia.org/wiki/POP-11
#  (also  Prolog, Common Lisp and Standard ML)
# e.g. https://en.wikipedia.org/wiki/Standard_ML

# Additional information about poplog can be found at this location
# http://www.cs.bham.ac.uk/research/projects/poplog/V16/
# including these older files, originally referring to 32bit linux poplog.
# http://www.cs.bham.ac.uk/research/projects/poplog/freepoplog.html
# http://www.cs.bham.ac.uk/research/projects/poplog/poplog.info.html
# [Apologies for duplication in those files.]

# This script starts from the files downloaded from github, and adds
# extra documentation and a collection of packages, including teaching
# materials, from the University of Birmingham.

# PREREQUISITES
# Before poplog can installed, various linux packages need to be installed. The
# commands for doing this depend on the version of linux, and can be found in
# https://www.cs.bham.ac.uk/research/projects/poplog/V16/required-packages.html
#
# That has scripts to be run in advance to set up Poplog prerequisites for users
# of Redhat-based linux systems, Debian/Ubuntu and Arch linux.
# Please send corresponding scripts to run for other versions of linux.
#
# THIS FILE
# This getpoplog.sh file can be downloaded, made executable and run. It then
# downloads additional files from https://www.cs.bham.ac.uk/research/projects/poplog/V16
# and uses them to set up a usable version of poplog on a local machine. This can
# be a private version used only by one individual, or a shared version accessible
# on other users of the machine, or installed on a linux file server whose contents
# can be mounted on individual workstations and other servers.
#
# USING THIS FILE
# When run it fetches and installs the contents of three files, used to create a
# directory poplog_base at the download location:
#
# 1. http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/latest_poplog_base.tar.bz2
#   Core poplog files including a tar file derived from the poplog github site set
#   up by Waldek Hebisch: https://github.com/hebisch/poplog
#   Creates poplog_base directory, and contents.
#
# The core is augmented with some documentation files and the Poplog 'packages' library
# both at the University of Birmingham, downloaded separately.
# 2. http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/docs.tar.bz2
# 3. http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/packages-V16.tar.bz2
#
# It also fetches scripts to be moved into the poplog_base directory and used
# either during installation or by end users.
#
# ------------------------------------------------------------------
#
# WHAT THIS FILE (GETPOPLOG.SH) DOES, IN MORE DETAIL:
#
# Note
# The latest version of getpoplog.sh accepts an optional extra parameter -nopie
# which determines whether or not poplog can be linked as a position-independent
# executable (PIE).
# This is not permitted in some recent versions of linux (e.g. Arch and recent versions
# of Debian). The extra parameter '-nopie', if present, invokes a change to exclude PIE.
# So, to install poplog on Arch or Debian 9 and "testing", run this command as
#
#  getpoplog.sh -nopie
#
# For other versions of linux that may not yet work, and '-nopie' can be omitted, e.g.
# for older versions of Fedora. It doesn't seem to be required for newer versions, but
# can be used.
#
# FETCH POPLOG INSTALLATION FILES.
# Choose an appropriate location to run this script to install poplog.
# Fetch this script using the following shell command, and make it executable.
#
#  wget https://www.cs.bham.ac.uk/research/projects/poplog/V16/getpoplog.sh
#  Make it runnable by the owner (it normally needs to be run by super-user):
#  chmod 755 getpoplog.sh
#
#  You may have to edit some uncommented parts of the script to fit your
#  environment. Also make sure you have previously installed the required
#  linux libraries for your version of linux.
#  See this file for guidance about required linux packages:
#
#   http://www.cs.bham.ac.uk/research/projects/poplog/V16/required-packages.html
#   (Please send corrections and additions to a.sloman AT cs.bham.ac.uk)
#
# This getpoplog.sh file is a simplified version, partly because the final
# steps are now run by the script build_all.sh, invoked after the tar files
# have been unpacked. (Previously build_all.csh was required)
# See changes for 'position independent' code, below.

# For the broader context please see:
#  https://www.cs.bham.ac.uk/research/projects/poplog/V16/AREADME.html

# RESULTS OF RUNNING THIS SCRIPT:

# Unpacking latest_poplog_base.tar.bz2 will have the following effect
# A directory poplog_base will be created in the directory in which it is run.
# Initially it contains scripts used to unpack and set up the poplog directory tree
# with root in poplog_base, whose path name has to be assigned to be environment
# variable $usepop for users of Poplog.
# Everything else in the final installed system is accessed via $usepop.
#
# This is the main poplog tar package
#    latest_poplog_base.tar.bz2

# It contains a slightly expanded version of contents of a tar file from the
#   github site set up by Waldek Hebisch: https://github.com/hebisch/poplog)
#
# When untarred it creates a directory
#       poplog_base,
# to be referenced via the $usepop environment variable, which contains all the core
# Poplog files required at run time, plus items added at Birmingham for use in the
# final configuration.
# Some of the downloaded files, including Poplog sources, are used to build the final
# usable poplog system.

# If this file is run with the '-nopie' parameter,
#
#   getpoplog.sh -nopie
#
# it will alter one of the core poplog system source files, to disable PIE
# (position independent execution, described in
#   https://access.redhat.com/blogs/766093/posts/1975793)
#
# Otherwise it should be run simply as follows (e.g. for older versions of linux):
#
#   getpoplog.sh
#
# Both versions download the same contents: they differ only in what they
# do during the installation process.
#
# Expert users may wish to modify some of the instructions before running
# the scripts.

# END OF PREAMBLE.

# Get the required poplog-specific tar files used for installation

echo "Running getpoplog.sh"

echo 'Download the latest "core" version of poplog with sources and documentation'
echo 'produced by Waldek Hebisch'
echo ''
echo 'wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/latest_poplog_base.tar.bz2'

wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/latest_poplog_base.tar.bz2

echo ''
echo 'Download core poplog documentation and tutorial files from Birmingham'
echo 'To be added to the poplog system in the $usepop/pop/{doc,help,teach,ref} directories'
echo ''
echo 'wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/docs.tar.bz2'
wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/docs.tar.bz2
echo ''

echo 'Download the poplog "packages" system from Birmingham'
echo '  to be added to the core poplog system,'
echo '  located in the $usepop/pop/packages sub-directory '

echo ''
echo 'wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/packages-V16.tar.bz2'
wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/packages-V16.tar.bz2


echo ''

echo 'Tar files containing the documentation files and the poplog "packages"'
echo 'are now ready to be unpacked'
echo ''

## later poplogout.sh and poplogut.csh could be included in the latest_poplog_base.tar.bz2'
##

echo 'Download poplogout.sh and poplogout.csh, for clearing environment variables'
echo '  to be located in poplog_base,'
echo '  to be located in the $usepop/pop/packages sub-directory '

echo ''
wget https://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/poplogout.sh
wget https://www.cs.bham.ac.uk/research/projects/poplog/V16/DL/poplogout.csh

echo ''
echo 'Download file to run inside poplog_base to build everything'
echo ''
echo 'wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/build_all.sh'
wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/build_all.sh

## 20 Aug 2020 Faulty build_all.sh fixed by Waldek Hebisch


echo ''
echo 'chmod 755 build_all.sh'
echo ''
chmod 755 build_all.sh
echo ''
echo ''

echo 'ls -ltr'
ls -ltr

echo ''

echo 'Unpack the poplog_base package, including contents downloaded from the'
echo 'github site'.
echo ''
echo 'tar xfj latest_poplog_base.tar.bz2'
tar xfj latest_poplog_base.tar.bz2

## echo ''
## echo 'Untarred - latest version of latest_poplog_base.tar.bz2'
## echo 'That creates the directory poplog_base with all the core files of poplog,'
## echo 'including files needed to create a minimal running pop11 system.'
## echo ''
## echo 'After that has been set up, additional documentation libraries will be added'
## echo 'And the packages file downloaded from
## echo '    http://www.cs.bham.ac.uk/research/projects/poplog/DL/packages-V16.tar.bz2'
## echo 'and unpacked, located at poplog_base/pop/packages.'
##

echo ''
echo 'Move poplogout.sh and poplogout.csh and build_all.sh to poplog_base'
mv poplogout.sh poplogout.csh build_all.sh poplog_base
echo ''
echo 'These files are  now in poplog_base'
## echo 'ls -ltr poplog_base'

ls -ltr poplog_base

echo ''
sleep 3
echo ''

## echo 'cd poplog_base and run build_all.sh'
##
## I could not make a .sh file work in this context
##
## echo ''
## echo 'cd poplog_base'

cd poplog_base

## NOPIE CHANGE 31 Dec 2019
## Note: for Arch linux and Debian Debian 9 and "testing"
## an extra instruction is needed at this point.
## This is controlled by the optional parameter -nopie when getpoplog-param.sh is invoked.

echo ""
echo "Checking whether -nopie parameter is present"
echo "parameter $1"
echo ""

if [[ $1 == "-nopie" ]];
then
    echo ''
    echo "patch 'asmout.p' to add '-no-pie' option"
    echo ''
    patch -p 1 < nopie.diff
    echo "PATCH DONE"
fi

echo ''
echo 'Now build Poplog - may take some time'
echo ''

## echo 'Running: build_all.sh .... script from Waldek Hebisch, to build'
## echo 'a new core poplog, including pop11, prolog, common lisp and poplog ml'
## echo 'with additional commands to unpack the documentation and packages'
## echo 'tar files from Birmingham'
echo ''
echo 'Running build_all.sh'

./build_all.sh

echo 'Installation complete!'
echo ''
echo 'Now change directory to poplog_base and use the contents of the file'
echo 'USEPOP to assign the path name to the environment variable $usepop'
echo ''
echo 'If you use sh or bash run this command IN THE poplog_base DIRECTORY:'
echo  '       export usepop=`cat USEPOP` '
echo ''
echo 'csh/tcsh users do this instead:'
echo '        setenv usepop `cat USEPOP`'
echo ''
echo 'In both cases this should then print out the full path name:'
echo '     echo $usepop'
echo ''
echo 'NB Now set up shell commands.'
echo ''
echo 'If using bash or sh as your shell set up paths and environment variables'
echo 'source $usepop/pop/com/poplog.sh'
echo ''
echo 'If using csh or tcsh as your shell set up paths and environment variables'
echo 'source $usepop/pop/com/poplog.csh'
echo ''
cd ..
echo 'Back to directory: '
pwd
echo ''
echo 'Fetching poplog startup instructions'
echo ''
wget http://www.cs.bham.ac.uk/research/projects/poplog/V16/INSTRUCTIONS.txt
echo ''
echo 'INSTRUCTIONS.txt downloaded'
echo ''
echo 'NB IF YOU INTEND TO USE MOTIF,'
echo 'MAKE SURE THE LINUX MOTIF LIBRARY HAS BEEN INSTALLED, E.G.'
echo 'motif-devel IN FEDORA, ETC, libmotif-dev IN UBUNTU AND openmotif IN ARCH'
echo ''
echo 'To link poplog with motif first make sure that $usepop is set to'
echo $usepop
echo ''
echo 'Then do'
echo ''
echo '$usepop/pop/src/newpop -link -x=-xm -norsv'
echo ''
echo 'Please read the document: INSTRUCTIONS.txt'
echo ''
echo 'HAVE FUN'
echo ''
exit
