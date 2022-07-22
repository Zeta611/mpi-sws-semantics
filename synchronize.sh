#!/bin/bash
set -e

#### CONFIGURATION #######################################################

MAIN_DIR="syncro"
MAIN_REPO_URL=git-rts@gitlab.mpi-sws.org:FP/semantics-code.git
MAIN_BRANCH="inline-solutions"


#### UTILITIES ###########################################################

# Usage: clone_repo $url $dir $branch
function clone_repo {
    URL=$1
    DIR=$2
    BRANCH=$3

    ## Clone enough history so that we're likely to have the commit
    git clone --quiet -b ${BRANCH} --depth 20 ${URL} "${DIR}"
    #cd "${DIR}"
    rm -rf "${DIR}/.git*"
    rm -rf "${DIR}/.gitignore"
    rm -rf "${DIR}/.gitattributes"
    rm -rf "${DIR}/.git"
    #cd ..
}

#### INITITIALIZATION ####################################################

# Deleting previously generated files.
echo "Deleting previously generated files (no backup)."
rm -rf ${MAIN_DIR}

#### PREPARE FILES ####################################################

# Clone the repo
clone_repo ${MAIN_REPO_URL} ${MAIN_DIR} ${MAIN_BRANCH}
cd ${MAIN_DIR}

# remove files that should not be here
find .  -maxdepth 1  ! \( -name '_CoqProject' -o -name 'README.md' -o -name 'STRUCTURE.md' -o -name 'Makefile' -o -name '*.opam' \) -type f -exec rm {} \;
find .  -maxdepth 1  ! \( -name 'theories' -o -name '.' -o -name '..' \) -type d -exec rm -rf {} \;

# remove files ending with _sol.v
find theories -name '*_sol.v' -type f -exec rm {} \;

# remove directories ending with _sol
find theories -type d -name '*_sol' -type d -prune -exec rm -rf {} \;

# remove solution-only segments and uncomment exercise-only segments
find theories -name '*.v' -type f -exec perl -0777 -i -p -e 's/(.*)\(\*[[:blank:]]*<solution-only>[[:blank:]]*\*\)(:?[[:blank:]]*[[:space:]])*(?:\n|.)*?\(\*[[:blank:]]*<\/solution-only>[[:blank:]]*\*\)(.*)\n?/$1$3/g; s/(.*)\(\*.*<exercise-only>(:?[[:blank:]]*[[:space:]])*((:?\n|.)*?)<\/exercise-only>(.*)\*\).*/$1$2$3/g; s/(.*)\(\*[[:blank:]]*<solution>[[:blank:]]*\*\)(:?[[:blank:]]*[[:space:]])*(?:\n|.)*?\(\*[[:blank:]]*<\/solution>[[:blank:]]*\*\)(.*)\n?/$1\  (\*FIXME\*\)\nAdmitted\.\n$3/g' {} \;


cd ..

#### FINALIZING ##############################################################

# Final message.
echo -e "Synchronized to folder [\e[32m${MAIN_DIR}\e[0m]."

# TODO: copy to current working dir and push it
