#!/bin/bash
set -e

#### CONFIGURATION #######################################################

MAIN_DIR="syncro"
MAIN_REPO_URL=git-rts@gitlab.mpi-sws.org:FP/semantics-code.git
MAIN_BRANCH="inline-solutions"

# The text to replace <solution> environments with.
# The regex variable $1 is bound to the current indentation.
DEFAULT_TEMPLATE_TEXT="\$1  \(\* FIXME: exercise \*\)\n\$1Admitted\.\n"

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

# remove solution files from CoqProject
perl -0777 -i -p -e 's/.*_sol\/.*\n//g; s/.*_sol\.v\n//g' _CoqProject

# assemble the regex for generating the exercises
# note: we need to escape $ for variables bound by the regex so bash doesn't replace them

# remove segments '(* <solution-only> *) .... (* </solution-only> *)'
remove_solution_regex="s/(.*)\(\*[[:blank:]]*<solution-only>[[:blank:]]*\*\)(:?[[:blank:]]*[[:space:]])*(?:\n|.)*?\(\*[[:blank:]]*<\/solution-only>[[:blank:]]*\*\)(.*)\n?/\$1\$3/g"
# replace segments '(* <exercise-only> my_exercise </exercise-only> *)' by 'my_exercise'
put_exercise_regex="s/(.*)\(\*.*<exercise-only>(:?[[:blank:]]*[[:space:]])*((:?\n|.)*?)<\/exercise-only>(.*)\*\).*/\$1\$2\$3/g"
# Replace segments '(* <solution> *) ... (* <solution> *) by the contents of DEFAULT_TEMPLATE_TEXT
# For proper indentation, this assumes that the leading '(* <solution> *)' is on its own line, and aligned to the current base indentation (e.g. aligned with 'Proof.').
# DEFAULT_TEMPLATE_TEXT has access to this indentation at regex variable $1
replace_solution_regex="s/(.*)\(\*[[:blank:]]*<solution>[[:blank:]]*\*\)(:?[[:blank:]]*[[:space:]])*(?:\n|.)*?\(\*[[:blank:]]*<\/solution>[[:blank:]]*\*\)(.*)\n?/${DEFAULT_TEMPLATE_TEXT}\$3/g"
# assmble the full regex doing all of these things
full_regex="${remove_solution_regex}; ${put_exercise_regex}; ${replace_solution_regex}"
find theories -name '*.v' -type f -exec perl -0777 -i -p -e "$full_regex" {} \;


cd ..

#### FINALIZING ##############################################################

# Final message.
echo -e "Synchronized to folder [\e[32m${MAIN_DIR}\e[0m]."

# TODO: copy to current working dir and push it
