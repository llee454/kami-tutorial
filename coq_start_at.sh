#!/bin/bash
# This script accepts two arguments: FILE, a Coq Vernacular file;
# and LINE, a number; starts coqtop and compiles the first LINE lines
# in FILE.

while getopts ":hv" option
do
  case $option in
    h) cat <<- EOF
Usage: coq_start_at.sh [options] FILE LINE

Accepts two arguments: FILE, a Coq Vernacular file path; and LINE, a
line number; starts coqtop and compiles the first LINE lines of FILE.

Example

> coq_start_at.sh -v example.v 40

Starts coqtop and compiles the first 40 lines of example.v.

Author

Larry D. Lee Jr. <llee454@gmail.com>
EOF
      exit 0;;
    v) verbose=1 ;;
  esac
done
shift $((OPTIND - 1))

coqtop_args="-Q Kami Kami -Q bbv/src/bbv bbv -Q coq-record-update/src/ RecordUpdate"
# coqtop_args=""

# Accepts one argument: emsg, an error message string; and prints
# the given error message.
function error () {
  local emsg=$1
  (>&2 echo -e "\033[41mError:\033[0m $emsg")
  exit 1
}

if [[ $# < 1 ]]
then
  error "Invalid command line. The FILE argument is missing."
else
  file=$1
fi

if [[ $# < 2 ]]
then
  error "Invalid command line. The LINE argument is missing."
else
  line=$2
fi

# Accepts one argument: message, a message string; and prints the
# given message iff the verbose flag has been set.
function display () {
  local message=$1

  if [[ $verbose == 1 ]]
  then
    echo -e "\033[44mNotice:\033[0m $message"
  fi
}

tmp_file=$(mktemp)
mv $tmp_file $tmp_file.v
tmp_file="$tmp_file.v"

cmd="head --lines $line $file > $tmp_file; rlwrap coqtop $coqtop_args -lv $tmp_file"
display "Cmd $cmd"
eval $cmd
