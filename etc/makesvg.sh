#!/usr/bin/env bash

# https://stackoverflow.com/a/246128/377022
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

lines="$(cat - | sed 's/^/~/g' | fold -w 80 -s | sed 's/^/  /g; s/^\s*~//g')"
nlines="$(( ( 11 + $(echo "$lines" | wc -l) * 12 ) / 10 ))em"
# https://www.unix.com/shell-programming-and-scripting/32049-line-maximum-no-characters.html
#nchars="$(echo "$lines" | awk ' length > max { max=length;row=NR } END{ print max}')em"
#nchars="100%"
nchars="$(echo "$lines" | (cd "$DIR" && ./stringwidth.py --max --int))em"

echo '<svg xmlns="http://www.w3.org/2000/svg" width="'"$nchars"'" height="'"$nlines"'"><text x="0" y="0">'
echo "$lines" | cat -v | sed 's/\&/&amp;/g; s/</\&lt;/g; s/>/\&gt;/g; s/"/\&quot;/g;'" s/'/\&apos;/g;"' s/^  /\&#160;\&#160;/g; s|^\(.*\)$|<tspan x="0" dy="1.2em">\1</tspan>|g'
echo '</text></svg>'
