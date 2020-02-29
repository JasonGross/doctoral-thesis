#!/bin/sh

lines="$(cat -)"
nlines=$(( ( 11 + $(echo "$lines" | wc -l) * 12 ) / 10 ))
# https://www.unix.com/shell-programming-and-scripting/32049-line-maximum-no-characters.html
nchars="$(echo "$lines" | awk ' length > max { max=length;row=NR } END{ print max}')"

echo '<svg xmlns="http://www.w3.org/2000/svg" width="'"$nchars"'em" height="'"$nlines"'em"><text x="0" y="0">'
echo "$lines" | sed s'|^\(.*\)$|<tspan x="0" dy="1.2em">\1</tspan>|g'
echo '</text></svg>'
