#!/usr/bin/env bash

TEXT="$(cat jgross-thesis.log |
        sed 's/\&/AMPERSAND/g' |
        tr '\n' '&' |
        sed 's/\&([A-Za-z0-9\.]\+)\s\+/ /g' |
        tr '&' '\n' |
        sed 's/AMPERSAND/\&/g' |
	grep -v '^[ ()\.\*]*$\|^\* \|^\. \|^[)(<{ ]\+[^ )>}/]*/\|^)<<\|^[a-zA-Z0-9\.<>/-]*$\|^This is LuaTeX\|^ system commands\|^Lua module:\|^LaTeX2e\|^Document Class:\|^luaotfload | conf :\|^luaotfload | init :\|^Lua-only attribute \|^Inserting `luaotfload\|^luaotfload | main : initialization completed \|^Babel <\|^\\[^=]*=\|^Copyright given to author,\|^Package: luatex85\|^Single spaced\|^Course VI/VIII\|^File: \|^luaotfload | db : \|^Package: \|^LaTeX Font Info:    Redeclaring font encoding\|^LaTeX Font Info:    Try loading font information\|^LaTeX Font Info:    Overwriting \|^(Font).*-->\|LaTeX Info: Redefining\|^For additional information on amsmath\|^Package [^ ]* [Ii]nfo\|^Driver file for \|^Package pgfplots: loading \|^touch \|^rm -f \|^===== Image \|^. LaTeX info: .xparse/\|^. Defining command \|^. Redefining command\|^. I.m going to patch macro\|^ Style option: \|^. lualatex-math info:\|^. unicode-math info:\|^LaTeX Info: Thecontrolsequence\|^Proof Tree (bussproofs) style macros\|^LaTeX Font Info:    Checking defaults\|^LaTeX Font Info:    ... okay\|^(load luc:\|^ Xy-pic version \|^ Copyright \|^ Xy-pic is \|^Loading kernel: \|^\s*loaded) \|^ Xy-pic option: \|^Including \|^Excluding \|^ ABD: EveryShipout initializing macros\|^ direction,$\|^ utility macros;\|^ objects,$\|^ decorations;\|^ circles,$\|^\*\*.*\.tex$\|^\[Loading MPS to PDF converter\|^Output written on \|^PDF statistics: \|^ [0-9]* compressed objects\|^ [0-9]* named destinations\|^ [0-9]* words of extra memory\|^Here is how much of \|^\s\+[0-9,]*\s\+\(strings\|words\|hlist,\|pdf_action,\|availlists:\|avail lists:\|multiletter control sequences\|fonts\) \|^\s\+[0-9,inpbs]* stack positions\|^Package pgfplots external lib: loading complementary code for your PGF version.\|^\]\s*([^)/]*/\|^\]\s*(load luc:\|^<use \|^\s*<xymatrix ' |
        sed 's/^LaTeX Warning:/Warning:/g; s/^Warning: TODO/TODO/g; s/^Warning: QUESTION/QUESTION/g; s/^Warning: MINOR/MINOR/g')$(echo; (cat jgross-thesis-biber.log |
	grep '^WARN')))"

UNKNOWN_WORDS="$(make --no-print-directory spellcheck | tr '\n' ',' | sed 's/,$//g; s/,/, /g')"
if [ ! -z "${UNKNOWN_WORDS}" ]; then
    TEXT="$TEXT$(echo; echo -n 'Unknown Words'): ${UNKNOWN_WORDS}"
fi

PREFIX=""
for i in '^TODO' \
             '^QUESTION FOR ADAM' \
             '^QUESTION FOR READERS' \
             '^MINOR TODO' \
             '^MINOR QUESTION FOR ADAM' \
             '^MINOR QUESTION FOR READERS' \
             '^Unknown [wW]ords' \
             '^Warning: Label .* multiply defined' \
             '^Warning: Reference .* undefined' \
             '^Warning: Citation .* undefined' \
             '^Warning:' \
             'Warning:' \
             'WARN' \
             'Missing character:' \
             'Font shape' \
             '^warning' \
             'Font Info' \
             'luaotfload | aux : font no ' \
             'luaotfload | aux : no font ' \
             'luaotfload' \
             #
do
    FOUND_TEXT="$(echo "$TEXT" | grep "$i")"
    if [ "$i" == "Missing character:" ]; then
        FOUND_TEXT="$(echo "${FOUND_TEXT}" | sort)"
    fi
    PREFIX="${PREFIX}$(echo; (echo "${FOUND_TEXT}" | uniq))"
    TEXT="$(echo "$TEXT" | grep -v "$i")"
done

PREFIX="$(echo "$PREFIX" | grep -v '^\s*$')"

echo "$PREFIX" |
    grep --color=auto '^.*TODO:\|^.*QUESTION FOR ADAM:\|^.*QUESTION FOR READERS:\|^.*Warning: Reference\|^.*Warning: Citation\|^.*Warning:\|^.*WARN\|^.*warning\|'
echo "$TEXT"
