#!/usr/bin/env bash

TEXT="$(cat jgross-thesis.log |
	grep -C 10 '^LaTeX Warning:\|on input line\|in paragraph at lines\|Xy-pic Warning:\|^Package [^ ]* Warning:' |
	tr '\r' '&' |
	tr '\n' '&' |
	sed 's/\&//g; s/\(\(on input line[^\.]*\| multiply defined\|multiply-defined labels\|Xy-pic Warning: [^\.]*\)\.\|in paragraph at lines [0-9-]*\([^\[\]]*\[\]\)*\)/\1\&/g; s/\(Underfull\|Overfull\)/\&\1/g; s/(Font)\s*/; /g; s/(biblatex)\s*/ /g' |
	tr '&' '\n' |
	grep -o 'LaTeX Warning:.*\|Xy-pic Warning:.*\|Font shape [^ ]* in size [^ ]* not available.*\|Package biblatex Warning: The following entry could not be found in the database: [^ ]*\|\(Under\|Over\)full ..box ([^)]*) in paragraph at lines.*' |
	grep -o 'MINOR.*\|TODO.*\|QUESTION.*\|Warning: Reference.*\|Warning: Citation.*\|Warning: Label.*\|Xy-pic Warning:.*\|Font shape [^ ]* in size [^ ]* not available.*\|Package [^ ]* Warning: .*\|\(Under\|Over\)full ..box ([^)]*) in paragraph at lines.*')$(echo; (cat jgross-thesis-biber.log |
	grep '^WARN'))"

((echo "$TEXT" | grep TODO);
 (echo "$TEXT" | grep 'QUESTION FOR ADAM');
 (echo "$TEXT" | grep 'QUESTION FOR READERS');
 (echo "$TEXT" | grep '^Warning:');
 (echo "$TEXT" | grep -v '^Warning:' | grep 'Warning:');
 (echo "$TEXT" | grep 'WARN');
 (echo "$TEXT" | grep 'Font shape');
 (echo "$TEXT" | grep -v 'TODO\|QUESTION FOR ADAM\|QUESTION FOR READERS\|Warning:\|Font shape\|WARN')) |
    grep --color=auto 'TODO:\|QUESTION FOR ADAM:\|QUESTION FOR READERS:\|Warning: Reference\|Warning: Citation\|Warning:\|WARN\|'
