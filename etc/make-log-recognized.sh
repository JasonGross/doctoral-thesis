#!/usr/bin/env bash

TEXT="$(cat jgross-thesis.log |
	grep -v '^[ ()\.\*]*$\|^This is LuaTeX\|^ system commands\|^Lua module:\|^LaTeX2e\|^Document Class:\|^luaotfload | conf :\|^luaotfload | init :\|^Lua-only attribute \|^Inserting `luaotfload\|^luaotfload | main : initialization completed \|^Babel <\|^\\[^=]*=\|^Copyright given to author,\|^Package: luatex85\|^Single spaced\|^Course VI/VIII\|^File: \|^luaotfload | db : \|^Package: \|^LaTeX Font Info:    Redeclaring font encoding\|^LaTeX Font Info:    Try loading font information\|^LaTeX Font Info:    Overwriting \|^(Font).*-->\|LaTeX Info: Redefining\|^For additional information on amsmath\|^[)( ]\+[^ )/]*/\|^)<<\|^Package [^ ]* [Ii]nfo\|^Driver file for \|^Package pgfplots: loading \|^touch \|^rm -f \|^===== Image \|^. LaTeX info: .xparse/\|^. Defining command \|^. Redefining command\|^. I.m going to patch macro\|^ Style option: \|^. lualatex-math info:\|^. unicode-math info:\|^LaTeX Info: Thecontrolsequence\|^Proof Tree (bussproofs) style macros\|^LaTeX Font Info:    Checking defaults\|^LaTeX Font Info:    ... okay\|^(load luc:')$(cat jgross-thesis-biber.log |
	grep '^WARN'))"

echo "$TEXT"
