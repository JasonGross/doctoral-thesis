#!/bin/bash

# ttg.sh - Text To Graphics

# Dependency: 'Inkscape'
# Dependency: 'wc'
# Dependency: 'tr'

# Dependency: 'sed'
# Soft Dependency: 'Liberation' font-family

EXEC='/usr/bin/inkscape'
WC='/usr/bin/wc'
TR='/usr/bin/tr'

SED='/bin/sed'

BOX='0 0 200 90'

if [ -z "$1" ] ; then
  echo
  echo "Usage: ./ttg.sh <Images-Base-Name> [Color] [Dimensions] [Input-File]"
  echo "Default Dimensions are '200x90' (WxH)."
  echo "Assume characters are 8x15 ."
  echo
  echo "This script will read from standard input,"
  echo "until ^D is entered, unless Input-File is specified."
  echo "The default Color is spelled 'black' ."
  echo
  echo "Creates Images-Base-Name.png and Images-Base-Name.svg ."
  echo
  echo "Blank lines will simply be ignored (Wontfix)."
  echo
  echo "When read from standard input, text will be treated as if HTML."
  echo "Hence, < > & will produce error messages, unless escaped by user."
  echo "To write P -> Q , enter P -&gt; Q ."
  echo "But, spaces are preserved."
  echo
  echo "When read from Input-File, text is first escape-coded to"
  echo "Input-File-tmp , which will be deleted if it exists."
  echo "Therefore, special characters will appear as-they-are then."
  echo
  echo "Images-Base-Name-tmp.svg will also be deleted, if it exists."
  echo
  exit 1
fi

if [ ! -x "$TR" ] ; then
  echo "tr Not Installed"
  exit 1
fi

if [ ! -z `echo "$2" | $TR -d '[a-z]'` ] ; then
  echo "Inavlid Color Keyword"
  echo "Hint: Only one word with lower-case letters allowed."
  exit 1
fi

if [ ! -z "$3" ] ; then

  if [ ! -x "$SED" ] ; then
    echo "sed Not Installed"
    exit 1
  fi

  BOX=`echo "$3" | $SED 's/[^[0-9]]*/ /g;s/ \+/ /g;s/^ \+\| \+$//g'`
  BOX="0 0 ${BOX}"
fi

if [ ! -x "$WC" ] ; then
  echo "wc Not Installed"
  exit 1
fi

if [ `echo "$BOX" | $WC -w` -ne "4" ] ; then
  echo "Invalid Dimensions Format"
  exit 1
fi

if [ ! -z "$4" ] ; then
  if [ ! -r "$4" ] ; then
    echo "Input-File '${4}' Does Not Exist or Can't Be Read."
    exit 1
  fi
fi

# Basic Escaping

TAB=$'\t'

unset ESCAPED
if [ ! -z "$4" ] ; then
  ESCAPED="${4}-tmp"
  cat "$4" | $SED 's/\&/\&amp;/g' |
  $SED 's/</\&lt;/g' |
  $SED 's/>/\&gt;/g' |
  $SED 's/'"${TAB}"'/    /g' > "$ESCAPED"
fi

# Roll Document

tee /dev/null > "${1}-tmp.svg" <<!EOF
<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<!-- Generated with ttg.sh - by Dirk Mittler -->

!EOF

echo "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"${BOX}\">" \
  >> "${1}-tmp.svg"
echo "  <g>" \
  >> "${1}-tmp.svg"

echo "    <text x=\"10\" y=\"0\" xml:space=\"preserve\" style=\"fill:${2:-black}\"" \
  >> "${1}-tmp.svg"
echo "        font-size=\"12\" font-family=\"Liberation\">" \
  >> "${1}-tmp.svg"

while IFS= read -r LINE
do
  echo "      <tspan x=\"10\" dy=\"15\">${LINE}</tspan>" \
    >> "${1}-tmp.svg"
done < "${ESCAPED:-/dev/stdin}"

tee /dev/null >> "${1}-tmp.svg" <<!EOF
    </text>
  </g>
</svg> 
!EOF

if [ ! -z "$ESCAPED" ] ; then
  rm -f "$ESCAPED"
fi

# Generate Output

if [ ! -x "$EXEC" ] ; then
  echo "Inkscape Not Installed!"
  exit 1
fi

if [ ! -z "$3" ] ; then
  $EXEC -z -D --export-area-snap -e "${1}.png" \
    "${1}-tmp.svg"

else
  $EXEC -z -e "${1}.png" "${1}-tmp.svg"
fi

$EXEC -z -T -l "${1}.svg" "${1}-tmp.svg"

rm -f "${1}-tmp.svg"

exit 0
