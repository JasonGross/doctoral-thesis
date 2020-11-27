WinWait, D:\cygwin\usr\local\bin\mosh-jgross-transparent-rooster.sh, 
IfWinNotActive, D:\cygwin\usr\local\bin\mosh-jgross-transparent-rooster.sh, , WinActivate, D:\cygwin\usr\local\bin\mosh-jgross-transparent-rooster.sh, 
WinWaitActive, D:\cygwin\usr\local\bin\mosh-jgross-transparent-rooster.sh, 
Sleep, 100
Send, rlwrap{SPACE}sh{ENTER}
Send, cd{SPACE}$HOME/Documents/repos/fiat-crypto{ENTER}clear{ENTER}
Sleep, 1000
Send, src/ExtractionOCaml/unsaturated_solinas{SPACE}
Sleep, 1000
Send, curve25519{SPACE}
Sleep, 1000
Send, 64{SPACE}
Sleep, 1000
Send, 5{SPACE}
Sleep, 1000
Send, 2{SHIFTDOWN}6{SHIFTUP}255-19{SPACE}
Sleep, 1000
Send, |{SPACE}less
Sleep, 500
Send, {ENTER}
Sleep, 1000
; src/ExtractionOCaml/unsaturated_solinas curve25519 64 5 2^255-19 | fold -w $(tput cols) | wc -l
; echo $(($(~/Documents/repos/fiat-crypto/src/ExtractionOCaml/unsaturated_solinas curve25519 64 5 2^255-19 | fold -w $COLUMNS | wc -l) - $(tput lines) - 2))
Loop, 907
{
  Send, {DOWN}
;  Sleep, 50
}
Send, {END}
Sleep, 1000
Send, q
Sleep, 500
Send, {UP}{BACKSPACE}{BACKSPACE}{BACKSPACE}{BACKSPACE}{BACKSPACE}{BACKSPACE}{BACKSPACE}"{HOME}bash -c "time{SPACE}
Sleep, 500
Send, {ENTER}
Sleep, 3000
Send, {CTRLDOWN}d{CTRLUP}

