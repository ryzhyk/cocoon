" Vim syntax file
" Language:	Cocoon
" Filenames:    *.ccn
"
" Place this file (or a link to it) under ~/.vim/syntax and add
" the following line to your .vimrc to enable syntax highlighting 
" automatically for Cocoon files:
" au BufRead,BufNewFile *.ccn             set filetype=ccn

syn clear

syn case match

"Comments in LOTOS are between (* and *)
syn region ccnComment	start="(\*"  end="\*)" contains=ccnTodo

"Operators !, |, =, :=, %, +
syn match  ccnDelimiter         ":="
syn match  ccnDelimiter	        "[\[\]!?@#\~&|\^=<>%+-,;\:\.]"

"Regular keywords
syn keyword ccnStatement        and bool case default endrefine filter fork function assume host havoc let not or pkt refine role send struct switch var

syn keyword ccnTodo             contained TODO FIXME XXX

"Loops
"syn keyword ccnRepeat

"Conditionals
syn keyword ccnConditional      case if then else

"Constants
syn keyword ccnConstant         true false pkt

"Storage class
"syn keyword ccnStorageClass

"Operators from the Abstract Data Types in IS8807
syn keyword ccnOperator	        default true false 

"Keywords for ADTs
syn keyword ccnType	        bool uint struct typedef

syn sync lines=250

" Verilog-style numeric literals
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[bB]\s*[0-1?]\+\>"
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[oO]\s*[0-7?]\+\>"
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[dD]\s*[0-9?]\+\>"
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[hH]\s*[0-9a-fA-F?]\+\>"
syn match ccnNumber "\<[+-]\=[0-9]\+\(\.[0-9]*\|\)\(e[0-9]*\|\)\>"


if !exists("did_ccn_syntax_inits")
  let did_ccn_syntax_inits = 1
  hi link ccnStatement		Statement
  hi link ccnOperator		Operator
  hi link ccnType		Type
  hi link ccnComment		Comment
  hi link ccnDelimiter          String
  hi link ccnConstant           Constant
  hi link ccnRepeat             Repeat
  hi link ccnConditional        Conditional
  hi link ccnTodo               Todo
  hi link ccnNumber             Number
  hi link ccnStorageClass       StorageClass
endif

let b:current_syntax = "ccn"

" vim: ts=8
