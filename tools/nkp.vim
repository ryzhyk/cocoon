" Vim syntax file
" Language:	NetKAT+
" Filenames:    *.nk+
"
" Place this file (or a link to it) under ~/.vim/syntax and add
" the following line to your .vimrc to enable syntax highlighting 
" automatically for NetKAT+ files:
" au BufRead,BufNewFile *.nk+             set filetype=nkp

syn clear

syn case match

"Comments in LOTOS are between (* and *)
syn region nkpComment	start="(\*"  end="\*)" contains=nkpTodo

"Operators !, |, =, :=, %, +
syn match  nkpDelimiter         ":="
syn match  nkpDelimiter	        "[\[\]!?@#\~&|\^=<>%+-,;\:\.]"

"Regular keywords
syn keyword nkpStatement        and bool case default endrefine filter function container not or pkt refine role struct switch

syn keyword nkpTodo             contained TODO FIXME XXX

"Loops
"syn keyword nkpRepeat

"Conditionals
syn keyword nkpConditional      case

"Constants
syn keyword nkpConstant         true false pkt

"Storage class
"syn keyword nkpStorageClass

"Operators from the Abstract Data Types in IS8807
syn keyword nkpOperator	        default true false 

"Keywords for ADTs
syn keyword nkpType	        bool uint struct typedef

syn sync lines=250

" Verilog-style numeric literals
syn match nkpNumber "\(\<\d\+\|\)'[sS]\?[bB]\s*[0-1?]\+\>"
syn match nkpNumber "\(\<\d\+\|\)'[sS]\?[oO]\s*[0-7?]\+\>"
syn match nkpNumber "\(\<\d\+\|\)'[sS]\?[dD]\s*[0-9?]\+\>"
syn match nkpNumber "\(\<\d\+\|\)'[sS]\?[hH]\s*[0-9a-fA-F?]\+\>"
syn match nkpNumber "\<[+-]\=[0-9]\+\(\.[0-9]*\|\)\(e[0-9]*\|\)\>"


if !exists("did_nkp_syntax_inits")
  let did_nkp_syntax_inits = 1
  hi link nkpStatement		Statement
  hi link nkpOperator		Operator
  hi link nkpType		Type
  hi link nkpComment		Comment
  hi link nkpDelimiter          String
  hi link nkpConstant           Constant
  hi link nkpRepeat             Repeat
  hi link nkpConditional        Conditional
  hi link nkpTodo               Todo
  hi link nkpNumber             Number
  hi link nkpStorageClass       StorageClass
endif

let b:current_syntax = "nkp"

" vim: ts=8
