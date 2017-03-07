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

syn region ccnComment	start="/\*"  end="\*/" contains=ccnTodo
syn region ccnCommentL  start="//" skip="\\$" end="$" keepend contains=ccnTodo

syn match  ccnDelimiter         "->"
syn match  ccnDelimiter         ":-"
syn match  ccnDelimiter	        "[\[\]!?@#\~&|\^=<>%+-,;\:\.]"

"Regular keywords
syn keyword ccnStatement        and bool fork function procedure assume host not or pkt refine role send switch primary table view foreign key check unique references match state drop in any the var

syn keyword ccnTodo             contained TODO FIXME XXX

"Loops
"syn keyword ccnRepeat

"Conditionals
syn keyword ccnConditional      switch if else

"Constants
syn keyword ccnConstant         true false

"Storage class
"syn keyword ccnStorageClass

"Operators 
syn keyword ccnOperator	        default

"Keywords for ADTs
syn keyword ccnType	        bool string int bit typedef sink

syn sync lines=250

" Verilog-style numeric literals
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[bB]\s*[0-1?]\+\>"
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[oO]\s*[0-7?]\+\>"
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[dD]\s*[0-9?]\+\>"
syn match ccnNumber "\(\<\d\+\|\)'[sS]\?[hH]\s*[0-9a-fA-F?]\+\>"
syn match ccnNumber "\<[+-]\=[0-9]\+\(\.[0-9]*\|\)\(e[0-9]*\|\)\>"


if !exists("did_ccn_syntax_inits")
  let did_ccn_syntax_inits = 1
  hi link ccnStatement          Statement
  hi link ccnOperator           Operator
  hi link ccnType               Type
  hi link ccnComment            Comment
  hi link ccnCommentL           Comment
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
