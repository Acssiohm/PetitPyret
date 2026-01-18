type binop =
  | Badd | Bsub | Bmul | Bdiv  (* + - * / *)
  | Beq | Bneq | Blt | Ble | Bgt | Bge  (* == != < <= > >= *)
  | Band | Bor                          (* && || *)

type constant =
  | Cbool of bool
  | Cstring of string
  | Cint of int

type ttype =
  | Tident of string
  | Tfun of ttype list * ttype
  | Tparam of string * ttype list

type pos = Lexing.position

type expr =
  | Ecst of pos * constant
  | Eident of pos * string
  | Ebinop of pos * binop * expr * expr
  | Ecall of pos * expr * expr list
  | Elam of pos * (string * ttype) list * ttype * expr
  | Eblock of pos * stmt list
  | Ecases of pos * ttype * expr * (string * string list * expr) list
  | Eif of pos * expr * expr * expr option
and stmt =
  | Sassign of pos * string * expr
  | Sfun of pos * string * string list * (string * ttype) list * ttype * expr
  | Svar of pos * string * ttype option * expr * bool
  | Sexpr of pos * expr

type prog = stmt list
