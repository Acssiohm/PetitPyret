
%{
  open Ast
%}

/* Déclaration des tokens */

%token EOF
%token <Ast.constant> CST
%token <string> IDENT

%token BLOCK
%token CASES BRANCH (* "|" *)
%token IF ELSE
%token END
%token FOR FROM
%token FUN LAM
%token LEFTPAR UNSPACED_LEFTPAR RIGHTPAR
%token LEFTCHEV SPACED_LEFTCHEV
%token RIGHTCHEV SPACED_RIGHTCHEV
%token OR AND ADD SUB MUL DIV
%token CMP_EQ CMP_NEQ CMP_LE CMP_GE 
%token VAR EQUAL ASSIGN 
%token COMMA COLON
%token ARROW IMPLY

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <stmt list> file

%%

/* Règles de grammaire */

file:
  | s = stmt* EOF { s }

big_block: 
  | s = stmt ls = big_block {match ls with | Eblock(_,l) ->  Eblock ($startpos, s :: l) | _ -> failwith "big_block: expected Eblock" }
  | s = val_stmt {  Eblock($startpos, [s]) } 

small_block: 
  | s = def_stmt ls = small_block { match ls with | Eblock(_, l) -> Eblock ($startpos, s :: l) | _ -> failwith "small_block: expected Eblock" }
  | s = val_stmt { Eblock ($startpos, [s]) } 

stmt:
  | s = def_stmt { s }
  | s = val_stmt { s }

def_stmt:
  | FUN f = IDENT pt = option(left_chev l = separated_nonempty_list(COMMA, IDENT) RIGHTCHEV {l}) b = funbody { 
    let (params, rt, body) = b in 
    match pt with
      | None -> Sfun ($startpos, f, [], params, rt, body)
      | Some l -> Sfun ($startpos, f, l, params, rt, body)
    }
  | VAR v = IDENT t = option( COLON COLON  t = ttype {t} ) EQUAL b=bexpr { Svar ($startpos, v, t, b, true) }
  | v = IDENT t = option( COLON COLON  t = ttype {t} ) EQUAL b=bexpr { Svar ($startpos, v, t, b, false) } 

val_stmt:
  | id = IDENT ASSIGN b = bexpr  {Sassign ($startpos, id, b)}
  | b  = bexpr {Sexpr ($startpos, b)}

left_par:
  | LEFTPAR {} 
  | UNSPACED_LEFTPAR {} 

left_chev:
  | LEFTCHEV {}
  | SPACED_LEFTCHEV {}

right_chev:
  | RIGHTCHEV {}
  | SPACED_RIGHTCHEV {}

all_block:
  | COLON b = small_block {b}
  | BLOCK COLON b = big_block {b}

funbody:
  | UNSPACED_LEFTPAR params = separated_list(COMMA, param) RIGHTPAR ARROW rt = ttype b = all_block END {(params, rt, b)}

param:
  | id = IDENT COLON COLON t = ttype {(id, t)}

ttype:
  | id = IDENT vart = option( left_chev tl = separated_nonempty_list(COMMA, ttype) right_chev {tl} ) { 
    match vart with
      | None -> Tident ( id)
      | Some tl -> Tparam ( id, tl)
    }
  | left_par ta = separated_list(COMMA, ttype) ARROW tr = ttype RIGHTPAR { Tfun ( ta, tr) }

bexpr:
  | e = expr l = option(bexpr_list) { match l with
      | None -> e
      | Some (op, elist) -> List.fold_left (fun curr ei -> Ebinop($startpos, op, curr, ei)) e elist
    }

bexpr_list:
  | l = nonempty_list(CMP_EQ           e = expr {e} ) { (Beq , l) }
  | l = nonempty_list(CMP_NEQ          e = expr {e} ) { (Bneq, l) }
  | l = nonempty_list(CMP_GE           e = expr {e} ) { (Bge , l) }
  | l = nonempty_list(CMP_LE           e = expr {e} ) { (Ble , l) } 
  | l = nonempty_list(SPACED_LEFTCHEV  e = expr {e} ) { (Blt , l) }
  | l = nonempty_list(SPACED_RIGHTCHEV e = expr {e} ) { (Bgt , l) }
  | l = nonempty_list(ADD              e = expr {e} ) { (Badd, l) }
  | l = nonempty_list(SUB              e = expr {e} ) { (Bsub, l) }
  | l = nonempty_list(MUL              e = expr {e} ) { (Bmul, l) }
  | l = nonempty_list(DIV              e = expr {e} ) { (Bdiv, l) }
  | l = nonempty_list(AND              e = expr {e} ) { (Band, l) }
  | l = nonempty_list(OR               e = expr {e} ) { (Bor , l) }

expr:
  | c = CST { Ecst($startpos, c) }
  | id = IDENT { Eident($startpos, id) }
  | LEFTPAR b = bexpr RIGHTPAR {b}
  | f = IDENT args = nonempty_list( arg ) { List.fold_left (fun f' arg -> Ecall($startpos, f', arg)) (Eident ($startpos, f)) args }
  | st = structure {st}

structure: 
  | BLOCK COLON b = big_block END {b}
  | ib = if_block {ib}
  | LAM b = funbody {let (b1, b2, b3) = b in Elam ($startpos, b1, b2, b3)}
  | CASES left_par t = ttype RIGHTPAR e = bexpr COLON brs = small_branch* END {Ecases ($startpos, t, e, brs)}
  | CASES left_par t = ttype RIGHTPAR e = bexpr BLOCK COLON brs = big_branch* END {Ecases ($startpos, t, e, brs)}
  | FOR id = IDENT p = for_params ARROW rt = ttype b = all_block END { 
    let (args, a) = p in 
    let c = List.fold_left (fun f' arg -> Ecall($startpos, f', arg)) (Eident ($startpos, id)) args in
    Ecall ($startpos, c , (Elam($startpos, List.map fst a, rt, b))::(List.map snd a)) }

for_params:
    | arg1 = for_calls params = for_params {let (args, a) = params in (arg1 :: args, a)}
    | a = for_dec {([], a)}
for_calls:
  | UNSPACED_LEFTPAR args = separated_nonempty_list(COMMA, bexpr) RIGHTPAR {args}
  | UNSPACED_LEFTPAR RIGHTPAR {[]}
for_dec:
  | UNSPACED_LEFTPAR l = separated_nonempty_list(COMMA, from) RIGHTPAR {l}
  | UNSPACED_LEFTPAR RIGHTPAR {[]}

if_block:
  | IF e = bexpr COLON b = small_block ELSE bi = small_else_if { Eif ($startpos, e, b, Some bi) }
  | IF e = bexpr BLOCK COLON b = big_block ELSE bi = big_else_if {  Eif ($startpos, e, b, Some bi) }

small_else_if:
  | IF e = bexpr COLON b = small_block ELSE bi = small_else_if { Eif ($startpos, e, b, Some bi) } 
  | IF e = bexpr COLON b = small_block END { Eif($startpos, e, b, None) } 
  | COLON b = small_block END { b } 

big_else_if:
  | IF e = bexpr COLON b = big_block ELSE bi = big_else_if { Eif($startpos, e, b, Some bi)} 
  | IF e = bexpr COLON b = big_block END {Eif($startpos, e, b, None)} 
  | COLON b = big_block END {b} 

arg:
  | UNSPACED_LEFTPAR l = separated_list(COMMA, bexpr) RIGHTPAR {l}

small_branch:
  | BRANCH x = IDENT l = option(branch_params)  IMPLY b = small_block {match l with | Some l' -> (x, l', b) | None -> (x, [], b) }
big_branch:
  | BRANCH x = IDENT l = option(branch_params) IMPLY b = big_block {match l with | Some l' -> (x, l', b) | None -> (x, [], b)}

branch_params:
  | left_par l = separated_nonempty_list(COMMA, IDENT) RIGHTPAR {l}

from:
  | x = param FROM e = bexpr {(x,e)}
