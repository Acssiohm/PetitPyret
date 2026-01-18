open Format
open X86_64
open Ast   
open Typer 
open Builtin

type aexpr =
  | AEcst of constant 
  | AEident of int 
  | AEclos_ident of int 
  | AEident_builtin of string
  | AEbinop of binop * aexpr * aexpr * typ 
  | AEcall of aexpr * aexpr list 
  | AElam of (bool * int * int) list * aexpr * int 
  | AEblock of astmt list 
  | AEcases of aexpr * aexpr * int * int * aexpr 
  | AEif of aexpr * aexpr * aexpr 
and astmt =
  | ASassign of bool * int * aexpr * int
  | ASfun of string * int * ( bool * int * int ) list * aexpr * int 
  | ASvar of int * aexpr * int
  | ASexpr of aexpr * int

exception VarUndef of string

module Smap = Map.Make(String)

type local_env = int Smap.t

type closure = { 
  (* env associate a key with : 
    - None : if it's in the non-local environnment but not used localy
    - Some pos : if it was used in the local environnement and put to the position pos
    - not in the map if it's not even in the non-local environnement *)
  env : int option Smap.t; 
  (* pos is the first available position - the position where will be the next enclosed key *)
  pos : int 
}

let non_localy_exists ( x : string ) (clos : closure )  =
  Smap.mem x clos.env
let enclose (x : string) (clos : closure) : closure * int =
  assert (non_localy_exists x clos);
  match Smap.find x clos.env with
    | None -> {env = Smap.add x (Some clos.pos) clos.env; pos = clos.pos+var_size }, clos.pos
    | Some pos -> clos, pos 

let is_enclosed (x : string) (clos : closure) : bool =
  assert (non_localy_exists x clos);
  Smap.find x clos.env <> None

let position_closure (x : string) (clos : closure) : int =
  assert (Smap.mem x clos.env);
  match Smap.find x clos.env with 
    | None -> raise Not_found
    | Some a -> a

let empty_sub_closure (env : local_env) (prev_clos : closure): closure =
  { env = (Smap.union (fun k -> assert false) (Smap.map (fun _ -> None) env ) (Smap.map (fun _ -> None) prev_clos.env )  ); pos = 0}
let empty_closure =
  { env = Smap.empty; pos = 0}
 

(******************************************************************************)
(***************** PHASE 1 : SPACE ALLOCATION OF VARIABLES ********************)
(******************************************************************************)

let rec alloc_expr (env: local_env) (fpcur: int) (clos : closure)  = function
  | TEcst (c) -> 
    AEcst (c), fpcur, clos
  
  | TEbinop(op, e1, e2, t) -> 
    let (e1', fsize1, clos1) = alloc_expr env fpcur clos e1 in
    let (e2', fsize2, clos12) = alloc_expr env fpcur clos1 e2 in
    AEbinop(op, e1', e2', t), max fsize1 fsize2, clos12
  
  | TEif( c, e1, e2) -> 
    let (e1', fsize1, clos1  ) = alloc_expr env fpcur clos   e1 in
    let (e2', fsize2, clos12 ) = alloc_expr env fpcur clos1  e2 in
    let (c',  fsize3, clos123) = alloc_expr env fpcur clos12 c in
      AEif(c', e1', e2'), max fsize1 (max fsize2 fsize3), clos123
  
  | TEident(x) -> 
    if Smap.mem x env then
      AEident(Smap.find x env), fpcur, clos
    else if non_localy_exists x clos then
      let (clos', pos) = enclose x clos in 
      AEclos_ident(pos), fpcur, clos'
    else if is_global_val x then 
      AEident_builtin( x ), fpcur, clos
    else failwith ("fonction pas implémentée : "^x)
  
  | TEblock(stmt_list) -> 
    let (rev_stmt_list', _, fsize_tot, clos_tot) = List.fold_left 
      (fun (rev_stmt_list, env_curr, fsize_curr, clos_curr) stmt_curr -> 
          let (stmt_curr', env', fsize', clos') = alloc_stmt env_curr fsize_curr clos_curr stmt_curr in 
          (stmt_curr'::rev_stmt_list, env', fsize', clos')) 
      ([], env, fpcur, clos) stmt_list
    in  AEblock(List.rev rev_stmt_list'), fsize_tot, clos_tot
  
  | TEcall(f, l) -> 
    let f', fpcur, clos = alloc_expr env fpcur clos f in 
    let (rev_arg_list, fsize_tot, clos_tot) = List.fold_left 
      (fun (l', fsize, clos) e -> 
        let e', fsize', clos = alloc_expr env fpcur clos e in 
        (e'::l', max fsize fsize', clos) ) 
      ([], fpcur, clos) l in 
    AEcall (f', List.rev rev_arg_list), fsize_tot, clos_tot
  
  | TElam(l, e) -> 
    let n = List.length l in 
    let env', a = List.fold_left (fun (env, pos) x -> (Smap.add x pos env, pos - var_size ) ) (Smap.empty, (n + 2)*var_size) l in
    assert (a = 2*var_size);
    let  (e', fpmax, ferm, clos') = alloc_funbody env' env clos e in 
    AElam (ferm, e', fpmax), fpcur, clos'
  
  | TEcases(e, b_empty, x, y, b_link) -> 
    let (e', fsize1, clos1 ) = alloc_expr env fpcur clos e in
    let (b_empty', fsize2, clos12 ) = alloc_expr env fpcur clos1 b_empty in
    let (b_link',  fsize3, clos123 ) = alloc_expr (Smap.add y (-fpcur - 2*var_size) (Smap.add x (-fpcur-var_size) env)) (fpcur + 2*var_size ) clos12 b_link in
    AEcases(e', b_empty', -fpcur-var_size, -fpcur - 2*var_size, b_link' ), max fsize1 (max fsize2 fsize3), clos123

and alloc_stmt (env : local_env) (fpcur : int) (clos : closure )  = function
  | TSexpr  (e, _)    -> let e', fpmax, clos = alloc_expr env fpcur clos e in ASexpr(e', fpmax-fpcur), env, fpcur, clos 
  | TSvar   (x, e)    -> let e', fpmax, clos = alloc_expr env fpcur clos e in ASvar(-fpcur-var_size, e', fpmax-fpcur), Smap.add x (-fpcur-var_size) env, fpcur+var_size, clos
  | TSassign(x, e)    -> 
    let e', fpmax, clos = alloc_expr env fpcur clos e in
    if Smap.mem x env then
      ASassign( true, Smap.find x env , e', fpmax-fpcur), env, fpcur, clos
    else
      let clos', pos = enclose x clos in
         ASassign(  false, pos , e', fpmax-fpcur), env, fpcur, clos'
  | TSfun   (f, l, e) ->
    let n = List.length l in 
    let env', a = List.fold_left (fun (env, pos) x -> (Smap.add x pos env, pos - var_size ) ) (Smap.empty, (n + 2)*var_size) (l @ [f] ) in
    assert (a = var_size);
    let  (e', fsize, ferm, clos) = alloc_funbody env' env clos e in 
    ASfun (f, -fpcur-var_size, ferm, e', fsize), Smap.add f (-fpcur-var_size) env, fpcur + var_size, clos
and alloc_funbody (funbody_env : local_env) (env : local_env) ( clos : closure) (e : texpr) =
  (* For the funbody the non-local variables are the current local and non-local variables 
  thus (empty_sub_closure env clos) creates an empty closure where all those are available 
  Moreover, the stack starts at rbp+var_size because a space is reserved for rbx *)
  let e', fpmax, sub_clos = alloc_expr funbody_env var_size (empty_sub_closure env clos) e in
  (* We add to our closure, the variable used inside the funbody *)
  let clos = Smap.fold ( fun k v clos -> if v <> None && non_localy_exists k clos then fst (enclose k clos) else clos ) sub_clos.env clos in
  (* Deduce the list of positions where to find the variable to be copied in the closure environnment of the function 
  they are of the form (is_local, copy_from_offset, copy_to_offset) where is_local says if it's on our the stack or in our closure *)
  let closure_moves = List.filter_map (
    fun (x, pos) ->
      match pos with 
      | None -> None (* the variable is not used inside e : don't need it *)
      | Some pos' -> Some (if Smap.mem x env then (true, Smap.find x env, pos') else (false, position_closure x clos, pos') )
    ) (Smap.bindings sub_clos.env) in 
  (e', fpmax, closure_moves, clos)

let alloc p = let (stmt_list_rev, _, fsize_tot) = 
  List.fold_left ( fun (stmt_list_rev_cur, env_cur, fpcur) stmt_cur -> 
    let (stmt_cur', env', fpcur', clos) = alloc_stmt env_cur fpcur empty_closure stmt_cur in 
    assert (clos = empty_closure);
    (stmt_cur'::stmt_list_rev_cur, env', fpcur')  ) 
    ([], Smap.empty, 0) p in 
  (List.rev stmt_list_rev, fsize_tot)



(******************************************************************************)
(*********************** PHASE 2 : CODE PRODUCTION ****************************)
(******************************************************************************)


let create_id = let r = ref 0 in fun () -> incr r; string_of_int !r

let (+++) = fun (a, b) (c, d) -> (a++c, b++d) 
let (++-) = fun (a, b) d -> (a, b) +++ (nop, d)
let rec compile_expr = function
  | AEcst(c) -> let (size, mov_data) = match c with
    | Cbool b -> 
      ( 2 * var_size, 
      movq (imm id_Boolean) (ind rax) 
      ++ movq (imm (if b then 1 else 0)) (ind ~ofs:var_size rax)  )
    | Cint x -> (* immediates of 64bits cannot be moved directly to memory, so we use an intermediate register : r11 *)
      ( 2 * var_size, 
      movq (imm id_Number) (ind rax) 
      ++ movq (imm x) !%r11 ++ movq !%r11 (ind ~ofs:var_size rax)  ) 
    | Cstring s -> let n = String.length s in
      let mov_str = Array.fold_left (++) nop (Array.init n (fun i -> movb (imm (int_of_char s.[i])) (ind ~ofs:(2*var_size+i) rax) ) ) in 
      ( 2*var_size + n + 1, 
      movq (imm id_String) (ind rax) 
      ++ leaq (ind ~ofs:(2*var_size) rax) r11 ++ movq !%r11 (ind ~ofs:var_size rax) 
      ++ mov_str 
      ++ movb (imm 0) (ind ~ofs:(2*var_size+n) rax) )  
    in
    nop, 
    movq (imm size) !%rdi ++
    call (get_safe_label "internal" "my_malloc") ++
    mov_data ++
    pushq !%rax 

  | AEbinop (Badd, e1, e2, t) when head t = TString -> 
    compile_expr e1 
    +++ compile_expr e2 
    ++- (popq rdx ++ popq rcx ++ 
    (* Calcul de la taille pour malloc *)
    movq (imm (2*var_size+1)) !%rax ++ (* +varsize +1 pour le header et le caractère NULL *)
    movq (ind ~ofs:var_size rcx ) !%rdi ++
    call ( get_safe_label "internal" "add_strlen" ) ++ 
    movq (ind ~ofs:var_size rdx ) !%rdi ++
    call ( get_safe_label "internal" "add_strlen" ) ++
    (* Allocation de la mémoire - en prenant soin de sauvegarder les callee saved *)
    pushq !%rcx ++
    pushq !%rdx ++
    movq !%rax !%rdi ++ 
    call ( get_safe_label "internal" "my_malloc" ) ++
    popq rdx ++
    popq rcx ++
    (* l'adresse de la valeur est retournée ici car déjà connue *)
    pushq !%rax ++ 
    (* on remplit le header*)
    movq (imm id_String) (ind rax) ++
    leaq (ind ~ofs:(2*var_size) rax) r11 ++
    movq !%r11 (ind ~ofs:var_size rax) ++
    (* on procède à la copie des deux string l'un après l'autre*)
    movq (ind ~ofs:var_size rax) !%rax ++
    movq (ind ~ofs:var_size rcx) !%rdi ++
    call ( get_safe_label "internal" "copy_str" ) ++
    movq (ind ~ofs:var_size rdx) !%rdi ++
    call ( get_safe_label "internal" "copy_str" ) ++
    (* on met le caractère NULL à la fin *)
    movb (imm 0) (ind rax))

  | AEbinop(Beq | Bneq as op, e1, e2, _ ) ->
    compile_expr e1 
    +++ compile_expr e2 
    ++- popq rsi 
    ++- popq rdi
    (* compare the two values*)
    ++- call ( get_safe_label "internal" "test_equality" ) 
    ++- (if op = Bneq then notq !%rax ++ andq (imm 1) !%rax else nop) (* negate the answer if it's Bneq *)
    (* allocate a variable for the result *)
    ++- pushq !%rax (* save the result *)
    ++- movq (imm (2 * var_size)) !%rdi 
    ++- call ( get_safe_label "internal" "my_malloc" ) 
    ++- popq r11 (* recover the result *)
    (* fill the result *)
    ++- movq !%r11 (ind ~ofs:var_size rax) 
    ++- movq (imm id_Boolean) (ind rax) 
    ++- pushq !%rax
    
  | AEbinop(Band | Bor as op, e1, e2, _) ->
    let id = create_id () in 
    (* test the value of e1, eventually return the lazy result *)
    compile_expr e1 
    ++- popq rax 
    ++- movq (ind ~ofs:var_size rax) !%rax 
    ++- cmpq (imm 0) !%rax 
    ++- (if op = Band then je else jne) ( (get_safe_label ("lazy_binop"^id) "answer_found")) (* go for the lazy result *) 
    (* test the value of e2 and combine it with the previous one *)
    ++- pushq !%rax (* save the result *)
    +++ compile_expr e2
    ++- popq rcx
    ++- popq rax
    ++- movq (ind ~ofs:var_size rcx) !%rcx
    ++- (if op = Band then andq else orq) !%rcx !%rax
    
    ++- safe_label ("lazy_binop"^id) "answer_found"
    ++- pushq !%rax (* save result *)
    (* create the boolean variable *)
    ++- movq (imm (2*var_size)) !%rdi 
    ++- call ( get_safe_label "internal" "my_malloc") 
    ++- movq (imm id_Boolean) (ind rax)
    ++- popq rcx (* recover result *)
    ++- movq !%rcx (ind ~ofs:var_size rax)
    (* return thr value *)
    ++- pushq !%rax

  | AEbinop (op, e1, e2, t) when not (head t = TString || op = Beq || op = Bneq ) -> 
    compile_expr e1 
    +++ compile_expr e2 
    ++- ( popq rcx ++ popq rax ++ (*deux registres callee saved*)
    movq (ind ~ofs:var_size rax) !%rax ++ 
    movq (ind ~ofs:var_size rcx) !%rcx ++
    (* On calcul dans rax la nouvelle valeur et place dans rcx le type de celle ci*)
    (match op with
    | Bdiv -> cqto ++ idivq !%rcx ++ movq (imm id_Number) !%rcx
    
    | Badd -> addq  !%rcx !%rax ++ movq (imm id_Number) !%rcx
    | Bsub -> subq  !%rcx !%rax ++ movq (imm id_Number) !%rcx
    | Bmul -> imulq !%rcx !%rax ++ movq (imm id_Number) !%rcx

    | Blt  -> cmpq !%rcx !%rax ++ movq (imm 0) !%rax ++ setl  !%al ++ movq (imm id_Boolean) !%rcx
    | Ble  -> cmpq !%rcx !%rax ++ movq (imm 0) !%rax ++ setle !%al ++ movq (imm id_Boolean) !%rcx
    | Bgt  -> cmpq !%rcx !%rax ++ movq (imm 0) !%rax ++ setg  !%al ++ movq (imm id_Boolean) !%rcx
    | Bge  -> cmpq !%rcx !%rax ++ movq (imm 0) !%rax ++ setge !%al ++ movq (imm id_Boolean) !%rcx
    
    | Band | Bor -> assert false 
    | Beq | Bneq -> assert false ) ++
    (* on sauvegarde les callee saved avant malloc *)
    pushq !%rax ++
    pushq !%rcx ++
    (* on a besoin de deux mots mémoire : type | valeur *)
    movq (imm (2*var_size)) !%rdi ++
    call ( get_safe_label "internal" "my_malloc") ++
    (* on récupère et copie le type *)
    popq rcx ++
    movq !%rcx (ind rax) ++
    (* on récupère et copie la valeur*)
    popq rcx ++
    movq !%rcx (ind ~ofs:var_size rax) ++
    (* on renvoie l'adresse donnée par malloc *)
    pushq !%rax)
  
  | AEif(c, e1, e2) ->
    let id = create_id() in
    (nop, nop)
    (* calculate the condition *)
    +++ compile_expr c 
    ++- popq rax
    ++- cmpq (imm 0) (ind ~ofs:var_size rax)
    (* go to the corresponding branch *)
    ++- je ( get_safe_label ("condition_"^id) "not_met") 
    +++ compile_expr e1 
    ++- jmp ( get_safe_label ("condition_"^id) "end") 
    
    ++- safe_label  ("condition_"^id) "not_met"
    +++ compile_expr e2 
    ++- safe_label ("condition_"^id) "end" 
      
  | AEident_builtin(s) -> 
     nop, pushq (lab (get_global_label s))
  
  | AEident(x) ->
    nop, pushq (ind ~ofs:x rbp) 

  | AEclos_ident(x) ->
    nop, pushq (ind ~ofs:x rbx)
  
  | AEblock(st_l) ->
    (List.fold_left compile_stmt (nop, nop) st_l) 
    ++- pushq !%rax (* rax conatins the result of the last statement *)

  | AEcall(f, l) ->
    (nop, nop) 
    ++- pushq !%r12 (* callee saved *)
    (* calculate the function *)
    +++ compile_expr f 
    ++- popq r12 
    (* put the arguments and environment on the stack and call the function *)
    +++ List.fold_left (+++) (nop, nop) (List.map 
    (fun a -> 
      compile_expr a 
      ++- movq (imm (3*var_size)) !%rdi 
      ++- call (get_safe_label "internal" "my_malloc") 
      ++- popq rcx
      ++- call (get_safe_label "internal" "copy_value")
      ++- pushq !%rax) l)
    ++- pushq !%r12 
    ++- call_star (ind ~ofs:var_size r12) 
    ++- popn ((1 + List.length l) * var_size) 
    ++- popq r12 (* recover callee saved *)
    (* put the result *)
    ++- pushq !%rax  

  | AElam(ferm, e, fpmax) ->
    compile_funbody "lambda" ("anonymous_" ^ create_id()) ferm e fpmax ++- pushq !%rax 

  | AEcases(e, b_empty, x, y, b_link) -> 
    let id_cases = create_id() in 
    (* compute e and compare its type : is it link or empty ? *)
    compile_expr e 
    ++- popq rax 
    ++- movq (ind rax) !%rcx 
    ++- cmpq (imm id_Link) !%rcx 
    ++- je ( get_safe_label ("cases_"^id_cases) "link_branch") 
    (* e = empty : do the empty branch *)
    +++ compile_expr b_empty 
    ++- jmp ( get_safe_label ("cases_"^id_cases) "end") 
    (* e = link(x, y) : put the values in the variable x and y then do the link branch *)
    ++- safe_label ("cases_"^id_cases) "link_branch" 
    ++- movq (ind ~ofs:var_size rax) !%r11 
    ++- movq !%r11 (ind ~ofs:x rbp) 
    ++- movq (ind ~ofs:(2*var_size) rax) !%r11 
    ++- movq !%r11 (ind ~ofs:y rbp) 
    +++ compile_expr b_link 
    ++- safe_label ("cases_"^id_cases) "end"

  | _ -> assert false

and compile_stmt (codefun, codemain) = function
  | ASexpr(e, fsize)   -> (codefun, codemain) ++- pushn fsize +++ (compile_expr e) ++- popq rax ++- popn fsize 
  | ASvar(x, e, fsize) -> (codefun, codemain) ++- pushn fsize +++ (compile_expr e) 
  ++- movq (imm (3*var_size)) !%rdi (* on prend un peu large avec 3*var_size, ça ne vaut pas le coup de calculer la taille exact à malloc *)
  ++- call (get_safe_label "internal" "my_malloc")
  ++- popq rcx
  ++- call (get_safe_label "internal" "copy_value")
  ++- popn fsize ++- movq !%rax (ind ~ofs:x rbp) ++- movq (imm 0) !%rax (* on met rax à 0 pour détexter les erreurs *)
  | ASassign(is_local, x, e, fsize) -> 
    let rb = (if is_local then rbp else rbx) in
  (codefun, codemain) ++- pushn fsize +++ (compile_expr e) 
  ++- popq rcx
  ++- movq (ind ~ofs:x rb) !%rax
  ++- call (get_safe_label "internal" "copy_value")
  ++- popn fsize ++- movq (lab (get_global_label "nothing")) !%rax
  | ASfun(f, x, ferm, e, fpmax) -> 
    let f = normalize f in 
    (codefun, codemain) +++ compile_funbody "user" f ferm e fpmax ++- movq !%rax (ind ~ofs:x rbp) 
and compile_funbody fun_type (fun_name : string) ferm e fpmax = 
  let intern_funs, fun_body = compile_expr e in 
  let fun_code = 
  safe_label fun_type fun_name  ++
  pushq !%rbp ++
  movq !%rsp !%rbp ++
  pushq !%rbx ++
  pushn fpmax ++
  movq (ind ~ofs:(2*var_size) rbp) !%r11 ++
  movq (ind ~ofs:(2*var_size) r11) !%rbx ++
  fun_body ++
  popq rax ++
  popn fpmax ++
  popq rbx ++
  popq rbp ++
  ret
  in 
  let alloc_fun_code = 
  let fun_block_size = 3 + List.length ferm in
  movq (imm (fun_block_size*var_size)) !%rdi ++
  call (get_safe_label "internal" "my_malloc") ++
  movq (imm id_Function) (ind rax) ++
  movq (ilab (get_safe_label fun_type fun_name)) (ind ~ofs:var_size rax) ++
  leaq (ind ~ofs:(3*var_size) rax) rdx ++
  movq !%rdx (ind ~ofs:(2*var_size) rax) ++
  (* copy the variables in the closure *)
  List.fold_left (++) nop (List.map 
  (fun (is_in_stack, dep, arr) -> 
    (if is_in_stack then movq (ind ~ofs:dep rbp) !%r11 
    else movq (ind ~ofs:dep rbx) !%r11) 
    ++ movq !%r11 (ind ~ofs:arr rdx) 
  ) ferm)
  in
  fun_code ++ intern_funs, alloc_fun_code

let compile_program p ofile =
  let fold_tstmt =
    TSfun("fold", ["f"; "init"; "l"], 
      TEcases( TEident("l"), 
        TEident("init"), 
        "x", "q", TEcall(TEident("fold"), [TEident("f"); TEcall( TEident("f"), [TEident("init"); TEident("x")]); TEident("q")] ))) 
    (*fold f init l :
      cases l :
        | empty => init
        | link(x, q) => fold f (f ident x) q
      end
    end *)
  in
  let p = fold_tstmt::p in
  let (p, fptot) = alloc p in
  let user_funs, main_code = List.fold_left compile_stmt (nop, nop) p in
  let p =
    { text =
    globl "main" ++ label "main" ++
    (* save the initial stack state globaly: used to exit *)
    movq !%rsp (lab ".Vrsp_main") ++ 
    movq !%rsp !%rbp ++

    pushn fptot ++
    List.fold_left (++) nop (List.map alloc_global (global_values ())) ++
    main_code ++
    popn fptot ++

    (* return 0 *)
    movq (imm 0) !%rax ++ 
    ret ++

    user_funs++
    all_builtin_funs ;
    data =( List.fold_left (++) nop (List.map (fun s -> label (get_global_label s) ++ dquad [1]) (global_values ())) ++
      label ".Vrsp_main" ++ dquad [1] ++
      
      label ".Sprint_true" ++ string "true"++
      label ".Sprint_false" ++ string "false" ++
      label ".Sprint_nothing" ++ string "nothing" ++
      label ".Sprint_int" ++ string "%lld" ++
      label ".Sprint_string" ++ string "%s" ++
      label ".Sprint_function" ++ string "<function : %p>" ++
      label ".Sprint_empty" ++ string "[list: ]" ++
      label ".Sprint_link" ++ string "[list: " ++
      label ".Sprint_comma" ++ string ", " ++
      label ".Sprint_right_par" ++ string "]" ++
      
      label ".Sprint_raise" ++ string "raised : %s\n" ++
      
      label ".Sprint_error_type" ++ string "compilator error : ill-formed type\n"++
      label ".Sprint_error_bool" ++ string "compilator error : ill-formed boolean\n" ++
      label ".Sprint_error_comparison" ++ string "runtime error : comparison of uncomparable types, probably two functions\n" 
      )
    }
  in
  let f = open_out ofile in
  let fmt = formatter_of_out_channel f in
  X86_64.print_program fmt p;
  fprintf fmt "@?";
  close_out f
