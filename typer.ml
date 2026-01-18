open Ast

type typ =
  | TAny
  | TNothing
  | TBoolean
  | TNumber
  | TString
  | TIdent of string
  | TList of typ
  | TFun of typ list * typ
  | Tvar of tvar
  
and tvar =
  { id : int;
    mutable def : typ option }

type texpr =
  | TEcst of constant 
  | TEident of string 
  | TEbinop of binop * texpr * texpr * typ
  | TEcall of texpr * texpr list 
  | TElam of string list * texpr 
  | TEblock of tstmt list 
  | TEcases of texpr * texpr * string * string * texpr 
  | TEif of texpr * texpr * texpr 
and tstmt =
  | TSassign of string * texpr 
  | TSfun of string * string list * texpr
  | TSvar of string * texpr 
  | TSexpr of texpr * typ 

type prog = stmt list
type tprog = tstmt list

exception TypeError of pos*string 

module V = struct
  type t = tvar
  let compare v1 v2 = Stdlib.compare v1.id v2.id
  let equal v1 v2 = v1.id = v2.id
  let create = let r = ref 0 in fun () -> incr r; { id = !r; def = None }
end
let rec head = function
  | Tvar tv as t -> (match tv.def with
      | None -> t
      | Some t -> head t )
  | x -> x
let rec canon t =
  match head t with
  | TList a -> TList (canon a)
  | TFun (a,b) -> TFun ( List.map canon a, canon b)
  | t' -> t'

let unification_error p t1 t2 = raise (TypeError (p, "Erreur d'unification"))

let rec occur tv t =
  match head t with
    | TList a -> occur tv a
    | TFun (a,b) -> List.exists (occur tv) a || occur tv b
    | Tvar{id;_} -> id = tv.id
    | _ -> false
    
let rec unify p accept_sub_type t1 t2  =
  match head t1 , head t2 with
  | TNumber, TNumber | TString , TString | TBoolean, TBoolean | TNothing, TNothing -> ()
  | TIdent s1, TIdent s2 when s1 = s2 -> ()
  | TList a1, TList a2 -> unify p accept_sub_type a1 a2 
  | TFun (args1, ret1), TFun (args2, ret2) ->
    if List.length args1 <> List.length args2 then
      unification_error p t1 t2
    else begin
      List.iter2 (unify p accept_sub_type) args2 args1 ;
      unify p accept_sub_type ret1 ret2
    end
  | Tvar tv1, Tvar tv2 when tv1.id = tv2.id -> ()
  | Tvar tv, t | t, Tvar tv -> if occur tv t then unification_error p t1 t2 else tv.def <- Some t 
  | _, TAny when accept_sub_type -> ()
  | _ -> unification_error p t1 t2

let rec is_subtype t1 t2 =
  match head t1 , head t2 with
  | TNumber, TNumber | TString , TString | TBoolean, TBoolean | TNothing, TNothing -> true
  | TIdent s1, TIdent s2 when s1 = s2 -> true
  | TList a1, TList a2 -> is_subtype a1 a2 
  | TFun (args1, ret1), TFun (args2, ret2) ->
    if List.length args1 <> List.length args2 then
      false
    else begin
      List.for_all2 (fun a2 a1 -> is_subtype a2 a1) args2 args1 &&
      is_subtype ret1 ret2
    end
  | _, TAny -> true
  | Tvar _, _ -> true
  | _ -> false

module Vset = Set.Make(V)
module Smap = Map.Make(String)
module Sset = Set.Make(String)
let rec fvars t =
  match head t with
    | TIdent _ | TNumber | TString | TBoolean | TNothing | TAny -> Vset.empty
    | TFun (args, ret) ->
      List.fold_left (fun acc t -> Vset.union acc (fvars t)) (fvars ret) args
    | TList a -> fvars a
    | Tvar tv -> Vset.singleton tv

type schema = { vars : Vset.t; typ : typ }

type env = { bindings : schema Smap.t; fvars : Vset.t; mutable_vars : Sset.t; variant_types : Sset.t }
let empty = {bindings = Smap.empty; fvars = Vset.empty; mutable_vars = Sset.empty; variant_types = Sset.empty }

let add p is_mut s t e =
  if s = "_" then e else
  if Smap.mem s e.bindings then raise ( TypeError (p, "Variable déjà définie: " ^ s)) else
  (* if Smap.mem s e.variant_types then raise ( TypeError (p, "Variable déjà définie comme type: " ^ s) ) else *)
  { bindings = Smap.add s {vars = Vset.empty; typ = t} e.bindings ; fvars = Vset.union e.fvars (fvars t); mutable_vars = if is_mut then Sset.add s e.mutable_vars else e.mutable_vars; variant_types = e.variant_types }

let add_gen p s t e =
  if s = "_" then e else
  if Smap.mem s e.bindings then raise ( TypeError (p, "Variable déjà définie: " ^ s)) else
  (* if Smap.mem s e.variant_types then raise (TypeError(p, "Variable déjà définie comme type: " ^ s)) else *)
  let upd_fvars = Vset.fold (fun tv curr_vars -> Vset.union (fvars (Tvar tv)) curr_vars) e.fvars Vset.empty in 
  { bindings = Smap.add s {vars = Vset.diff (fvars t) upd_fvars; typ = t} e.bindings ; fvars = upd_fvars; mutable_vars = e.mutable_vars; variant_types = e.variant_types }

let is_mutable s e =
  Sset.mem s e.mutable_vars

let add_variant_type p s e =
  if List.mem s ["Number"; "String"; "Boolean"; "Nothing"; "Any"; "List"] then raise ( TypeError (p, "Type réservé: " ^ s)) else
  if Sset.mem s e.variant_types then raise ( TypeError (p, "Type déjà défini: " ^ s)) else
  (* if Smap.mem s e.bindings then raise ( TypeError (p, "Type déjà définie comme variable: " ^ s) )else *)
  { bindings = e.bindings ; fvars = e.fvars; mutable_vars = e.mutable_vars; variant_types = Sset.add s e.variant_types }

module Vmap = Map.Make(V)

let find p s e =
  let vars = ref Vmap.empty in
  let sch = try Smap.find s e.bindings  
  with
    | Not_found -> raise (TypeError (p, "Variable inconnue: " ^ s)) in
  Vset.iter (fun tv -> vars := if Vset.mem tv e.fvars  then !vars else Vmap.add tv (V.create()) !vars ) sch.vars;
  let rec replace_vars t =
    match t with
      | TList a -> TList (replace_vars a)
      | TFun (args, ret) -> TFun ( List.map replace_vars args, replace_vars ret)
      | TIdent _ | TNumber | TString | TBoolean | TNothing | TAny -> t
      | Tvar v -> (try let nv = Vmap.find v !vars in Tvar nv with | Not_found -> Tvar v)
  in
  replace_vars sch.typ

let find_variant_type s e =
  Sset.mem s e.variant_types

let rec convert_ttype_and_gen p evn gen_map = function
  | Tident "Number" -> TNumber
  | Tident "String" -> TString
  | Tident "Boolean" -> TBoolean
  | Tident "Nothing" -> TNothing
  | Tident "Any" -> TAny
  | Tparam ("List", [t]) -> TList (convert_ttype_and_gen p evn gen_map t)
  | Tfun (args, ret) -> TFun ( List.map (convert_ttype_and_gen p evn gen_map) args , convert_ttype_and_gen p evn gen_map ret)
  | Tident a -> 
    (try Smap.find a gen_map with
      | Not_found -> (if find_variant_type a evn then TIdent a else raise (TypeError (p, "Variable de type inconnue: " ^ a))))
  | _ -> raise (TypeError (p, "Type inconnue"))
let convert_ttype p evn t =
  convert_ttype_and_gen p evn Smap.empty t

let rec w_e evn : expr -> texpr * typ = function
  | Eident(p, s) -> let t = find p s evn in TEident(s) , t
  | Ecst(_, c) -> (match c with | Cbool _ -> TEcst(c), TBoolean | Cstring _ -> TEcst (c),TString | Cint _ -> TEcst(c), TNumber)
  | Eblock(_, sl)-> let (sl', t) = w_s evn sl in TEblock (sl') , t
  | Eif(p, c, bi, be) -> let (c_t, tc) = w_e evn c in unify p false tc TBoolean ;
    let (bi_t, tbi) = w_e evn bi in
    begin match be with
      | None -> TEif( c_t, bi_t, TEcall (TEident("raise"), [TEcst (Cstring "error")])), tbi
      | Some be' -> let (be_t, tbe) = w_e evn be' in 
        unify p false tbi tbe ; TEif( c_t, bi_t, be_t),tbi end 
  | Ecall (p, f, args) -> 
    let (f_t, tf) = w_e evn f in
    let args_t = List.map (w_e evn) args in
    let tret = Tvar (V.create()) in
    unify p true tf (TFun (List.map snd args_t, tret));
    TEcall (f_t, List.map fst args_t),tret
  | Ecases (p, t, ex, brs) -> let ex_t,tex = w_e evn ex in unify p true tex (convert_ttype p evn t); let alpha = Tvar (V.create()) in
    unify p false tex  (TList alpha) ;
    begin match brs with
      | ("link", [x;y], ex1)::("empty", [], ex2 )::[] | ("empty", [], ex2 )::("link", [x;y], ex1)::[] -> 
        let (ex1_t, tex1) = w_e (add p false y (TList alpha) (add p false x alpha evn)) ex1 in
        let (ex2_t, tex2) = w_e evn ex2 in
        unify p false tex1 tex2 ;
        let (ex_t,tex) = w_e evn ex in  
        TEcases (ex_t, ex2_t, x, y, ex1_t), tex1
      | _ -> raise (TypeError(p, "Cases should match link(x,y) and empty lists" ) )
    end 
  | Elam (p, args, rt, body) -> 
    let args' = List.map (fun (arg, t) -> (arg, convert_ttype p evn t)) args in
    let evn' = List.fold_left (fun acc (arg, t) -> add p false arg t acc) evn args' in
    let body_t, tbody = w_e evn' body in
    let rt = convert_ttype p evn rt in
    unify p true tbody rt ;
    TElam (List.map fst args', body_t) , TFun (List.map snd args', rt)
  | Ebinop (p, op, e1, e2) ->
    let e1_t, te1 = w_e evn e1 in
    let e2_t, te2 = w_e evn e2 in 
    begin match op with
      | Badd -> 
        if (is_subtype te1 TNumber) && (is_subtype te2 TNumber) then
        (unify p false te1 TNumber ;
        unify p false te2 TNumber ;
        ((TEbinop (op, e1_t, e2_t, TNumber)), TNumber) )
        else if (is_subtype te1 TString) && (is_subtype te2 TString) then
        (unify p false te1 TString ;
        unify p false te2 TString ;
        TEbinop (op, e1_t, e2_t, TString), TString )
        else raise (TypeError(p, "Type error in addition : you can only add two integers or two strings"))
      | Bsub | Bmul | Bdiv -> 
        unify p false te1 TNumber ;
        unify p false te2 TNumber ;
        TEbinop (op, e1_t, e2_t, TNumber), TNumber
      | Beq | Bneq -> 
        TEbinop (op, e1_t, e2_t, TBoolean), TBoolean
      | Blt | Ble | Bgt | Bge -> 
        unify p false te1 TNumber ;
        unify p false te2 TNumber ;
        TEbinop (op, e1_t, e2_t, TBoolean), TBoolean
      | Band | Bor -> 
        unify p false te1 TBoolean ;
        unify p false te2 TBoolean ;
        TEbinop (op, e1_t, e2_t, TBoolean), TBoolean
    end
and w_s evn sl = 
  let (sl_t, _) = List.fold_left begin fun (sl_t,evn') -> 
    function
    | Sassign (p, s, ex) -> let t = find p s evn' in
    if not (is_mutable s evn') then raise  (TypeError(p, "Tentative de modifier une variable immuable: "^s))  else  
    let ex_t, tex = w_e evn' ex in unify p true tex t; (TSassign(s, ex_t)::sl_t, evn') 
    | Svar (p, x, t_opt, ex, is_mutable) -> let ex_t, tex = w_e evn' ex in 
      (match t_opt with
        | Some t -> unify p true tex (convert_ttype p evn' t) 
        | None -> ()) ;
      (TSvar (x, ex_t)::sl_t, (if is_mutable then add p true else add_gen p) x tex evn')
    | Sexpr (_, ex) -> let ex_t, tex = w_e evn' ex in TSexpr (ex_t, tex)::sl_t, evn'
    | Sfun (p, f, variants, params, ret_t, body) -> 
      let variants_gen = List.fold_left (fun acc alpha -> Smap.add alpha (Tvar (V.create())) acc ) Smap.empty variants in
      let evn_variants = List.fold_left (fun acc alpha -> add_variant_type p alpha acc ) evn' variants in
      let ret_t' = convert_ttype p evn_variants ret_t in
      let param_types = List.map (fun (_, t) -> convert_ttype p evn_variants t) params in
      let param_types_gen = List.map (fun (_,t) -> convert_ttype_and_gen p evn_variants variants_gen t) params in
      let fun_type_gen = TFun (param_types_gen, convert_ttype_and_gen p evn_variants variants_gen ret_t) in
      let evn2 = add_gen p f fun_type_gen evn_variants in
      let evn3 = List.fold_left2 (fun acc (param, _) t -> add p false param t acc) evn2 params param_types in
      let body_t, tbody = w_e evn3 body in
      unify p true tbody ret_t' ;
      (TSfun (f, List.map fst params, body_t)::sl_t, add_gen p f fun_type_gen evn' )
    end ([],evn) sl in
  List.rev sl_t, match List.hd sl_t with | TSassign _ -> TNothing | TSexpr (_, t) -> t | _ -> TNothing
let w e p =
  if p = [] then [] else
  fst (w_s e p)
  
let typed_ast ( p : Ast.prog ) : tprog =
  let evn = List.fold_left (fun acc (s, t) -> add_gen Lexing.dummy_pos s t acc) empty 
  [("nothing", TNothing); 
  ("num-modulo", TFun([TNumber; TNumber], TNumber)); 
  ("empty", TList (Tvar(V.create())));
  ("link", let alpha = Tvar (V.create()) in TFun( [alpha; TList alpha ], TList alpha ));
  ("print", let alpha = Tvar (V.create()) in TFun( [alpha ], alpha ));
  ("raise", TFun( [TString], Tvar (V.create()) ));
  ("each", let alpha = Tvar (V.create()) in let beta = Tvar (V.create()) in TFun([TFun([alpha], beta); TList alpha], TNothing  ) );
  ("fold", let alpha = Tvar (V.create()) in let beta = Tvar (V.create()) in TFun([TFun([alpha;beta], beta); alpha; TList beta], alpha  ) );
   ] in
    w evn p

