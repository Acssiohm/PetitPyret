open Format
open Lexing
open Parser
open Typer


(* Option de compilation, pour s'arrêter à l'issue du parser *)
let parse_only = ref false
let type_only = ref false

(* Nom du fichier source *)
let ifile = ref ""
let ofile = ref ""

let set_file f s = f := s

(* Les options du compilateur que l'on affiche avec --help *)
let options =
  ["--parse-only", Arg.Set parse_only,
   "  Pour ne faire uniquement que la phase d'analyse syntaxique";
   "--type-only", Arg.Set type_only,
   "  Pour ne faire uniquement que la phase de typage";
   "-o", Arg.String (set_file ofile), 
   "<file>  Pour indiquer le mom du fichier de sortie"]

let usage = "usage: pyretc [option] file.arr"

(* localise une erreur en indiquant la ligne et la colonne *)
let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n" !ifile l (c-1) c

let () =
  (* Parsing de la ligne de commande *)
  Arg.parse options (set_file ifile) usage;

  (* On vérifie que le nom du fichier source a bien été indiqué *)
  if !ifile="" then begin eprintf "Aucun fichier à compiler\n@?"; exit 1 end;

  (* Ce fichier doit avoir l'extension .arr *)
  if not (Filename.check_suffix !ifile ".arr") then begin
    eprintf "Le fichier d'entrée doit avoir l'extension .arr\n@?";
    Arg.usage options usage;
    exit 1
  end;
  (* Par défaut, le fichier cible a le même nom que le fichier source, 
     seule l'extension change *)
  if !ofile="" then ofile := Filename.chop_suffix !ifile ".arr" ^ ".s";
  (* Ouverture du fichier source en lecture *)
  let f = open_in !ifile in

  (* Création d'un tampon d'analyse lexicale *)
  let buf = Lexing.from_channel f in

  try
    (* Parsing: la fonction  Parser.file transforme le tampon lexical en un
       arbre de syntaxe abstraite si aucune erreur (lexicale ou syntaxique)
       n'est détectée.
       La fonction Lexer.next_tokens est utilisée par Parser.file pour obtenir
       le prochain token. *)
    let p = Parser.file Lexer.next_tokens buf in
    close_in f;

    (* On s'arrête ici si on ne veut faire que le parsing *)
    if !parse_only then exit 0;
    let tp = Typer.typed_ast p in

    if !type_only then exit 0;
    (* Phase de compilation *)
    Compile.compile_program tp !ofile
  with
    | Lexer.Lexing_error c ->
	(* Erreur lexicale. On récupère sa position absolue et
	   on la convertit en numéro de ligne *)
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur lexicale: %s@." c;
	exit 1
    | Parser.Error ->
	(* Erreur syntaxique. On récupère sa position absolue et on la
	   convertit en numéro de ligne *)
	localisation (Lexing.lexeme_start_p buf);
	eprintf "Erreur syntaxique@.";
	exit 1
    | Typer.TypeError (p, s) -> 
  localisation p;
	eprintf "Erreur de typage: %s@." s; 
  exit 1
  (* Erreur pendant le typage *)
