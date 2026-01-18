
{
  open Lexing
  open Ast
  open Parser
  
  exception Lexing_error of string

  let ident_or_keyword =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["block", BLOCK; 
      "if", IF;
      "else", ELSE; 
      "end", END;
      "for", FOR;
      "from", FROM; 
      "cases", CASES;
      "fun", FUN; 
      "lam", LAM;
      "or", OR;
      "and", AND;
      "true", CST (Cbool true); 
      "false", CST (Cbool false);
      "var", VAR];
    fun s -> try Hashtbl.find h s with Not_found -> IDENT s

  let string_buffer = Buffer.create 1024

  let last_token = ref EOF


}
let letter = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = letter ( '-'* (letter | digit)+ )*
let integer = ('+' | '-')? ['0'-'9']+
let space = ' ' | '\t'

rule next_token_s spaced = parse
  | '|'     { BRANCH }
  | "="     { EQUAL }
  | ":="    { ASSIGN }
  | "->"    { ARROW }
  | "=>"    { IMPLY } 
  | ','     { COMMA }

  | " < "   { SPACED_LEFTCHEV }
  | "<"     { LEFTCHEV }
  | " > "   { SPACED_RIGHTCHEV }
  | ">"     { RIGHTCHEV }
  
  | (space | '\n' as sp1) ("==" | "<>" | "<=" | ">=" | "+" | "-" | "*" | "/" as op ) (space | '\n' as sp2) 
  { (if sp1 = '\n' then new_line lexbuf);(if sp2 = '\n' then new_line lexbuf);
    match op with
      | "==" -> CMP_EQ
      | "<>" -> CMP_NEQ
      | "<=" -> CMP_LE
      | ">=" -> CMP_GE
      | "+" -> ADD
      | "-" -> SUB
      | "*" -> MUL
      | "/" -> DIV
      | _ -> assert false }
  | "==" | "<>" | "<=" | ">=" | "+" | "-" | "*" | "/" as op { raise (Lexing_error ("Binary operation '"^op^"' should be preceded and followed by a space")) }
  | ':'     { (match !last_token with 
    |ELSE -> if spaced then raise (Lexing_error "Cannot have a space bewtween 'else' and ':'" ) 
    |BLOCK -> if spaced then raise (Lexing_error "Cannot have a space bewtween 'block' and ':'" )
    |COLON -> if spaced then raise (Lexing_error "Cannot have a space bewtween two ':' " )
    | _ -> ());
    COLON }
  | '('     {
    match !last_token with 
    |RIGHTPAR|RIGHTCHEV|IDENT _|LAM -> if spaced then raise (Lexing_error "Cannot have a space between ')' or '>' or 'lam' or identifiant and an open parentheses '(' " ) 
      else UNSPACED_LEFTPAR 
    | _ -> LEFTPAR }
  | ')'     { RIGHTPAR }
  | "#|"    { next_multiline_comment 1 lexbuf }
  | "#"     { next_singleline_comment lexbuf } 
  | '\n'    { new_line lexbuf; next_token_s true lexbuf}
  | ident as id 
          { ident_or_keyword id }
  | space+{ next_token_s true lexbuf }
  | integer as s (('+' | '-')? as t)
            { if t <> "" then (raise (Lexing_error t)) else begin try CST (Cint (int_of_string s))
              with _ -> raise (Lexing_error ("constant too large: " ^ s)) end }
  | ['"' '\'']  as d   { CST (Cstring (next_string d lexbuf)) }
  | eof     { EOF }
  | _ as c  {raise (Lexing_error ("illegal character: " ^ String.make 1 c)) }

and next_string d = parse
  | ['"' '\''] as c 
      { if c = d then (let s = Buffer.contents string_buffer in
	Buffer.reset string_buffer;
	s) else (Buffer.add_char string_buffer c;
	next_string d lexbuf) }
  | "\\n"
      { Buffer.add_char string_buffer '\n';
	next_string d lexbuf }
  | "\\t"
      { Buffer.add_char string_buffer '\t';
	next_string d lexbuf }
  | "\\\""
      { Buffer.add_char string_buffer '"';
	next_string d lexbuf }
  | "\\'"
      { Buffer.add_char string_buffer '\'';
	next_string d lexbuf }
  | "\\\\"
      { Buffer.add_char string_buffer '\\';
	next_string d lexbuf }
  | '\n' { raise (Lexing_error "no multiline string") }
  | '\\' { raise (Lexing_error "invalid escape in string") }
  | _ as c
      { Buffer.add_char string_buffer c;
	next_string d lexbuf }
  | eof
      { raise (Lexing_error "unterminated string") }
and next_multiline_comment depth = parse
  | "#|" { next_multiline_comment (depth + 1) lexbuf }
  | "|#" { if depth = 1 then next_token_s true lexbuf
          else next_multiline_comment (depth - 1) lexbuf }
  | '\n' { new_line lexbuf; next_multiline_comment depth lexbuf }
  | _    { next_multiline_comment depth lexbuf }
  | eof  { raise (Lexing_error "unterminated comment") }
and next_singleline_comment = parse
  | '\n' { new_line lexbuf; next_token_s true lexbuf }
  | _    { next_singleline_comment lexbuf }
  | eof  { EOF }

{
  let next_tokens lexbuf = 
    let t = next_token_s false lexbuf in
    last_token := t;
    t 
}