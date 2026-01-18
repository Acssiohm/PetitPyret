open Format
open X86_64
open Ast   
open Typer 

let test_change = true

(******************************************************************************)
(******************************** CONSTANTS ***********************************)
(******************************************************************************)
let var_size = 8

(* TYPES : *)
let id_Nothing = 0
let id_Boolean = 1
let id_Number = 2
let id_String = 3
let id_Empty = 4
let id_Link = 5
let id_Function = 6

(******************************************************************************)
(*********************** PUSH & POP UTILITY INSTRUCTIONS **********************)
(******************************************************************************)

let popn n = addq (imm n) !%rsp
let pushn n = subq (imm n) !%rsp

(******************************************************************************)
(****************************** NORMALIZATION *********************************)
(******************************************************************************)

let normalize (s : string) : string =
  let res = ref "" in  
  String.iter (fun c -> res := !res ^ (if c = '-' then  "._." else String.make 1 c) ) s;
  !res

let get_safe_label (block_name : string) (label_name : string) =
  String.iter ( fun c -> assert (c <> '.')) (block_name^label_name);
  assert (block_name <> "") ;
  normalize block_name ^ "." ^ normalize label_name  

let safe_label (block_name : string) (label_name : string) =
  label (get_safe_label block_name label_name)

(******************************************************************************)
(***************************** GLOBAL VALUES **********************************)
(******************************************************************************)

let global_values () =
  ["nothing"; "empty"; "print"; "link"; "each"; "num-modulo"; "raise"] 
let is_global_val s =
  List.mem s (global_values ())

let get_global_type_id s =
  assert (is_global_val s);
  match s with
    | "nothing" -> id_Nothing
    | "empty" -> id_Empty
    | _ -> id_Function

let get_global_label s =
  assert (is_global_val s);
  get_safe_label "builtin_value" s

let alloc_global_variable data_list label_position =
  movq (imm (List.length data_list)) !%rdi ++
  call ( get_safe_label "internal" "my_malloc") ++
  let copy_data = List.mapi (fun i v -> movq v (ind ~ofs:(i*var_size) rax)) data_list in
  (List.fold_left (++) nop copy_data) ++ 
  movq !%rax (lab label_position)

let alloc_global s =
  assert (is_global_val s);
  let type_id = get_global_type_id s in
  if type_id = id_Function then alloc_global_variable [imm id_Function; ilab ( get_safe_label "user" s)] (get_global_label s)
  else (assert (type_id = id_Empty || type_id = id_Nothing); alloc_global_variable [imm type_id] (get_global_label s))


(******************************************************************************)
(********************** C LIBRARY WRAPPER FUNCTIONS  **************************)
(******************************************************************************)

let my_printf =
  safe_label "internal" "my_printf" ++ 
  pushq !%rbp ++
  movq !%rsp !%rbp ++

  (* call printf with aligned stack and rax = 0 *)
  andq (imm (-16)) !%rsp ++
  movq (imm 0) !%rax ++
  call "printf" ++
  movq !%rbp !%rsp ++

  popq rbp ++
  ret
let my_malloc = 
  safe_label "internal" "my_malloc" ++
  pushq !%rbp ++
  movq !%rsp !%rbp ++

  (* call malloc with aligned stack *)
  andq (imm (-16)) !%rsp ++
  call "malloc" ++
  movq !%rbp !%rsp ++
  
  popq rbp ++
  ret 

let c_library_wrapper_funs =
  my_printf ++
  my_malloc

(******************************************************************************)
(************************** SPECIAL EXIT ROUTINE ******************************)
(******************************************************************************)

let my_exit_routine k =
  assert (k <> 0); (*souldn't be used on a normal execution*)
  movq (lab ".Vrsp_main") !%rsp ++ (* force the stack to the initial position *)
  movq (imm k) !%rax ++ (* exit k *)
  ret (* the initial value on the stack is the return address of main -> exit *)

(******************************************************************************)
(*************************** UTILITY FUNCTIONS ********************************)
(******************************************************************************)

let add_strlen =
  safe_label "internal" "add_strlen" ++

  (* loop until the NULL character *)
  cmpb (imm 0) (ind rdi) ++
  jz  (get_safe_label "add_strlen" "zero_found") ++
  incq !%rax ++ (* increments the length *)
  incq !%rdi ++ (* increments the position *)
  jmp ( get_safe_label "internal" "add_strlen" ) ++

  safe_label "add_strlen" "zero_found" ++
  ret

let copy_str =
  safe_label "internal" "copy_str" ++
  (* loop until the NULL character *)
  cmpb (imm 0) (ind rdi)  ++
  jz ( get_safe_label "copy_str" "zero_found" ) ++
  (* copies the current character *)
  movb (ind rdi) !%r11b ++
  movb !%r11b (ind rax) ++
  (* increments both positions *)
  incq !%rax ++
  incq !%rdi ++
  jmp ( get_safe_label "internal" "copy_str") ++

  safe_label "copy_str" "zero_found" ++
  ret

let copy_value =
  safe_label "internal" "copy_value" 
  ++ movq (ind rcx) !%r11
  ++ movq !%r11 (ind rax)
  ++ testq (imm 0b11) (ind rcx)
  ++ jz "1f"
  ++ movq (ind ~ofs:var_size rcx) !%r11
  ++ movq !%r11 (ind ~ofs:var_size rax)
  ++ cmpq (imm 3) (ind rcx)
  ++ jle "1f"
  ++ movq (ind ~ofs:(2*var_size) rcx) !%r11
  ++ movq !%r11 (ind ~ofs:(2*var_size) rax)
  ++ label "1"
  ++ ret
let test_equality =
  safe_label "internal" "test_equality" ++

  (* Tes the equality of types *)
  movq (ind rdi) !%rax ++
  cmpq !%rax (ind rsi) ++
  jne (get_safe_label "test_equality" "found_difference") ++

  testq (imm 0b11) !%rax  ++ (* matches trivial types : nothing(0) empty(0b100) *)
  jnz (get_safe_label "test_equality" "not_trivial_type") ++
  jmp (get_safe_label "test_equality" "are_equal") ++

  safe_label "test_equality" "not_trivial_type" ++
  cmpq (imm 2) !%rax  ++ (* matches the types containning one word : boolean(1) number(2) *)
  jg ( get_safe_label "test_equality" "not_single_mem") ++ 
  (* tests the only word memory after the type *)
  movq (ind ~ofs:var_size rdi) !%rax ++
  cmpq !%rax (ind ~ofs:var_size rsi) ++
  jne ( get_safe_label "test_equality" "found_difference") ++
  jmp ( get_safe_label  "test_equality" "are_equal" )++

  (* the two remaining comparable types*)
  safe_label "test_equality" "not_single_mem" ++
  cmpq (imm id_String) !%rax  ++
  je ( get_safe_label "test_equality" "compare_strings") ++
  cmpq (imm id_Link) !%rax  ++
  je ( get_safe_label "test_equality" "compare_link")++
  
  (* uncomparable types : we can't compare two functions *)
  movq (ilab ".Sprint_error_comparison") !%rdi ++
  call (get_safe_label "internal" "my_printf") ++
  my_exit_routine 1 ++

  safe_label "test_equality" "compare_link" ++
  (* compare current element - first element of both lists *)
  pushq !%rdi ++ (* caller saved *)
  pushq !%rsi ++ (* caller saved *)
  movq (ind ~ofs:var_size rdi) !%rdi ++ 
  movq (ind ~ofs:var_size rsi) !%rsi ++
  call ( get_safe_label  "internal" "test_equality")++
  popq rsi ++ (* recover *)
  popq rdi ++ (* recover *)
  
  (* the result of the comparison is in rax *)
  cmpq (imm 0) !%rax ++
  je ( get_safe_label "test_equality" "found_difference") ++

  (* compare the res of the list "recursively" *)
  movq (ind ~ofs:(2*var_size) rdi) !%rdi ++
  movq (ind ~ofs:(2*var_size) rsi) !%rsi ++
  jmp ( get_safe_label "internal" "test_equality" ) ++

  safe_label "test_equality" "compare_strings" ++
  movq (ind ~ofs:var_size rdi) !%rdi ++
  movq (ind ~ofs:var_size rsi) !%rsi ++
  movb  (ind rdi) !%r11b ++

  (* rdi and rsi contain the current positions in the string
  and r11b contain the char pointed by rdi *)
  safe_label "test_equality" "loop_compare_str" ++
  (* If the current characters are different or NULL we can answer*)
  cmpb (ind rsi) !%r11b ++
  jne ( get_safe_label "test_equality" "found_difference" ) ++ 
  cmpb (imm 0) !%r11b ++
  je ( get_safe_label "test_equality" "are_equal" ) ++
  (* go to next character and loop *)
  incq !%rdi ++
  incq !%rsi ++
  movb  (ind rdi) !%r11b ++
  jmp ( get_safe_label "test_equality" "loop_compare_str") ++

  (* Return the result in rax *)
  safe_label "test_equality" "are_equal" ++
  movq (imm 1) !%rax ++
  ret ++
  safe_label "test_equality" "found_difference" ++
  movq (imm 0) !%rax ++
  ret 

let utility_funs =
  add_strlen ++
  copy_str ++
  copy_value ++
  test_equality

(******************************************************************************)
(************************ BUILT-IN GLOBAL FUNCTIONS ***************************)
(******************************************************************************)

let pp_raise =
  safe_label "user" "raise" ++
  pushq !%rbp ++ 
  movq !%rsp !%rbp ++

  (* puts the argument string in rsi *)
  movq (ind ~ofs:(3*var_size) rbp) !%rdi ++
  leaq (ind ~ofs:var_size rdi) rsi ++
  (* print the raise message *)
  movq (ilab ".Sprint_raise") !%rdi ++ 
  call ( get_safe_label "internal" "my_printf") ++

  (* recover stack state : unecessary but to avoid future errors *)
  popq rbp ++ 
  (* exit 3 *)
  my_exit_routine 3 

let link =
  safe_label "user" "link" ++
  pushq !%rbp ++
  movq !%rsp !%rbp ++

  (* malloc 3 words of memory for a link variable *)
  movq (imm (3*var_size)) !%rdi ++
  call ( get_safe_label "internal" "my_malloc") ++
  (* puts the type id *)
  movq (imm id_Link) (ind rax) ++
  (* copies the value *)
  movq (ind ~ofs:(4*var_size) rbp) !%rdi ++ (*arg 1*)
  movq !%rdi (ind ~ofs:var_size rax) ++
  (* copies the pointer to the next list *)
  movq (ind ~ofs:(3*var_size) rbp) !%rdi ++ (*arg 2*)
  movq !%rdi (ind ~ofs:(2*var_size) rax) ++

  popq rbp ++ 
  ret

let print =
  safe_label "user" "print" ++
  pushq !%rbp ++
  movq !%rsp !%rbp ++

  (* get the argument : adress of a value block *)
  movq (ind ~ofs:(3*var_size) rbp) !%rdi ++
  (* get the type id *)
  movq (ind rdi) !%rax ++
  
  (* compare the type and go to the corresponding label *)
  cmpq (imm id_Boolean) !%rax ++
  je ( get_safe_label "print" "will_print_bool" ) ++ 
  cmpq (imm id_Number) !%rax ++
  je ( get_safe_label "print" "will_print_int" ) ++
  cmpq (imm id_String) !%rax ++
  je ( get_safe_label "print" "will_print_string" ) ++
  cmpq (imm id_Nothing) !%rax ++
  je ( get_safe_label "print" "will_print_nothing" )++
  cmpq (imm id_Empty) !%rax ++
  je ( get_safe_label "print" "will_print_empty" )++
  cmpq (imm id_Link) !%rax ++
  je ( get_safe_label "print" "will_print_link" )++
  cmpq (imm id_Function) !%rax ++
  je ( get_safe_label "print" "will_print_function" ) ++

  (* unknown type id : exit with an error -
  it shouldn't occur if the compilor is correct *)
  movq (ilab ".Sprint_error_type") !%rdi ++
  call ( get_safe_label "internal" "my_printf" ) ++
  my_exit_routine 2 ++

  (* Compare against the two possible boolean values 
  we could optimize but I prefered to make sure I detect potential errors *)
  safe_label "print" "will_print_bool" ++
  movq (ind ~ofs:var_size rdi) !%rsi ++
  cmpq (imm 0) !%rsi  ++
  je ( get_safe_label "print" "will_print_false" ) ++
  cmpq (imm 1) !%rsi  ++ 
  je ( get_safe_label "print" "will_print_true" ) ++
  
  (* unknown boolean value : exit with an error - 
  it shouldn't occur if the compilor is correct  *)
  movq (ilab ".Sprint_error_bool") !%rdi ++
  call ( get_safe_label "internal" "my_printf") ++
  my_exit_routine 2 ++

  (* The .will_print_<type> labels fill the registers and jump to .end_print to print them *)

  safe_label "print" "will_print_false" ++
  movq (ilab ".Sprint_false") !%rdi ++
  jmp ( get_safe_label "print" "end_print") ++ 

  safe_label "print" "will_print_true" ++
  movq (ilab ".Sprint_true") !%rdi ++
  jmp ( get_safe_label "print" "end_print") ++
  
  safe_label "print" "will_print_int" ++
  movq (ind ~ofs:var_size rdi) !%rsi ++
  movq (ilab ".Sprint_int") !%rdi ++
  jmp ( get_safe_label "print" "end_print") ++

  safe_label "print" "will_print_string" ++
  movq (ind ~ofs:var_size rdi) !%rsi ++
  movq (ilab ".Sprint_string") !%rdi ++
  jmp ( get_safe_label "print" "end_print" )++

  safe_label "print" "will_print_nothing" ++
  movq (ilab ".Sprint_nothing") !%rdi ++
  jmp ( get_safe_label "print" "end_print" ) ++

  safe_label "print" "will_print_empty" ++
  movq (ilab ".Sprint_empty") !%rdi ++
  jmp ( get_safe_label "print" "end_print" ) ++

  (* .will_print_link is at the end because it's more complex *)

  safe_label "print" "will_print_function" ++
  movq (ind ~ofs:var_size rdi) !%rsi ++
  movq (ilab ".Sprint_function") !%rdi ++
  jmp ( get_safe_label "print" "end_print" ) ++

  safe_label "print" "end_print" ++
  (* actually prints what we want to print *)
  andq (imm (-16)) !%rsp ++
  movq (imm 0) !%rax ++
  call "printf" ++
  
  movq (ind ~ofs:(3*var_size) rbp) !%rax ++ (* return the argument *)

  movq !%rbp !%rsp ++ (* recover stack alignement *)

  popq rbp ++ 
  ret ++

  safe_label "print" "will_print_link" ++
  (* save the value in a callee saved because we will need it *)
  pushq !%r13 ++
  movq !%rdi !%r13 ++
  (* align the stack for all the library calls - so we only do it one time *)
  pushq !%r12 ++
  movq !%rsp !%r12 ++
  andq (imm (-16)) !%rsp ++

  (* print the inital "[list :" *)
  movq (ilab ".Sprint_link") !%rdi ++
  movq (imm 0) !%rax ++ (* put rax = 0 for printf *)
  call "printf" ++

  (* skip the first comma *)
  jmp ( get_safe_label "print" "no_comma" ) ++

  (* the loop prints the elements of the list r13 : , el1, el2, ...,elk  *)
  safe_label "print" "loop_print_link" ++

  (* nothing to do if r13 is the empty list*)
  cmpq (imm id_Empty) (ind r13) ++
  je ( get_safe_label "print" "end_print_link" ) ++
  (* print the comma*)
  movq (ilab ".Sprint_comma") !%rdi ++
  movq (imm 0) !%rax ++
  call "printf" ++

  safe_label "print" "no_comma" ++
  (* call print with the first element the list r13 : el1 *)
  pushq (ind ~ofs:var_size r13) ++
  pushn var_size ++ (* fake fermeture / environnement *)
  call ( get_safe_label "user" "print") ++
  popn (2*var_size)++

  (* loop to print the remaining elements , el2, ..., elk *)
  movq (ind ~ofs:(2*var_size) r13) !%r13++
  jmp ( get_safe_label "print" "loop_print_link" )++

  (* finish by printing the closing bracket : ] *)
  safe_label "print" "end_print_link" ++
  movq (ilab ".Sprint_right_par") !%rdi ++
  movq (imm 0) !%rax ++
  call "printf" ++

  (* recover the alignment of the stack and the callee saved*)
  movq !%r12 !%rsp ++
  popq r12 ++
  popq r13 ++

  (* return the initial value *)
  movq (ind ~ofs:(3*var_size) rbp) !%rax ++
  popq rbp ++ 
  ret

let each =
  safe_label "user" "each" ++
  (* save stack state and update stack frame *)
  pushq !%rbp ++
  movq !%rsp !%rbp ++
  (* the list is put in rax and the function in rcx *)
  movq (ind ~ofs:(3*var_size) rbp) !%rax ++
  movq (ind ~ofs:(4*var_size) rbp) !%rcx ++
  safe_label "each" "apply" ++
  (* if the list empty there's nothing to do *)
  cmpq (imm id_Empty) (ind rax) ++
  je ( get_safe_label "each" "end_each" )++
  (* save rax and rcx *)
  pushq !%rax ++
  pushq !%rcx ++
  (* We want call the argument function on the current list element*)
  pushq (ind ~ofs:var_size rax) ++ 
  pushq !%rcx ++ (* put the fermeture / environnement *)
  call_star (ind ~ofs:var_size rcx) ++
  popn (2*var_size) ++ 
  (* we ignore the result of the function - which is in rax and should be nothing*)
  (* recover rax and rcx*)
  popq rcx ++
  popq rax ++
  (* We repeat with the same function and the next sub-list *)
  movq (ind ~ofs:(2*var_size) rax) !%rax ++
  jmp ( get_safe_label "each" "apply") ++  
  
  safe_label "each" "end_each"++
  (* Return nothing at the end *)
  movq (lab (get_global_label "nothing")) !%rax ++
  popq rbp ++ 
  ret

let num_modulo =
  safe_label "user" "num-modulo" ++
  pushq !%rbp ++
  movq !%rsp !%rbp ++

  (* Put the two values in rax and rcx *)
  movq (ind ~ofs:(4*var_size) rbp) !%rax ++
  movq (ind ~ofs:(3*var_size) rbp) !%rcx ++

  movq (ind ~ofs:var_size rax) !%rax ++ 
  movq (ind ~ofs:var_size rcx) !%rcx ++
  (* modulo calculation, the result is in rdx *)
  cqto ++ idivq !%rcx ++

  (* We want to standardize the sign of the modulo*)
  cmpq (imm 0) !%rdx ++ 
  je ( get_safe_label "num-modulo" "matched_sign" ) ++
  setl !%al ++
  cmpq (imm 0) !%rcx ++ 
  setl !%ah ++
  xorb !%ah !%al ++
  cmpb (imm 0) !%al ++
  je ( get_safe_label "num-modulo" "matched_sign") ++
  addq !%rcx !%rdx ++ (* if the sign is not the same as rcx, adding rcx one time should make it work, because |rdx| < |rcx| *)

  (* Here rdx has the same sign as rcx, which is what we want*)
  safe_label "num-modulo" "matched_sign" ++
  pushq !%rdx ++ (* caller saved *)

  (* Allocate a new Number *)
  movq (imm (2*var_size)) !%rdi ++
  call ( get_safe_label "internal" "my_malloc") ++
  movq (imm id_Number) (ind rax) ++
  (* recover the modulo value and put it in the number *)
  popq rdx ++ 
  movq !%rdx (ind ~ofs:var_size rax) ++

  (* The number is implicitly returned in rax *)
  popq rbp ++ 
  ret

(* fold is compiled in compile.ml because it can deriectly be coded in pyret *)
let builtin_global_funs =
  pp_raise ++
  link ++
  print ++
  each ++
  num_modulo

let all_builtin_funs =
  c_library_wrapper_funs ++
  utility_funs ++
  builtin_global_funs