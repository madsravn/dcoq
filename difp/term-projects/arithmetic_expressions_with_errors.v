(* arithmetic_expressions_with_errors.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: ... *)
(* Student number: ... *)

(* ********** *)

Require Import Arith NPeano String List unfold_tactic.

Check div.
Compute (div 5 3, div 6 3, div 7 3, div 8 3, div 9 3).

(* ********** *)

(* The arithmetic expressions: *)

Inductive expression : Type :=
  | Lit : nat -> expression
  | Plus : expression -> expression -> expression
  | Times : expression -> expression -> expression
  | Minus : expression -> expression -> expression
  | Divide : expression -> expression -> expression.

(* ********** *)

(* An expressible value is the result of evaluating an expression: *)

Definition expressible := nat.

(* Type conversion between natural numbers and expressible values: *)

Definition nat_to_expressible (n : nat) : expressible :=
  n.

Definition expressible_to_nat (v : expressible) : nat :=
  v.

(* Operations over expressible values: *)

Definition plus_expressible (v1 v2 : expressible) : expressible :=
  nat_to_expressible (expressible_to_nat v1 + expressible_to_nat v2).

Definition times_expressible (v1 v2 : expressible) : expressible :=
  nat_to_expressible (expressible_to_nat v1 * expressible_to_nat v2).

Definition ltb_expressible (v1 v2 : expressible) : bool :=
  ltb (expressible_to_nat v1) (expressible_to_nat v2).

Definition minus_expressible (v1 v2 : expressible) : expressible :=
  nat_to_expressible (expressible_to_nat v1 - expressible_to_nat v2).

Definition zerop_expressible (v : expressible) : bool :=
  match expressible_to_nat v with
    | 0 => true
    | _ => false
  end.

Definition divide_expressible (v1 v2 : expressible) : expressible :=
  nat_to_expressible (div (expressible_to_nat v1) (expressible_to_nat v2)).

(* ********** *)

(* The result of interpreting an arithmetic expression :
   * an expressible value, or
   * an error message
*)

Inductive result : Type :=
  | Value : expressible -> result
  | Error : string -> result.

(* ********** *)

(* Two useful lemmas: *)

Lemma same_Value :
  forall v_1 v_2 : nat,
    Value v_1 = Value v_2 -> v_1 = v_2.
Proof.
  intros v_1 v_2 H_Value.
  injection H_Value.  (* Ja, ja, we didn't see this one in class... *)
  intro H_tmp.
  exact H_tmp.
Qed.

(* Note: you won't need "injection" in this term project. *)

Lemma same_Error :
  forall s_1 s_2 : string,
    Error s_1 = Error s_2 -> s_1 = s_2.
Proof.
  intros s_1 s_2 H_Error.
  injection H_Error.
  intro H_tmp.
  exact H_tmp.
Qed.

(* ********** *)

(* Specification of the interpreter: *)

Definition specification_of_interpret (interpret : expression -> result) :=
  (forall n : nat,
     interpret (Lit n) = Value (nat_to_expressible n))
  /\
  ((forall (e1 e2 : expression) (s1 : string),
      interpret e1 = Error s1 ->
      interpret (Plus e1 e2) = Error s1)
   /\
   (forall (e1 e2 : expression) (v1 : expressible) (s2 : string),
      interpret e1 = Value v1 ->
      interpret e2 = Error s2 ->
      interpret (Plus e1 e2) = Error s2)
   /\
   (forall (e1 e2 : expression) (v1 v2 : expressible),
      interpret e1 = Value v1 ->
      interpret e2 = Value v2 ->
      interpret (Plus e1 e2) = Value (plus_expressible v1 v2)))
  /\
  ((forall (e1 e2 : expression) (s1 : string),
      interpret e1 = Error s1 ->
      interpret (Times e1 e2) = Error s1)
   /\
   (forall (e1 e2 : expression) (v1 : expressible) (s2 : string),
      interpret e1 = Value v1 ->
      interpret e2 = Error s2 ->
      interpret (Times e1 e2) = Error s2)
   /\
   (forall (e1 e2 : expression) (v1 v2 : expressible),
      interpret e1 = Value v1 ->
      interpret e2 = Value v2 ->
      interpret (Times e1 e2) = Value (times_expressible v1 v2)))
  /\
  ((forall (e1 e2 : expression) (s1 : string),
      interpret e1 = Error s1 ->
      interpret (Minus e1 e2) = Error s1)
   /\
   (forall (e1 e2 : expression) (v1 : expressible) (s2 : string),
      interpret e1 = Value v1 ->
      interpret e2 = Error s2 ->
      interpret (Minus e1 e2) = Error s2)
   /\
   (forall (e1 e2 : expression) (v1 v2 : expressible),
      interpret e1 = Value v1 ->
      interpret e2 = Value v2 ->
      ltb_expressible v1 v2 = true ->
      interpret (Minus e1 e2) = Error "numerical underflow")
  /\
   (forall (e1 e2 : expression) (v1 v2 : expressible),
      interpret e1 = Value v1 ->
      interpret e2 = Value v2 ->
      ltb_expressible v1 v2 = false ->
      interpret (Minus e1 e2) = Value (minus_expressible v1 v2)))
   /\
  ((forall (e1 e2 : expression) (s1 : string),
      interpret e1 = Error s1 ->
      interpret (Divide e1 e2) = Error s1)
   /\
   (forall (e1 e2 : expression) (v1 : expressible) (s2 : string),
      interpret e1 = Value v1 ->
      interpret e2 = Error s2 ->
      interpret (Divide e1 e2) = Error s2)
   /\
   (forall (e1 e2 : expression) (v1 v2 : expressible),
      interpret e1 = Value v1 ->
      interpret e2 = Value v2 ->
      zerop_expressible v2 = true ->
      interpret (Divide e1 e2) = Error "division by zero")
   /\
   (forall (e1 e2 : expression) (v1 v2 : nat),
      interpret e1 = Value v1 ->
      interpret e2 = Value v2 ->
      zerop_expressible v2 = false ->
      interpret (Divide e1 e2) = Value (divide_expressible v1 v2))).

(* ********** *)

(* The byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction
  | SUB : byte_code_instruction
  | DIV : byte_code_instruction.

(* Byte-code programs: *)

Inductive byte_code_program : Type :=
  | Program : list byte_code_instruction -> byte_code_program.

(* A stackable value is what can be put on the data stack: *)

Definition stackable := nat.

(* Type conversion between natural numbers and stackable values: *)

Definition nat_to_stackable (n : nat) : stackable :=
  n.

Definition stackable_to_nat (v : stackable) : nat :=
  v.

Definition stackable_to_expressible (v : stackable) : expressible :=
  v.

(* Operations over stackable values: *)

Definition plus_stackable (v1 v2 : stackable) : stackable :=
  nat_to_stackable (stackable_to_nat v1 + stackable_to_nat v2).

Definition times_stackable (v1 v2 : stackable) : stackable :=
  nat_to_stackable (stackable_to_nat v1 * stackable_to_nat v2).

Definition ltb_stackable (v1 v2 : stackable) : bool :=
  ltb (stackable_to_nat v1) (stackable_to_nat v2).

Definition minus_stackable (v1 v2 : stackable) : stackable :=
  nat_to_stackable (stackable_to_nat v1 - stackable_to_nat v2).

Definition zerop_stackable (v : stackable) : bool :=
  match stackable_to_nat v with
    | 0 => true
    | _ => false
  end.

Definition divide_stackable (v1 v2 : stackable) : stackable :=
  nat_to_stackable (div (stackable_to_nat v1) (stackable_to_nat v2)).

(* The data stack: *)

Definition data_stack := list stackable.

(* The result of decoding and executing a byte-code instruction: *)

Inductive intermediate_result : Type :=
  | OK : data_stack -> intermediate_result
  | KO : string -> intermediate_result.

(* Specification of decoding and executing a byte-code instruction: *)

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> intermediate_result) :=
  (forall (n : nat) (ds : data_stack),
     decode_execute (PUSH n) ds = OK (nat_to_stackable n :: ds))
  /\
  ((forall (v1 v2 : stackable) (ds : data_stack),
      decode_execute ADD (v2 :: v1 :: ds) = OK ((plus_stackable v1 v2) :: ds))
   /\
   (forall (v2 : stackable),
      decode_execute ADD (v2 :: nil) = KO "data-stack underflow")
   /\
   (decode_execute ADD nil = KO "data-stack underflow"))
  /\
  ((forall (v1 v2 : stackable) (ds : data_stack),
      decode_execute MUL (v2 :: v1 :: ds) = OK ((times_stackable v1 v2) :: ds))
   /\
   (forall (v2 : stackable),
      decode_execute MUL (v2 :: nil) = KO "data-stack underflow")
   /\
   (decode_execute MUL nil = KO "data-stack underflow"))
  /\
  ((forall (v1 v2 : stackable) (ds : data_stack),
     ltb_stackable v1 v2 = true ->
     decode_execute SUB (v2 :: v1 :: ds) = KO "numerical underflow")
   /\
   (forall (v1 v2 : stackable) (ds : data_stack),
      ltb_stackable v1 v2 = false ->
      decode_execute SUB (v2 :: v1 :: ds) = OK ((minus_stackable v1 v2) :: ds))
   /\
   (forall (v2 : stackable),
      decode_execute SUB (v2 :: nil) = KO "data-stack underflow")
   /\
   (decode_execute SUB nil = KO "data-stack underflow"))
  /\
  ((forall (v1 v2 : stackable) (ds : data_stack),
      zerop_stackable v2 = true ->
      decode_execute DIV (v2 :: v1 :: ds) = KO "division by zero")
   /\
   (forall (v1 v2 : stackable) (ds : data_stack),
      zerop_stackable v2 = false ->
      decode_execute DIV (v2 :: v1 :: ds) = OK ((divide_stackable v1 v2) :: ds))
   /\
   (forall (v2 : stackable),
      decode_execute DIV (v2 :: nil) = KO "data-stack underflow")
   /\
   (decode_execute DIV nil = KO "data-stack underflow")).

(* The end result of the fetch-decode-execute loop: *)

Inductive end_result : Type :=
  | End_OK : data_stack -> end_result
  | End_KO : string -> end_result.

(* Specification of the fetch-decode-execute loop: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> end_result) :=
  forall decode_execute : byte_code_instruction -> data_stack -> intermediate_result,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
       fetch_decode_execute_loop nil ds = End_OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
       decode_execute bci ds = OK ds' ->
       fetch_decode_execute_loop (bci :: bcis') ds =
       fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
       decode_execute bci ds = KO s ->
       fetch_decode_execute_loop (bci :: bcis') ds = End_KO s).

(* Specification of the virtual machine: *)

Definition specification_of_run (run : byte_code_program -> result) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> end_result,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction)
            (v : stackable),
       fetch_decode_execute_loop bcis nil = End_OK (v :: nil) ->
       run (Program bcis) = Value (stackable_to_expressible v))
    /\
    (forall (bcis : list byte_code_instruction)
            (v : stackable),
       fetch_decode_execute_loop bcis nil = End_OK nil ->
       run (Program bcis) = Error "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (v v' : stackable)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = End_OK (v :: v' :: ds'') ->
       run (Program bcis) = Error "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = End_KO s ->
       run (Program bcis) = Error s).

(* ********** *)

(* Specification of the auxiliary compile function: *)

Definition specification_of_compile_aux (compile_aux : expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Lit n) = PUSH n :: nil)
  /\
  (forall e1 e2 : expression,
     compile_aux (Plus e1 e2) = (compile_aux e1) ++ (compile_aux e2) ++ (ADD :: nil))
  /\
  (forall e1 e2 : expression,
     compile_aux (Times e1 e2) = (compile_aux e1) ++ (compile_aux e2) ++ (MUL :: nil))
  /\
  (forall e1 e2 : expression,
     compile_aux (Minus e1 e2) = (compile_aux e1) ++ (compile_aux e2) ++ (SUB :: nil))
  /\
  (forall e1 e2 : expression,
     compile_aux (Divide e1 e2) = (compile_aux e1) ++ (compile_aux e2) ++ (DIV :: nil)).

(* Specification of the compiler: *)

Definition specification_of_compile (compile : expression -> byte_code_program) :=
  forall compile_aux : expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall e : expression,
      compile e = Program (compile_aux e).

(* ********** *)

(* You are asked to:

   * define unit tests of course;

   * prove that all the specifications specify unique functions;

   * implement an interpreter, a virtual machine, and a compiler
     and prove that they satisfy their respective specification; and

   * prove that compiling an expression and running it with the virtual machine
     gives the same result (i.e., the same expressible value or the same error message)
     as interpreting that expression.

*)

(* If you feel like over-achieving:

   * make _minimal_ modifications to the VM
     to make it a Magritte VM;

   * devise a Magritte interpreter
     and argue why it is one;

   * prove that compiling an expression and running it with the
     Magritte virtual machine gives the same result as interpreting
     that expression with the Magritte interpreter; and

   * define a decompiler
     and prove that it is a left inverse of the compiler.

*)

(* ********** *)

(* end of arithmetic_expressions_with_errors.v *)
