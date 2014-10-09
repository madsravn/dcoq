(* byte_code_verification.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: ... *)
(* Student number: ... *)

(* ********** *)

Require Import Arith String List unfold_tactic.

(* ********** *)

(* The arithmetic expressions: *)

Inductive expression : Type :=
  | Lit : nat -> expression
  | Plus : expression -> expression -> expression
  | Times : expression -> expression -> expression.

(* ********** *)

(* Specification of the interpreter: *)

Definition specification_of_interpret (interpret : expression -> nat) :=
  (forall n : nat,
     interpret (Lit n) = n)
  /\
  (forall e1 e2 : expression,
     interpret (Plus e1 e2) = (interpret e1) + (interpret e2))
  /\
  (forall e1 e2 : expression,
     interpret (Times e1 e2) = (interpret e1) * (interpret e2)).

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction.

(* Byte-code programs: *)

Inductive byte_code_program := 
  | Program : list byte_code_instruction -> byte_code_program.

(* Data stack: *)

Definition data_stack := list nat.

(* The result of decoding and executing a byte-code instruction: *)

Inductive intermediate_result : Type :=
  | OK : data_stack -> intermediate_result
  | KO : string -> intermediate_result.

(* Specification of decoding and executing a byte-code instruction: *)

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> intermediate_result) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((forall (n1 n2 : nat)
           (ds : data_stack),
      decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds))
   /\
   (forall (n2 : nat),
      decode_execute ADD (n2 :: nil) = KO "stack underflow for ADD")
   /\
   (decode_execute ADD nil = KO "stack underflow for ADD"))
  /\
  ((forall (n1 n2 : nat)
           (ds : data_stack),
      decode_execute MUL (n2 :: n1 :: ds) = OK ((n1 * n2) :: ds))
   /\
   (forall (n2 : nat),
      decode_execute MUL (n2 :: nil) = KO "stack underflow for MUL")
   /\
   (decode_execute MUL nil = KO "stack underflow for MUL")).

(* The result of the fetch-decode-execute loop: *)

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

(* The result of running the virtual machine :
   * a natural number, or
   * an error message
*)

Inductive result : Type :=
  | Value : nat -> result
  | Error  : string -> result.

(* Specification of the virtual machine: *)

Definition specification_of_run (run : byte_code_program -> result) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> end_result,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = End_OK (n :: nil) ->
       run (Program bcis) = Value n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = End_OK nil ->
       run (Program bcis) = Error "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = End_OK (n :: n' :: ds'') ->
       run (Program bcis) = Error "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = End_KO s ->
       run (Program bcis) = Error s).

(* ********** *)

(* You are asked to:

   * adjust your compiler for arithmetic expressions
     for the new type of byte-code programs;

   * prove that the new specifications above define unique functions;

   * implement a virtual machine that satisfies the specification above;

   * implement the byte-code verifier of the PL lecture notes at
       http://users-cs.au.dk/danvy/dProgSprog/Lecture-notes/week-18.html#index-61
  
       Definition verify (p : byte_code_program) : bool :=
         ...
  
   * prove that the compiler emits well-behaved byte-code programs:
  
       Theorem the_compiler_emits_well_behaved_code :
         forall ae : arithmetic_expression,
           verify (compile ae) = true.
  
   * prove that if a byte-code program is well behaved,
     it yields no errors at run time:
  
       Theorem safe_run :
         forall p : byte_code_program,
           verify p = true ->
           exists n : nat,
             execute p = Value n.
*)

(* ********** *)

(* end of byte_code_verification.v *)
