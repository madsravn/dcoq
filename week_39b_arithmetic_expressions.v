(* week_39b_arithmetic_expressions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working version, make sure to download
   the updated version after class.
*)

(* ********** *)

Require Import Arith Bool unfold_tactic List.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Source syntax: *)

Inductive arithmetic_expression : Type :=
  | Lit : nat -> arithmetic_expression
  | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
  | Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Exercise 0:
   Write samples of arithmetic expressions.
*)

Compute (Times (Lit 5) (Plus (Lit 3) (Lit 4))).
Compute (Plus (Lit 1) (Lit 2)).
Compute (Times (Lit 1) (Lit 2)).
Compute (Plus (Lit 1) (Plus (Lit 2) (Plus (Lit 3) (Lit 4)))).
Compute (Times (Lit 1) (Times (Lit 2) (Times (Lit 3) (Lit 4)))).

(* ********** *)

Definition specification_of_interpret (interpret : arithmetic_expression -> nat) :=
  (forall n : nat,
     interpret (Lit n) = n)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Plus ae1 ae2) = (interpret ae1) + (interpret ae2))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Times ae1 ae2) = (interpret ae1) * (interpret ae2)).

(* Exercise 1:
   Write unit tests.
*)



(* TODO: Lav nogle flere *)
Definition unit_test_for_interpret (interpret : arithmetic_expression -> nat) :=
  (interpret (Lit 5) =n= 5)
  &&
  (interpret (Times (Lit 1) (Lit 2)) =n= 2)
  &&
  (interpret (Plus (Lit 1) (Plus (Lit 2) (Lit 3))) =n= 6)
  &&
  (interpret (Times (Plus (Lit 1) (Lit 2)) (Plus (Lit 2) (Lit 3))) =n= 15)
  .

(* Exercise 2:
   Define an interpreter as a function
   that satisfies the specification above
   and verify that it passes the unit tests.
*)

Fixpoint interpreter ( ae : arithmetic_expression) : nat :=
  match ae with
    | Lit n => n
    | Plus ae1 ae2 => (interpreter ae1) + (interpreter ae2)
    | Times ae1 ae2 => (interpreter ae1) * (interpreter ae2)
  end.

Compute (interpreter (Times (Lit 7) (Plus (Lit 5) (Lit 6)))).
Compute unit_test_for_interpret interpreter.


(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction.

(* ********** *)

(* Byte-code programs: *)

Definition byte_code_program := list byte_code_instruction.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

(* Exercise 3:
   specify a function
     execute_byte_code_instruction : instr -> data_stack -> data_stack
   that executes a byte-code instruction, given a data stack
   and returns this stack after the instruction is executed.

   * Executing (PUSH n) given s has the effect of pushing n on s.

   * Executing ADD given s has the effect of popping two numbers
     from s and then pushing the result of adding them.

   * Executing MUL given s has the effect of popping two numbers
     from s and then pushing the result of multiplying them.

   For now, if the stack underflows, just assume it contains zeroes.
*)

Compute( 1 :: 2 :: 3 :: nil).
Compute( head ( 1 :: 2 :: 3 :: nil)).

Fixpoint execute_byte_code_instruction (instruction : byte_code_instruction) ( dstack : data_stack) : data_stack :=
  match instruction with
    | PUSH n => n :: dstack
    | ADD => match dstack with
               | x :: y :: stack => (plus x y) :: stack
               | x :: stack => x :: stack
               | nil => 0 :: nil                                    
             end
    | MIL => match dstack with
               | x :: y :: stack => (mult x y) :: stack
               | x :: stack => x :: stack
               | nil => 0 :: nil
             end                                 
  end. 

Compute(execute_byte_code_instruction (PUSH 4) (1 :: 2 :: nil)).
Compute(execute_byte_code_instruction (MUL) (nil)).
Compute(execute_byte_code_instruction (MUL) (3 :: 2 :: nil)).


(* ********** *)

(* Exercise 4:
   Define a function
     execute_byte_code_program : byte_code_program -> data_stack -> data_stack
   that executes a given byte-code program on a given data stack,
   and returns this stack after the program is executed.
*)

Fixpoint execute_byte_code_program (program : byte_code_program) (dstack : data_stack) : data_stack :=
  match program with
    | nil => dstack
    | p1 :: byte_codes => execute_byte_code_program byte_codes (execute_byte_code_instruction p1 dstack)
  end.

Compute(execute_byte_code_program ((PUSH 4) :: (PUSH 3) :: (MUL) :: nil) (0 :: nil)).

(* ********** *)

(* Exercise 5:
   Prove that for all programs p1, p2 and data stacks s,
   executing (p1 ++ p2) with s
   gives the same result as
   (1) executing p1 with s, and then
   (2) executing p2 with the resulting stack.

  DOING INDUCTION ON P1
*)

Lemma plus_plus : 
  forall p : byte_code_program,
    nil ++ p = p.
Proof.
  intro p.
  (* C-c C-a C-n  _ ++ _*)
  unfold app.
  reflexivity.
Qed.


Lemma unfold_byte_code_program_bc : 
  forall s : data_stack,
    execute_byte_code_program nil s = s.
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Lemma unfold_byte_code_program_ic :
  forall (p1 : byte_code_instruction) (program : byte_code_program) (s : data_stack),
    execute_byte_code_program (p1 :: program) s = 
    execute_byte_code_program program (execute_byte_code_instruction p1 s).
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Theorem list_of_programs : 
  forall ( p1 p2 : byte_code_program) (s : data_stack),
    execute_byte_code_program p1 (execute_byte_code_program p2 s) =
    execute_byte_code_program  (p1 ++ p2) s.
Proof.         
  intros p1 p2.
  intro s.

  induction p1 as [ | p1' IHp1' IHsp1'].
  rewrite -> plus_plus.
  rewrite -> unfold_byte_code_program_bc.
  reflexivity.

  rewrite -> unfold_byte_code_program_ic.
  
Admitted.
  




(* ********** *)

Definition specification_of_compile (compile : arithmetic_expression -> byte_code_program) :=
  (forall n : nat,
     compile (Lit n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Plus ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Times ae1 ae2) = (compile ae1) ++ (compile ae2)++ (MUL :: nil)).

(* Exercise 6:
   Define a compiler as a function
   that satisfies the specification above
   and uses list concatenation, i.e., ++.
*)

(* Exercise 7:
   Write a compiler as a function with an accumulator
   that does not use ++ but :: instead,
   and prove it equivalent to the compiler of Exercise 6.
*)

(* ********** *)

(* Exercise 8:
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program
   over an empty data stack.
  INDUCTION ON THE AE
*)

(* ********** *)

(* Exercise 9:
   Write a Magritte-style execution function for a byte-code program
   that does not operate on natural numbers but on syntactic representations
   of natural numbers:

   Definition data_stack := list arithmetic_expression.

   * Executing (PUSH n) given s has the effect of pushing (Lit n) on s.

   * Executing ADD given s has the effect of popping two arithmetic
     expressions from s and then pushing the syntactic representation of
     their addition.

   * Executing MUL given s has the effect of popping two arithmetic
     expressions from s and then pushing the syntactic representation of
     their multiplication.

   Again, for this week's exercise,
   assume there are enough arithmetic expressions on the data stack.
   If that is not the case, just pad it up with syntactic representations
   of zero.

*)

(* Exercise 10:
   Prove that the Magrite-style execution function from Exercise 9
   implements a decompiler that is the left inverse of the compiler
   of Exercise 6.
*)

(* ********** *)

(* end of week_39b_arithmetic_expressions.v *)
