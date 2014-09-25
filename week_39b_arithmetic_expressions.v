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
  | Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
  | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

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
     interpret (Times ae1 ae2) = (interpret ae1) * (interpret ae2))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Minus ae1 ae2) = (interpret ae1) - (interpret ae2)).

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
  && (interpret (Times (Times (Lit 2) (Lit 3)) (Times (Lit 4) (Lit 5))) =n= 120)
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
    | Minus ae1 ae2 => (interpreter ae1) - (interpreter ae2)
  end.

Compute (interpreter (Times (Lit 7) (Plus (Lit 5) (Lit 6)))).
Compute unit_test_for_interpret interpreter.

Lemma unfold_interpreter_lit :
  forall n : nat,
    interpreter (Lit n) = n.
Proof.
  unfold_tactic interpreter.
Qed.

Lemma unfold_interpreter_times :
  forall a b : arithmetic_expression,
    interpreter (Times a b) = (interpreter a) * (interpreter b).
Proof.
  unfold_tactic interpreter.
Qed.

Lemma unfold_interpreter_plus : 
  forall a b : arithmetic_expression,
    interpreter (Plus a b) = (interpreter a) + (interpreter b).
Proof.
  unfold_tactic interpreter.
Qed.

Lemma unfold_interpreter_minus :
  forall a b : arithmetic_expression,
    interpreter (Minus a b) = (interpreter a) - (interpreter b).
Proof.
  unfold_tactic interpreter.
Qed.

  
Lemma interpreter_fits_the_specification_of_interpreter :
  forall exp : arithmetic_expression,
    specification_of_interpret interpreter.
Proof.
  unfold specification_of_interpret.
  split.
    
    intro n.
    apply (unfold_interpreter_lit n).

    split.

      intros ae1 ae2.
      apply (unfold_interpreter_plus ae1 ae2).
      
      split.
        intros ae1 ae2.
        apply (unfold_interpreter_times ae1 ae2).

        intros ae1 ae2.
        apply (unfold_interpreter_minus ae1 ae2).

Qed.


(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction
  | SUB : byte_code_instruction.

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


(*
  Also, execute_byte_code_instruction is not recursive, so make sure to define it with Definition, not with Fixpoint.
*)

(* TODO: Skal vi ændre den måde x :: stack virker? *)
Definition execute_byte_code_instruction (instruction : byte_code_instruction) ( dstack : data_stack) : data_stack :=
  match instruction with
    | PUSH n => n :: dstack
    | ADD => match dstack with
               | x :: y :: stack => (plus x y) :: stack
               | x :: stack => x :: stack
               | nil => 0 :: nil                                    
             end
    | MUL => match dstack with
               | x :: y :: stack => (mult x y) :: stack
               | x :: stack => x :: stack
               | nil => 0 :: nil
             end                                 
    | SUB => match dstack with
               | x :: y :: stack => (minus x y) :: stack
               | x :: stack => x :: stack
               | nil => 0 :: nil
             end                                             
  end. 


Compute(execute_byte_code_instruction (PUSH 4) (1 :: 2 :: nil)).
Compute(execute_byte_code_instruction (MUL) (nil)).
Compute(execute_byte_code_instruction (MUL) (3 :: 2 :: nil)).
Compute(execute_byte_code_instruction (MUL) (1 :: nil)).



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

Theorem about_list_of_instructions : 
  forall ( p1 p2 : byte_code_program) (s : data_stack),
    execute_byte_code_program p2 (execute_byte_code_program p1 s) =
    execute_byte_code_program  (p1 ++ p2) s.
Proof.         
  intros p1 p2.
  induction p1 as [ | p1' p1s' IHsp1'].

  intro s.
  unfold app.
  rewrite -> unfold_byte_code_program_bc.
  reflexivity.

  intro s.
  rewrite -> unfold_byte_code_program_ic.
  rewrite <- (app_comm_cons).
  rewrite -> (unfold_byte_code_program_ic).
  rewrite -> (IHsp1' (execute_byte_code_instruction p1' s)).
  reflexivity.
Qed.
  

(* ********** *)

Definition specification_of_compile (compile : arithmetic_expression -> byte_code_program) :=
  (forall n : nat,
     compile (Lit n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Plus ae1 ae2) = (compile ae2) ++ (compile ae1) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Times ae1 ae2) = (compile ae2) ++ (compile ae1)++ (MUL :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Minus ae1 ae2) = (compile ae2) ++ (compile ae1) ++ (SUB :: nil)).

(* Exercise 6:
   Define a compiler as a function
   that satisfies the specification above
   and uses list concatenation, i.e., ++.
*)

Fixpoint compile_plusplus (ae : arithmetic_expression) : byte_code_program :=
  match ae with
    | Lit n => (PUSH n) :: nil
    | Plus ae1 ae2 => (compile_plusplus ae2) ++ (compile_plusplus ae1) ++ (ADD :: nil)
    | Times ae1 ae2 => (compile_plusplus ae2) ++ (compile_plusplus ae1) ++ (MUL :: nil)
    | Minus ae1 ae2 => (compile_plusplus ae2) ++ (compile_plusplus ae1) ++ (SUB :: nil)
  end.

Lemma unfold_compile_plusplus_lit :
  forall n : nat,
    compile_plusplus (Lit n) = (PUSH n) :: nil.
Proof.
  unfold_tactic compile_plusplus.
Qed.

Lemma unfold_compile_plusplus_plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_plusplus (Plus ae1 ae2) = (compile_plusplus ae2) ++ (compile_plusplus ae1) ++ (ADD :: nil).
Proof.
  unfold_tactic compile_plusplus.
Qed.

Lemma unfold_compile_plusplus_times :
  forall ae1 ae2 : arithmetic_expression,
    compile_plusplus (Times ae1 ae2) = (compile_plusplus ae2) ++ (compile_plusplus ae1) ++ (MUL :: nil).
Proof.
  unfold_tactic compile_plusplus.
Qed.

Lemma unfold_compile_plusplus_minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_plusplus (Minus ae1 ae2) = (compile_plusplus ae2) ++ (compile_plusplus ae1) ++ (SUB :: nil).
Proof.
  unfold_tactic compile_plusplus.
Qed.

Theorem compile_plusplus_fits_the_specification_of_compile :
  forall ae : arithmetic_expression,
    specification_of_compile compile_plusplus.
Proof.
  unfold specification_of_compile.
  split.
    intro n.
    apply (unfold_compile_plusplus_lit).
    
    split.
      intros ae1 ae2.
      apply (unfold_compile_plusplus_plus).

      split.
        intros ae1 ae2.
        apply (unfold_compile_plusplus_times).

        intros ae1 ae2.
        apply (unfold_compile_plusplus_minus).
Qed.

(* Exercise 7:
   Write a compiler as a function with an accumulator
   that does not use ++ but :: instead,
   and prove it equivalent to the compiler of Exercise 6.
*)

Fixpoint compile_acc (ae : arithmetic_expression) (acc : byte_code_program) : byte_code_program :=
  match ae with
    | Lit n => (PUSH n) :: acc
    | Plus ae1 ae2 => (compile_acc ae2 (compile_acc ae1 (ADD :: acc)))
    | Times ae1 ae2 => (compile_acc ae2 (compile_acc ae1 (MUL :: acc)))
    | Minus ae1 ae2 => (compile_acc ae2 (compile_acc ae1 (SUB :: acc)))
  end.

Compute(compile_acc (Plus (Lit 5) (Lit 3)) nil).

Lemma unfold_compile_acc_lit :
  forall (n : nat) (acc : byte_code_program),
    compile_acc (Lit n) acc = (PUSH n) :: acc.
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_plus :
  forall (ae1 ae2 : arithmetic_expression) (acc : byte_code_program),
    compile_acc (Plus ae1 ae2) acc = compile_acc ae2 (compile_acc ae1 (ADD :: acc)).
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_times :
  forall (ae1 ae2 : arithmetic_expression) (acc : byte_code_program),
    compile_acc (Times ae1 ae2) acc = compile_acc ae2 (compile_acc ae1 (MUL :: acc)).
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_minus :
  forall (ae1 ae2 : arithmetic_expression) (acc : byte_code_program),
    compile_acc (Minus ae1 ae2) acc = compile_acc ae2 (compile_acc ae1 (SUB :: acc)).
Proof.
  unfold_tactic compile_acc.
Qed.



Compute(execute_byte_code_program(compile_plusplus (Minus (Lit 5) (Lit 3))) nil).

Compute(execute_byte_code_program(compile_plusplus (Minus (Lit 3) (Lit 5))) nil).

Compute(execute_byte_code_program(compile_acc (Minus (Lit 5) (Lit 3)) nil) nil).

Compute(execute_byte_code_program(compile_acc (Minus (Lit 3) (Lit 5)) nil) nil).



(* EUREKA *)

Lemma about_compile_acc :
  forall (ae : arithmetic_expression) (acc bcp : byte_code_program),
    (compile_acc ae acc) ++ bcp = compile_acc ae (acc ++ bcp).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHa1 ae2 IHa2 | ae1' IHa1' ae2' IHa2' | ae1'' IHa1'' ae2'' IHa2'' ].

  intros acc bcp.
  rewrite ->2 (unfold_compile_acc_lit).
  Check(app_comm_cons).
  rewrite <- (app_comm_cons).
  reflexivity.

  intros acc bcp.
  rewrite ->2 (unfold_compile_acc_plus).
  rewrite -> (app_comm_cons).
  rewrite <- (IHa1 (ADD :: acc) bcp).
  rewrite <- (IHa2). 
  reflexivity.
  
  intros acc bcp.
  rewrite ->2 (unfold_compile_acc_times).
  rewrite -> (app_comm_cons).
  rewrite <- (IHa1' (MUL :: acc) bcp).
  rewrite <- (IHa2').
  reflexivity.

  intros acc bcp.
  rewrite ->2 (unfold_compile_acc_minus).
  rewrite -> (app_comm_cons).
  rewrite <- (IHa1'' (SUB :: acc) bcp).
  rewrite <- (IHa2'').
  reflexivity.
Qed.

Lemma compile_plusplus_fits_compile_acc :
  forall (ae : arithmetic_expression) (acc : byte_code_program),
    compile_acc ae acc = (compile_plusplus ae) ++ acc.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHa1 ae2 IHa2 | ae1' IHa1' ae2' IHa2' | ae1'' IHa1'' ae2'' IHa2''].
  intro acc.
  rewrite -> (unfold_compile_acc_lit).
  rewrite -> (unfold_compile_plusplus_lit).
  unfold app.
  reflexivity.

  intro acc.
  rewrite -> (unfold_compile_acc_plus).
  rewrite -> (unfold_compile_plusplus_plus).
  rewrite <- (IHa1).
  rewrite <- (IHa2).
  rewrite ->2 (about_compile_acc).
  unfold app.
  reflexivity.

  intro acc.
  rewrite -> (unfold_compile_acc_times).
  rewrite -> (unfold_compile_plusplus_times).
  rewrite <- (IHa1').
  rewrite <- (IHa2').
  rewrite ->2 (about_compile_acc).
  unfold app.
  reflexivity.

  intro acc.
  rewrite -> (unfold_compile_acc_minus).
  rewrite -> (unfold_compile_plusplus_minus).
  rewrite <- (IHa1'').
  rewrite <- (IHa2'').
  rewrite ->2 (about_compile_acc).
  unfold app.
  reflexivity.

Qed.


(* ********** *)

(* Exercise 8:
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program
   over an empty data stack.
  INDUCTION ON THE AE
*)



Definition check_stack (stack : data_stack) : nat :=
  match stack with
    | x :: nil => x
    | _ => 0
  end.

Check(specification_of_compile).
Check(specification_of_interpret).



Lemma executing_compile_is_the_same_as_interpreting :
  forall (ae : arithmetic_expression),
    interpreter ae = check_stack ( execute_byte_code_program (compile_acc ae nil) nil).
Proof.
  intro ae.
  induction ae as [ a | ae1 IHa1 ae2 IHa2 | ae1' IHa1' ae2' IHa2' | ae1'' IHa1'' ae2'' IHa2''].

  rewrite -> (unfold_interpreter_lit).
  rewrite -> (unfold_compile_acc_lit).
  rewrite -> (unfold_byte_code_program_ic).
  rewrite -> (unfold_byte_code_program_bc).
  unfold execute_byte_code_instruction.
  unfold check_stack.
  reflexivity.

  rewrite -> (unfold_interpreter_plus).
  rewrite -> (unfold_compile_acc_plus).

  rewrite -> (IHa1).
  rewrite -> (IHa2).
  rewrite ->4 (compile_plusplus_fits_compile_acc).
  rewrite <- (about_list_of_instructions).
  SearchAbout(app).
  rewrite -> (app_assoc).
  rewrite -> (about_list_of_instructions).
  rewrite <-3 (compile_plusplus_fits_compile_acc).

  rewrite -> (unfold_byte_code_program_ic).


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
