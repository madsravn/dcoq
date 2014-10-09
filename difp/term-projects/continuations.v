(* continuations.v *)
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

(* You are asked to:


   * define unit tests of course;


   * prove that the specification above specifies a unique function;


   * implement an interpreter in direct style

       Fixpoint interpreter_ds (e : expression) : result :=
         ...
  
       Definition interpreter_v0 (e : expression) : result :=
         interpreter_ds ...

     and prove that it satisfies the specification of the interpreter;


   * write an interpreter in continuation-passing style,

       Fixpoint interpreter_cps (ans : Type)
                                (e : expression)
                                (k : result -> ans) : ans :=
         ...
  
       Definition interpreter_v1 (e : expression) : result :=
         interpreter_cps ...

     and prove that it satisfies the specification of the interpreter;


   * write an interpreter in continuation-passing style
     with two continuations, one for values and the other for errors,     

       Fixpoint interpreter_cps2 (ans : Type)
                                 (e : expression)
                                 (vk : expressible -> ans)
                                 (ek : string -> ans) : ans :=
         ...
  
       Definition interpreter_v2 (e : expression) : result :=
         interpreter_cps2 ...

     and prove that it satisfies the specification of the interpreter.


   * write a continuation-based interpreter
     with one continuation,

       Fixpoint interpreter_cps' (e : expression)
                                 (k : expressible -> result) : result :=
         ...
  
       Definition interpreter_v3 (e : expression) : result :=
         interpreter_cps' ...

     and prove that it satisfies the specification of the interpreter.
     (Note: "continuation-based" means that interpreter_cps' is using
     a continuation and all of its calls are tail calls,
     but the type of its result is not an abstract type of answers.)
*)

(* ********** *)

(* end of continuations.v *)
