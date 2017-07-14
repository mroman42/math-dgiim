(* # Preface *)
(*
In order to open this lecture in Coq(ide)/Proofgeneral, you need to compile the
Coq file `lecture1.v` into an _object file_ `lecture.vo` first. The `.vo` file
contains a lambda term that represents the definitions and proofs in the `.v`
file, in which all uses of tactics have been compiled away.

Compiling a Coq file can be done in two ways:

- Open your terminal, and run `coqc lecture1.v`.
- Open the file `lecture1.v` in Coqide or Proofgeneral, and press in the menu
  "Compile", press "Compile buffer".
*)
Require Export lecture1.
Open Scope string_scope.

(* # Contents *)
(*
The topics of this lecture are:

- Using inductive types to represent syntax of program languages.
- Using inductive relations to represent big and small step operational semantics.
- The use of tactics to automate proofs.

# Tactics

In this lecture, we will learn how to use the following tactics:

- `inv` : the tactic `inv H` performs inversion on a hypothesis of an indexed
  inductive type. It can be thought of as the dual of applying a constructor.
- `subst` : the tactic `subst x`, where `x` is a variable, checks whether there
  is a hypothesis `H : x = y` or `H : y = x`, and then substitutes all
  occurrences of `x` in the goal and the all other hypotheses by `y`. After
  that, it removes `H`. 
- `change` : the tactic `change x into y` substitutes all occurrences of `x`
  into `y` provided `x` and `y` are equal by computation (also called
  _definitionally equal_).
- `apply .. in ..` : this is variant of the `apply` tactic that can be used in
  hypotheses.

     H1 : R a0 .. an,
     H2 : forall x1 .. xn, P x1 .. xn -> R x1 .. xn
     |- Q
    ------------------------------------------------- 'apply H2 in H1`
     H1 : P a0 .. an,
     H2 : forall x1 .. xn, P x1 .. xn -> R x1 .. xn
     |- Q

- `eapply` : this tactic behaves like `apply`, but it may leave existential
  variables (evar) for universally quantified premises that cannot be inferred. 
- `eassumption` : this tactic behaves like `assumption`, but can be used when
  the goal contains an evar.
- `eauto` : a brute-force depth first search mechanism.
*)

(*
Technical node: the standard `inversion` tactic of Coq is not so good as it
leaves a lot of garbage. Inspired by CompCert, we define a smarter version,
which directly substitutes all equalities that have been generated, and clears
the original hypothesis. Source: http://compcert.inria.fr/doc/html/Coqlib.html.
*)
Ltac inv H := inversion H; clear H; subst.

(* # A language for extended arithmetic expressions *)
(*
We will start by formalizing the semantics of a very simple language: arithmetic
expressions extended with conditionals and let expressions. In the second part
of this lecture, we will extend this language with additional features, namely
while loops and mutable state.

The syntax of our arithmetic expression language is as follows:

Values:        v ::= b | n
Operators:    op ::= + | - | <= | < | ==
Expressions:   e ::= x | v | let x := e1 in e2 | e1 `op` e2 | if e1 then e2 else e3

Here, `b` ranges over Booleans, `n` over natural numbers, and `x` over
variables, which are bound by the let construct.

As we have seen before, we make use of Coq's module system to put this language
definition in its own namespace. That way, we do not get conflicting names when
we define our extended language.
*)
Module stateless_language.
(* ## Syntax *)
(*
As is usual in Coq, or any common functional programming language, we represent
the syntax by a series of inductive data types. 
*)
Inductive val : Type :=
  | VBool : bool -> val
  | VNat : nat -> val.

Inductive bin_op : Type :=
  | PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive expr : Type :=
  | EVar : string -> expr
  | EVal : val -> expr
  | ELet : string -> expr -> expr -> expr
  | EOp : bin_op -> expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr.

(*
We use strings to represent variables, and do that for two reasons: it keeps
the syntax conceptually simple and allows us to write down concrete terms
with a higher level of convenience. String in Coq have type `string` and the
usual syntax "this is a string" can be used to write strings.

(We could use Coq's expressive notation machinery to define a parser and pretty
printer for our language, so that we could use notations that are very close to
those we use informally. In this lecture, we will not do that, instead we will
be very explicit about the ASTs that we use).
*)

(*
Now let us take a look at some examples.
*)
(* `10 + 20 == 30` *)
Definition example1 : expr :=
  EOp EqOp
    (EOp PlusOp (EVal (VNat 10)) (EVal (VNat 20)))
    (EVal (VNat 30)).

(* `let x := 10 + 20 in let y := 5 <= x in y` *) 
Definition example2 : expr :=
  ELet "x" (EOp PlusOp (EVal (VNat 10)) (EVal (VNat 20)))
    (ELet "y" (EOp LeOp (EVal (VNat 5)) (EVar "x"))
    (EVar "y")).

(* ### Exercise *)
(*
Turn the following expressions into corresponding `expr`s in Coq.
*)
(* `let x := false in x` *)
Definition example3 : expr := EVar "exercise".

(* `let x := (let y := 1 + 1 in y) in x + x` *)
Definition example4 : expr := EVar "exercise".

(* `if 10 <= 12 then 1 else 2` *)
Definition example5 : expr := EVar "exercise".

(* ## Semantics of operators *)
(* We start by defining the semantics of binary operations. We do this by
defining a function:

  eval_bin_op : bin_op -> val -> val -> option val

We have seen the `option` already in the previous lecture, but we will take a
look at it again:

  Inductive option (A : Type) : Type :=
    | None
    | Some : A -> option A

In the semantics of binary operators, we use `None` to handle errors, and `Some`
to handle actual results. Errors occur when operators are applied to the wrong
kind of arguments, for example, when the operator `<=` (LeOp) is applied to
Boolean arguments.
*)
Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | MinusOp, VNat n1, VNat n2 => Some (VNat (n1 - n2))
  | LeOp, VNat n1, VNat n2 => Some (VBool (Nat.leb n1 n2))
  | LtOp, VNat n1, VNat n2 => Some (VBool (Nat.ltb n1 n2))
  | EqOp, VNat n1, VNat n2 => Some (VBool (Nat.eqb n1 n2))
  | EqOp, VBool n1, VBool n2 => Some (VBool (Bool.eqb n1 n2))
  | _, _, _ => None
  end.

(* ### Exercise *)
(*
You could avoid the partiality in `eval_bin_op` by representing values in a
dependently typed way, i.e. as values indexed by types. You can do this as an
exercise in Agda or Coq. In this lecture, we will not pursue this approach,
because Coq's facilities for programming with dependent types are not as good as
Agda's (Coq's focus is mostly on proving, whereas Agda's focus is more on
programming).
*)

(* ## Substitution *)
(*
The next function that we define is substitution, which we will use to define
the semantics of let expressions. Substitution `subst x w e` replaces variables
`x` by value `w` in the expression `e`. We define is by structural recursion
over the expression `e`.
*)
Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EVal v => EVal v
  | EVar y => if string_dec x y then EVal w else EVar y
  | ELet y e1 e2 =>
     if string_dec x y
     then ELet y (subst x w e1) e2
     else ELet y (subst x w e1) (subst x w e2)
  | EOp op e1 e2 => EOp op (subst x w e1) (subst x w e2)
  | EIf e1 e2 e3 => EIf (subst x w e1) (subst x w e2) (subst x w e3)
  end.
(*
Convince yourself that this definition is indeed structurally recursive.
*)

(*
Technical note: Note that the definition of substitution becomes significantly
more complicated when we consider the case where the term that is being
substituted (here `w`) may contain free variables. In that case, one has to deal
with _variable capture_. Consider the following example in lambda calculus:

  (λ x y, x y) y → (λ y, x y)[x:=y]

By substituting naively, the RHS will become `λ y, y y`, which is wrong.
Instead, one should first-alpha rename, so that substitution results in
`λ z, y z`.

Since we only substitute values (which are closed by definition, as they cannot
contain variables), we do not have to deal with this problem, but it will
evidently occur when dealing with richer languages. To that end, one may use
a different representation of binders, such as De Bruijn indexes.
*)

(*
The next step is to define the semantics of expressions. We could try to do
this in a similar way as we have defined the semantics of operators, namely,
by defining a function:

  eval : expr -> option val

Unfortunately, this does not quite work. The definition below is rejected by
Coq because it is not structurally recursive.
*)
Fail Fixpoint eval (e : expr) : option val :=
  match e with
  | EVar x => None
  | EVal v => Some v
  | ELet y e1 e2 =>
     match eval e1 with
     | Some v => eval (subst y v e2)
     | None => None
     end
  | EOp op e1 e2 =>
     match eval e1 with
     | Some v1 =>
       match eval e2 with
       | Some v2 => eval_bin_op op v1 v2
       | None => None
       end
     | None => None
     end
   | EIf e1 e2 e3 =>
      match eval e1 with
      | Some (VBool true) => eval e2
      | Some (VBool false) => eval e3
      | _ => None
      end
   end.
(*
The problem here is that `subst y v e2` is not smaller than `e2`, so Coq
rejects this definition.

We could circumvent this problem by defining the evaluation function using a
map that associates variables to values (a _stack_), and look up values in the
stack when evaluating variables. This is a fun suggestion for a *homework
exercise* (including proving a correspondence with the big- and small-step
semantics below), but we will not pursue that direction in this lecture. The
reason for that is that we will consider while loops in the next part, and then
evaluation will inevitably not be total.
*)

(* ## Big-step semantics *)
(*
In the lecture, we will explore two different, but commonly used ways of
defining a semantics:

- Big-step style, by a relation

    big_step : expr -> val -> Prop

  That relates expressions and their values.

- Small-step style, by a relation

    step : expr -> expr -> Prop

  That performs one step of execution, of which we then take the reflexive/
  transitive closure.

We will formalize both using inductive relations. Let us start with the big-step
style.
*)
Inductive big_step : expr -> val -> Prop :=
  | Val_big_step v : big_step (EVal v) v
  | Let_big_step y e1 e2 v1 v2 :
     big_step e1 v1 ->
     big_step (subst y v1 e2) v2 ->
     big_step (ELet y e1 e2) v2
  | If_big_step_true e1 e2 e3 v :
     big_step e1 (VBool true) ->
     big_step e2 v ->
     big_step (EIf e1 e2 e3) v
  | If_big_step_false e1 e2 e3 v :
     big_step e1 (VBool false) ->
     big_step e3 v ->
     big_step (EIf e1 e2 e3) v
  | Op_big_step e1 e2 op v1 v2 v :
     big_step e1 v1 ->
     big_step e2 v2 ->
     eval_bin_op op v1 v2 = Some v ->
     big_step (EOp op e1 e2) v.

(*
In the definition of an inductive relation, like the big-step semantics above,
one should really think the constructors as _inference rules_:

  --------------------- `Val_big_step`
   big_step (EVal v) v


   big_step e1 v1     big_step (subst y v1 e2) v2
  ------------------------------------------------ `Let_big_step`
              big_step (ELet y e1 e2) v2


   big_step e1 (VBool true)       big_step e2 v
  ---------------------------------------------- `If_big_step_true`
           big_step (EIf e1 e2 e3) v


   big_step e1 (VBool false)      big_step e3 v
  ---------------------------------------------- `If_big_step_true`
           big_step (EIf e1 e2 e3) v


   big_step e1 v1    big_step e2 v2    eval_bin_op op v1 v2 = Some v
  ------------------------------------------------------------------- `Op_big_step`
                      big_step (EOp op e1 e2) v

*)

(*
Now let us take a look at the example programs we have seen before to see how we
can use the inference rules to prove that said programs have a certain value. 
*)
Lemma big_step_example1 : big_step example1 (VBool true).
Proof.
  unfold example1. (* expose the definition of `example1` *)
  (* At the top-level we have an `EOp`, so the only choice is to use the
  constructor `Op_big_step`, which corresponds to the inference rule for binary
  operators:

    Op_big_step e1 e2 op v1 v2 v :
      big_step e1 v1 ->
      big_step e2 v2 ->
      eval_bin_op op v1 v2 = Some v ->
      big_step (EOp op e1 e2) v.

  As we have seen in the previous lecture, we could use the tactic `apply` to
  reduce proving our current goal to proving the premises of the above rule.
  Let us try that:
  *)
  Fail apply Op_big_step.
  (*
  Unfortunately, this does not quite work, Coq complains that it cannot guess
  the values `v1` and `v2` (i.e. the resulting values of the sub-expressions).
  To remedy that problem, we could explicitly specify these values, by using
  the `with` keyword of the `apply` tactic:

    apply Op_big_step with (v1:=VNat 30) (v2:=VNat 30).

  You should try to carry out the proof this way, but as you will see, it
  quickly becomes tedious. Instead, we will look at another tactic: `eapply`.
  *)
  eapply Op_big_step.
  (*
  After executing this tactic, we get goals:

  1. `big_step (EOp PlusOp (EVal (VNat 10)) (EVal (VNat 20))) ?v1`
  2. `big_step (EVal (VNat 30)) ?v2`
  3. `eval_bin_op EqOp ?v1 ?v2 = Some (VBool true)`

  What we see here is something new, _existential variables_ (or _evars_ for
  short) `?v1` and `?v2`. Evars represent holes, that have to be instantiated at
  a later point while carrying out the proof.
  *)
  - (* We use `eapply` again for the nested binary operator. *)
    eapply Op_big_step.
    (* After this, we get evars `?v10` and `?v20` for the values of the
    sub-expressions `EVal (VNat 10)` and `EVal (VNat 20)` *)
    + eapply Val_big_step. (* By using `Val_big_step, we instantiate `?v10`. *)
    + eapply Val_big_step. (* By using `Val_big_step, we instantiate `?v20`. *)
    + (* The goal here is `eval_bin_op PlusOp (VNat 10) (VNat 20) = Some ?v1`.
      Since `eval_bin_op is a function, we can perform proof by computation,
      which will evaluate the LHS to `Some (VNat 30)`. *)
      simpl.
      (* The goal now becomes `Some (VNat 30) = Some ?v1`. By using the tactic
      `reflexivity`, `?v1` will be instantiated with `VNat 30`. *)
      reflexivity.
  - eapply Val_big_step.
  - simpl. reflexivity.
Qed.

Lemma big_step_example2 : big_step example2 (VBool true).
Proof.
  unfold example2.
  eapply Let_big_step.
  - eapply Op_big_step.
    + apply Val_big_step.
    + apply Val_big_step.
    + simpl. reflexivity.
  - (* In our goal we have:

      subst "x" (VNat 30)
        (ELet "y" (EOp LeOp (EVal (VNat 5)) (EVar "x")) (EVar "y"))

    Yet again, since `subst` is a function, we can proceed by proof by
    computation. *)
    simpl.
    eapply Let_big_step.
    + eapply Op_big_step.
      * apply Val_big_step.
      * apply Val_big_step.
      * simpl. reflexivity.
    + simpl. apply Val_big_step.
Qed.

(* ### Exercise *)
(*
Prove the following lemmas.
*)
Lemma big_step_example3 : big_step example3 (VBool false).
Proof. Admitted.

Lemma big_step_example4 : big_step example4 (VNat 4).
Proof. Admitted.

Lemma big_step_example5 : big_step example5 (VNat 1).
Proof. Admitted.

(* ## Automating proofs using `eauto` *)
(*
As we have seen above, carrying out these proofs are very tedious. In most cases
(apart from cases for the if construct), there is just one rule that we can
apply. We will now look into automating this.

In order to automate these proofs, we will use the `eauto` tactic, which
performs a "brute force" first, by trying to `eapply` individual lemmas from a
database of lemmas. It does do this in a depth first fashion, i.e. it will
backtrack whenever multiple lemmas could be `eapply`ed (for example, in the case
of the conditional expression if).
*)
Create HintDb exec.
(*
The command `Create HintDb` creates a _database_ of lemmas named `exec` that can
be used by `eauto`. As we can see, this database is initially empty.
*)
Print HintDb exec.

(*
In order to make this hint database useful, we add all constructors of the
inductive relation `big_step` (i.e. all the inference rules of the big-step
semantics) to the database.
*)
Hint Constructors big_step : exec.
(*
Now we can see that the hint database is populated.
*)
Print HintDb exec.

(*
Let us see it in practice.
*)
Lemma big_step_example :
  big_step (EIf (EVal (VBool true)) (EVal (VNat 10)) (EVal (VNat 11))) (VNat 10).
Proof.
  eauto with exec. (* We can now invoke `eauto` with the hint database. *)

Restart.
  (* This solved the goal, but we it gives us no clue what just happened. To
  see what is going on, we can use the `debug` keyword. *)
  debug eauto with exec.

  (*
  1 depth=5 
  1.1 depth=4 simple apply If_big_step_false
  1.2 depth=4 simple apply If_big_step_true
  1.2.1 depth=4 simple apply Val_big_step
  1.2.1.1 depth=4 simple apply Val_big_step
  *)

  (* Note that `eauto` is in fact making use of backtracking, it first tries
  `If_big_step_false`, and notices that it fails, and in turn uses, after
  backtracking uses `If_big_step_true`. *)
Qed.

(*
As we have seen in our manual proofs (e.g. `big_step_example2`), we were not
just using `eapply`, but we also had to:

- Prove goals of the shape `eval_bin_op op v1 v1 = Some ?v` by computation
- Simplify substitutions by proof by computations.

Using the `Hint Extern` command, we can instruct `eauto` to run tactics when
the goal matches a certain shape. The number `10` indices the level of
precedence the hint, where a lower number means that the hint is applied
earlier.
*)
Hint Extern 10 (eval_bin_op _ _ _ = Some _) => simpl; reflexivity : exec.
Hint Extern 10 (big_step (subst _ _ _) _) => progress simpl : exec.
Print HintDb exec.

Lemma big_step_example1_automated : big_step example1 (VBool true).
Proof.
  unfold example1.
  debug eauto with exec.
  (*
  1 depth=5 
  1.1 depth=4 simple eapply Op_big_step
  1.1.1 depth=3 simple eapply Op_big_step
  1.1.1.1 depth=3 simple apply Val_big_step
  1.1.1.1.1 depth=3 simple apply Val_big_step
  1.1.1.1.1.1 depth=3 (*external*) (simpl; reflexivity)
  1.1.1.1.1.1.1 depth=3 simple apply Val_big_step
  1.1.1.1.1.1.1.1 depth=3 simple apply @eq_refl
  *)
Qed.

Lemma big_step_example2_automated : big_step example2 (VBool true).
Proof.
  unfold example2.
  (* Let us first do this example in a couple of steps, by doing top-level
  steps by hand. *)
  eapply Let_big_step.
  { debug eauto with exec.
    (*
    1 depth=5 
    1.1 depth=4 simple eapply Op_big_step
    1.1.1 depth=4 simple apply Val_big_step
    1.1.1.1 depth=4 simple apply Val_big_step
    1.1.1.1.1 depth=4 (*external*) (simpl; reflexivity)
    *) }
  simpl.
  eapply Let_big_step.
  { eauto with exec. }
  eauto with exec.
Restart.
  (* Now we do it all in one go. *)
  unfold example2.
  debug eauto with exec. (* This did not do anything. The problem is that we
  reached the maximal search depth, which is 5 by default.

  1 depth=5 
  1.1 depth=4 simple eapply Let_big_step
  1.1.1 depth=3 simple eapply Op_big_step
  1.1.1.1 depth=3 simple apply Val_big_step
  1.1.1.1.1 depth=3 simple apply Val_big_step
  1.1.1.1.1.1 depth=3 (*external*) (simpl; reflexivity)
  1.1.1.1.1.1.1 depth=2 (*external*) (progress simpl)
  1.1.1.1.1.1.1.1 depth=1 simple eapply Let_big_step
  1.1.1.1.1.1.1.1.1 depth=0 simple eapply Op_big_step
  *)
  debug eauto 10 with exec.
  (*
  1 depth=10 
  1.1 depth=9 simple eapply Let_big_step
  1.1.1 depth=8 simple eapply Op_big_step
  1.1.1.1 depth=8 simple apply Val_big_step
  1.1.1.1.1 depth=8 simple apply Val_big_step
  1.1.1.1.1.1 depth=8 (*external*) (simpl; reflexivity)
  1.1.1.1.1.1.1 depth=7 (*external*) (progress simpl)
  1.1.1.1.1.1.1.1 depth=6 simple eapply Let_big_step
  1.1.1.1.1.1.1.1.1 depth=5 simple eapply Op_big_step
  1.1.1.1.1.1.1.1.1.1 depth=5 simple apply Val_big_step
  1.1.1.1.1.1.1.1.1.1.1 depth=5 simple apply Val_big_step
  1.1.1.1.1.1.1.1.1.1.1.1 depth=5 (*external*) (simpl; reflexivity)
  1.1.1.1.1.1.1.1.1.1.1.1.1 depth=4 (*external*) (progress simpl)
  1.1.1.1.1.1.1.1.1.1.1.1.1.1 depth=4 simple apply Val_big_step
  *)
Qed.

Lemma big_step_example3_automated : big_step example3 (VBool false).
Proof. Admitted.

Lemma big_step_example4_automated : big_step example4 (VNat 4).
Proof. Admitted.

Lemma big_step_example5_automated : big_step example5 (VNat 1).
Proof. Admitted.

(* ## Determinism of the big-step semantics *)
(*
The idea of the big-step semantics `big_step e v` is that it associates to
expressions their value. We will now establish that this value is in fact
unique, i.e. that the big-step semantics is _deterministic_.
*)
Lemma big_step_deterministic e v1 v2 :
  big_step e v1 ->
  big_step e v2 ->
  v1 = v2.
Proof.
  intros Hstep1.
  revert v2. (* We have to generalize the induction hypothesis, because `v2`
  will differ each time we need the induction hypothesis. *)

  (* Since we have defined the big-step semantics using an inductive type, we
  can perform induction over the derivation. We can do this using the
  `induction` tactic. Before doing this, it is worth taking a look at the
  induction scheme for `big_step` *)
  Check big_step_ind.
  (* Formatted in a nicer way:

    (forall v, P (EVal v) v) ->

    (forall y e1 e2 v1 v2,
       big_step e1 v1 ->
       P e1 v1 ->
       big_step (subst y v1 e2) v2 ->
       P (subst y v1 e2) v2 ->
       P (ELet y e1 e2) v2) ->

    (forall e1 e2 e3 v,
       big_step e1 (VBool true) ->
       P e1 (VBool true) ->
       big_step e2 v ->
       P e2 v ->
       P (EIf e1 e2 e3) v)

    (forall e1 e2 e3 v,
       big_step e1 (VBool false) ->
       P e1 (VBool false) ->
       big_step e3 v ->
       P e3 v ->
       P (EIf e1 e2 e3) v)

    (forall e1 e2 op v1 v2 v,
       big_step e1 v1 ->
       P e1 v1 ->
       big_step e2 v2 ->
       P e2 v2 ->
       eval_bin_op op v1 v2 = Some v ->
       P (EOp op e1 e2) v)
   ----------------------------------------------------    
    forall e v, big_step e v -> P e v
  *)
  induction Hstep1.
  - (* Case for values *)
    intros v' Hstep2.
    (* Now we need a new tactic. Let us take a look at the hypotheses:

       Hstep2 : big_step (EVal v) v'

    By looking at the constructors of `big_step`, we know that the only way
    how we can prove `big_step (EVal v) v'` is by means of the constructor
    `Val_big_step`, which means that `v'` should be `v`. We use the `inv` tactic
    to obtain that information.

    (Note the close correspondence between dependent pattern matching in
    Agda (for example, on `Vec (S n)` where we know it is in fact a cons) and
    inversion in Coq. *)
    inv Hstep2.
    reflexivity.
  - (* Case for let *)
    intros v' Hstep2. inv Hstep2.
    assert (v1 = v0).
    { apply IHHstep1_1. assumption. }
    subst v0.
    apply IHHstep1_2. assumption.
  - (* case for if-true *)
    intros v' Hstep2. inv Hstep2.
    + apply IHHstep1_2. assumption.
    + assert (VBool true = VBool false).
      { apply IHHstep1_1. assumption. }
      discriminate.
  - (* case for if-false *)
    intros v' Hstep2. inv Hstep2.
    + assert (VBool false = VBool true).
      { apply IHHstep1_1. assumption. }
      discriminate.
    + apply IHHstep1_2. assumption.
  - (* case for op *)
    intros v' Hstep2. inv Hstep2.
    assert (v1 = v0).
    { apply IHHstep1_1. assumption. }
    subst v0.
    assert (v2 = v3).
    { apply IHHstep1_2. assumption. }
    subst v3.
    rewrite H in H6. injection H6 as H6. assumption.
Qed.

(* ### Exercise (for experts) *)
(* Try to use Coq's tactic language to automate the above proof. *)

(* ## Small-step semantics *)
(*
We will now give a small-step semantics for our little language.

First first define a head reduction relation:
*)
Inductive head_step : expr -> expr -> Prop :=
  | Let_headstep y e2 v1 :
     head_step (ELet y (EVal v1) e2) (subst y v1 e2)
  | If_headstep_true e2 e3 :
     head_step (EIf (EVal (VBool true)) e2 e3) e2
  | If_headstep_false e2 e3 :
     head_step (EIf (EVal (VBool false)) e2 e3) e3
  | Op_headstep op v1 v2 v :
     eval_bin_op op v1 v2 = Some v ->
     head_step (EOp op (EVal v1) (EVal v2)) (EVal v).

(*
The next step is to lift head reduction to whole terms, by allowing redexes
to be reduced at any evaluation position, instead of just at the head position.
We define this lifting by means of _evaluation contexts_:

  E := □ | let x := E in e2 | E `op` e2 | e1 `op` E | if E then e2 else e3

Evaluation contexts should be seen as expressions a hole `□`. By means of the
function `fill : ctx -> expr -> expr`, which fills an expression in the hole
of an evaluation context, we can now lift head reduction to whole expressions:

         head_step e1 e2
  ------------------------------
   step (fill E e1) (fill E e2) 

Note that holes only appear at a call-by-value evaluation positions, an in
particular this means that we do not have the following evaluation contexts:

  let x := e1 in E
  if e1 then E else e2
  if e1 then e2 else e3

After all, in `let x := e1 in e2`, the expression `e1` should be evaluated
entirely before `e2`, and in `if e1 then e2 else e3`, the expression `e1` should
be evaluated entirely before evaluating either `e2` or `e3`.

In Coq, we formalize evaluation contexts in two stages. First we define
_evaluation context items_:

  E := let x := □ in e2 | □ `op` e2 | e1 `op` □ | if □ then e2 else e3

And then define evaluation contexts as lists of evaluation contexts.
*)
Inductive ctx_item :=
  | LetCtx : string -> expr -> ctx_item
  | OpCtxL : bin_op -> expr -> ctx_item
  | OpCtxR : bin_op -> val -> ctx_item
  | IfCtx : expr -> expr -> ctx_item.

Notation ctx := (list ctx_item).

(*
We first define a function for putting an expression in the hole of an
evaluation context item, and then lift said function to evaluation contexts.
*)
Definition fill_item (E : ctx_item) (e : expr) : expr :=
  match E with
  | LetCtx s e2 => ELet s e e2
  | OpCtxL op e2 => EOp op e e2
  | OpCtxR op v1 => EOp op (EVal v1) e
  | IfCtx e2 e3 => EIf e e2 e3
  end.

Fixpoint fill (E : ctx) (e : expr) : expr :=
  match E with
  | nil => e
  | E1 :: E2 => fill_item E1 (fill E2 e)
  end.

Inductive step : expr -> expr -> Prop :=
  | do_step E e1 e2 :
     head_step e1 e2 ->
     step (fill E e1) (fill E e2).

(*
Finally, we define the transitive/reflexive closure of the reduction relation.
 *)
Inductive steps : expr -> expr -> Prop :=
  | steps_refl e :
     steps e e
  | steps_step e1 e2 e3 :
     step e1 e2 ->
     steps e2 e3 ->
     steps e1 e3.

(* ## Correspondence between big-step and small-step semantics *)
(*
Now that we have defined two different styles of semantics for our little
language, we are going to show that these are the same. Formally speaking,
this means we will show:

  steps e (EVal v) <-> big_step e v

This will be expressed by the lemmas:

1. steps_val_big_step : forall e v,
     steps e (EVal v) -> big_step e v

2. big_step_steps_val : forall e v,
     big_step e v -> steps e (EVal v)
*)

(* ### Direction 1 *)
(*
We will prove our final result:

  steps e (EVal v) -> big_step e v

in several steps.

a. head_step_big_step :
     head_step e1 e2 -> big_step e2 v -> big_step e1 v
b. step_big_step :
     step e1 e2 -> big_step e2 v -> big_step e1 v
c. steps_big_step :
     steps e1 e2 -> big_step e2 v -> big_step e1 v
d. steps_val_big_step :
     steps e (EVal v) -> big_step e v.

So, in words, we first show that the big-step semantics is preserved by head
reduction, then by whole program reduction, and finally by multiple steps
of program reduction. In the progress of proving that (b) follows from (a), we
have to establish various properties about the way evaluation contexts interact
with the big-step semantics.
*)
Lemma head_step_big_step e1 e2 v :
  head_step e1 e2 ->
  big_step e2 v ->
  big_step e1 v.
Proof.
  intros Hhead Hbig.
  destruct Hhead. (* head reduction is not a recursive inductive datatype, so
  we perform case-analysis on the derivation *)
  - (* case let *)
    eapply Let_big_step. eapply Val_big_step. assumption.
  - (* case if-true *)
    eapply If_big_step_true. eapply Val_big_step. assumption.
  - (* case if-false *)
    eapply If_big_step_false. eapply Val_big_step. assumption.
  - (* case op *)
    inv Hbig.
    eapply Op_big_step.
    eapply Val_big_step.
    eapply Val_big_step.
    assumption.
Qed.

(*
As we have just seen, the above proof contains a lot of repetition. Each case
basically follows the same pattern:

1. Perform inversion on hypotheses `big_step (EVal v1) v2` to obtain that `v1`
   and `v2` are in fact the same.
2. Apply the rules of the big-step semantics.

We have already seen how to automate step (1), namely using the eauto tactic.
For step (2), we  write a custom tactic `inv_big_step_vals` that repeatedly
checks whether there is a hypothesis `big_step (EVal v1) v2`, and if so,
performs inversion on it. 
*)
Tactic Notation "inv_big_step_vals" :=
  repeat
  match goal with
  | H : big_step (EVal _) _ |- _ => inv H
  end.

(*
To keep things understandable, we create hint databases that contain just the
constructors of `big_step` and `head_step` respectively.
*)
Create HintDb big_step.
Hint Constructors big_step : big_step.
Create HintDb head_step.
Hint Constructors head_step : head_step.

Lemma head_step_big_step_automated e1 e2 v :
  head_step e1 e2 ->
  big_step e2 v ->
  big_step e1 v.
Proof.
  intros Hhead Hbig.
  destruct Hhead; inv_big_step_vals; eauto with big_step.
Qed.

(* #### Exercise *)
(*
Prove the lemmas below. If you feel confident, try to make use of the tactics
for automation we have seen so far. Before starting to write any Coq, carefully
think how you would do the proof on paper! You have to use a variety of proof
techniques:

- Induction on evaluation contexts (i.e. lists of evaluation context items).
- Case analysis on evaluation context items.
- Inversion on the big-step semantics.

Also, make sure to reuse the lemmas that you have already proven. 
*)
Lemma big_step_fill_item E e v v' :
  big_step e v' ->
  big_step (fill_item E (EVal v')) v ->
  big_step (fill_item E e) v.
Proof. Admitted.

Lemma big_step_fill_item_inv E e v :
  big_step (fill_item E e) v ->
  exists v', big_step e v' /\ big_step (fill_item E (EVal v')) v.
Proof. Admitted.

Lemma big_step_fill E e v v' :
  big_step e v' ->
  big_step (fill E (EVal v')) v ->
  big_step (fill E e) v.
Proof.
  (* This proof is given to give you inspiration for the other proofs. *)
  revert v.
  induction E as [|E E' IH]; intros v Hbig1 Hbig2; simpl in *.
  { inv_big_step_vals. assumption. }
  apply big_step_fill_item_inv in Hbig2. destruct Hbig2 as (v''&?&?).
  eapply big_step_fill_item.
  + apply IH. eassumption. eassumption.
  + eassumption.
Qed.

Lemma big_step_fill_inv E e v :
  big_step (fill E e) v ->
  exists v', big_step e v' /\ big_step (fill E (EVal v')) v.
Proof. Admitted.

Lemma step_big_step e1 e2 v :
  step e1 e2 ->
  big_step e2 v ->
  big_step e1 v.
Proof. Admitted.

Lemma steps_big_step e1 e2 v :
  steps e1 e2 ->
  big_step e2 v ->
  big_step e1 v.
Proof. Admitted.

Lemma steps_val_big_step e v :
  steps e (EVal v) ->
  big_step e v.
Proof.
  eauto using steps_big_step.
Admitted.

(* ### Direction 2 *)
(*
We will prove our final result:

  big_step e v -> steps e (EVal v)

As for the previous direction, there are a bunch of helper lemmas that will
help you prove the final result. *)
Lemma steps_trans e1 e2 e3 :
  steps e1 e2 ->
  steps e2 e3 ->
  steps e1 e3.
Proof. Admitted.

Lemma head_step_step e1 e2 :
  head_step e1 e2 ->
  step e1 e2.
Proof.
  intros.
  (* Here we cannot just apply the constructor `do_step`. To do that, the goal
  should be of the shape:

    step (fill E e1) (fill E e2)

  However, we now that `fill [] e` computes to `e` by the definition of `fill`.
  We use the `change` tactic to replace a term by another term that is equal up
  to computation (definitionally equal). *)
  change e1 with (fill [] e1).
  change e2 with (fill [] e2).
  (* Now the goal is of the right shape. *)
  apply do_step.
  assumption.
Qed.

Lemma step_fill_item E e1 e2 :
  step e1 e2 ->
  step (fill_item E e1) (fill_item E e2).
Proof.
  (* Hint: here you need to perform case analysis on `step e1 e2`, and then use
  the `change` tactic again to turn the goal into the right shape to use the
  constructor `do_step`. *) 
Admitted.

Lemma steps_fill_item E e1 e2 :
  steps e1 e2 ->
  steps (fill_item E e1) (fill_item E e2).
Proof.
Admitted.

Lemma big_step_steps_val e v :
  big_step e v ->
  steps e (EVal v).
Proof.
  intros Hbig. induction Hbig.
  - apply steps_refl.
  - (* Below, I show how to handle one case. You should finish the remaining
    cases. *)
    change (ELet y e1 e2) with (fill_item (LetCtx y e2) e1).
    eapply steps_trans.
    + apply steps_fill_item. eassumption.
    + simpl. eapply steps_step.
      * eapply head_step_step. eauto with head_step.
      * eassumption.
  -
Admitted.
End stateless_language.

(* # A stateful mini ML-like language *)
(*
We will now extend our arithmetic expression language with while loops and
mutable state, which brings it close to an ML-like language without functions.
The syntax of our mini-ML like language is:

Values:        v ::= b | n | ()
Operators:    op ::= + | - | <= | < | ==
Expressions:   e ::= x
                   | v
                   | let x := e1 in e2
                   | e1 ; e2
                   | e1 `op` e2
                   | if e1 then e2 else e3
                   | while e1 { e2 }
                   | alloc e
                   | free e
                   | !e
                   | e1 := e2

As we see, there are some new constructs:

- Sequencing of expressions (e1 ; e2)
- While loops (while e1 { e2 }).
- Allocation of a new reference (`alloc e`, which yields a new location in
  memory whose is value is given by the expression `e`).
- Deallocation of a reference (`free e`, which deallocates a location in memory
  that is given by the expression `e`).
- Loading from memory (`! e`, which loads a value from the location given by the
  expression `e`).
- Storing in memory (`e1 := e2`, which stores the value given by `e2` at the
  location given by `e1`).

Note that since all our expressions need to have a return value, we have added
the unit value `()` to deal with expressions that we just execute for their
side-effects.

Extend our arithmetic expression language with mutable state is relatively
straightforward: we need a type `mem` to represent memories, and then we keep
track of in the big- and small-step operational semantics. The types of these
semantics then become:
  
  big_step : expr -> val -> Prop
  step : expr -> mem -> expr -> mem -> Prop

And of course, we have to add corresponding reduction rules for each new
construct.

In order to represent memories, we will use our type of finite maps that we
have developed in the previous lecture. Using that type, we can represent
memories as:

  mem := map val

In order to give the semantics of the memory operations (alloc, free, load,
store) we can simply use the operations on finite maps that we already
defined (`minsert`, `mdelete`, `mlookup`, and `minsert`, respectively). There is
just one additional operation that we need, when allocating a new reference, we
need to use a location that is not already in use. So, before formalizing our
ML-like language, we will first define the operation:

  mfresh : map A -> nat

that yields an unused index in the map.
*)

(* ## Picking fresh locations in a map *)
(*
As usual, we first define the operation on raw maps, and then lift it to maps
(raw maps bundled with a proof of well-formedness). 
*)
Definition mfresh_raw {A} (m : map_raw A) : nat := length m.

Definition mfresh {A} (m : map A) : nat := mfresh_raw (map_car m).

(* ### Exercise *)
(*
Prove the following lemmas.
*)
Definition mfresh_lookup_raw {A} (m : map_raw A) :
  mlookup_raw m (mfresh_raw m) = None.
Proof. Admitted.

Definition mfresh_lookup {A} (m : map A) : mlookup m (mfresh m) = None.
Proof. Admitted.

Module Export stateful_language.
(* ## Syntax *)
(*
We extend the syntax of our arithmetic language by adding constructors for the
new constructs.
*)
Inductive val : Type :=
  | VUnit : val (* new *)
  | VBool : bool -> val
  | VNat : nat -> val
  | VLoc : nat -> val (* new *).

Inductive bin_op : Type :=
  | PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive expr : Type :=
  | EVar : string -> expr
  | EVal : val -> expr
  | ELet : string -> expr -> expr -> expr
  | ESeq : expr -> expr -> expr (* new *)
  | EOp : bin_op -> expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | EWhile : expr -> expr -> expr (* new *)
  | EAlloc : expr -> expr (* new *)
  | EFree : expr -> expr (* new *)
  | ELoad : expr -> expr (* new *)
  | EStore : expr -> expr -> expr (* new *).

(*
Let us take a look at an example:

  div n1 n2 :=
    let x := alloc n1 in
    let y := alloc 0 in
    while (n1 <= x) {
      x := !x - n2;
      y := !y + 1
    };
    !y
*)
Definition div (n1 n2 : nat) : expr :=
  ELet "x" (EAlloc (EVal (VNat n1)))
    (ELet "y" (EAlloc (EVal (VNat 0)))
      (ESeq
        (EWhile (EOp LeOp (EVal (VNat n2)) (ELoad (EVar "x")))
          (ESeq
            (EStore (EVar "x") (EOp MinusOp (ELoad (EVar "x")) ((EVal (VNat n2)))))
            (EStore (EVar "y") (EOp PlusOp (ELoad (EVar "y")) ((EVal (VNat 1)))))
          )
        )
        (ELoad (EVar "y")))).

(* ## Semantics of operators *)
Definition eval_bin_op (op : bin_op) (v1 v2 : val) : option val :=
  match op, v1, v2 with
  | PlusOp, VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | MinusOp, VNat n1, VNat n2 => Some (VNat (n1 - n2))
  | LeOp, VNat n1, VNat n2 => Some (VBool (Nat.leb n1 n2))
  | LtOp, VNat n1, VNat n2 => Some (VBool (Nat.ltb n1 n2))
  | EqOp, VNat n1, VNat n2 => Some (VBool (Nat.eqb n1 n2))
  | EqOp, VBool n1, VBool n2 => Some (VBool (Bool.eqb n1 n2))
  | EqOp, VUnit, VUnit => Some (VBool true) (* new *)
  | EqOp, VLoc l1, VLoc l2 => Some (VBool (Nat.eqb l1 l2)) (* new *) 
  | _, _, _ => None
  end.

(* ## Substitution *)
Fixpoint subst (x : string) (w : val) (e : expr) : expr :=
  match e with
  | EVal v => EVal v
  | EVar y => if string_dec x y then EVal w else EVar y
  | ELet y e1 e2 =>
     if string_dec x y
     then ELet y (subst x w e1) e2
     else ELet y (subst x w e1) (subst x w e2)
  | ESeq e1 e2 => ESeq (subst x w e1) (subst x w e2)
  | EOp op e1 e2 => EOp op (subst x w e1) (subst x w e2)
  | EIf e1 e2 e3 => EIf (subst x w e1) (subst x w e2) (subst x w e3)
  | EWhile e1 e2 => EWhile (subst x w e1) (subst x w e2)
  | EAlloc e => EAlloc (subst x w e)
  | EFree e => EFree (subst x w e)
  | ELoad e => ELoad (subst x w e)
  | EStore e1 e2 => EStore (subst x w e1) (subst x w e2)
  end.

(* ## Big-step semantics *)
Notation mem := (map val).

Inductive big_step : expr -> mem -> val -> mem -> Prop :=
  | Val_big_step m v : big_step (EVal v) m v m
  | Let_big_step m1 m2 m3 y e1 e2 v1 v2 :
     big_step e1 m1 v1 m2 ->
     big_step (subst y v1 e2) m2 v2 m3 ->
     big_step (ELet y e1 e2) m1 v2 m3
  | Seq_big_step m1 m2 m3 e1 e2 v1 v2 :
     big_step e1 m1 v1 m2 ->
     big_step e2 m2 v2 m3 ->
     big_step (ESeq e1 e2) m1 v2 m3
  | If_big_step_true m1 m2 m3 e1 e2 e3 v :
     big_step e1 m1 (VBool true) m2 ->
     big_step e2 m2 v m3 ->
     big_step (EIf e1 e2 e3) m1 v m3
  | If_big_step_false m1 m2 m3 e1 e2 e3 v :
     big_step e1 m1 (VBool false) m2 ->
     big_step e3 m2 v m3 ->
     big_step (EIf e1 e2 e3) m1 v m3
  | While_big_step_true m1 m2 m3 m4 e1 e2 v1 v2 :
     big_step e1 m1 (VBool true) m2 ->
     big_step e2 m2 v1 m3 ->
     big_step (EWhile e1 e2) m3 v2 m4 ->
     big_step (EWhile e1 e2) m1 v2 m4
  | While_big_step_false m1 m2 e1 e2 :
     big_step e1 m1 (VBool false) m2 ->
     big_step (EWhile e1 e2) m1 VUnit m2
  | Op_big_step m1 m2 m3 e1 e2 op v1 v2 v :
     big_step e1 m1 v1 m2 ->
     big_step e2 m2 v2 m3 ->
     eval_bin_op op v1 v2 = Some v ->
     big_step (EOp op e1 e2) m1 v m3
  | Alloc_big_step m1 m2 e v :
     big_step e m1 v m2 ->
     big_step (EAlloc e) m1 (VLoc (mfresh m2)) (minsert (mfresh m2) v m2)
  | Free_big_step m1 m2 e l :
     big_step e m1 (VLoc l) m2 ->
     mlookup m2 l <> None -> (* make sure that we only deallocate locations that exist *)
     big_step (EFree e) m1 VUnit (mdelete l m2)
  | Load_big_step m1 m2 e l v :
     big_step e m1 (VLoc l) m2 ->
     mlookup m2 l = Some v ->
     big_step (ELoad e) m1 v m2
  | Store_big_step m1 m2 m3 e1 e2 l v :
     big_step e1 m1 (VLoc l) m2 ->
     big_step e2 m2 v m3 ->
     mlookup m3 l <> None -> (* make sure that we only assign to locations that exist *)
     big_step (EStore e1 e2) m1 VUnit (minsert l v m3).

(* ### Example *)
(*
We add some additional hints to the hint database to deal with memories.
*)
Create HintDb exec.
Hint Constructors big_step : exec.
Hint Extern 10 (eval_bin_op _ _ _ = Some _) => simpl; reflexivity : exec.
Hint Extern 10 (big_step (subst _ _ _) _ _ _) => progress simpl : exec.
Hint Extern 10 (mlookup _ _ = Some _) => reflexivity : exec.
Hint Extern 10 (mlookup _ _ <> None) => discriminate : exec.

Lemma big_step_div_15_5 : exists m,
  big_step (div 15 5) mempty (VNat 3) m.
Proof.
  eexists. unfold div.
  debug eauto 100 with exec.
Qed.

Lemma big_step_div_21_5 : exists m,
  big_step (div 21 5) mempty (VNat 4) m.
Proof.
  eexists. unfold div.
  debug eauto 100 with exec.
Qed.

Lemma big_step_div_14_3 : exists m,
  big_step (div 14 3) mempty (VNat 4) m.
Proof.
  eexists. unfold div.
  debug eauto 100 with exec.
Qed.

(* ### Exercise *)
(*
Prove the following lemma.
*)
Lemma big_step_deterministic e1 m1 e2 m2 e2' m2' :
  big_step e1 m1 e2 m2 ->
  big_step e1 m1 e2' m2' ->
  e2 = e2' /\ m2 = m2'.
Proof. Admitted.

(* ## Small-step semantics *)
Inductive head_step : expr -> mem -> expr -> mem -> Prop :=
  | Let_headstep m y e2 v1 :
     head_step (ELet y (EVal v1) e2) m (subst y v1 e2) m
  | Seq_headstep m e2 v1 :
     head_step (ESeq (EVal v1) e2) m e2 m
  | If_headstep_true m e2 e3 :
     head_step (EIf (EVal (VBool true)) e2 e3) m e2 m
  | If_headstep_false m e2 e3 :
     head_step (EIf (EVal (VBool false)) e2 e3) m e3 m
  | While_headstep m e1 e2 :
     head_step (EWhile e1 e2) m (EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit)) m
  | Op_headstep m op v1 v2 v :
     eval_bin_op op v1 v2 = Some v ->
     head_step (EOp op (EVal v1) (EVal v2)) m (EVal v) m
  | Alloc_headstep m v :
     head_step (EAlloc (EVal v)) m (EVal (VLoc (mfresh m))) (minsert (mfresh m) v m)
  | Free_headstep m l :
     mlookup m l <> None ->
     head_step (EFree (EVal (VLoc l))) m (EVal VUnit) (mdelete l m)
  | Load_headstep m l v :
     mlookup m l = Some v ->
     head_step (ELoad (EVal (VLoc l))) m (EVal v) m
  | Store_headstep m l v :
     mlookup m l <> None ->
     head_step (EStore (EVal (VLoc l)) (EVal v)) m (EVal VUnit) (minsert l v m).

Inductive ctx_item : Type :=
  | LetCtx : string -> expr -> ctx_item
  | SeqCtx : expr -> ctx_item
  | OpCtxL : bin_op -> expr -> ctx_item
  | OpCtxR : bin_op -> val -> ctx_item
  | IfCtx : expr -> expr -> ctx_item
  | AllocCtx : ctx_item
  | FreeCtx : ctx_item
  | LoadCtx : ctx_item
  | StoreCtxL : expr -> ctx_item
  | StoreCtxR : val -> ctx_item.

Notation ctx := (list ctx_item).

Definition fill_item (E : ctx_item) (e : expr) : expr :=
  match E with
  | LetCtx s e2 => ELet s e e2
  | SeqCtx e2 => ESeq e e2
  | OpCtxL op e2 => EOp op e e2
  | OpCtxR op v1 => EOp op (EVal v1) e
  | IfCtx e2 e3 => EIf e e2 e3
  | AllocCtx => EAlloc e
  | FreeCtx => EFree e
  | LoadCtx => ELoad e
  | StoreCtxL e2 => EStore e e2
  | StoreCtxR v1 => EStore (EVal v1) e
  end.

Fixpoint fill (E : ctx) (e : expr) : expr :=
  match E with
  | nil => e
  | E1 :: E2 => fill_item E1 (fill E2 e)
  end.

Inductive step : expr -> mem -> expr -> mem -> Prop :=
  | do_step E m1 m2 e1 e2 :
     head_step e1 m1 e2 m2 ->
     step (fill E e1) m1 (fill E e2) m2.

Inductive steps : expr -> mem -> expr -> mem -> Prop :=
  | steps_refl m e :
     steps e m e m
  | steps_step m1 m2 m3 e1 e2 e3 :
     step e1 m1 e2 m2 ->
     steps e2 m2 e3 m3 ->
     steps e1 m1 e3 m3.

(* ## Correspondence between big-step and small-step semantics *)

Tactic Notation "inv_big_step_vals" :=
  repeat
  match goal with
  | H : big_step (EVal _) _ _ _ |- _ => inv H
  end.

Create HintDb big_step.
Hint Constructors big_step : big_step.
Create HintDb head_step.
Hint Constructors head_step : head_step.

(* ### Exercise *)
(*
Prove the following lemmas. If you have automated your proofs for the arithmetic
language, it should be relatively easy to adapt your proofs.
*)
Lemma head_step_big_step m1 m2 m3 e1 e2 v :
  head_step e1 m1 e2 m2 ->
  big_step e2 m2 v m3 ->
  big_step e1 m1 v m3.
Proof. Admitted.

Lemma big_step_fill_item m1 m2 m3 E e v v' :
  big_step e m1 v' m2 ->
  big_step (fill_item E (EVal v')) m2 v m3 ->
  big_step (fill_item E e) m1 v m3.
Proof. Admitted.

Lemma big_step_fill_item_inv m1 m3 E e v :
  big_step (fill_item E e) m1 v m3 ->
  exists v' m2, big_step e m1 v' m2 /\ big_step (fill_item E (EVal v')) m2 v m3.
Proof. Admitted.

Lemma big_step_fill m1 m2 m3 E e v v' :
  big_step e m1 v' m2 ->
  big_step (fill E (EVal v')) m2 v m3 ->
  big_step (fill E e) m1 v m3.
Proof. Admitted.

Lemma big_step_fill_inv m1 m3 E e v :
  big_step (fill E e) m1 v m3 ->
  exists v' m2, big_step e m1 v' m2 /\ big_step (fill E (EVal v')) m2 v m3.
Proof. Admitted.

Lemma step_big_step m1 m2 m3 e1 e2 v :
  step e1 m1 e2 m2 ->
  big_step e2 m2 v m3 ->
  big_step e1 m1 v m3.
Proof. Admitted.

Lemma steps_big_step m1 m2 m3 e1 e2 v :
  steps e1 m1 e2 m2 ->
  big_step e2 m2 v m3 ->
  big_step e1 m1 v m3.
Proof. Admitted.

Lemma steps_val_big_step m1 m2 e v :
  steps e m1 (EVal v) m2 ->
  big_step e m1 v m2.
Proof. Admitted.

Lemma steps_trans m1 m2 m3 e1 e2 e3 :
  steps e1 m1 e2 m2 ->
  steps e2 m2 e3 m3 ->
  steps e1 m1 e3 m3.
Proof. Admitted.

Lemma head_step_step m1 m2 e1 e2 :
  head_step e1 m1 e2 m2 ->
  step e1 m1 e2 m2.
Proof. Admitted.

Lemma step_fill_item m1 m2 E e1 e2 :
  step e1 m1 e2 m2 ->
  step (fill_item E e1) m1 (fill_item E e2) m2.
Proof. Admitted.

Lemma steps_fill_item m1 m2 E e1 e2 :
  steps e1 m1 e2 m2 ->
  steps (fill_item E e1) m1 (fill_item E e2) m2.
Proof. Admitted.

Lemma big_step_steps_val m1 m2 e v :
  big_step e m1 v m2 ->
  steps e m1 (EVal v) m2.
Proof. Admitted.
End stateful_language.

(*
We want to use the ML-like language in the next lecture. By exporting, we
make the definitions in the module `stateful_language` available at the
top-level namespace.
*)
Export stateful_language.
