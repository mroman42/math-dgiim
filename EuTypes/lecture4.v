Require Export lecture3.

(* # Contents *)
(*
In this lecture, we will be formalizing a separation logic for the ML-like
language that we discussed in the second lecture. The topics that we discuss
during the lecture are as follows:

- Separation logic
- Deep embedding versus shallow embedding
- Weakest preconditions
*)
(* # Separation logic *)
(*
The syntax of our separation logic is as follows:

  P, Q ::= emp
         | P ** Q | P -* Q
         | emp | l ~> v
         | All x, P | Ex x, P |
         | wp e (fun v => Q)

We will not explain all of these connectives in detail right immediately. The
semantics of most will be described in the course of this lecture, accompanied
by a formal description in Coq. However, we will highlight the core connectives
of separation logic, whose informal semantics is as follows:

  l ~> v := _the points-to connective_
            the memory consists of exactly one location `l` with value `v`

  P ** Q := _separating conjunction_
            the memory can be split into two _disjoint_ parts, so that the
            first satisfies P and the second satisfies Q

  emp    := _the empty connective_
            the memory is empty

Using these connectives, one can give very precise descriptions of memory
footprints, for example:

  l1 ~> 6 ** l2 ~> 8
  \Ex v, l1 ~> v ** l2 ~> 2 * v

The first example describes a memory that consists of two locations `l1` and
`l2` that respectively contain the values 6 and 8. Since the separation
conjunction `P ** Q` ensures that the parts of the memory described by `P` and
`Q` are disjoint, we know that `l1` and `l2` are in different (i.e. they do not
alias). This makes separating conjunction very different from conjunction
`P /\ Q`, which says that `P` and `Q` both hold for the same memory. 

The second example describes the memories that contain two different locations
`l1` and `l2`, so that the value of `l2` is twice that of `l1`.

Making use of separating conjunction, we can give very concise specifications of
programs that manipulate pointers, for example, take the following Hoare logic
specification of the swap function:

  {{ l ~> v ** k ~> w }} swap l k {{ l ~> w ** k ~> v }}
     ^                               ^
   precondition                     postcondition

This specification expresses that swap is indeed swapping, as witnessed by the
fact that the values of the locations `l` and `k` have been swapped. But apart
from that, it also expresses in the precondition that the locations `l` and `k`
should be different before executing the program, and in the postcondition
that these are still different.
*)

(* # Shallow embedding versus deep embedding *)
(*
In the second lecture, we have already seen how we could use Coq to model a
programming language. In that section, we started by defining a _syntax_ for
our language in terms of an inductive type, and then gave an operational
semantics for this language. The approach of first defining a syntax is called
a _deep embedding_.

In this section, we proceed differently: we are not going to define an explicit
syntax for our separation logic. Instead, we are going to define the connectives
of our separation logic directly by their _semantic interpretation_.  This is
called a _shallow embedding_.
*)

(* # Shallow embedding of separation logic *)
(*
The first question that we need to answer is: what will be the semantic
interpretation of the connectives of our separation logic? As we have just seen,
formulas in separation logic describe sets of memories. For example:

  \Ex v, l1 ~> v ** l2 ~> 2 * v

Describes describes all memories that contain two different locations `l1` and
`l2`, so that the value of `l2` is twice that of `l1`.

The natural way to describe sets of memories in Coq is by means of a predicate:
*)
Definition iProp := mem -> Prop.

(*
Now, let us try to give a semantic interpretation of separating conjunction.
For this, recall the informal description of `P ** Q`: the memory can be split
into two _disjoint_ parts, so that the first satisfies `P` and the second
satisfies `Q`. In the previous lecture we put a lot of effort in formalizing
disjointness and unions of finite maps. Since our memories are represented as
finite maps, that effort will pay of now:
*)
Definition iSep (P Q : iProp) : iProp := fun m =>
  exists m1 m2, m = munion m1 m2 /\ mdisjoint m1 m2 /\ P m1 /\ Q m2.
Notation "P ** Q" := (iSep P Q) (at level 80, right associativity).

(*
Recall that in predicates are functions. So, to construct an element of type
`iProp` (i.e. `mem -> Prop`) we use a lambda abstraction of Coq.

In order to write down separation logic propositions in a concise way, we use
the `Notation` command to setup Coq's parser and pretty printer.
*)

(*
In the same spirit as separating conjunction, we can now describe the points-to
connective and the empty connective. These definitions crucially relies on the
singleton finite map `msingleton l v` and the empty finite map `mempty` that we
have defined in the first lecture.
*)
Definition points_to (l : nat) (v : val) : iProp := fun m =>
  m = msingleton l v.
Notation "l ~> v" := (points_to l v) (at level 20).

Definition iEmp : iProp := fun m => m = mempty.
Notation "'emp'" := iEmp.

(*
Together with separating conjunction, we have a corresponding form of
implication: the magic wand `P -* Q`. It describes the memories described by `Q`
minus those described by `P`, i.e., it describes the memories such that, if you
(disjointly) add memories satisfying `P`, you obtain resources satisfying `Q`.
*)
Definition iWand (P Q : iProp) : iProp := fun m =>
  forall m2, mdisjoint m2 m -> P m2 -> Q (munion m2 m).
Notation "P -* Q" :=
  (iWand P Q) (at level 99, Q at level 200, right associativity).

(*
Finally, we lift the quantifiers of Coq into our separation logic. Note that
we use the functions of Coq to represent the binder.
*)
Definition iForall {A} (P : A -> iProp) : iProp := fun m => forall x, P x m.
Notation "'All' x1 .. xn , P" :=
  (iForall (fun x1 => .. (iForall (fun xn => P)) ..))
  (at level 200, x1 binder, xn binder, right associativity).

Definition iExists {A} (P : A -> iProp) : iProp := fun m => exists x, P x m.
Notation "'Ex' x1 .. xn , P" :=
  (iExists (fun x1 => .. (iExists (fun xn => P)) ..))
  (at level 200, x1 binder, xn binder, right associativity).

(*
In order to express mathematical statements in our separation logic (for as
equality, that a number is even, ...), we will now define an embedding of Coq
propositions (type `Prop`) into the propositions of our separation logic (type
`iProp`). We define this using (higher-order) existential quantification.
*)
Definition iPure (p : Prop) : iProp := Ex _ : p, emp.
Notation "@[ p ]" := (iPure p) (at level 20, p at level 200).

(* ## Weakest preconditions and Hoare triples *)
(*
So far, we have defined basic logical connectives of our separation logic. But
last, but not least, we of course need some way of expressing properties of
programs. We do this using Hoare triples:

  {{ P }} e {{ Q }}

In this lecture, we consider Hoare triples for total program correctness, so the
intuitive meaning of the Hoare triple is:

  If the precondition holds for the memory before hand, then the
  expression `e` results in a value `v`, such that `Q v` holds.

Note that our postconditions have type `val -> iProp`, which allows us to
talk about the result value of an expression. For example:

  {{ l ~> v ** k ~> w }}
    swap l k
  {{ fun v => @[ v = VUnit ] ** l ~> w ** k ~> v }}

Instead of defining Hoare triples directly, we first define the notion of
weakest preconditions.

  wp e Q

And then define Hoare triples as :

  {{ P }} e {{ Q }} := P |- wp e Q

Where |- is the point-wise entailment of `iProp`:
*)

Definition iEntails (P Q : iProp) : Prop := forall m, P m -> Q m.
Notation "P |- Q" := (iEntails P Q) (at level 99, Q at level 200).

(*
Now, before we give the formal definition of weakest preconditions, there is
one final catch. An important part of separation logic is that we have the
so-called _framing_ rule:

        {{ P }} e {{ Q }}
  -----------------------------
   {{ P ** R }} e {{ P ** R }}

Let us see this rule in action. As we have seen before, we can give the
following specification to the swap function:

  {{ l ~> v ** k ~> w }} swap l k {{ l ~> w ** k ~> v }}

This specification looks overly restrictive as the pre- and post-condition say
that the memory should exactly contain the locations `l` and `k`. However,
using the frame rule, we can derive also:

  {{ l ~> v ** k ~> w ** R }} swap l k {{ l ~> w ** k ~> v ** R }}

Where `R` is any formula of separation logic, for example, `k' ~> w'` for
some other location `k'`. As we see here, the frame rule allows us to reason
locally: we can state and prove specifications with a small memory footprint,
and then use framing to extend them to bigger memory footprints, so that we can
use the specification in larger contexts too.

In order to make sure that we can prove the framing rule, the definition of
weakest preconditions becomes slightly more complicated. We also have to
qualify over all possible frames `mf`:
*)
Definition wp (e : expr) (Q : val -> iProp) : iProp := fun m =>
  forall mf, mdisjoint m mf ->
    exists m' v, mdisjoint m' mf /\
                 big_step e (munion m mf) v (munion m' mf) /\
                 Q v m'.

Definition hoare (P : iProp) (e : expr) (Q : val -> iProp) : Prop :=
  P |- wp e Q.

(* # Basic rules of the logic *)
(*
Let us first prove that entailment |- is a pre-order, i.e. it is reflexive and
transitive. These properties are crucial to compose proofs.
*)
Lemma iEntails_refl P : P |- P.
Proof.
  unfold iEntails.
  intros m Hm.
  assumption.
Qed.
Lemma iEntails_trans P Q R : (P |- Q) -> (Q |- R) -> P |- R.
Proof.
  (* Note that we do not really have to unfold `iEntails`: the `intros` tactic
  will do that for us. *)
  intros HPQ HQR m HP. apply HQR. apply HPQ. assumption.
Qed.

(* ## Rules for separating conjunction *)
(*
We now prove the key properties of separating conjunction: monotonicity, the
identity laws w.r.t. `emp`, commutativity, and associativity.
*)
Lemma iSep_mono_l P1 P2 Q : (P1 |- P2) -> P1 ** Q |- P2 ** Q.
Proof.
  intros HP m Hm.
  unfold iSep in Hm.
  destruct Hm as [m1 Hm].
  destruct Hm as [m2 Hm].
  destruct Hm as [Heq Hm].
  destruct Hm as [Hdisj Hm].
  destruct Hm as [HPm1 HQm2].
(* As we see, writing down this sequence of existential and conjunction
eliminations becomes pretty tedious. It requires many tactics, and we have to
name all the auxiliary results. Fortunately, Coq allows us to nest these
`destruct`s in the following way. *)
Restart.
  intros HP m Hm.
  unfold iSep in Hm.
  destruct Hm as [m1 [m2 [Heq [Hdisj [HPm1 HQm2]]]]].
(* This is much shorter, but still results in a lot of brackets. Coq provides
yet another syntax to make this more concise. *)
Restart.
  intros HP m Hm.
  unfold iSep in Hm.
  destruct Hm as (m1 & m2 & Heq & Hdisj & HPm1 & HQm2).
(*
The syntax `(x1 & x2 & ... & xn)` is just sugar for `[x1 [x2 [... [xn-1 xn]]]]`.

And finally, we can even perform the eliminations directly while introducing:
*)
Restart.
  intros HP m (m1 & m2 & Heq & Hdisj & HP1 & HQ).
  subst m.
  unfold iSep.
  exists m1, m2.
  split.
  { reflexivity. }
  split.
  { assumption. }
  split.
  { apply HP. assumption. }
  assumption.
Restart.
(* Or to make the proof even shorter, we can use `eauto`, which uses all
hypotheses (including implications, like the entailment) in the context by
default. *)
  intros HP m (m1 & m2 & Heq & Hdisj & HPm1 & HQm2).
  subst m. unfold iSep. eauto 10.
Qed.
Lemma iSep_comm P Q : P ** Q |- Q ** P.
Proof.
  intros m (m1 & m2 & Heq & Hdisj & HP & HQ).
  exists m2, m1.
  rewrite <-munion_comm by assumption.
  auto using mdisjoint_sym.
Qed.
Lemma iSep_assoc P Q R : P ** (Q ** R) |- (P ** Q) ** R.
Proof.
  intros m (m1 & m' & Heq & Hdisj & HP & (m2 & m3 & Heq' & Hdisj' & HQ & HR)).
  subst.
  exists (munion m1 m2), m3. split.
  { rewrite munion_assoc. reflexivity. }
  split.
  { eauto using mdisjoint_union_l, mdisjoint_union_inv_rr. }
  split.
  { exists m1, m2. eauto using mdisjoint_union_inv_rl. }
  assumption.
Qed.

(** ### Exercise *)
(*
Prove the following laws.
*)
Lemma iSep_emp_l P : P |- emp ** P.
Proof. Admitted.
Lemma iSep_emp_l_inv P : emp ** P |- P.
Proof. Admitted.

(* ## Rules for magic wand *)
Lemma iWand_intro_r P Q R : (P ** Q |- R) -> P |- Q -* R.
Proof.
  intros H m Hm m' ? HQ. apply H. rewrite munion_comm by assumption.
  exists m, m'; auto using mdisjoint_sym.
Qed.
Lemma iWand_elim P Q : P ** (P -* Q) |- Q.
Proof.
  intros m (m1 & m2 & ? & ? & ? & ?). subst.
  apply H2; auto.
Qed.

(* ## Rules for universal quantification *)
Lemma iForall_intro {A} P (Q : A -> iProp) :
  (forall x, P |- Q x) -> (P |- All x, Q x).
Proof. intros H m HP x. apply H. assumption. Qed.
Lemma iForall_elim {A} (P : A -> iProp) x : (All z, P z) |- P x.
Proof. intros m HP. apply HP. Qed.

(* ## Rules for existential quantification *)
(* ### Exercise *)
(*
Prove the following laws.
*)
Lemma iExist_intro {A} (P : A -> iProp) x : P x |- Ex z, P z.
Proof. Admitted.
Lemma iExist_elim {A} (P : A -> iProp) Q :
  (forall x, P x |- Q) -> (Ex z, P z) |- Q.
Proof. Admitted.

(* ## Derived rules of the logic *)
(*
So far, we have proved a bunch of rules for our separation logic by unfolding
the definition of the separation logic connectives. However, it turns out that
many additional rules can be _derived_ from the rules we have seen so far.
*)
Lemma iSep_emp_r P : P |- P ** emp.
Proof.
  apply iEntails_trans with (emp ** P).
  { apply iSep_emp_l. }
  apply iSep_comm.
Qed.
Lemma iSep_emp_r_inv P : P ** emp |- P.
Proof.
  apply iEntails_trans with (emp ** P).
  { apply iSep_comm. }
  apply iSep_emp_l_inv.
Qed.

Lemma iSep_mono_r P Q1 Q2 :
  (Q1 |- Q2) -> P ** Q1 |- P ** Q2.
Proof.
  intros HQ. apply iEntails_trans with (Q1 ** P).
  { apply iSep_comm. }
  apply iEntails_trans with (Q2 ** P).
  { apply iSep_mono_l. assumption. }
  apply iSep_comm.
Qed.

(*** ## Exercise *)
(*
Prove the following derived laws. Make sure to not unfold the definitions of
the connectives of our separation logic, but only use the rules we have already
proven. Hint: you need to use transitivity of entailment many times.
*)
Lemma iSep_mono P1 P2 Q1 Q2 :
  (P1 |- P2) -> (Q1 |- Q2) -> P1 ** Q1 |- P2 ** Q2.
Proof. Admitted.

(* This lemma is quite subtle: you need to use the rules for commutativity,
associativity and monotonicity of separating conjunction. I advice to first work
out the proof on paper, and then do it in Coq. *)
Lemma iSep_assoc' P Q R : (P ** Q) ** R |- P ** (Q ** R).
Proof. Admitted.

Lemma iWand_intro_l P Q R : (Q ** P |- R) -> P |- Q -* R.
Proof. Admitted.

(* This lemma is very difficult: you need to use the introduction and
elimination rules for magic wand `-*`. *)
Lemma iExist_sep {A} (P : A -> iProp) Q :
  (Ex x, P x) ** Q |- Ex x, P x ** Q.
Proof. Admitted.

Lemma iPure_intro (p : Prop) : p -> emp |- @[ p ].
Proof. Admitted.

Lemma iPure_elim (p : Prop) P Q : (p -> P |- Q) -> @[ p ] ** P |- Q.
Proof. Admitted.

(* ## Logical rules for weakest preconditions *)
(*
We now prove the framing rule for weakest preconditions. Convince yourself
that from this rule, we get the framing rule for Hoare triples.

The proof below is a bit subtle, as we need to use properties about `munion`
and `mdisjoint` many times.
*)
Lemma wp_frame Q R e :
  wp e Q ** R |- wp e (fun v => Q v ** R).
Proof.
  intros m (m1 & m2 & Heq & Hdisj & Hwp & HR). subst m.
  intros mf Hm.
  destruct (Hwp (munion m2 mf)) as (m' & v & Hdisj' & Hbig & HQ).
  { eauto using mdisjoint_union_r, mdisjoint_union_inv_ll. }
  exists (munion m' m2), v. split.
  { eauto 4 using mdisjoint_union_l, mdisjoint_union_inv_rr, mdisjoint_union_inv_lr. }
  split.
  { rewrite <-!munion_assoc. assumption. }
  exists m', m2. split.
  { reflexivity. }
  eauto using mdisjoint_union_inv_rl.
Qed.

(* ### Exercise *)
(*
Prove the rule below.
*)
Lemma wp_mono Q R e :
  (forall v, Q v |- R v) ->
  wp e Q |- wp e R.
Proof. Admitted.

(* # Structural rules for weakest preconditions *)
Lemma wp_val v Q : Q v |- wp (EVal v) Q.
Proof. intros m HQ mf Hm. exists m, v. eauto with big_step. Qed.

Lemma wp_ctx E e Q :
  wp e (fun w => wp (fill E (EVal w)) Q) |- wp (fill E e) Q.
Proof.
  intros m Hwp mf Hdisj.
  destruct (Hwp mf) as (m' & v & Hdisj' & Hbig & Hwp').
  { assumption. }
  destruct (Hwp' mf) as (m'' & v'' & Hdisj'' & Hbig' & HQ).
  { assumption. }
  eauto 10 using big_step_fill.
Qed.

Lemma wp_let x e1 e2 Q :
  wp e1 (fun v => wp (subst x v e2) Q) |- wp (ELet x e1 e2) Q.
Proof.
  intros m Hwp mf Hdisj.
  destruct (Hwp mf Hdisj) as (mf' & v' & Hdisj' & Hbig & Hwp2).
  destruct (Hwp2 mf Hdisj') as (mf'' & v'' & Hdisj'' & Hbig' & HQ).
  exists mf'',  v''. eauto with big_step.
Qed.

(* ### Exercise *)
(*
Prove the rules below: all of these follow the same structure as the proofs
above.
*)
Lemma wp_seq e1 e2 Q :
  wp e1 (fun _ => wp e2 Q) |- wp (ESeq e1 e2) Q.
Proof. Admitted.

Lemma wp_if_true e2 e3 Q :
  wp e2 Q |- wp (EIf (EVal (VBool true)) e2 e3) Q.
Proof. Admitted.

Lemma wp_if_false e2 e3 Q :
  wp e3 Q |- wp (EIf (EVal (VBool false)) e2 e3) Q.
Proof. Admitted.

Lemma wp_while e1 e2 Q :
  wp (EIf e1 (ESeq e2 (EWhile e1 e2)) (EVal VUnit)) Q |- wp (EWhile e1 e2) Q.
Proof. Admitted.

Lemma wp_op op v1 v2 v Q :
  eval_bin_op op v1 v2 = Some v ->
  Q v |- wp (EOp op (EVal v1) (EVal v2)) Q.
Proof. Admitted.

(* # Stateful rules for weakest preconditions *)
(*
We finish by proving the rules for the operations of our language that
manipulate the state. Let us take a look at the rules for load and store (in
mixed informal and Coq notations):

  l ~> v ** (l ~> v -* Q v)     |- wp !l Q.
  l ~> v ** (l ~> w -* Q VUnit) |- wp (!l := w) Q.

So, what does the second rule say: In order to prove the weakest precondition
of a store, we have to show that `l` already exists in the memory. This is done
by showing that we have the points-to connective `l ~> v`. Now, since the only
way of introducing a separating conjunction is monotonicity, this means we have
to give up the point-to connective `l ~> v`, which leaves us with
`l ~> w -* Q VUnit`. By introducing the magic wand, we consequentially get the
point-to connective back, but now with the new value `w`.

The same kind of pattern is used for the other rules.
*)
Lemma wp_load l v Q :
  l ~> v ** (l ~> v -* Q v) |- wp (ELoad (EVal (VLoc l))) Q.
Proof.
  intros m HQ mf Hdisj.
  destruct HQ as (m1 & m2 & Heq & Hdisj' & Hpointsto & HQ). subst m.
  unfold points_to in Hpointsto. subst m1.
  exists (munion (msingleton l v) m2), v. split.
  { assumption. }
  split.
  { eapply Load_big_step.
    - eapply Val_big_step.
    - rewrite <-munion_assoc. rewrite munion_lookup.
      rewrite msingleton_lookup. simpl. reflexivity. }
  apply HQ.
  { assumption. }
  unfold points_to. reflexivity.
Qed.

(* ### Exercise (very difficult) *)
(*
Prove the rules below: all of these follow the same structure as the proofs
above. Hint: you need to make extensive use of properties about finite maps.
Use Coq's `Search` command to find these. For example:
*)
Search (minsert _ _ (msingleton _ _) = _).
(*
Yields:

  minsert_singleton:
    forall (A : Type) (i : nat) (x y : A),
    minsert i x (msingleton i y) = msingleton i x
*)
Lemma wp_store l v w Q :
  l ~> v ** (l ~> w -* Q VUnit) |- wp (EStore (EVal (VLoc l)) (EVal w)) Q.
Proof. Admitted.

Lemma wp_alloc v Q :
  (All l, l ~> v -* Q (VLoc l)) |- wp (EAlloc (EVal v)) Q.
Proof. Admitted.

Lemma wp_free l v Q :
  l ~> v ** Q VUnit |- wp (EFree (EVal (VLoc l))) Q.
Proof. Admitted.

(* # An example *)
(*
Finally, we will look at an example. We take the simplest program that
manipulates pointers: the swap function.
*)

(*
  swap x y :=
    let tmp := !x in
    x := !y;
    y := tmp
*)
Definition swap (x y : val) : expr :=
  ELet "tmp" (ELoad (EVal x))
    (ESeq (EStore (EVal x) (ELoad (EVal y)))
          (EStore (EVal y) (EVar "tmp"))).

(* Transitivity with the premises swapped *)
Lemma iEntails_trans' P Q R : (Q |- R) -> (P |- Q) -> P |- R.
Proof. eauto using iEntails_trans. Qed.

Lemma swap_correct l k v w :
  hoare
    (l ~> v ** k ~> w)
    (swap (VLoc l) (VLoc k))
    (fun ret => @[ret = VUnit] ** l ~> w ** k ~> v).
Proof.
  unfold hoare.
  unfold swap.
  eapply iEntails_trans'.
  { apply wp_let. }
  eapply iEntails_trans'.
  { apply wp_load. }
  apply iSep_mono_r. apply iWand_intro_l.
  simpl.
  eapply iEntails_trans'.
  { apply (wp_ctx (SeqCtx _ :: StoreCtxR _ :: nil)). }
  eapply iEntails_trans'.
  { apply wp_load. }
  eapply iEntails_trans'.
  { apply iSep_comm. }
  apply iSep_mono_l. apply iWand_intro_r.
  simpl.
  eapply iEntails_trans'.
  { apply (wp_ctx (SeqCtx _ :: nil)). }
  eapply iEntails_trans'.
  { apply wp_store. }
  apply iSep_mono_r. apply iWand_intro_l.
  simpl.
  eapply iEntails_trans'.
  { apply wp_seq. }
  eapply iEntails_trans'.
  { apply wp_val. }
  eapply iEntails_trans'.
  { apply wp_store. }
  eapply iEntails_trans'.
  { apply iSep_comm. }
  apply iSep_mono_l. apply iWand_intro_r.
  eapply iEntails_trans.
  { apply iSep_emp_l. }
  apply iSep_mono_l.
  apply iPure_intro.
  reflexivity.
Qed.

(* # Conclusion *)
(*
As you have seen, proving the correctness of our simple example already takes
a lot of work. For example, we have to:

- Use transitivity of entailment to use the weakest precondition rules.
- After we have used a rule for a load or store, we have to "frame".
- We often have to reorder the premises on the LHS of the turnstile.
- We have to pick evaluation contexts ourselves when we use `wp_ctx`.

Of course, most of these steps are completely mechanical, and as such, Coq is
well capable of automating this. Unfortunately, automating proofs in separation
logic in Coq is beyond the scope of these lectures.

If you would like to know more about it, please take a look at the following
paper:

  Robbert Krebbers, Amin Timany and Lars Birkedal
  Interactive Proofs in Higher-Order Concurrent Separation Logic
  POPL 2017

If you want to see separation logic in Coq in practice, try the Iris project,
a state-of-the art higher-order concurrent separation logic that has been
implemented and verified in Coq:

  http://iris-project.org

*)
