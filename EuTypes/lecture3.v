Require Export lecture2.
Require Import EqNat.

(* # Contents *)
(*
In the next lecture, we will be defining a program logic in the form of a
separation logic for our ML-like language. The crucial feature of separation
logic is that it allows one to talk about _disjointness_ of memories. In this
part of the lecture, we will prepare for the next lecture by defining the
following operations on maps, and proving properties about them:

  munion : map A -> map A -> map A
  mdisjoint : map A -> map A -> Prop

A crucial thing that you will learn now is reuse existing lemmas on finite maps
to prove derived properties.
*)

(* # The union operation on finite maps *)
(*
In order to model separation logic in Coq, we need to have an operation that
takes the union of two finite maps:

  munion : map A -> map A -> map A

That satisfies

  mlookup (munion m1 m2) i =
    option_union (mlookup m1 i) (mlookup m2 i)

Where `option_union` is the (left-biased) union operation on the `option` type,
which is defined as follows:
*)
Definition option_union {A} (mx my : option A) : option A :=
  match mx with
  | Some x => Some x
  | None => my
  end.

(*
As is usual, we define the union operation in several stages: 1.) we define it
on raw maps, 2.) we prove that it preserves well-formedness of maps, 3.) lift
the operation to maps (which are bundled with a proof of well-formedness) 4.) we
prove the lookup property on raw maps, and finally 5.) lift that property from
raw maps to maps.
*)
Fixpoint munion_raw {A} (m1 m2 : map_raw A) : map_raw A :=
  match m1, m2 with
  | mx :: m1, my :: m2 => option_union mx my :: munion_raw m1 m2
  | [], m2 => m2
  | m1, [] => m1
  end.

Lemma munion_raw_wf {A} b (m1 m2 : map_raw A) :
  map_wf b m1 -> map_wf b m2 -> map_wf b (munion_raw m1 m2).
Proof. (* left as an optional exercise *) Admitted.

Lemma munion_lookup_raw {A} (m1 m2 : map_raw A) (i : nat) :
  mlookup_raw (munion_raw m1 m2) i =
    option_union (mlookup_raw m1 i) (mlookup_raw m2 i).
Proof. (* left as an optional exercise *) Admitted.

Definition munion {A} (m1 m2 : map A) : map A :=
  let (m1,Hm1) := m1 in
  let (m2,Hm2) := m2 in
  make_map (munion_raw m1 m2) (munion_raw_wf _ m1 m2 Hm1 Hm2).

Lemma munion_lookup {A} (m1 m2 : map A) (i : nat) :
  mlookup (munion m1 m2) i =
    option_union (mlookup m1 i) (mlookup m2 i).
Proof. (* left as an optional exercise *) Admitted.

(* ## Properties of the union operation *)
(*
Now that we have defined the operation `munion` and have proven the lemma
`munion_lookup`, we prove some properties. The crucial thing to notice is that
the lemma `munion_lookup` fully specifies the behavior of the union operation,
after we have proven that, we never have to unfold the definition again. Let us
take a look at an example.
*)
Lemma munion_empty_l {A} (m : map A) : munion mempty m = m.
Proof.
  (* Note that apply also works with bi-implications, like `map_eq`:

    m1 = m2 <-> (forall i : nat, mlookup m1 i = mlookup m2 i)

  *)
  apply map_eq. intros i.
  rewrite munion_lookup.
  rewrite mempty_lookup.
  simpl.
  reflexivity.
Qed.

Lemma munion_insert_l {A} (m : map A) i x :
  minsert i x m = munion (msingleton i x) m.
Proof.
  apply map_eq. intros j. rewrite munion_lookup.
  (* In order to proceed, we need to make a case distinction between whether
  the natural numbers `i` and `j` are equal or not. For this we use the lemma:

    Nat.eq_dec: forall n m : nat, {n = m} + {n <> m}

  The lemma says that for any two natural numbers, we have either a proof
  of `x = y` that they are equal, or a proof of `n <> m` that they are unequal.
  The result of the lemma is a `sumbool`:

    Inductive sumbool (A B : Prop) : Set :=
      left : A -> {A} + {B} | right : B -> {A} + {B}

  On which we will perform a case analysis using the `destruct` tactic.
  *)
  destruct (Nat.eq_dec i j) as [Heq|Hneq].
  - subst i.
    rewrite minsert_lookup. rewrite msingleton_lookup.
    simpl. reflexivity.
  - (* In this case, we will use the lemma `insert_lookup_ne`:

        i <> j -> mlookup (minsert i y m) j = mlookup m j

    Note that contrary to most lemmas we have used for rewriting so far, this
    lemma has a premise `i <> j`. As a result, when we say:

      rewrite minsert_lookup_ne

    We will get an additional goal for proving the premise `i <> j`. In this
    case, however, it is trivial to prove the premise `i <> j`, after all, we
    already have a hypothesis `Hneq : i <> j`. As such, we can make use of the
    `by` argument of the `rewrite` tactic as follows:
    *)
    rewrite minsert_lookup_ne by assumption.
    (*
    This causes the `assumption` tactic to be used for proving the premise of
    the lemma that we wish to rewrite with.
    *)
    rewrite msingleton_lookup_ne by assumption. 
    (*
    Note that `msingleton_lookup_ne` has a similar premise.
    *)
    simpl. reflexivity.
Qed.

(* ### Exercise *)
(*
Prove the following properties. In order to prove the properties about maps, you
should make use of the lemma `map_eq`, and the lookup lemmas for the various
operations involved.
*)
Lemma munion_empty_r {A} (m : map A) : munion mempty m = m.
Proof. Admitted.

Lemma option_union_assoc {A} (mx my mz : option A) :
  option_union mx (option_union my mz) = option_union (option_union mx my) mz.
Proof. Admitted.

Lemma munion_assoc {A} (m1 m2 m3 : map A) :
  munion m1 (munion m2 m3) = munion (munion m1 m2) m3.
Proof. Admitted.

Lemma minsert_union {A} (m1 m2 : map A) i x :
  minsert i x (munion m1 m2) = munion (minsert i x m1) m2.
Proof. Admitted.

Lemma mdelete_union {A} (m1 m2 : map A) i :
  mdelete i (munion m1 m2) = munion (mdelete i m1) (mdelete i m2).
Proof. Admitted.

(* ## Disjointness of finite maps *)
(*
So far, we have proved associativity of the union operation on finite maps, but
not yet commutativity. Unfortunately, this property does not hold
unconditionally. In case `m1` and `m2` both contain the key `i`, but with
different values, we do not have `munion m1 m2 = munion m2 m1`. To deal with
this issue, we define a relation:

  mdisjoint : map  A -> map A -> Prop

Which states that two maps are _disjoint_, i.e. they do not have any keys in
common. We can then state commutativity as:

  mdisjoint m1 m2 -> munion m1 m2 = munion m2 m1.
*)
Definition mdisjoint {A} (m1 m2 : map A) : Prop :=
  forall i, mlookup m1 i = None \/ mlookup m2 i = None.

Lemma option_union_None_r {A} (mx : option A) : option_union mx None = mx.
Proof. destruct mx; simpl; reflexivity. Qed.

Lemma munion_comm {A} (m1 m2 : map A) :
  mdisjoint m1 m2 -> munion m1 m2 = munion m2 m1.
Proof.
  intros Hdisj. apply map_eq; intros i.
  rewrite !munion_lookup. (* Using the modifier `!` of the rewrite tactic, we
  can rewrite using a lemma as many times as possible. *)
  destruct (Hdisj i) as [Hi | Hi].
  - rewrite Hi. simpl. rewrite option_union_None_r. reflexivity.
  - rewrite Hi. simpl. rewrite option_union_None_r. reflexivity.
Qed.

(*
Let us prove some more properties about disjointness of finite maps.
*)
Lemma mdisjoint_empty_l {A} (m : map A) : mdisjoint mempty m.
Proof.
  intros i. left.
  rewrite mempty_lookup. reflexivity.
Qed.

Lemma mdisjoint_sym {A} (m1 m2 : map A) : mdisjoint m1 m2 -> mdisjoint m2 m1.
Proof.
  intros Hm i.
  unfold mdisjoint in Hm.
  (* As we see now, we have a hypothesis

    Hm : forall i : nat, mlookup m1 i = None \/ mlookup m2 i = None

  Which contains a disjunction below a universal quantifier. As we have seen
  before, we can use the `destruct` tactic to eliminate disjunctions. But how
  can we deal with disjunctions below a universal quantifier?

  Well, the answer is simple: we first have to instantiate the universal
  quantifier. But how do we do that? By the Curry-Howard correspondence, we
  know that `forall` quantifiers are in fact dependent functions, which means
  that when we have `H : forall x : A, P x`, we just write `H a` to obtain
  something of type `P a`.

  So, in this case, we have:

    Hm i : mlookup m1 i = None \/ mlookup m2 i = None

  On which we can then do a case analysis.
  *)
  destruct (Hm i) as [Hm1|Hm2].
  - right. assumption.
  - left. assumption.
Qed.

(* ### Exercise *)
(* Prove the properties below. Do not forget that you can use

  destruct (Nat.eq_dec i j) as [Heq|Hneq].
  
To make a case analysis between whether `i` and `j` are equal or not.
*)
Lemma mdisjoint_singleton {A} (m : map A) i x :
  mlookup m i = None -> mdisjoint (msingleton i x) m.
Proof. Admitted.

Lemma mdisjoint_singleton_inv {A} (m : map A) i x :
  mdisjoint (msingleton i x) m -> mlookup m i = None.
Proof. Admitted.

Lemma mdisjoint_union_l {A} (m1 m2 m3 : map A) :
  mdisjoint m1 m3 ->
  mdisjoint m2 m3 ->
  mdisjoint (munion m1 m2) m3.
Proof. Admitted.
Lemma mdisjoint_union_inv_ll {A} (m1 m2 m3 : map A) :
  mdisjoint (munion m1 m2) m3 ->
  mdisjoint m1 m3.
Proof. Admitted.
Lemma mdisjoint_union_inv_lr {A} (m1 m2 m3 : map A) :
  mdisjoint (munion m1 m2) m3 ->
  mdisjoint m2 m3.
Proof. Admitted.

(*
Note that the properties below can be derived from the properties you have just
proven. You should not unfold the definition `mdisjoint`.
*)
Lemma mdisjoint_union_r {A} (m1 m2 m3 : map A) :
  mdisjoint m3 m1 ->
  mdisjoint m3 m2 ->
  mdisjoint m3 (munion m1 m2).
Proof. Admitted.
Lemma mdisjoint_union_inv_rl {A} (m1 m2 m3 : map A) :
  mdisjoint m3 (munion m1 m2) ->
  mdisjoint m3 m1.
Proof. Admitted.
Lemma mdisjoint_union_inv_rr {A} (m1 m2 m3 : map A) :
  mdisjoint m3 (munion m1 m2) ->
  mdisjoint m3 m2.
Proof. Admitted.

(* ### Exercise *)
(*
And finally, some more properties about finite maps that will need later.
*)
Lemma minsert_singleton {A} i (x y : A) :
  minsert i x (msingleton i y) = msingleton i x.
Proof. Admitted.

Lemma mdelete_singleton {A} i (x : A) :
  mdelete i (msingleton i x) = mempty.
Proof. Admitted.

Lemma mdelete_None {A} (m : map A) i :
  mlookup m i = None -> mdelete i m = m.
Proof. Admitted.
