From Trakt Require Import Trakt.


Section Issue11.

  Variable P : nat -> Prop.
  Variable P' : nat -> bool.
  Hypothesis P_P' : forall x, P x <-> P' x = true.
  Trakt Add Relation 1 P P' P_P'.

  (* In this example, it is incorrect to replace P with P' *)
  Goal forall f : nat -> Prop, (forall r : nat, f r = P r) -> True.
  Proof.
    trakt bool.
  Abort.

  (* When the context around P is an equivalence, it is correct *)
  Goal forall f : nat -> Prop, (forall r : nat, f r <-> P r) -> True.
  Proof.
    trakt bool.
  Abort.

End Issue11.
