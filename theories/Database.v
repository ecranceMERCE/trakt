(*******************************************************************************)
(*                           *                     Trakt                       *)
(*  _______        _    _    *            Copyright (C) 2022 MERCE             *)
(* |__   __|      | |  | |   *     (Mitsubishi Electric R&D Centre Europe)     *)
(*    | |_ __ __ _| | _| |_  *        Enzo Crance <enzo.crance@inria.fr>       *)
(*    | | '__/ _` | |/ / __| ***************************************************)
(*    | | | | (_| |   <| |_  * This file is distributed under the terms of the *)
(*    |_|_|  \__,_|_|\_\\__| *   GNU Lesser General Public License Version 3   *)
(*                           *  (see LICENSE file for the text of the license) *)
(*******************************************************************************)

From elpi Require Import elpi.

From Coq Require Import Bool.

Lemma and_impl_morphism : forall {A B A' B' : Prop},
  (A' -> A) -> (B' -> B) -> (A' /\ B' -> A /\ B).
Proof.
  intros A B A' B' HA HB [ProofA' ProofB'].
  apply (conj (HA ProofA') (HB ProofB')).
Qed.

Lemma andb_and_impl : forall (x y : bool), x && y = true -> x = true /\ y = true.
Proof.
  intros [] []; cbv [andb].
  1: split; reflexivity.
  all: discriminate.
Qed.

Lemma and_andb_impl : forall (x y : bool), x = true /\ y = true -> x && y = true.
Proof.
  intros [] []; cbv [andb]; try (intros [_ H]; exact H).
  intros [H _]; exact H.
Qed.

Lemma or_impl_morphism : forall {A B A' B' : Prop},
  (A' -> A) -> (B' -> B) -> (A' \/ B' -> A \/ B).
Proof.
  intros A B A' B' HA HB [ProofA' | ProofB'].
  - left. apply (HA ProofA').
  - right. apply (HB ProofB').
Qed.

Lemma orb_or_impl : forall (x y : bool), x || y = true -> x = true \/ y = true.
Proof.
  intros [] []; cbv [orb]; try (intro H; left; exact H).
  intro H; right; exact H.
Qed.

Lemma or_orb_impl : forall (x y : bool), x = true \/ y = true -> x || y = true.
Proof.
  intros [] []; cbv [orb]; try reflexivity.
  intros [H | H]; exact H.
Qed.

Lemma not_impl_morphism : forall {A A' : Prop},
  (A -> A') -> (~ A' -> ~ A).
Proof.
  intros A A' HA ProofNotA' ProofA.
  apply (ProofNotA' (HA ProofA)).
Qed.

Lemma negb_not_impl : forall (x : bool), negb x = true -> ~ x = true.
Proof.
  intros []; cbv [negb].
  intro H; discriminate H.
  intros _ H; discriminate H.
Qed.

Lemma not_negb_impl : forall (x : bool), ~ x = true -> negb x = true.
Proof.
  intros []; cbv [negb]; auto.
Qed.

Elpi Db logic.db lp:{{
  logical-connector
    {{ and }} {{ andb }} [covariant, covariant]
    {{ and_impl_morphism }} {{ andb_and_impl }} {{ and_andb_impl }}.

  logical-connector
    {{ or }} {{ orb }} [covariant, covariant]
    {{ or_impl_morphism }} {{ orb_or_impl }} {{ or_orb_impl }}.
  
  logical-connector
    {{ not }} {{ negb }} [contravariant]
    {{ not_impl_morphism }} {{ negb_not_impl }} {{ not_negb_impl }}.
}}.

Lemma iff_impl_ind : forall {A B A' B' : Prop},
  (A' -> A) -> (A -> A') -> (B' -> B) -> (B -> B') -> (A' <-> B') -> (A <-> B).
Proof.
  intros A B A' B' HA1 HA HB1 HB [HAB' HBA'].
  split.
  - intro a; exact (HB1 (HAB' (HA a))).
  - intro b; exact (HA1 (HBA' (HB b))).
Qed.

Lemma iff_Booleqb_impl : forall (x y : bool), x = true <-> y = true -> Bool.eqb x y = true.
Proof.
  intros [] []; cbn [eqb]; intros [H1 H2]; auto.
Qed.

Lemma Booleqb_iff_impl : forall (x y : bool), Bool.eqb x y = true -> x = true <-> y = true.
Proof.
  intros [] []; cbn [eqb]; intro H; split; auto.
Qed.

Elpi Db embeddings.db lp:{{ }}.
Elpi Db symbols.db lp:{{ }}.
Elpi Db relations.db lp:{{ }}.
Elpi Db conversion.db lp:{{ }}.