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

From Trakt Require Import Trakt.

From Coq Require Import ZArith.
From mathcomp Require Import ssrint.

Delimit Scope Z_scope with Z.

(* ===== int ==================================================================================== *)

(* embedding *)

Axiom Z_of_int : int -> Z.
Axiom Z_to_int : Z -> int.

Axiom int_Z_gof_id : forall (x : int), x = Z_to_int (Z_of_int x).
Axiom int_Z_fog_id : forall (z : Z), Z_of_int (Z_to_int z) = z.
Trakt Add Embedding (int) (Z) (Z_of_int) (Z_to_int) (int_Z_gof_id) (int_Z_fog_id).

(* symbol *)

Axiom addz_Zadd_embed_eq : forall (x y : int),
  Z_of_int (intZmod.addz x y) = (Z_of_int x + Z_of_int y)%Z.
Trakt Add Symbol (intZmod.addz) (Z.add) (addz_Zadd_embed_eq).

(* relation *)

Axiom eqint_Zeqb_equiv : forall (x y : int), x = y <-> (Z_of_int x =? Z_of_int y)%Z = true.
Trakt Add Relation (@eq int) (Z.eqb) (eqint_Zeqb_equiv).

Goal forall (x y : int), intZmod.addz x y = intZmod.addz y x.
Proof.
  trakt Z bool.
Abort.

(* ===== nat ==================================================================================== *)

(* embeddings in bool and Prop *)

Axiom nat_Z_gof_id : forall (n : nat), n = Z.to_nat (Z.of_nat n).
Axiom nat_Z_bool_fog_cond_id : forall (z : Z), (0 <=? z)%Z = true -> Z.of_nat (Z.to_nat z) = z.
Axiom nat_Z_bool_cond_f_always_true : forall (n : nat), (0 <=? Z.of_nat n)%Z = true.
Trakt Add Embedding
  (nat) (Z) (Z.of_nat) (Z.to_nat) (nat_Z_gof_id) (nat_Z_bool_fog_cond_id)
    (nat_Z_bool_cond_f_always_true).

Axiom nat_Z_Prop_fog_cond_id : forall (z : Z), (0 <= z)%Z -> Z.of_nat (Z.to_nat z) = z.
Axiom nat_Z_Prop_cond_f_always_true : forall (n : nat), (0 <= Z.of_nat n)%Z.
Trakt Add Embedding
  (nat) (Z) (Z.of_nat) (Z.to_nat) (nat_Z_gof_id) (nat_Z_Prop_fog_cond_id)
    (nat_Z_Prop_cond_f_always_true).

(* symbols *)

Axiom Natadd_Zadd_embed_eq : forall (n m : nat),
  Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%Z.
Trakt Add Symbol (Nat.add) (Z.add) (Natadd_Zadd_embed_eq).

Axiom S_Zadd1_embed_eq : forall (n : nat), Z.of_nat (S n) = (1 + Z.of_nat n)%Z.
Trakt Add Symbol (S) (Z.add 1%Z) (S_Zadd1_embed_eq).

(* relations *)

Axiom Nateqb_Zeqb_equiv : forall (n m : nat), n =? m = (Z.of_nat n =? Z.of_nat m)%Z.
Trakt Add Relation (Nat.eqb) (Z.eqb) (Nateqb_Zeqb_equiv).

Axiom eqnat_eqZ_equiv : forall (n m : nat), n = m <-> Z.of_nat n = Z.of_nat m.
Trakt Add Relation (@eq nat) (@eq Z) (eqnat_eqZ_equiv).

Axiom eqnat_Zeqb_equiv : forall (n m : nat), n = m <-> (Z.of_nat n =? Z.of_nat m)%Z = true.
Trakt Add Relation (@eq nat) (Z.eqb) (eqnat_Zeqb_equiv).

Axiom Nateqb_eqnat_refl : forall (n m : nat), Nat.eqb n m = true <-> n = m.
Trakt Add Relation (Nat.eqb) (@eq nat) (Nateqb_eqnat_refl).

Goal forall (n m : nat), Nat.eqb (S n + m) (m + S n) = true.
Proof.
  trakt Z Prop. (* or trakt Z bool. *)
Abort.

(* ===== decidable type ========================================================================= *)

Axiom E : Type.
Module E.
  Axiom eqb : E -> E -> bool.
  Axiom isDecidable : forall (x y : E), x = y <-> eqb x y = true.
End E.
Trakt Add Relation (@eq E) (E.eqb) (E.isDecidable).

Goal forall (x : E), x = x.
Proof.
  trakt E bool.
Abort.

(* ===== uninterpreted function ================================================================= *)

Goal forall (f : nat -> nat) (n m : nat), f (S n + m) = f(m + S n).
Proof.
  trakt Z bool.
Abort.

(* ===== projections ============================================================================ *)

Axiom mulz_Zmul_embed_eq : forall (x y : int),
  Z_of_int (intRing.mulz x y) = (Z_of_int x * Z_of_int y)%Z.
Trakt Add Symbol (intRing.mulz) (Z.mul) (mulz_Zmul_embed_eq).

Axiom Posz_id_embed_eq : forall (n : nat), Z_of_int (Posz n) = Z.of_nat n.
Trakt Add Symbol (Posz) (@id Z) (Posz_id_embed_eq).

From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.
Delimit Scope Z_scope with Z.

Axiom O_Z0_embed_eq : Z.of_nat O = Z0.
Trakt Add Symbol (O) (Z0) (O_Z0_embed_eq).

Axiom one_Z1_embed_eq : Z_of_int 1%R = 1%Z.
Trakt Add Symbol (1%R : int) (1%Z) (one_Z1_embed_eq).

Axiom eqopint_eqint_equiv : forall (x y : int), x == y <-> x = y.
Trakt Add Relation (@eq_op int_eqType : int -> int -> bool) (@eq int) (eqopint_eqint_equiv).

Axiom eqint_eqZ_equiv : forall (x y : int), x = y <-> Z_of_int x = Z_of_int y.
Trakt Add Relation (@eq int) (@eq Z) (eqint_eqZ_equiv).

Trakt Add Conversion (@GRing.add).
Trakt Add Conversion (@GRing.mul).
Trakt Add Conversion (@GRing.one).

Local Open Scope ring_scope.

Goal forall (f : int -> int) (x : int), x == 4 = true -> f (2%:Z * x + 1) == f 5 = true.
Proof.
  (* Set Printing All. *)
  trakt Z Prop.
Abort.

(* ===== with logic ============================================================================= *)

Goal forall (f : int -> nat) (x y : int) (b : bool),
  true = false || (b && false) || (x == x) && (f y == f y).
Proof.
  trakt Z Prop.
Abort.
