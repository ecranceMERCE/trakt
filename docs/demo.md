# Quick demo

!> This is only a showcase example.
For a more complete and precise overview, please head to the [tutorial](tutorial.md) and see the example files on [GitHub](https://github.com/ecranceMERCE/trakt).

Here is a very small example of the possibilities of Trakt.
Consider the following goal:

```coq
Goal forall (f : int -> nat) (x : int), f (x + 0)%R = f x.
```

It involves:
- the `nat` type from the standard library;
- the `int` type from the [MathComp](https://github.com/math-comp/math-comp) library;
- universal quantifiers, one of them on a function;
- general operations that are projections on structures (`GRing.add` hidden behind the general `+` notation, as well as `GRing.zero` behind `0`);
- equality in `Prop`.

Say the proof automation tactic we want to use is able to handle arithmetic and logic, when arithmetic is expressed in `Z` and logic in `bool`.
In order to prove this goal, we need to apply a preprocessing phase with `trakt Z bool`.

Before running the tactic, we need to make the following declarations:
- `int` is embeddable into `Z`;
- `nat` is embeddable into `Z` with a positivity condition;
- the equality on `nat` can be replaced with the boolean equality on `Z`;
- the addition on `int` can be replaced with the addition on `Z`;
- the projections `GRing.add`, `GRing.zero` and `GRing.Zmodule.sort` can trigger Coq conversion to detect the underlying terms.

First, we need to declare the **embedding** on `nat`:

```coq
Lemma nat_Z_gof_id : forall (n : nat), n = Z.to_nat (Z.of_nat n).
Proof. (* ... *) Qed.

Lemma nat_Z_fog_cond_id : forall (z : Z), 0 <=? z = true -> Z.of_nat (Z.to_nat z) = z.
Proof. (* ... *) Qed.

Lemma nat_Z_cond_always_true : forall (n : nat), 0 <=? Z.of_nat n = true.
Proof. (* ... *) Qed.

Trakt Add Embedding (nat) (Z) (Z.of_nat) (Z.to_nat) (nat_Z_gof_id) (nat_Z_fog_cond_id) (nat_Z_cond_always_true).
```

Similar declarations must be done on `int`.
Then, we need to declare the equality as a **relation** (the `2` argument here indicates that the relation is binary):

```coq
Lemma eqnat_Zeqb_equiv : forall (n m : nat), n = m <-> Z.eqb (Z.of_nat n) (Z.of_nat m) = true.
Proof. (* ... *) Qed.

Trakt Add Relation 2 (@eq nat) (Z.eqb) (eqnat_Zeqb_equiv).
```

Next, we need Trakt to consider the addition and zero on `int` as known **symbols**:

```coq
Lemma addz_Zadd_embed_eq : forall (x y : int), Z_of_int (addz x y) = Z.add (Z_of_int x) (Z_of_int y).
Proof. (* ... *) Qed.

Trakt Add Symbol (addz) (Z.add) (addz_Zadd_embed_eq).

Lemma i0_Z0_embed_eq : Z_of_int i0 = Z.add (Z_of_int x) (Z_of_int y).
Proof. (* ... *) Qed.

Trakt Add Symbol (i0) (Z0) (i0_Z0_embed_eq).
```

!> Here, `Z_of_int` and `i0` are fictional and not present in the real MathComp library.
We introduce them for the purpose of the example.

Finally, we need to tell Trakt that Coq conversion must be enabled on the MathComp projections, so that the tool is able to detect the real values hidden behind them.

```coq
Trakt Add Conversion (@GRing.add).
Trakt Add Conversion (@GRing.zero).
Trakt Add Conversion (@GRing.Zmodule.sort).
```

Now that everything is declared, we can run `trakt Z bool` on the goal and obtain the following output:

```coq
forall (f' : Z -> Z), (forall (x : Z), 0 <=? f' x = true) -> forall (x' : Z), f' (x' + 0) =? f' x' = true
```

This new goal has all integers expressed in `Z` and logic expressed in `bool`.
Our proof automation tactic will therefore be able to prove it.