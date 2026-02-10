# Auxiliary tactics

Trakt also comes with some auxiliary tactics.
They were developed as an additional layer to make Trakt compatible with the [SMTCoq](https://smtcoq.github.io/) plugin, but they are available to all the users.

### Preprocessing hypotheses

The `trakt_pose` tactic is available to perform the same work as `trakt`, this time on a **hypothesis** or any previously declared term instead of the goal.
The following call takes a previously declared term `t`, makes types in `t` converge to `A` and expresses logic in `Prop`, adding the output term to the context as `H`.

```coq
trakt_pose A Prop : t as H.
```

### Considering the arrow as a regular logical connector

Trakt treats the arrow as a special logical connector that **remains untouched** in the output goal, in the normal behaviour.
However, some proof automation tactics may require logical implication to be expressed in `bool`, for example with the `implb` term.
To that end, the user can call `trakt_boolify_arrows` after `trakt`.

### Putting a goal back into prenex form

When preprocessing universally quantified terms, Trakt may add conditions right after the quantifiers in the output goal.
This is the case for **partial embeddings** like `nat` to `Z`, where a positivity condition is added after the output quantifier.
Some proof automation tactics require the quantifiers in the goal and hypotheses to be in prenex form.
Unfortunately, if an input hypothesis chains several quantifiers with a partial embedding, the output of Trakt mixes quantifiers and conditions, which breaks the prenex form.
Here is an example:

``` coq
(* before trakt *)
forall (n m : nat), ...
(* after trakt *)
forall (n' : Z), 0 <= n' -> forall (m' : Z), 0 <= m' -> ...
```

The `trakt_reorder_quantifiers` tactic is available to correct this situation if needed.
