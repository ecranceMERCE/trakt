# Presentation

Automation tactics in [Coq](https://coq.inria.fr/) are usually tailored for specific subsets of goals.
Yet, when designing their proof statements, Coq users can choose from a range of different inductive types with advantages and drawbacks (computational efficiency, ease of proof, etc).
This variability can lead to a situation where the tactic the user would like to use to prove a goal cannot understand this goal, because the types at use are not recognised by this tactic.
However, if the goal falls into the scope of this tactic, the goal can be proven equivalent to a **converged** one, _i.e._ expressing values in the types that are said to be recognised in the input specification of the tactic.
This also applies to logic, as some tactics may prefer an input in `Prop` and others in `bool`.

**Trakt** is a plugin made to solve this problem by automatically preprocessing goals into their converged version, before the user hands them to an automation tactic.
It draws inspiration from the [`zify`](https://coq.inria.fr/refman/addendum/micromega.html#zify-pre-processing-of-arithmetic-goals) tactic in the Coq standard library.
It exposes Coq commands so that the users can fill a knowledge database to specify which types and values they require to be translated (the approach is similar to the `zify` typeclasses), as well as a tactic to launch the preprocessing, that consists in casting all the possible values in the goal into the given target type, and expressing the logic in the expected logical type.
The `trakt` tactic therefore needs 2 arguments, the target type for the underlying theory (or **target embedding type**), and the **target logical type** (`Prop` or `bool`).

The translation is:
- **certifying**: it leaves no proof obligation to the user;
- **generic**: it is not biased towards an automation tactic in particular;
- **efficient**: it tries to make sparse use of Coq conversion.

Trakt is implemented in [Coq-Elpi](https://github.com/LPCIC/coq-elpi/).
