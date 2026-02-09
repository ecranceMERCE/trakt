# Installation

Trakt is a prototype only available on GitHub for now.
It can be installed by running the following commands in the terminal:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update && opam install coq-trakt
```

Should you prefer experimenting with the latest development version, please install with this command instead:

```bash
opam pin add coq-trakt https://github.com/rocq-trakt/trakt.git
```

Trakt is distributed under the [LGPL-3](https://choosealicense.com/licenses/lgpl-3.0/) license.