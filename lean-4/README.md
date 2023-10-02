# Lean 4 interface

This folder contains [Lean](https://leanprover-community.github.io) code that imports the certificates
generated by GAP as formally verified mathematical objects.

## Installation

Install Lean 4 by following [these instructions](https://leanprover-community.github.io/get_started.html). 
When successful, you should have the exectables `elan` (for installing and updating versions of Lean), `lean` itself, and `lake` (the Lean build system).

Lean 4 is best used in interactive mode using the Visual Studio Code editor, please consult the Lean documentation.

You may also run in this folder from the command line:

1. `elan update` to make sure you have an up-to-date version of Lean
2. `lake build` or `make build-lean` to compile the Lean files
3. `lake clean` or `make clean-lean` to remove the compiled Lean files