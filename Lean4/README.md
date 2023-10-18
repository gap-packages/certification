# Lean 4 interface

This folder contains [Lean](https://leanprover-community.github.io) code that imports JSON certificates
for formally verified mathematical objects. Such certificates can be generated easily by Computer Algebra
Systems and other tools equipped with abilities to perform computations on mathematical objects.

The code presented here is a proof of concept, whose purpose is to lay out basic design principle.
It implements simple graphs with certificates for connectedness and disconnectedness.

## Installation

Install Lean 4 by following [these instructions](https://leanprover-community.github.io/get_started.html). 
When successful, you should have the exectables `elan` (for installing and updating versions of Lean), `lean` itself, and `lake` (the Lean build system).

## Usage

Before compiling and using the package, run these commands in the present folder:

* `elan update` to make sure you have an up-to-date version of Lean
* `lake exe cache get` to get a cached version of Mathlib (or else wait for it to compile)

Lean 4 is best used in interactive mode using the [Visual Studio Code](https://code.visualstudio.com) editor, please consult the Lean documentation.
Once you set it up, simply open the file [`Examples.lean`](Examples.lean), which should trigger compilation.

Alternatively, build the files from the command line:

* `lake build` to compile the Lean files
* `lake clean` to remove the compiled Lean files

## Code organization

The code is organized as follows:

* [`JSON2Lean.Graph`](./JSON2Lean/Graph.lean), [`JSON2Lean.Graph`](./JSON2Lean/Edge.lean), and [`JSON2Lean.Graph`](./JSON2Lean/Connetivity.lean): a bit of graph theory.
* [`JSON2Lean.SetTree`](./JSON2Lean/SetTree.lean) and [`JSON2Lean.MapTree`](./JSON2Lean/MapTree.lean):
  finite sets and maps implemented as binary search trees.
* [`JSON2Lean.JsonData`](./JSON2Lean/JsonData.lean) parsing and loading of raw JSON data.
* [`JSON2Lean.Certificate`](./JSON2Lean/Certificate.lean) generation of *quoted* Lean 4 objects from raw data.
* [`JSON2Lean.LoadGraph`](./JSON2Lean/LoadGraph.lean) top-level `load_graph` command that ties all the parts together: load JSON from a file, convert it to raw data, generate quoted Lean objects and submit them to the kernel, install instancess that witness connectedness and disconnectedness.
