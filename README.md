[![CI](https://github.com/gap-packages/certification/actions/workflows/CI.yml/badge.svg)](https://github.com/gap-packages/certification/actions/workflows/CI.yml)
[![Code Coverage](https://codecov.io/github/gap-packages/certification/coverage.svg?branch=main&token=)](https://codecov.io/gh/gap-packages/certification)
[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/gap-packages/certification/HEAD)

# certification

This GAP package shows how one can transfer mathematical objects from GAP to the Lean 4 proof assistant, so that
the proof assistant formally verifies the mathematical objects and its properties. At present it is
just a proof of concept supporting transfer of simple graphs, together with certificates for their connectedness
or disconnectedness. The technique can be extended to many other kinds of mathematical objects, as well as to
other computer algebra systems and proof assistants.

The GAP source is organized a standard package. Please consult `[Lean4/README.md](Lean4/README.md)` on how to use
the Lean 4 part of the repository.

To transfer from GAP to Lean 4 a graph `G` and the fact that `G` is connected, we proceed as follows:

1. Generate in GAP the graph `G`, as well as a certificate `C` show that `G` is connected.
   (`C` is essentially a spanning tree, see below.)
2. Export `G` and `C` to JSON.
3. Import JSON into Lean 4 to obtain (unverified) data.
4. Reconstruct from the data the (formally verified) graph `G` and a theorem stating that `G` is connected.

The same recipe works for disconnectedness. As a general rule of thumb, computational tasks should be delegated to
the computer algebra system, and formal verification of certificates to the proof assistant.
The GAP package performs the first two steps, and the attached Lean 4 code the last two steps. 

## The JSON format

We use JSON as the format for data exchange, as it can easily be produced in GAP and parsed in Lean 4.
You may wish to look at examples in `[Lean4/examples](./Lean4/examples)` folder and the formalization
in `[Lean4/JSON2Lean/JsonData.lean](./Lean4/JSON2Lean/JsonData.lean)` to clarify the description of
the format given here.

We refer to the contents of a JSON file as “data”, rather than “certificate”, to distinguish such “raw” data
from the formally verified mathematical objects and cerificates.

A JSON file contains data in the following form:
```json
{ "graph" : ⟨graph-data⟩,
  "connectivityData" : ⟨connectivity-data⟩,
  "disconnectivityData" : ⟨disconnectivity-data⟩
}
```
The fields `"connectivity-data"` and `"disconnectivity-data` are both optional. 

### Graph description

The format of `⟨graph-representation⟩` is
```json
{ "vertexSize" : ⟨number⟩,
  "edges" : ⟨list-of-edges⟩
}
```
where `⟨number⟩` is the number of vertices. The vertices are indexed from `0` to `⟨number⟩ - 1`.
An edge from vertex `i` to vertex `j`, where `i < j` is represented as the two-element array `[i,j]`.
Finally, `⟨list-of-edges⟩` is the list of all edges, ordered lexicographically.

The connectivity and disconnectivity data requires representation of finite maps.
The map `x₁ ↦ y₁, …, xᵢ ↦ yᵢ` is represented as an associative array `[[x₁,y₁], …, [xᵢ,yᵢ]]`, where `x₁, …, xᵢ` must be ordered.

### Connectivity data

The `⟨connectivity-data⟩` describes a spanning tree and has the following form:
```json
{ "root" : ⟨vertex⟩,
  "next" : ⟨vertex-to-vertex-map⟩,
  "distToRoot" : ⟨vertex-to-number-map⟩
}
```
The spanning tree so represented is rooted at `root`, the map `next` takes each vertex one step closer to the `root`
(and maps `root` to itself), and `distToRoot` decreases as we move along using `next` (which guarantees that `next`
does not generate any cycles). Please consult the formal specification `ConnectivityCertificate` in
`[JSON2Lean/Connectivity.lean](./JSON2Lean/Connectivity.lean)`.

### Disconnectivity 

The `⟨disconnectivity-data⟩` describes a coloring of vertices by colors `0` and `1`, together with two vertices,
one of each color:
```json
{ "color" : , ⟨vertex-to-0,1-map⟩
  "vertex0" : ⟨vertex-of-color-0⟩,
  "vertex1" : ⟨vertex-of-color-1⟩
}
```
Adjacent vertices must have the same color.

### Indulging the proof assistant

Some of the requirements given above seem unecessary. For example, why insist that maps be given in the order of
ascending keys, when it is easy to sort lists? And why must we explicitly provide `vertex0` and `vertex1` when they
can be found easily by scanning the coloring? The proof assistant is like the princess from
[The Princess and the Pea](https://en.wikipedia.org/wiki/The_Princess_and_the_Pea), it must be pampered.

Specifically, suppose we did not require that maps be given as lists sorted by the keys. In order for the proof assistant
to build an efficient map from the list (say, a balanced search tree) it would have to be able to compare *unverified* keys
(to sort the array, or to build the search tree) in the order of *verified* keys. This sort of mixing of meta-level and
kernel-level is as annoying as a pea.

## Acknowledgement

The present work was initiated at Dagstuhl Seminar 23401 [Automated mathematics: integrating proofs, algorithms and data](https://www.dagstuhl.de/23401)
by [Andrej Bauer](https://www.andrej.com/) and [Olexandr Konovalov](https://olexandr-konovalov.github.io). We thank
[Schloss Dagstuhl - Leibniz Center of Informatics](https://www.dagstuhl.de/) for the support.
