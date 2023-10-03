[![CI](https://github.com/gap-packages/certification/actions/workflows/CI.yml/badge.svg)](https://github.com/gap-packages/certification/actions/workflows/CI.yml)
[![Code Coverage](https://codecov.io/github/gap-packages/certification/coverage.svg?branch=main&token=)](https://codecov.io/gh/gap-packages/certification)
[![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/gap-packages/certification/HEAD)

# certification
Certificates for theorem provers

## JSON exchange format

This section describes the JSON format for exporting & importing graphs.

### Maps

A naive way to represent a map `{x_1 ↦ y_1, ..., x_n ↦ y_n}` is to use a an associative list `[(x_1, y_1), ..., (x_n,
y_n)]`. This is inefficient but simple. We may later switch to something better, such as balanced search trees.

### Simple undirected graph

The format is as follows:
```
{
    "graph": {
        "vertexSize": ⟨number-of-vertices⟩,
        "edges" : ⟨edges-list⟩
    },
    "certificate1" : ⋯,
    "certificate2" : ⋯,
    ⋯
}
```
The vertices are numbers from `0` to `⟨number-of-vertices⟩` (excluded). An adjancency list is a list of lists of
integers. The `n`-th list is the list of vertices of vertex `x_n`.

### Connectivity witness

A connectivity certificate is as follows:
```
"connectivityCertificate": {
    "root": ⟨root⟩,
    "next": ⟨next-map⟩,
    "distToRoot": ⟨dist-map⟩
}
```
The above information encodes a rooted spanning tree. One of the vertices is designated as the root.
The `next` field is a map from vertices to vertices, which takes each vertex to the next vertex on the
(unique) path to the root. The root must map to itself. The `distToRoot` maps each vertex to the distance
to the root.


#### Example: The cycle on 7 vertices

```
{
    "graph": {
        "vertexSize": 7,
        "edges" : [ [ 1, 2 ], [ 1, 7 ], [ 2, 3 ], [ 3, 4 ], [ 4, 5 ], [ 5, 6 ], [ 6, 7 ] ]
    },
    "connectivityCertificate": {
        "root": 6,
        "next": [ [0, 6], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6], [6, 6] ],
        "distToRoot": [ [1, 1], [1, 5], [2, 4], [3, 3], [4, 2], [5, 1], [6, 0] ]
    }
}
```
