import Lake
open Lake DSL

package «GAP2Lean» {
  srcDir := "src"
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib GAP2Lean where
  roots := #[
    `BoundedOrder,
    `OrdEq,
    `TreeSet,
    `TreeMap,
    `Edge,
    `Graph,
    `Invariant.EdgeSize,
    `Invariant.NeighborhoodMap,
    `Invariant.DegreeMap,
    `Invariant.ConnectedComponents,
    `JsonDecoder
--    `Test,
--    `OneGraph,
--    `Query,
--    `Tactic,
--    `Walk,
--    `Bipartite,
  ]
