gap> START_TEST("connected_graph.tst");
gap> LoadPackage("digraphs", false);
true
gap> ReadPackage( "certification", "tst/connected_graph_certificate.g");
true
gap> IsConnectedDigraph_Certified := 
> CertifiedFunction( IsConnectedDigraph,
>                    rec( certifunc := connected_graph_certificate) );
<certified <Property "IsConnectedDigraph">>
gap> D := Digraph([ [7,2], [1,3], [2,4], [3,5], [4,6], [5,7], [6,1] ]);
<immutable digraph with 7 vertices, 14 edges>
gap> IsConnectedDigraph_Certified(D);
got result true
certifying...
connected!
rec(
  connectivityCertificate := rec(
      distToRoot := [  ],
      next := [ [ 1, 1 ], [ 2, 1 ], [ 3, 2 ], [ 4, 3 ], [ 5, 6 ], [ 6, 7 ], 
          [ 7, 1 ] ],
      root := 1 ),
  graph := rec(
      adjacencyList := [ [ 2, 7 ], [ 1, 3 ], [ 2, 4 ], [ 3, 5 ], [ 4, 6 ], 
          [ 5, 7 ], [ 1, 6 ] ],
      vertexSize := 7 ) )
true
gap> D := Digraph([[1, 3], [4], [3], []]);;
gap> IsConnectedDigraph_Certified(D);
got result false
certifying...
not connected!
false
gap> STOP_TEST("connected_graph.tst");

#############################################################################
##
#E
