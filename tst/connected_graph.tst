gap> START_TEST("connected_graph.tst");
gap> LoadPackage("digraphs", false);
true
gap> ReadPackage( "certification", "tst/connected_graph_certificate.g");
true
gap> IsConnectedDigraph_Certified := 
> CertifiedFunction( IsConnectedDigraph,
>                    rec( certifunc := connected_graph_certificate) );
<certified <Property "IsConnectedDigraph">>
gap> D := Digraph([ [1,2], [2,3], [3,4], [4,5], [5,6], [6,7], [7,1]]);;
gap> IsConnectedDigraph_Certified(D);
got result true
certifying...
connected!
rec(
  graph := rec(
      adjacencyList := [ [ 1, 2 ], [ 2, 3 ], [ 3, 4 ], [ 4, 5 ], [ 5, 6 ], 
          [ 6, 7 ], [ 1, 7 ] ],
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
