gap> START_TEST("connected_graph.tst");
gap> LoadPackage("digraphs", false);
true
gap> ReadPackage( "certification", "tst/connected_graph_certificate.g");
true
gap> IsConnectedDigraph_Certified;
<certified <Property "IsConnectedDigraph">>
gap> D := Digraph([ [7,2], [1,3], [2,4], [3,5], [4,6], [5,7], [6,1] ]);
<immutable digraph with 7 vertices, 14 edges>
gap> res := IsConnectedDigraph_Certified(D);
[ true, 
  rec( 
      connectivityCertificate := 
        rec( 
          distToRoot := [ [ 0, 0 ], [ 1, 1 ], [ 2, 2 ], [ 3, 3 ], [ 4, 3 ], 
              [ 5, 2 ], [ 6, 1 ] ], 
          next := [ [ 0, 0 ], [ 1, 0 ], [ 2, 1 ], [ 3, 2 ], [ 4, 5 ], 
              [ 5, 6 ], [ 6, 0 ] ], root := 0 ), 
      graph := 
        rec( 
          edges := [ [ 0, 1 ], [ 0, 6 ], [ 1, 2 ], [ 2, 3 ], [ 3, 4 ], 
              [ 4, 5 ], [ 5, 6 ] ], vertexSize := 7 ) ) ]
gap> D := Digraph([[2], [1], []]);;
gap> res := IsConnectedDigraph_Certified(D);
[ false, 
  rec( graph := rec( edges := [ [ 0, 1 ] ], vertexSize := 3 ), 
      nonconnectivityCertificate := 
        rec( color := [ [ 0, 0 ], [ 1, 0 ], [ 2, 1 ] ], vertex0 := 0, 
          vertex1 := 2 ) ) ]
gap> STOP_TEST("connected_graph.tst");

#############################################################################
##
#E
