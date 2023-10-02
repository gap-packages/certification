gap> START_TEST("connected_graph.tst");
gap> LoadPackage("digraphs", false);
true
gap> ReadPackage( "certification", "tst/connected_graph_certificate.g");
true
gap> IsConnectedDigraph_Certified := 
> CertifiedFunction( IsConnectedDigraph,
>                    rec( certifunc := connected_graph_certificate) );
<certified <Property "IsConnectedDigraph">>
gap> D := Digraph([[2], [3], []]);;
gap> IsConnectedDigraph_Certified(D);
true
gap> D := Digraph([[1, 3], [4], [3], []]);;
gap> IsConnectedDigraph_Certified(D);
false
gap> STOP_TEST("connected_graph.tst");

#############################################################################
##
#E
