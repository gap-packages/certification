connected_graph_certificate := function( is_connected, g )
local cr;
if is_connected then
  Print("connected!\n");
  cr := rec( 
    graph := rec( 
      vertexSize := DigraphNrVertices(g),
      adjacencyList := AsGraph(g).adjacencies ));
  Print(cr,"\n");  
else
  Print("not connected!\n");
fi;
end;