connected_graph_certificate := function( is_connected, g )
if is_connected then
  Print("connected!\n");
  cr := rec( 
    graph := rec( 
      vertexSize := DigraphNrVertices(g)));
  Print(cr,"\n");  
  Print(GapToJsonString(cr),"\n");  
else
  Print("not connected!\n");
fi;
end;