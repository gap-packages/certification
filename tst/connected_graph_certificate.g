Graph2Lean:=function(g)
return rec( vertexSize := DigraphNrVertices(g),
         adjacencyList := AsGraph(g).adjacencies );
end;

ConnectivityCertificate2Lean:=function(g)
return rec( );
end;

connected_graph_certificate := function( is_connected, g )
local cr;
if is_connected then
  Print("connected!\n");
  cr := rec( graph := Graph2Lean(g),
             connectivityCertificate := ConnectivityCertificate2Lean(g) );
  Print(cr,"\n");  
else
  Print("not connected!\n");
fi;
end;