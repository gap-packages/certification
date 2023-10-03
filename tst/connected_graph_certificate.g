Graph2Lean:=function(g)
local edges_from_zero, x, i;
edges_from_zero := List( DigraphEdges(g), x -> List(x, i -> i-1) );
return rec( vertexSize := DigraphNrVertices(g),
                 edges := Set(List(edges_from_zero,SortedList)));
end;

ConnectivityCertificate2Lean:=function(g)
local root, reverse_spanning_tree, next, i, distToRoot;
root := 1;
reverse_spanning_tree := DigraphReverse( DigraphShortestPathSpanningTree(g, root));
next := ShallowCopy(OutNeighbours(reverse_spanning_tree));
for i in [1..DigraphNrVertices(g)] do
  if next[i] = [ ] then
    # we have root
    next[i] := [i-1,i-1];
  else
    next[i] := Concatenation([i-1], next[i]-1);
  fi;
od;
distToRoot := [ ];
for i in [1..DigraphNrVertices(g)] do
  if i = root then
    Add(distToRoot, [i-1,0]);
  else
    Add(distToRoot, [i-1, Length(DigraphShortestPath(reverse_spanning_tree,i,root)[1])-1] );
  fi;
od;
return rec( root := root-1,
            next := next,
      distToRoot := distToRoot);
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