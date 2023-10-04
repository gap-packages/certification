# Wrapped version of `IsConnectedDigraph` to produce certificate
#
LoadPackage("digraphs");
LoadPackage("certification");


# Graph is given by the number of vertices and the list of edges 
Graph2Lean:=function(g)
local edges_from_zero, x, i;
# Digraphs vertices are numbered from 1, but we need from 0
edges_from_zero := List( DigraphEdges(g), x -> List(x, i -> i-1) );
return rec( vertexSize := DigraphNrVertices(g),
                 # Erase arrows: sort each edge and remove duplicates
                 # Return sorted list of edges
                 edges := Set(List(edges_from_zero, SortedList)));
end;


# For a connected graph, the certificate is its rooted spanning tree
ConnectivityCertificate2Lean:=function(g)
local root, reverse_spanning_tree, next, i, distToRoot;
root := 1; # Just pick the first vertex as a root

# Reverse the edges to trace paths from each vertex to the root
reverse_spanning_tree := DigraphReverse( DigraphShortestPathSpanningTree(g, root));

# The mapping from vertices to vertices, which maps each vertex to the next
# vertex on the path to the root. Use `ShallowCopy` to modify in-place.
# Shift to number vertices from zero.
next := ShallowCopy(OutNeighbours(reverse_spanning_tree));
for i in [1..DigraphNrVertices(g)] do
  if next[i] = [ ] then
    # we have root - it maps to itself
    next[i] := [i-1,i-1];
  else
    next[i] := Concatenation([i-1], next[i]-1);
  fi;
od;

# The mapping from vertices to their distance to the root.
# Shift to number vertices from zero.
distToRoot := [ ];
for i in [1..DigraphNrVertices(g)] do
  if i = root then
    # we have root - the distance is zero
    Add(distToRoot, [i-1,0]);
  else
    Add(distToRoot, [i-1, Length(DigraphShortestPath(reverse_spanning_tree,i,root)[1])-1] );
  fi;
od;

# Assemble the output
return rec( root := root-1,
            next := next,
      distToRoot := distToRoot);

end;


# Put all together into the certification function
connected_graph_certificate := function( is_connected, g )
local cr;
if is_connected then
  cr := rec( graph := Graph2Lean(g),
             connectivityCertificate := ConnectivityCertificate2Lean(g) );
else
  cr := rec( graph := Graph2Lean(g),
             nonconnectivityCertificate := "TO BE IMPLEMENTED" );
fi;
return cr;
end;


# Create a wrapper around IsConnectedDigraph
IsConnectedDigraph_Certified := CertifiedFunction( 
  IsConnectedDigraph,
  rec( certifunc := connected_graph_certificate) );
