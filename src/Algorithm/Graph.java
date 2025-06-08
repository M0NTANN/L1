package Algorithm;

//@ model import java.util.Map<String, List<String>> as StringToListMap;
//@ model import java.util.List<String> as StringList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Collections;
import java.util.Set;
import java.util.HashSet;

public class Graph {
    private Map<String, List<String>> adj;
    private Map<String, Integer> vertexIndices;
    private List<String> vertices;
    private int vertexCount;

    //@ public invariant adj != null;
    //@ public invariant vertexIndices != null;
    //@ public invariant vertices != null;
    //@ public invariant vertexCount >= 0;
    //@ public invariant vertexCount == vertices.size();

    public Graph() {
        adj = new HashMap<String, List<String>>();
        vertexIndices = new HashMap<String, Integer>();
        vertices = new ArrayList<String>();
        vertexCount = 0;
    }

    /*@ requires u != null && v != null;
      @ ensures adj.containsKey(u) && adj.containsKey(v);
      @ ensures \old(!adj.containsKey(u)) ==> vertexCount == \old(vertexCount) + 1;
      @ ensures \old(!adj.containsKey(v)) ==> vertexCount == \old(vertexCount) + 1;
      @ ensures adj.get(u).contains(v) && adj.get(v).contains(u);
      @*/
    public void addEdge(String u, String v) {
        if (u == null || v == null) {
            throw new IllegalArgumentException("Vertex cannot be null");
        }

        adj.putIfAbsent(u, new LinkedList<String>());
        adj.putIfAbsent(v, new LinkedList<String>());

        if (!vertexIndices.containsKey(u)) {
            vertexIndices.put(u, vertexCount++);
            vertices.add(u);
        }
        if (!vertexIndices.containsKey(v)) {
            vertexIndices.put(v, vertexCount++);
            vertices.add(v);
        }

        adj.get(u).add(v);
        adj.get(v).add(u);
    }

    public void removeEdge(String u, String v) {
        if (adj.containsKey(u) && adj.containsKey(v)) {
            adj.get(u).remove(v);
            adj.get(v).remove(u);
        }
    }

    public List<String> getAdjacentVertices(String vertex) {
        return adj.getOrDefault(vertex, Collections.emptyList());
    }

    public Graph clone() {
        Graph clone = new Graph();
        for (Map.Entry<String, List<String>> entry : adj.entrySet()) {
            clone.adj.put(entry.getKey(), new LinkedList<>(entry.getValue()));
        }
        clone.vertexIndices = new HashMap<>(vertexIndices);
        clone.vertices = new ArrayList<>(vertices);
        clone.vertexCount = vertexCount;
        return clone;
    }

    public int getVertexCount() {
        return vertexCount;
    }

    public List<String> getVertices() {
        return new ArrayList<>(vertices);
    }

    public boolean hasEulerianCycle() {
        for (List<String> neighbors : adj.values()) {
            if (neighbors.size() % 2 != 0) {
                return false;
            }
        }
        return vertexCount > 0;
    }
}