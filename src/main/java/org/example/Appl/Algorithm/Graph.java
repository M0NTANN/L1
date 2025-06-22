package org.example.Appl.Algorithm;

import java.util.*;

public class Graph {
    public Map<String, List<String>> adj;
    private Map<String, Integer> vertexIndices;
    private List<String> vertices;
    private int vertexCount;

    public Graph() {
        adj = new HashMap<>();
        vertexIndices = new HashMap<>();
        vertices = new ArrayList<>();
        vertexCount = 0;
    }

    public void addEdge(String u, String v) {
        if (!adj.containsKey(u)) {
            adj.put(u, new LinkedList<>());
            vertexIndices.put(u, vertexCount++);
            vertices.add(u);
        }
        if (!adj.containsKey(v)) {
            adj.put(v, new LinkedList<>());
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
        return Collections.unmodifiableList(adj.getOrDefault(vertex, Collections.emptyList()));
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
                return true;
            }
        }
        return vertexCount <= 0;
    }
}