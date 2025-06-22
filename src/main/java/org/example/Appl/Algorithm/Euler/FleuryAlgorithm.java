package org.example.Appl.Algorithm.Euler;

import org.example.Appl.Algorithm.CycleSolver;
import org.example.Appl.Algorithm.Graph;

import java.util.*;

public class FleuryAlgorithm implements CycleSolver {
    private final Graph workingGraph;
    private final Map<String, List<String>> adj = new HashMap<>();
    private final Map<String, Integer> edgeCounts = new HashMap<>();
    private int totalEdges;

    public FleuryAlgorithm(Graph graph) {
        this.workingGraph = graph.clone();
        for (String vertex : workingGraph.getVertices()) {
            adj.put(vertex, new ArrayList<>(workingGraph.getAdjacentVertices(vertex)));
        }
        totalEdges = calculateEdges();
    }

    private int calculateEdges() {
        int count = 0;
        for (Map.Entry<String, List<String>> entry : adj.entrySet()) {
            edgeCounts.put(entry.getKey(), entry.getValue().size());
            count += entry.getValue().size();
        }
        return count / 2;
    }

    private void removeEdge(String u, String v) {
        adj.get(u).remove(v);
        adj.get(v).remove(u);
        edgeCounts.put(u, edgeCounts.get(u) - 1);
        edgeCounts.put(v, edgeCounts.get(v) - 1);
        totalEdges--;
    }

    private boolean isBridge(String u, String v) {
        if (adj.get(u).size() == 1) return false;
        removeEdge(u, v);
        int before = countReachableVertices(u);
        adj.get(u).add(v);
        adj.get(v).add(u);
        edgeCounts.put(u, edgeCounts.get(u) + 1);
        edgeCounts.put(v, edgeCounts.get(v) + 1);
        totalEdges++;
        int after = countReachableVertices(u);
        return before != after;
    }

    private int countReachableVertices(String start) {
        Set<String> visited = new HashSet<>();
        Deque<String> stack = new ArrayDeque<>();
        stack.push(start);
        int count = 0;
        while (!stack.isEmpty()) {
            String vertex = stack.pop();
            if (visited.add(vertex)) {
                count++;
                for (String neighbor : adj.get(vertex)) {
                    if (!visited.contains(neighbor)) {
                        stack.push(neighbor);
                    }
                }
            }
        }
        return count;
    }

    @Override
    public List<String> findCycle() {
        List<String> cycle = new ArrayList<>();
        if (!workingGraph.hasEulerianCycle()) return cycle;

        Stack<String> stack = new Stack<>();
        String startVertex = adj.keySet().iterator().next();
        stack.push(startVertex);

        while (!stack.isEmpty()) {
            String current = stack.peek();
            if (edgeCounts.get(current) > 0) {
                String next = null;
                for (String neighbor : new ArrayList<>(adj.get(current))) {
                    if (!isBridge(current, neighbor)) {
                        next = neighbor;
                        break;
                    }
                }
                if (next == null) next = adj.get(current).get(0);
                stack.push(next);
                removeEdge(current, next);
            } else {
                cycle.add(stack.pop());
            }
        }

        Collections.reverse(cycle);
        return cycle;
    }
}
