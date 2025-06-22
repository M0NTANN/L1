package main.java.org.example.Appl.Algorithm.Euler;

import main.java.org.example.Appl.Algorithm.CycleSolver;
import main.java.org.example.Appl.Algorithm.Graph;
import java.util.*;

public class HierholzerAlgorithm implements CycleSolver {
    private final Graph workingGraph;
    private int remainingEdges;
    private final Map<String, Integer> edgeCounts;


    //@ requires graph != null;
    //@ ensures workingGraph != null && remainingEdges >= 0;
    public HierholzerAlgorithm(Graph graph) {
        this.workingGraph = graph.clone();
        this.edgeCounts = new HashMap<>();
        this.remainingEdges = calculateEdges();
    }

    //@ ensures \result == (\sum String v; edgeCounts.containsKey(v); edgeCounts.get(v)) / 2;
    private int calculateEdges() {
        int count = 0;
        for (String vertex : workingGraph.getVertices()) {
            int degree = workingGraph.getAdjacentVertices(vertex).size();
            edgeCounts.put(vertex, degree);
            count += degree;
        }
        return count / 2;
    }

    //@ requires u != null && v != null;
    //@ requires workingGraph.getAdjacentVertices(u).contains(v);
    //@ ensures edgeCounts.get(u) == \old(edgeCounts.get(u)) - 1;
    //@ ensures edgeCounts.get(v) == \old(edgeCounts.get(v)) - 1;
    //@ ensures remainingEdges == \old(remainingEdges) - 1;
    private void removeEdge(String u, String v) {
        workingGraph.removeEdge(u, v);
        edgeCounts.put(u, edgeCounts.get(u) - 1);
        edgeCounts.put(v, edgeCounts.get(v) - 1);
        remainingEdges--;
    }

    //@ ensures workingGraph.hasEulerianCycle() && remainingEdges > 0 ==>
    //@         !\result.isEmpty() && \result.get(0).equals(\result.get(\result.size()-1));
    //@ ensures !workingGraph.hasEulerianCycle() ==> \result.isEmpty();
    @Override
    public List<String> findCycle() {
        List<String> cycle = new ArrayList<>();

        if (workingGraph.hasEulerianCycle()) {
            return cycle;
        }

        Stack<String> stack = new Stack<>();
        List<String> path = new ArrayList<>();
        String startVertex = workingGraph.getVertices().getFirst();
        stack.push(startVertex);

        while (!stack.isEmpty()) {
            String current = stack.peek();
            List<String> neighbors = workingGraph.getAdjacentVertices(current);

            if (!neighbors.isEmpty()) {
                String next = neighbors.getFirst();
                stack.push(next);
                removeEdge(current, next);
            } else {
                path.add(stack.pop());
            }
        }

        if (path.isEmpty() || !path.getFirst().equals(path.getLast()) || remainingEdges != 0) {
            return new ArrayList<>();
        }

        Collections.reverse(path);
        return path;
    }
}