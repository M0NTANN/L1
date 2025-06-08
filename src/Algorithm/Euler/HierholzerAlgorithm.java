package Algorithm.Euler;

import Algorithm.Graph;
import java.util.*;

public class HierholzerAlgorithm {
    private final Graph workingGraph;
    private int remainingEdges;
    private final Map<String, Integer> edgeCounts;

    //@ public invariant workingGraph != null;
    //@ public invariant edgeCounts != null;
    //@ public invariant remainingEdges >= 0;
    //@ public invariant (\forall String v; edgeCounts.containsKey(v); edgeCounts.get(v) >= 0);

    /*@ requires graph != null;
      @ ensures workingGraph != null && remainingEdges >= 0;
      @*/
    public HierholzerAlgorithm(Graph graph) {
        this.workingGraph = graph.clone();
        this.edgeCounts = new HashMap<String, Integer>();
        this.remainingEdges = calculateEdges();
    }

    /*@ ensures \result == (\sum String v; edgeCounts.containsKey(v); edgeCounts.get(v)) / 2;
      @*/
    private int calculateEdges() {
        int count = 0;
        for (String vertex : workingGraph.getVertices()) {
            int degree = workingGraph.getAdjacentVertices(vertex).size();
            edgeCounts.put(vertex, degree);
            count += degree;
        }
        return count / 2;
    }

    /*@ requires u != null && v != null;
      @ requires workingGraph.getAdjacentVertices(u).contains(v);
      @ ensures edgeCounts.get(u) == \old(edgeCounts.get(u)) - 1;
      @ ensures edgeCounts.get(v) == \old(edgeCounts.get(v)) - 1;
      @ ensures remainingEdges == \old(remainingEdges) - 1;
      @*/
    private void removeEdge(String u, String v) {
        workingGraph.removeEdge(u, v);
        edgeCounts.put(u, edgeCounts.get(u) - 1);
        edgeCounts.put(v, edgeCounts.get(v) - 1);
        remainingEdges--;
    }

    /*@ ensures \result != null;
      @ ensures workingGraph.hasEulerianCycle() && remainingEdges > 0 ==>
      @         !\result.isEmpty() && \result.get(0).equals(\result.get(\result.size()-1));
      @ ensures !workingGraph.hasEulerianCycle() ==> \result.isEmpty();
      @*/
    public List<String> findEulerianCycle() {
        List<String> cycle = new ArrayList<String>();

        if (!workingGraph.hasEulerianCycle()) {
            return cycle;
        }

        if (remainingEdges == 0) {
            return cycle;
        }

        Stack<String> stack = new Stack<String>();
        List<String> path = new ArrayList<String>();
        String startVertex = workingGraph.getVertices().get(0);
        stack.push(startVertex);

        while (!stack.isEmpty()) {
            String current = stack.peek();

            if (edgeCounts.get(current) > 0) {
                String next = workingGraph.getAdjacentVertices(current).get(0);
                stack.push(next);
                removeEdge(current, next);
            } else {
                path.add(stack.pop());
            }
        }

        if (path.isEmpty() || !path.get(0).equals(path.get(path.size()-1)) || remainingEdges != 0) {
            return new ArrayList<String>();
        }

        Collections.reverse(path);
        return path;
    }
}