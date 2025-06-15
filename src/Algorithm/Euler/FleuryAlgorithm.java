package Algorithm.Euler;
import Algorithm.Graph;
import java.util.*;

public class FleuryAlgorithm {
    public final Graph workingGraph;
    private final Map<String, List<String>> adj;
    private final Map<String, Integer> edgeCounts;
    private int totalEdges;


    //@ requires graph != null;
    //@ ensures workingGraph != null && totalEdges >= 0;
    public FleuryAlgorithm(Graph graph) {
        this.workingGraph = graph.clone();
        this.adj = new HashMap<String, List<String>>();
        for (String vertex : workingGraph.getVertices()) {
            adj.put(vertex, new ArrayList<String>(workingGraph.getAdjacentVertices(vertex)));
        }
        this.edgeCounts = new HashMap<String, Integer>();
        this.totalEdges = calculateEdges();
    }

    //@ ensures \result == (\sum String v; edgeCounts.containsKey(v); edgeCounts.get(v)) / 2;
    private int calculateEdges() {
        int count = 0;
        for (Map.Entry<String, List<String>> entry : adj.entrySet()) {
            edgeCounts.put(entry.getKey(), entry.getValue().size());
            count += entry.getValue().size();
        }
        return count / 2;
    }

    //@ requires u != null && v != null;
    //@ requires adj.containsKey(u) && adj.containsKey(v);
    //@ ensures edgeCounts.get(u) == \old(edgeCounts.get(u)) - 1;
    //@ ensures edgeCounts.get(v) == \old(edgeCounts.get(v)) - 1;
    //@ ensures totalEdges == \old(totalEdges) - 1;
    private void removeEdge(String u, String v) {
        adj.get(u).remove(v);
        adj.get(v).remove(u);
        edgeCounts.put(u, edgeCounts.get(u) - 1);
        edgeCounts.put(v, edgeCounts.get(v) - 1);
        totalEdges--;
    }

    //@ requires u != null && v != null;
    //@ requires adj.containsKey(u) && adj.containsKey(v);
    //@ requires adj.get(u).contains(v);
    //@ ensures \result == (countReachableVertices(u, new HashSet<String>()) != \old(countReachableVertices(u, new HashSet<String>())));
    private boolean isBridge(String u, String v) {
        if (adj.get(u).size() == 1) {
            return false;
        }

        removeEdge(u, v);
        Set<String> visited = new HashSet<String>();
        int countBefore = countReachableVerticesIterative(u);
        adj.get(u).add(v);
        adj.get(v).add(u);
        edgeCounts.put(u, edgeCounts.get(u) + 1);
        edgeCounts.put(v, edgeCounts.get(v) + 1);
        totalEdges++;

        visited = new HashSet<String>();
        int countAfter = countReachableVerticesIterative(u);

        return countBefore != countAfter;
    }

    //@ requires start != null && visited != null;
    //@ ensures \result >= 1;
    private int countReachableVerticesIterative(String start) {
        Set<String> visited = new HashSet<>();
        Deque<String> stack = new ArrayDeque<>();
        stack.push(start);
        int count = 0;

        while (!stack.isEmpty()) {
            String vertex = stack.pop();
            if (!visited.contains(vertex)) {
                visited.add(vertex);
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

    //@ ensures workingGraph.hasEulerianCycle() && totalEdges > 0 ==> !\result.isEmpty() && \result.get(0).equals(\result.get(\result.size()-1));
    //@ ensures !workingGraph.hasEulerianCycle() ==> \result.isEmpty();
    public List<String> findEulerianCycle() {
        List<String> cycle = new ArrayList<String>();

        if (!workingGraph.hasEulerianCycle()) {
            return cycle;
        }

        if (totalEdges == 0) {
            return cycle;
        }

        Stack<String> stack = new Stack<String>();
        String startVertex = adj.keySet().iterator().next();
        stack.push(startVertex);

        while (!stack.isEmpty()) {
            String current = stack.peek();

            if (edgeCounts.get(current) > 0) {
                String nextVertex = null;
                boolean foundNonBridge = false;

                for (String neighbor : adj.get(current)) {
                    if (!isBridge(current, neighbor)) {
                        nextVertex = neighbor;
                        foundNonBridge = true;
                        break;
                    }
                }

                if (!foundNonBridge) {
                    nextVertex = adj.get(current).get(0);
                }

                stack.push(nextVertex);
                removeEdge(current, nextVertex);
            } else {
                cycle.add(stack.pop());
            }
        }

        if (!cycle.isEmpty() && cycle.get(0).equals(cycle.get(cycle.size()-1)) && totalEdges == 0) {
            Collections.reverse(cycle);
            return cycle;
        }

        return new ArrayList<String>();
    }
}