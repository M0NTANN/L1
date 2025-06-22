package main.java.org.example.Appl.Algorithm.Hamilton;

import main.java.org.example.Appl.Algorithm.CycleSolver;
import main.java.org.example.Appl.Algorithm.Graph;

import java.util.*;

public class BackTracking implements CycleSolver {
    private final Graph workingGraph;
    private final List<String> path = new ArrayList<>();
    private final Set<String> visited = new HashSet<>();
    private boolean cycleFound = false;

    public BackTracking(Graph graph) {
        this.workingGraph = graph.clone();
    }



    @Override
    public List<String> findCycle() {
        if (workingGraph.getVertices().isEmpty()) return Collections.emptyList();

        String startVertex = workingGraph.getVertices().get(0);
        path.add(startVertex);
        visited.add(startVertex);
        solve(startVertex);

        return cycleFound ? path : Collections.emptyList();
    }

    private void solve(String currentVertex) {
        if (cycleFound) return;

        if (path.size() == workingGraph.getVertexCount()) {
            if (workingGraph.getAdjacentVertices(currentVertex).contains(path.get(0))) {
                path.add(path.get(0));
                cycleFound = true;
            }
            return;
        }

        for (String neighbor : workingGraph.getAdjacentVertices(currentVertex)) {
            if (!visited.contains(neighbor)) {
                path.add(neighbor);
                visited.add(neighbor);
                solve(neighbor);
                if (cycleFound) return;
                path.remove(path.size() - 1);
                visited.remove(neighbor);
            }
        }
    }
}
