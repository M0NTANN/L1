package Algorithm.Hamilton;

import Algorithm.Graph;

import java.util.*;

public class BackTracking {
    private final Graph workingGraph;
    private final List<String> path;
    private final Set<String> visited;
    private boolean cycleFound;

    public BackTracking(Graph graph) {
        this.workingGraph = graph.clone();
        this.path = new ArrayList<>();
        this.visited = new HashSet<>();
        this.cycleFound = false;
    }

    public List<String> findHamiltonianCycle() {
        if (workingGraph.getVertices().isEmpty()) {
            return Collections.emptyList();
        }

        // Начинаем с первой вершины
        String startVertex = workingGraph.getVertices().get(0);
        path.add(startVertex);
        visited.add(startVertex);

        solve(startVertex);

        return cycleFound ? path : Collections.emptyList();
    }

    private void solve(String currentVertex) {
        // Если уже нашли цикл, прекращаем поиск
        if (cycleFound) {
            return;
        }

        // Базовый случай: все вершины посещены
        if (path.size() == workingGraph.getVertexCount()) {
            // Проверяем есть ли ребро обратно в начальную вершину
            if (workingGraph.getAdjacentVertices(currentVertex).contains(path.get(0))) {
                path.add(path.get(0)); // Замыкаем цикл
                cycleFound = true;
            }
            return;
        }

        // Перебираем всех соседей текущей вершины
        for (String neighbor : workingGraph.getAdjacentVertices(currentVertex)) {
            if (!cycleFound && !visited.contains(neighbor)) {
                // Делаем шаг
                path.add(neighbor);
                visited.add(neighbor);

                // Рекурсивный вызов
                solve(neighbor);

                // Если нашли цикл, прекращаем поиск
                if (cycleFound) {
                    return;
                }

                // Откат
                path.remove(path.size() - 1);
                visited.remove(neighbor);
            }
        }
    }

}
