package org.example.Appl.Algorithm;

import org.example.Appl.Algorithm.Euler.FleuryAlgorithm;
import org.example.Appl.Algorithm.Euler.HierholzerAlgorithm;
import org.example.Appl.Algorithm.Hamilton.BackTracking;

public class CycleSolverFactory {
    public static CycleSolver createSolver(String type, Graph graph) {
        return switch (type) {
            case "BackTrack" -> new BackTracking(graph);
            case "Fluery" -> new FleuryAlgorithm(graph);
            case "Hierholzer" -> new HierholzerAlgorithm(graph);
            default -> throw new IllegalArgumentException("Unknown solver type: " + type);
        };
    }
}
