package Algorithm;

import Algorithm.Euler.FleuryAlgorithm;
import Algorithm.Euler.HierholzerAlgorithm;
import Algorithm.Hamilton.BackTracking;

import java.util.List;
import java.util.Scanner;
import java.util.stream.Collectors;

public class Interf {

    public static void Inter() {
        Scanner scanner = new Scanner(System.in);
        Graph g = new Graph();

        while (true) {
            System.out.println("1 - добавить вершину\n" +
                    "2 - нахождение Эйлерова цикла\n" +
                    "3 - нахождение Гамильтонова цикла\n" +
                    "4 - закрыть\n\n");
            int option = scanner.nextInt();
            scanner.nextLine();

            switch (option) {
                case 1:
                    System.out.println("Введите первую вершину ребра: ");
                    String u = scanner.nextLine();
                    System.out.println("Введите вторую вершину ребра: ");
                    String v = scanner.nextLine();
                    g.addEdge(u, v);
                    break;

                case 2:
                    System.out.println("1 - Алгоритм Флёри\n" +
                            "2 - Алгоритм Хирхольцера\n\n");
                    int option2 = scanner.nextInt();
                    scanner.nextLine();

                    List<String> eulerPath;
                    switch (option2) {
                        case 1:
                            eulerPath = new FleuryAlgorithm(g).findEulerianCycle();
                            break;
                        case 2:
                            eulerPath = new HierholzerAlgorithm(g).findEulerianCycle();
                            break;
                        default:
                            System.out.println("Неверный выбор");
                            continue;
                    }

                    if (eulerPath.isEmpty()) {
                        System.out.println("Эйлеров цикл не существует");
                    } else {
                        System.out.println("Эйлеров цикл: " +
                                eulerPath.stream()
                                        .collect(Collectors.joining(" -> ")));
                    }
                    break;

                case 3:
                    // Ищем гамильтоновы циклы
                    BackTracking hcb = new BackTracking(g);
                    List<String> cycles = hcb.findHamiltonianCycle();

                    // Выводим результат
                    if (cycles.isEmpty()) {
                        System.out.println("Гамильтоновы циклы не найдены");
                    } else {
                        System.out.println("Найдены гамильтоновы циклы: " +
                                cycles.stream()
                                        .map(Object::toString)
                                        .collect(Collectors.joining(" -> ")));
                    }
                    break;

                case 4:
                    return;
                default:
                    System.out.println("Неверный выбор");
            }
        }
    }
}