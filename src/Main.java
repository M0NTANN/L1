import Algorithm.Graph;
import Algorithm.Euler.FleuryAlgorithm;
import Algorithm.Euler.HierholzerAlgorithm;
import Algorithm.Hamilton.BackTracking;

import java.util.List;
import java.util.Scanner;
import java.util.stream.Collectors;

public class Main {

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        Graph g = new Graph();

        long startTime;
        long endTime;
        long timeElapsed;


        while (true) {
            System.out.println("""
                    1 - добавить вершину
                    2 - нахождение Эйлерова цикла
                    3 - нахождение Гамильтонова цикла
                    4 - закрыть
                    
                    """);
            int option = scanner.nextInt();
            scanner.nextLine();

            switch (option) {
                case 1:
                    /*
                    System.out.println("Введите первую вершину ребра: ");
                    String u = scanner.nextLine();
                    System.out.println("Введите вторую вершину ребра: ");
                    String v = scanner.nextLine();
                    g.addEdge(u, v);*/
                    for (int i = 0; i<=10; i++){
                        int last = i+1;
                        if (last == 11)
                            last = 0;
                        g.addEdge(Integer.toString(i), Integer.toString(last));
                    }
                    break;

                case 2:
                    System.out.println("""
                            1 - Алгоритм Флёри\
                            
                            2 - Алгоритм Хирхольцера
                            
                            """);
                    int option2 = scanner.nextInt();
                    scanner.nextLine();

                    List<String> eulerPath;
                    switch (option2) {
                        case 1:
                            startTime = System.nanoTime();
                            eulerPath = new FleuryAlgorithm(g).findEulerianCycle();
                            endTime = System.nanoTime();
                            timeElapsed = endTime - startTime;
                            System.out.println(timeElapsed);
                            break;
                        case 2:
                            startTime = System.nanoTime();
                            eulerPath = new HierholzerAlgorithm(g).findEulerianCycle();
                            endTime = System.nanoTime();
                            timeElapsed = endTime - startTime;
                            System.out.println(timeElapsed);
                            break;
                        default:
                            System.out.println("Неверный выбор");
                            continue;
                    }

                    if (eulerPath.isEmpty()) {
                        System.out.println("Эйлеров цикл не существует");
                    } else {
                        System.out.println("Эйлеров цикл: " +
                                String.join(" -> ", eulerPath));
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