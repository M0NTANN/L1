import Algorithm.*;
import Algorithm.Euler.FleuryAlgorithm;
import Algorithm.Euler.HierholzerAlgorithm;
import Algorithm.Hamilton.BackTracking;

import java.util.List;
import java.util.Scanner;
import java.util.stream.Collectors;

public class Main {
    public static void main(String[] args){
        Scanner scanner = new Scanner(System.in);


        Graph g = new Graph();

        while (true) {
            System.out.println("" +
                    "1 - добавить вершину \n" +
                    "2 - нахождение Эйлерова цикла \n" +
                    "3 - нахождение Гамильтонова цикла \n" +
                    "4 - закрыть \n\n");
            int option = scanner.nextInt();
            scanner.nextLine();

            switch (option) {
                case 1: // кейс с вводом содержимого n строк
                    //System.out.println("Введите первую вершину ребра: ");
                    //String u = String.valueOf(new Scanner(System.in));
                    //System.out.println("Введите вторую вершину ребра: ");
                    //String v = String.valueOf(new Scanner(System.in));
                    g.addEdge("0", "11");
                    g.addEdge("11", "2");
                    g.addEdge("2", "3");
                    g.addEdge("3", "4");
                    g.addEdge("3", "11");
                    g.addEdge("4", "0");
                    break;

                case 2:  //кейс с выводом содержимого n строк
                    System.out.println("" +
                            "1 - Алгоритм Флёри \n" +
                            "2 - Алгоритм Хирхольцера \n\n");
                    int option2 = scanner.nextInt();
                    scanner.nextLine();

                    switch (option2) {
                        case 1:
                            List<String> eulerPathFleury = new FleuryAlgorithm(g).findEulerianCycle();

                            if (eulerPathFleury.isEmpty()) {
                                System.out.println("Эйлеров цикл не существует");
                            } else {
                                System.out.println("Эйлеров цикл: " +
                                        eulerPathFleury.stream()
                                                .map(Object::toString)
                                                .collect(Collectors.joining(" -> ")));
                            }
                            System.out.println("\n\n");
                            break;


                        case 2:  //кейс с выводом содержимого n строк
                            List<String> eulerPathHier  = new HierholzerAlgorithm(g).findEulerianCycle();
                            if (eulerPathHier.isEmpty()) {
                                System.out.println("Эйлеров цикл не существует");
                            } else {
                                System.out.println("Эйлеров цикл: " +
                                        eulerPathHier.stream()
                                                .map(Object::toString)
                                                .collect(Collectors.joining(" -> ")));
                            }
                            System.out.println("\n\n");
                            break;

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
            }
        }
    }
}