import Algorithm.Graph;
import Algorithm.Euler.FleuryAlgorithm;
import Algorithm.Euler.HierholzerAlgorithm;
import Algorithm.Hamilton.BackTracking;
import javafx.application.Application;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Stage;

import java.util.List;
import java.util.stream.Collectors;

public class GraphAlgorithmsApp extends Application {
    private Graph graph = new Graph();
    private TextArea outputArea = new TextArea();

    public static void main(String[] args) {
        launch(args);
    }

    @Override
    public void start(Stage primaryStage) {
        primaryStage.setTitle("Алгоритмы поиска циклов в графе");

        // Создаем вкладки
        TabPane tabPane = new TabPane();

        // Вкладка для добавления вершин
        Tab addVertexTab = new Tab("Добавление ребер", createAddEdgeTab());
        addVertexTab.setClosable(false);

        // Вкладка для Эйлеровых циклов
        Tab eulerTab = new Tab("Эйлеровы циклы", createEulerTab());
        eulerTab.setClosable(false);

        // Вкладка для Гамильтоновых циклов
        Tab hamiltonTab = new Tab("Гамильтоновы циклы", createHamiltonTab());
        hamiltonTab.setClosable(false);

        tabPane.getTabs().addAll(addVertexTab, eulerTab, hamiltonTab);

        // Область вывода результатов
        outputArea.setEditable(false);
        outputArea.setWrapText(true);
        outputArea.setPrefHeight(150);

        // Основной layout
        VBox mainLayout = new VBox(10);
        mainLayout.setPadding(new Insets(10));
        mainLayout.getChildren().addAll(tabPane, outputArea);

        primaryStage.setScene(new Scene(mainLayout, 600, 500));
        primaryStage.show();
    }

    private VBox createAddEdgeTab() {
        TextField vertex1Field = new TextField();
        TextField vertex2Field = new TextField();

        Button addButton = new Button("Добавить ребро");
        addButton.setOnAction(e -> {
            String u = vertex1Field.getText().trim();
            String v = vertex2Field.getText().trim();

            if (!u.isEmpty() && !v.isEmpty()) {
                graph.addEdge(u, v);
                outputArea.appendText("Добавлено ребро: " + u + " - " + v + "\n");
                vertex1Field.clear();
                vertex2Field.clear();
            } else {
                showAlert("Ошибка", "Введите обе вершины");
            }
        });

        Button generateButton = new Button("Сгенерировать большой граф (80k вершин)");
        generateButton.setOnAction(e -> {
            outputArea.appendText("Начало генерации большого графа...\n");
            new Thread(() -> {
                for (int i = 0; i <= 80000; i++) {
                    int last = i + 1;
                    if (last == 80001) last = 0;
                    graph.addEdge(Integer.toString(i), Integer.toString(last));
                }
                javafx.application.Platform.runLater(() ->
                        outputArea.appendText("Граф сгенерирован (80001 вершина в цикле)\n"));
            }).start();
        });

        VBox layout = new VBox(10);
        layout.setPadding(new Insets(10));
        layout.getChildren().addAll(
                new Label("Вершина 1:"), vertex1Field,
                new Label("Вершина 2:"), vertex2Field,
                addButton, generateButton
        );

        return layout;
    }

    private VBox createEulerTab() {
        ToggleGroup algorithmGroup = new ToggleGroup();

        RadioButton fleuryButton = new RadioButton("Алгоритм Флёри");
        fleuryButton.setToggleGroup(algorithmGroup);
        fleuryButton.setSelected(true);

        RadioButton hierholzerButton = new RadioButton("Алгоритм Хирхольцера");
        hierholzerButton.setToggleGroup(algorithmGroup);

        Button findButton = new Button("Найти Эйлеров цикл");
        findButton.setOnAction(e -> {
            new Thread(() -> {
                List<String> eulerPath;
                if (fleuryButton.isSelected()) {
                    outputArea.appendText("Запуск алгоритма Флёри...\n");
                    eulerPath = new FleuryAlgorithm(graph).findEulerianCycle();
                } else {
                    outputArea.appendText("Запуск алгоритма Хирхольцера...\n");
                    eulerPath = new HierholzerAlgorithm(graph).findEulerianCycle();
                }

                javafx.application.Platform.runLater(() -> {
                    if (eulerPath.isEmpty()) {
                        outputArea.appendText("Эйлеров цикл не существует\n");
                    } else {
                        outputArea.appendText("Эйлеров цикл: " +
                                String.join(" -> ", eulerPath) + "\n");
                    }
                });
            }).start();
        });

        VBox layout = new VBox(10);
        layout.setPadding(new Insets(10));
        layout.getChildren().addAll(
                new Label("Выберите алгоритм:"),
                fleuryButton, hierholzerButton,
                findButton
        );

        return layout;
    }

    private VBox createHamiltonTab() {
        Button findButton = new Button("Найти Гамильтонов цикл");
        findButton.setOnAction(e -> {
            new Thread(() -> {
                outputArea.appendText("Поиск Гамильтоновых циклов (метод перебора)...\n");
                BackTracking hcb = new BackTracking(graph);
                List<String> cycles = hcb.findHamiltonianCycle();

                javafx.application.Platform.runLater(() -> {
                    if (cycles.isEmpty()) {
                        outputArea.appendText("Гамильтоновы циклы не найдены\n");
                    } else {
                        outputArea.appendText("Найден Гамильтонов цикл: " +
                                cycles.stream()
                                        .map(Object::toString)
                                        .collect(Collectors.joining(" -> ")) + "\n");
                    }
                });
            }).start();
        });

        VBox layout = new VBox(10);
        layout.setPadding(new Insets(10));
        layout.getChildren().addAll(
                new Label("Алгоритм перебора с возвратом:"),
                findButton
        );

        return layout;
    }

    private void showAlert(String title, String message) {
        Alert alert = new Alert(Alert.AlertType.WARNING);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message);
        alert.showAndWait();
    }
}