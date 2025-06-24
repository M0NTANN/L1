package org.example.Appl;

import com.sun.javafx.scene.layout.region.Margins;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Stage;
import org.example.Appl.Algorithm.Graph;
import org.example.Appl.Algorithm.CycleSolver;
import org.example.Appl.Algorithm.CycleSolverFactory;
import org.example.Appl.DataBase.User;
import org.example.Appl.DataBase.UserReq;

import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

public class GraphAlgorithmsApp extends Application {
    private Graph graph = new Graph();
    private TextArea outputArea = new TextArea();

    private User currentUser;
    private final UserReq userReq = new UserReq();

    private int dd;



    @Override
    public void start(Stage primaryStage) {


        showLoginDialog(primaryStage);

    }

    private void showMainInterface(Stage primaryStage) {
        primaryStage.setTitle("Алгоритмы циклов — пользователь: " + currentUser.getUsername());

        TabPane tabPane = new TabPane();
        tabPane.getTabs().addAll(
                new Tab("Добавление ребер", createAddEdgeTab()),
                new Tab("Эйлеровы циклы", createEulerTab()),
                new Tab("Гамильтоновы циклы", createHamiltonTab()),
                new Tab("История", createHistoryTab())
        );

        for (Tab tab : tabPane.getTabs()) tab.setClosable(false);

        outputArea.setEditable(false);
        outputArea.setWrapText(true);
        outputArea.setPrefHeight(150);

        VBox mainLayout = new VBox(10, tabPane, outputArea);
        mainLayout.setPadding(new Insets(10));

        primaryStage.setScene(new Scene(mainLayout, 600, 500));

    }


    private void showLoginDialog(Stage primaryStage) {


        primaryStage.setTitle("Авторизация");



        TextField usernameField = new TextField();
        PasswordField passwordField = new PasswordField();

        Button loginButton = new Button("Войти");
        Button registrateButton = new Button("Зарегистрироваться");





        usernameField.textProperty().addListener((obs, oldVal, newVal) ->
                loginButton.setDisable(newVal.trim().isEmpty() || passwordField.getText().trim().isEmpty()));
        passwordField.textProperty().addListener((obs, oldVal, newVal) ->
                loginButton.setDisable(usernameField.getText().trim().isEmpty() || newVal.trim().isEmpty()));

        usernameField.textProperty().addListener((obs, oldVal, newVal) ->
                registrateButton.setDisable(newVal.trim().isEmpty() || passwordField.getText().trim().isEmpty()));
        passwordField.textProperty().addListener((obs, oldVal, newVal) ->
                registrateButton.setDisable(usernameField.getText().trim().isEmpty() || newVal.trim().isEmpty()));

        loginButton.setOnAction(e -> {
            User user = new User(0, usernameField.getText(), passwordField.getText());
            if (userReq.authenticate(user.getUsername(), user.getPassword())) {
                currentUser = user;
                currentUser = userReq.getUserByUsername(user.getUsername()); // получить ID
                showMainInterface(primaryStage);
            }
            else {
                showAlert("Ошибка входа", "Неверные данные пользователя");
            }
        });



        registrateButton.setOnAction(e -> {
            User user = new User(0, usernameField.getText(), passwordField.getText());
            userReq.registrationUser(user.getUsername(), user.getPassword());
            usernameField.setText("");
            passwordField.setText("");

        });


        VBox mainLayout = new VBox(10);
        mainLayout.setPadding(new Insets(10));
        mainLayout.getChildren().addAll(
                new Label("Логин:"), usernameField,
                new Label("Пароль:"), passwordField,
                loginButton, registrateButton);

        primaryStage.setScene(new Scene(mainLayout, 210, 210));
        primaryStage.show();

    }





    private VBox createHistoryTab() {
        TextArea historyArea = new TextArea();
        historyArea.setEditable(false);
        historyArea.setWrapText(true);

        Button refreshButton = new Button("Обновить историю");
        refreshButton.setOnAction(e -> {
            List<String> history = userReq.getUserHistory(currentUser.getId());
            historyArea.setText(String.join("\n", history));
        });

        VBox layout = new VBox(10, refreshButton, historyArea);
        layout.setPadding(new Insets(10));
        return layout;
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

        findButton.setOnAction(e->{
            List<String> cycle;
            if (fleuryButton.isSelected()) {
                outputArea.appendText("Запуск алгоритма Флёри...\n");
                String algoType = "Fluery";
                CycleSolver solver = CycleSolverFactory.createSolver(algoType, graph);
                cycle = solver.findCycle();
            } else {
                outputArea.appendText("Запуск алгоритма Хирхольцера...\n");
                String algoType = "Hierholzer";
                CycleSolver solver = CycleSolverFactory.createSolver(algoType, graph);
                cycle = solver.findCycle();
            }

            if (cycle.isEmpty()) {
                outputArea.appendText("Эйлеров цикл не существует\n");
                userReq.saveGraphResult(currentUser.getId(), "Euler", "Эйлеров цикл не существует для");
            } else {
                outputArea.appendText("Эйлеров цикл: " +
                        String.join(" -> ", cycle) + "\n");
                userReq.saveGraphResult(currentUser.getId(), "Euler", String.join(" -> ", cycle));
            }
        });

//        findButton.setOnAction(e -> {
//            new Thread(() -> {
//
//                List<String> cycle;
//
//                if (fleuryButton.isSelected()) {
//                    outputArea.appendText("Запуск алгоритма Флёри...\n");
//                    String algoType = "Fluery";
//                    CycleSolver solver = CycleSolverFactory.createSolver(algoType, graph);
//                    cycle = solver.findCycle();
//                } else {
//                    outputArea.appendText("Запуск алгоритма Хирхольцера...\n");
//                    String algoType = "Hierholzer";
//                    CycleSolver solver = CycleSolverFactory.createSolver(algoType, graph);
//                    cycle = solver.findCycle();
//                }
//
//
//                javafx.application.Platform.runLater(() -> {
//                    if (cycle.isEmpty()) {
//                        outputArea.appendText("Эйлеров цикл не существует\n");
//                        userReq.saveGraphResult(currentUser.getId(), "Euler", String.join(" -> ", cycle));
//                    } else {
//                        outputArea.appendText("Эйлеров цикл: " +
//                                String.join(" -> ", cycle) + "\n");
//                        userReq.saveGraphResult(currentUser.getId(), "Euler", String.join(" -> ", cycle));
//                    }
//                });
//            }).start();
//        });

        VBox layout = new VBox(10);
        layout.setPadding(new Insets(10));
        layout.getChildren().addAll(
                new Label("Выберите алгоритм:"),
                fleuryButton,
                hierholzerButton,
                findButton
        );

        return layout;
    }

    private VBox createHamiltonTab() {
        Button findButton = new Button("Найти Гамильтонов цикл");
        findButton.setOnAction(e -> {
            new Thread(() -> {
                CycleSolver solver = CycleSolverFactory.createSolver("BackTrack", graph);
                List<String> cycles = solver.findCycle();

                javafx.application.Platform.runLater(() -> {
                    if (cycles.isEmpty()) {
                        outputArea.appendText("Гамильтоновы циклы не найдены\n");
                        userReq.saveGraphResult(currentUser.getId(), "Hamilton",  cycles.stream().map(Object::toString).collect(Collectors.joining(" -> ")) + "Гамильтоновы циклы не найдены");

                    } else {
                        outputArea.appendText("Найден Гамильтонов цикл: " +
                                cycles.stream().map(Object::toString).collect(Collectors.joining(" -> ")) + "\n");
                        userReq.saveGraphResult(currentUser.getId(), "Hamilton",  cycles.stream().map(Object::toString).collect(Collectors.joining(" -> ")) );
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