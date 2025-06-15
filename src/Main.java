import Algorithm.Graph;
import Algorithm.Euler.FleuryAlgorithm;
import Algorithm.Euler.HierholzerAlgorithm;
import Algorithm.Hamilton.BackTracking;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Insets;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.control.Label;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

import java.util.List;
import java.util.Scanner;
import java.util.stream.Collectors;

import static javafx.application.Application.launch;

public class Main {


    public static void main(String[] args) {
        // Запуск JavaFX приложения
        GraphAlgorithmsApp.launch(GraphAlgorithmsApp.class, args);
    }
}