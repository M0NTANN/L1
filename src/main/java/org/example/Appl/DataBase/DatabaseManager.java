package org.example.Appl.DataBase;

import java.sql.*;

public class DatabaseManager {
    private static final String URL = "jdbc:mysql://localhost:3306/graphdb";
    private static final String USER = "root";
    private static final String PASSWORD = "rootroot";

    public static Connection getConnection() throws SQLException {
        return DriverManager.getConnection(URL, USER, PASSWORD);
    }
}
