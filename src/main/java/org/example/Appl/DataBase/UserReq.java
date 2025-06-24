package org.example.Appl.DataBase;

import java.sql.*;
import java.util.ArrayList;
import java.util.List;

public class UserReq {
    public boolean authenticate(String username, String password) {
        try (Connection conn = DatabaseManager.getConnection();
             PreparedStatement stmt = conn.prepareStatement("SELECT * FROM users WHERE username=? AND password=?")) {
            stmt.setString(1, username);
            stmt.setString(2, password);
            ResultSet rs = stmt.executeQuery();
            return rs.next();
        } catch (SQLException e) {
            e.printStackTrace();
            return false;
        }
    }

    public void saveGraphResult(int userId, String algorithm, String resultPath) {
        try (Connection conn = DatabaseManager.getConnection();
             PreparedStatement stmt = conn.prepareStatement(
                     "INSERT INTO results(user_id, algorithm, result_data) VALUES (?, ?, ?)")) {
            stmt.setInt(1, userId);
            stmt.setString(2, algorithm);
            stmt.setString(3, resultPath);
            stmt.executeUpdate();
        } catch (SQLException e) {
            e.printStackTrace();
        }
    }

    public void registrationUser(String login, String pass) {
        try (Connection conn = DatabaseManager.getConnection();
             PreparedStatement stmt = conn.prepareStatement(
                     "INSERT INTO users (username, password) VALUES (?, ?)")) {
            stmt.setString(1, login);
            stmt.setString(2, pass);
            stmt.executeUpdate();
        } catch (SQLException e) {
            e.printStackTrace();
        }
    }

    public User getUserByUsername(String username) {
        try (Connection conn = DatabaseManager.getConnection();
             PreparedStatement stmt = conn.prepareStatement("SELECT * FROM users WHERE username=?")) {
            stmt.setString(1, username);
            ResultSet rs = stmt.executeQuery();
            if (rs.next()) {
                return new User(rs.getInt("id"), rs.getString("username"), rs.getString("password"));
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return null;
    }

    public List<String> getUserHistory(int userId) {
        List<String> history = new ArrayList<>();
        try (Connection conn = DatabaseManager.getConnection();
             PreparedStatement stmt = conn.prepareStatement("SELECT algorithm, result_data, created_at FROM results WHERE user_id=? ORDER BY created_at DESC")) {
            stmt.setInt(1, userId);
            ResultSet rs = stmt.executeQuery();
            while (rs.next()) {
                String algo = rs.getString("algorithm");
                String data = rs.getString("result_data");
                String time = rs.getString("created_at");
                history.add("[" + time + "] " + algo + ": " + data);
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return history;
    }
}
