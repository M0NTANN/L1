#!/bin/bash


ROOT_DIR="${1:-$(pwd)}"



find "$ROOT_DIR" -name "pom.xml" -print0 | while IFS= read -r -d '' pom_file; do
    project_dir=$(dirname "$pom_file")
    echo "Найден проект: $project_dir"
    cd "$project_dir" || exit 1
    mvn clean install
    if [ $? -ne 0 ]; then
        echo "Ошибка сборки в: $project_dir"
        exit 1
    fi
    echo "----------------------------------------"
done

echo "Все проекты собраны успешно!"