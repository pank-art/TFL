#!/bin/bash

python "main.py"
python "solver.py"

# Проверяем код завершения
if [ $? -eq 0 ]; then
  echo "Программа успешно выполнена."
else
  echo "Произошла ошибка при выполнении программы."
fi

# Добавьте команду read, чтобы окно не закрылось сразу
# shellcheck disable=SC2162
read -p "Нажмите Enter, чтобы завершить..."