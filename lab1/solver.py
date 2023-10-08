from z3 import *

def main():
    # Открываем файл с расширением .smt2
    with open("smt.smt2", "r") as smt2_file:
        smt2_content = smt2_file.read()

    # Создаем контекст Z3
    solver = Solver()

    # Загружаем содержимое SMT2 файла в контекст Z3 и решаем его
    solver.from_string(smt2_content)

    with open("out.txt", "w") as file:
        # Проверяем, можно ли найти модель (решение)
        if solver.check() == sat:
            model = solver.model()
            file.write("sat\n")
            file.write(str(model))
        else:
            file.write("unsat")


if __name__ == "__main__":
    main()
