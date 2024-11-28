from core.pda import PDA

if __name__ == "__main__":
    file_name = input("Введите имя файла, содержащаго PDA (data/pda.json):  ")
    pda = PDA.import_from_file(file_name)

    w = input("Введите строку для разбора:   ")
    ans = pda.run(w)

    print(ans)
    print(f"Строка {w}{"" if ans else " не"} распознается автоматом из файла {file_name}")

