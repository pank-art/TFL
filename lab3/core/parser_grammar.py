import re


def parse_grammar(grammar: str):
    """
    Парсит контекстно-свободную грамматику из строки.

    :param grammar: Многострочная строка с правилами грамматики.
    :return: Словарь правил грамматики {NT: [[правая часть 1], [правая часть 2], ...]}.
    """
    # Регулярные выражения для проверки
    nt_pattern = r"^[A-Z][0-9]*$|^\[[A-Za-z]+[0-9]*\]$"  # Нетерминал
    t_pattern = r"^[a-z]$"  # Терминал
    rule_pattern = re.compile(
        r"^\s*([A-Z][0-9]*|\[[A-Za-z]+[0-9]*\])\s*->\s*(([A-Z][0-9]*|\[[A-Za-z]+[0-9]*\]|[a-z])\s*)+$"
    )

    rules = {}

    for line in grammar.splitlines():
        line = line.strip()
        if not line:  # Пропуск пустых строк
            continue

        match = rule_pattern.match(line)
        if not match:
            raise ValueError(f"Неверный синтаксис правила: {line}")

        nt, production = line.split("->", 1)
        nt = nt.strip()
        production = production.strip()

        # Проверяем правильность нетерминала
        if not re.match(nt_pattern, nt):
            raise ValueError(f"Неверный нетерминал: {nt}")

        # Разбиваем правую часть на символы (терминалы и нетерминалы)
        production_parts = re.findall(r"[A-Z][0-9]*|\[[A-Za-z]+[0-9]*\]|[a-z]", production)

        # Проверяем правильность символов в правой части
        for part in production_parts:
            if not (re.match(nt_pattern, part) or re.match(t_pattern, part)):
                raise ValueError(f"Неверный символ в правой части: {part}")

        # Добавляем правило
        if nt not in rules:
            rules[nt] = []
        rules[nt].append(production_parts)

    return rules


if __name__ == "__main__":
    with open('./grammar.txt', 'r') as file:
        grammar_text = file.read()

        rules = parse_grammar(grammar_text)
        print("Разобранные правила:")
        print(rules)
        for nt, productions in rules.items():
            print(f"{nt} -> {productions}")
