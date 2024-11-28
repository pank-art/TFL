from collections import defaultdict, deque
from graphviz import Digraph
import json


def to_subscript_number_in_string(text):
    subscript_digits = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")
    return text.translate(subscript_digits)

class PDA:
    def __init__(self):
        self.states = set()  # Множество состояний
        self.start_state = None  # Начальное состояние
        self.accept_state = None  # Финальное состояния
        self.transitions = defaultdict(lambda: defaultdict(list))  # Таблица переходов
        self.input_alphabet = set()  # Алфавит входной строки
        self.stack_alphabet = set()  # Алфавит стека. x ∈ self.stack_alphabet
        self.deterministic = True  # Детерминированный ли PDA

    def add_state(self, state, is_start=False, is_accept=False):
        """Добавляет состояние в PDA."""
        self.states.add(state)
        if is_start:
            self.start_state = state
        if is_accept:
            self.accept_state = state

    def add_transition(self, from_state, input_symbol, stack_top, to_state, stack_action):
        """
        Добавляет переход в PDA.
        - from_state: текущее состояние.
        - input_symbol: символ из входной строки (или ε для пустого символа).
        - stack_top: символ на вершине стека.
        - to_state: состояние, в которое переходим.
        - stack_action: список символов для записи в стек (или ε).
        """
        # Проверка на существование идентичного перехода
        existing_transitions = self.transitions[from_state][(input_symbol, stack_top)]
        if (to_state, stack_action) in existing_transitions:
            #print(f"Переход из состояния {from_state} с символом '{input_symbol}' и стековым символом '{stack_top}' "
            #      f"в состояние {to_state} с действием {stack_action} уже существует.")
            return  # Не добавляем дублирующий переход

        self.transitions[from_state][(input_symbol, stack_top)].append((to_state, stack_action))
        if input_symbol != "ε":
            self.input_alphabet.add(input_symbol)
        if stack_top != "ε" and stack_top != "x":
            self.stack_alphabet.add(stack_top)
        if stack_action != "ε":
            self.stack_alphabet.update(s for s in stack_action if s != "x")

    def __repr__(self):
        """Возвращает текстовое представление PDA для отладки."""
        result = []
        result.append(f"States: {self.states}")
        result.append(f"Start state: {self.start_state}")
        result.append(f"Accept state: {self.accept_state}")
        result.append("Transitions:")
        for from_state, transitions in self.transitions.items():
            for (input_symbol, stack_top), targets in transitions.items():
                for to_state, stack_action in targets:
                    result.append(f"  {from_state} --({input_symbol}, {stack_top}/{stack_action})--> {to_state}")

        return "\n".join(result)

    def visualize_pda(self, filename="data/pda"):
        """
        Визуализирует PDA с использованием Graphviz.
        """
        dot = Digraph(format="pdf", graph_attr={"rankdir": "LR"})

        # Узлы
        for state in self.states:
            shape = "doublecircle" if state == self.accept_state else "ellipse"
            dot.node(str(state), f"{state}", shape=shape)

        # Переходы
        for from_state, state_transitions in self.transitions.items():
            for (input_symbol, stack_top), transitions in state_transitions.items():
                for to_state, stack_action in transitions:
                    str_stack_action = "".join(s for s in stack_action)
                    label = f"{input_symbol}, {to_subscript_number_in_string(stack_top)} / {to_subscript_number_in_string(str_stack_action)}"
                    dot.edge(str(from_state), str(to_state), label=label)

        # Начальная стрелка
        if self.start_state is not None:
            dot.node("start", "", shape="point")
            dot.edge("start", str(self.start_state), label="start")

        # Сохранение и вывод
        dot.render(filename, view=True)
        print(f"PDA визуализирован и сохранён в файл {filename}.png")

    def export_to_file(self, filename="data/pda.json"):
        """
        Сохраняет PDA в файл в формате JSON.
        """
        data = {
            "states": list(self.states),
            "start_state": self.start_state,
            "accept_state": self.accept_state,
            "transitions": {
                str(from_state): {
                    f"{symbol},{stack_top}": [
                        {"to_state": to_state, "stack_action": stack_action}
                        for to_state, stack_action in transitions
                    ]
                    for (symbol, stack_top), transitions in state_transitions.items()
                }
                for from_state, state_transitions in self.transitions.items()
            },
            "deterministic": self.deterministic,
        }
        with open(filename, "w") as f:
            json.dump(data, f, indent=4)
        print(f"PDA успешно экспортирован в {filename}.")

    @classmethod
    def import_from_file(cls, filename="data/pda.json"):
        """
        Загружает PDA из файла в формате JSON.
        """
        with open(filename, "r") as f:
            data = json.load(f)

        pda = cls()
        pda.states = set(data["states"])
        pda.start_state = data["start_state"]
        pda.accept_state = data["accept_state"]
        pda.deterministic = data["deterministic"]
        for from_state, state_transitions in data["transitions"].items():
            from_state = int(from_state) if from_state.isdigit() else from_state
            for transition_key, transitions in state_transitions.items():
                symbol, stack_top = transition_key.split(",")
                for transition in transitions:
                    to_state = transition["to_state"]
                    stack_action = transition["stack_action"]
                    pda.add_transition(from_state, symbol, stack_top, to_state, stack_action)
        print(f"PDA успешно импортирован из {filename}.")
        return pda

    def run(self, input_string: str):
        """
        Проверяет, распознаёт ли PDA заданную строку.
        :param input_string: строка для проверки.
        :return: True, если строка распознаётся, иначе False.
        """

        # Очередь для отслеживания состояния (state, remaining_input, stack)
        queue = deque()
        queue.append((self.start_state, input_string, ["S0"]))  # Начальное состояние

        while queue:
            current_state, remaining_input, stack = queue.popleft()

            # Условие успешного завершения
            if not remaining_input and stack == ["S0", f"S{self.accept_state}"] and current_state == self.accept_state:
                return True

            # Текущий входной символ
            input_symbol = remaining_input[0] if remaining_input else "ε"

            # Возможные переходы
            for (symbol, stack_top), transitions in self.transitions[current_state].items():
                # Проверяем входной символ и вершину стека
                if (symbol == input_symbol or symbol == "ε") and (
                        not stack or stack[-1] == stack_top or stack_top == "x"):
                    for to_state, stack_action in transitions:
                        # Создаём новую копию входных данных и стека
                        new_remaining_input = remaining_input[1:] if symbol == input_symbol else remaining_input
                        new_stack = stack[:-1] if stack and stack_top != "x" else stack

                        # Добавляем новые символы в стек
                        if stack_action != "ε":
                            if "x" in stack_action:
                                stack_action.remove("x")
                            new_stack.extend(stack_action[::-1])  # Переворачиваем для правильного порядка
                        else:
                            new_stack = stack[:-1]  # Если нужно только снять со стека

                        # Добавляем новое состояние в очередь
                        queue.append((to_state, new_remaining_input, new_stack))

        # Если очередь пуста, а строка не принята
        return False

