import re
from collections import defaultdict

from graphviz import Digraph

from core.parser_grammar import parse_grammar
from core.pda import PDA


class LR0PosDFA:
    def __init__(self, grammar: dict):
        self.grammar = grammar  # Грамматика
        self.states = []  # Список состояний
        self.transitions = defaultdict(dict)  # Переходы
        self.action = defaultdict(dict)  # Действия (reduce или accept)
        self.deterministic = True  # Детерминированный ли PDA получится

        # Добавляем новое начальное правило S' -> S
        self._add_start_rule()

        # Строим Position DFA
        self._build_pda()

    def _add_start_rule(self):
        """
        Добавляет новое начальное правило S' -> S.
        """
        old_start = list(self.grammar.keys())[0]
        new_start = "S'"
        if new_start in self.grammar:
            raise ValueError("В вашей грамматике уже присутствует нетерминал S'. Переименуйте его.")
        # Добавляем новое правило S' -> S
        self.grammar = {new_start: [[old_start]]} | self.grammar

    def _closure(self, items):
        """
        Добавляет правила для нетерминала, перед которым точка.
        """
        closure = set(items)
        while True:
            new_items = set(closure)
            for nt, alpha, beta in closure:
                if beta:  # Если есть символ после точки
                    first_symbol = beta[0]
                    if first_symbol in self.grammar:  # Если это нетерминал
                        for production in self.grammar[first_symbol]:
                            new_items.add((first_symbol, tuple(), tuple(production)))
            if new_items == closure:
                break
            closure = new_items
        return closure

    def _goto(self, items, symbol):
        """
        Переход по любому символу.
        """
        new_items = set()
        non_deterministic = False
        for nt, alpha, beta in items:
            if beta and beta[0] == symbol:
                new_items.add((nt, tuple(alpha) + (beta[0],), tuple(beta[1:])))
                if len(beta[1:]) == 0:
                    non_deterministic = True  # После перехода по symbol получили свертку

        if non_deterministic and len(new_items) > 1:
            self.deterministic = False  # В одном состоянии со сверткой есть ещё правила, значит в PDA появится недетерминизм

        return self._closure(new_items)

    def _build_pda(self):
        """
        Строит PDA на основе элементов и переходов.
        """
        # Стартовое состояние
        start_symbol = list(self.grammar.keys())[0]  # S'
        first_production = self.grammar[start_symbol][0]  # ['S']
        start_state = self._closure({(start_symbol, tuple(), tuple(first_production))})

        self.states.append(start_state)
        state_map = {frozenset(start_state): 0}  # Маппинг состояний на индексы

        # Построение состояний
        worklist = [start_state]
        while worklist:
            current_state = worklist.pop(0)
            current_index = state_map[frozenset(current_state)]

            for symbol in set(sym for nt, alpha, beta in current_state for sym in (alpha + beta)):
                goto_state = self._goto(current_state, symbol)
                if not goto_state:
                    continue
                goto_frozen = frozenset(goto_state)
                if goto_frozen not in state_map:  # Добавляем состояние, если такого нет
                    state_map[goto_frozen] = len(self.states)
                    self.states.append(goto_state)
                    worklist.append(goto_state)
                self.transitions[current_index][symbol] = state_map[goto_frozen]  # Добавляем переход

            # Обработка снижения (reduce)
            for nt, alpha, beta in current_state:
                if not beta:  # Если точка в конце правила
                    if nt == start_symbol:  # Если это правило S' -> S
                        self.action[current_index]["$"] = "accept"
                    else:
                        production = "".join(alpha)
                        self.action[current_index][f"{nt}->{production}"] = f"reduce"

    def __repr__(self):
        """Возвращает текстовое представление LR0PosDFA для отладки."""
        print("States:")
        for idx, state in enumerate(self.states):
            print(f"State {idx}: {state}")

        print("\nTransitions:")
        for from_state in self.transitions:
            for symbol in self.transitions[from_state]:
                to_state = self.transitions[from_state][symbol]
                print(f"From state {from_state} on '{symbol}' -> State {to_state}")

        print("\nActions:")
        for state in self.action:
            for symbol in self.action[state]:
                print(f"State {state} on '{symbol}' -> {self.action[state][symbol]}")

    def visualize_pos_dfa(self, filename="data/pos_dfa"):
        """Визуализирует LR0PosDFA с помощью Graphviz."""
        dot = Digraph(graph_attr={"rankdir": "LR"})

        # Добавляем узлы
        for i, state in enumerate(self.states):
            state_label = f"State {i}\n" + "\n".join(
                [f"{nt} -> {''.join(alpha)}.{''.join(beta)}" for nt, alpha, beta in state]
            )
            dot.node(str(i), state_label, shape="ellipse")

        # Добавляем переходы
        for from_state, transitions in self.transitions.items():
            for symbol, to_state in transitions.items():
                label = f"{symbol}"
                dot.edge(str(from_state), str(to_state), label=label)

        # Добавляем действия
        for state, actions in self.action.items():
            for symbol, action in actions.items():
                label = f"{symbol}: {action}"
                dot.node(f"accept_{state}", label, shape="box", color="green")
                dot.edge(str(state), f"accept_{state}", label)

        # Сохраняем и рендерим
        dot.render(filename, view=True)

    def convert_to_pda(self):
        """Создаем PDA на основе данного позиционного автомата"""
        pda = PDA()
        pda.deterministic = self.deterministic

        # Добавляем состояния
        for i in range(len(self.states)):
            is_accept = any(nt == "S'" and len(beta) == 0 for nt, _, beta in self.states[i])
            pda.add_state(i, is_start=(i == 0), is_accept=is_accept)

        # Добавляем переходы
        for from_state, transitions in self.transitions.items():
            for symbol, to_state in transitions.items():
                stack_action = [f"S{to_state}", "x"]  # Добавляем в стек S с номером состояния, в которое переходим
                if re.match(r"^[a-z]$", symbol):
                    pda.add_transition(from_state, symbol, "x", to_state, stack_action)

        # Добавляем действия reduce
        for state, actions in self.action.items():
            for symbol, action in actions.items():
                if action == "reduce":
                    nt, production = symbol.split("->")

                    # Для каждого символа в правой части добавляем ε-переход
                    num_pops = self._len_split_production(production)  # Разделение и подсчет терминалов и нетерминалов
                    current_state = state
                    for i in range(num_pops):
                        next_state = f"pop_{symbol}_{i}"
                        pda.add_state(next_state)  # Дополнительное состояние для снятия нужного кол-ва символов со стека
                        pda.add_transition(current_state, "ε", "x", next_state, "ε")
                        current_state = next_state

                    # Ищу состояния, которые были num_pops переходов назад
                    reduce_from_states = []
                    reduce_to_states = [state]
                    for i in range(num_pops):
                        for from_state, transitions in self.transitions.items():
                            for _, to_state in transitions.items():
                                if to_state in reduce_to_states:
                                    reduce_from_states.append(from_state)
                        reduce_to_states = reduce_from_states
                        reduce_from_states = []

                    for reduce_state in reduce_to_states:
                        for from_state, transitions in self.transitions.items():
                            for s, to_state in transitions.items():
                                if reduce_state == from_state and s == nt:  # Выбираем состояния, в которые переходим по свертке
                                    pda.add_transition(current_state, "ε", f"S{reduce_state}", to_state,
                                                       [f"S{to_state}", f"S{reduce_state}"])

        return pda

    def _len_split_production(self, production: str):
        """
        Разделить production на терминалы и нетерминалы. Вернуть их количество.
        """
        length = 0
        tokens = []

        for i in range(len(production)):
            for j in range(i + 1, len(production)):
                buffer = production[i:j]
                if buffer in self.grammar:
                    tokens.append(buffer)
                    break

        for nt in tokens:
            length += production.count(nt)
            production = production.replace(nt, "")

        return length + len(production)


if __name__ == "__main__":
    with open('../data/grammar.txt', 'r') as file:
        grammar_text = file.read()

        rules = parse_grammar(grammar_text)

        # Создание и вывод PDA
        pos_dfa = LR0PosDFA(rules)
        # pos_dfa.print_pda()
        pos_dfa.visualize_pos_dfa('../data/pos_dfa')

        pda = pos_dfa.convert_to_pda()
        pda.visualize_pda('../data/pda')
        print("Deterministic?", pda.deterministic)



