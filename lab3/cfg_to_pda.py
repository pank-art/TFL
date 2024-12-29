from core.parser_grammar import parse_grammar
from core.position import LR0PosDFA

if __name__ == "__main__":
    with open('data/grammar.txt', 'r') as file:
        grammar_text = file.read()

        grammar = parse_grammar(grammar_text)

        pos_dfa = LR0PosDFA(grammar)

        vis = input("Визуализировать позиционный автомат? (д/н) (y/n)   ")
        if vis.strip() == 'y' or vis.strip() == 'д':
            pos_dfa.visualize_pos_dfa()

        pda = pos_dfa.convert_to_pda()

        vis = input("Визуализировать PDA? (д/н) (y/n)   ")
        if vis.strip() == 'y' or vis.strip() == 'д':
            pda.visualize_pda()

        print(f"Детерминированный PDA?: {pda.deterministic}")

        pda.export_to_file()

