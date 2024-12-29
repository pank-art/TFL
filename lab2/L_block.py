import re
import copy
from mat import auto_inclusion, auto_equivalence
from relict_mat import membershipQuery, equivalenceQuery

max_size = 0
alphabet = ""

# грамматика
"""
[program] ::= [eol]*([definition][eol]+)+
[definition] ::= [const] [lbr-1] ([eol]*[sentence])* [eol]*[rbr-1]
[sentence] ::= [pattern][equal][expression][sep]
[pattern] ::= [lbr-3][pattern][rbr-3]|[pattern][blank][pattern] | [var] | [const] |
[expression] ::= [var] | [const] | 
                [expression][blank][expression][lbr-3][expression] [rbr-3] |
                 [lbr-2] [const] [blank] [expression] [rbr-2]
"""


class L:
    def __init__(self):
        self.s = ['E']
        self.e = ['E']
        self.table = [[False]]
        self.alphabet = set()
        self.len_s = 0
        self.s_exp = []
        self.table_exp = []

    def __str__(self):
        tabl = ''
        tabl += '\t\t'
        for e in self.e:
            if len(e) > 3:
                tabl += e + '\t'
            else:
                tabl += e + '\t\t'
        tabl += '\n'

        for i in range(len(self.s)):
            if len(self.s[i]) > 3:
                tabl += self.s[i] + '\t'
            else:
                tabl += self.s[i] + '\t\t'
            for incl in self.table[i]:
                tabl += str(int(incl)) + '\t\t'
            tabl += '\n'

        tabl += '----------------------------------------\n'

        for i in range(len(self.s_exp)):
            if len(self.s_exp[i]) > 3:
                tabl += self.s_exp[i] + '\t'
            else:
                tabl += self.s_exp[i] + '\t\t'
            for incl in self.table_exp[i]:
                tabl += str(int(incl)) + '\t\t'
            tabl += '\n'

        return tabl

    def copy(self):
        """Создает глубокую копию объекта L"""
        return copy.deepcopy(self)

    def expansion(self):
        """Расширяется таблица и проверяются необходимые условия"""
        # print("expansion")
        for i in range(len(self.s)):
            for y in self.alphabet:
                if i >= self.len_s and not simplify_epsilon(self.s[i] + y) in self.s and not simplify_epsilon(
                        self.s[i] + y) in self.s_exp:
                    self.s_exp.append(simplify_epsilon(self.s[i] + y))
                    self.table_exp.append([])
                    for j in range(len(self.e)):
                        self.table_exp[-1].append(
                            inclusion(simplify_epsilon(self.s_exp[-1] + self.e[j])))

        self.len_s = len(self.s)

        indexes = []
        full = 1
        for i in range(len(self.table_exp)):
            if not self.table_exp[i] in self.table:
                self.table.append(self.table_exp[i])
                self.s.append(self.s_exp[i])
                indexes.append(i)
                full = 0

        for j, i in enumerate(indexes):
            self.s_exp.pop(i - j)
            self.table_exp.pop(i - j)

        if full:
            equal = eq(self)
            if equal == True:
                print(self)
                print('Nice')
                return True
            else:
                return self._add_suff(equal)
        else:
            return self.expansion()

    def _add_suff(self, suff):
        """Добавляем суффиксы"""
        # print("add_suff")
        all_suff = [suff[i:] for i in range(len(suff))]
        for s in all_suff:
            if s not in self.e:
                self.e.append(s)
        self._update_table()
        self.len_s = 0
        return self.expansion()

    def _update_table(self):
        """Добавляем значения для новых суффиксов"""
        # print("update_table")
        for i in range(len(self.s)):
            for j in range(len(self.e)):
                if j >= len(self.table[i]):
                    self.table[i].append(inclusion(simplify_epsilon(self.s[i] + self.e[j])))

        for i in range(len(self.s_exp)):
            for j in range(len(self.e)):
                if j >= len(self.table_exp[i]):
                    self.table_exp[i].append(inclusion(simplify_epsilon(self.s_exp[i] + self.e[j])))

    # Далее блочная вариант (не проверенный) и без расширенной части таблицы
    def add_word_block(self, w: str, w_start, w_end):
        """Добавление слова, принадлежащего какому-то из подавтоматов"""
        print("add_word_block")
        for x in w:
            self.alphabet.add(x)

        self.only_add_suff(w)
        self.update_table_block(w_start, w_end)
        self.expansion_block(w_start, w_end)

    def only_add_suff(self, suff):
        """Добавление суффиксов без обновления значений"""
        print("only_add_suff")
        all_suff = [suff[i:] for i in range(len(suff))]
        for s in all_suff:
            if s not in self.e:
                self.e.append(s)

    def update_table_block(self, w_start, w_end):
        """Добавление значений для новых суффиксов подавтоматов"""
        print("update_table_block")
        for i in range(len(self.s)):
            for j in range(len(self.e)):
                if j >= len(self.table[i]):
                    self.table[i].append(inclusion(simplify_epsilon(w_start + self.s[i] + self.e[j] + w_end)))

    def expansion_block(self, w_start, w_end):
        """Расширение таблицы для подавтомата (без проверки эквивалентности)"""
        print("expansion_block")
        s_exp = []
        for i in range(len(self.s)):
            for y in self.alphabet:
                if i >= self.len_s and not (self.s[i] + y) in self.s:
                    s_exp.append(simplify_epsilon(self.s[i] + y))
        print(s_exp)
        table_exp = []
        for i in range(len(s_exp)):
            table_exp.append([])
            for j in range(len(self.e)):
                table_exp[i].append(inclusion(simplify_epsilon(w_start + s_exp[i] + self.e[j] + w_end)))
        self.len_s = len(self.s)

        full = 1
        for i in range(len(table_exp)):
            if not table_exp[i] in self.table:
                self.table.append(table_exp[i])
                self.s.append(s_exp[i])
                full = 0

        if full:
            return True
        else:
            return self.expansion_block(w_start, w_end)


def eq(l: L):
    table_string = ""
    for i in range(len(l.s)):
        for j in range(len(l.e)):
            if l.table[i][j]:
                table_string += "1 "
            else:
                table_string += "0 "

    for i in range(len(l.s_exp)):
        for j in range(len(l.e)):
            if l.table_exp[i][j]:
                table_string += "1 "
            else:
                table_string += "0 "

    Sm = ""
    for x in l.s:
        if x == "E":
            Sm += "ε "
        else:
            Sm += str(x) + " "
    Em = ""
    for x in l.e:
        if x == "E":
            Em += "ε "
        else:
            Em += str(x) + " "

    Nm = ""
    for x in l.s_exp:
        if x == "E":
            Nm += "ε "
        else:
            Nm += str(x) + " "

    Sm = Sm[:len(Sm) - 1]
    Em = Em[:len(Em) - 1]
    Nm = Nm[:len(Nm) - 1]
    table_string = table_string[:len(table_string) - 1]

    equal = equivalenceQuery(Sm, Nm, Em, table_string)
    if equal[0] == 2:
        return True
    else:
        return equal[1]


def inclusion(s: str):
    s = s.replace("E", "ε")
    return membershipQuery(s)


def simplify_epsilon(s: str) -> str:
    # Если строка состоит только из одного или нескольких эпсилонов, то оставить только один
    if s == 'E' * len(s):
        return 'E'
    # Убираем все эпсилоны внутри строки
    return s.replace('E', '')


def conc(l1: L, l2: L) -> L:
    new = L()
    worlds1 = []
    worlds2 = []
    for i in range(len(l1.s)):
        if l1.table[i][0] == 1:
            worlds1.append(l1.s[i])

    for i in range(len(l2.e)):
        if l2.table[0][i] == 1:
            worlds2.append(l2.e[i])

    for i, s in enumerate(l1.s):
        if s != 'E':
            if all(val == 0 for val in l1.table[i]):
                continue
            new.s.append(s)

    for i, s in enumerate(l2.s):
        if s != 'E':
            if all(val == 0 for val in l2.table[i]):
                continue
            new.s.append(simplify_epsilon(worlds1[0] + s))

    first = 1
    for w1 in worlds1:
        for w2 in worlds2:
            if w1 == 'E':
                w1 = ''
            if w2 == 'E':
                w2 = ''
            new.only_add_suff(simplify_epsilon(w1 + w2))
            for j in range(len(new.e)):
                if j >= len(new.table[0]):
                    new.table[0].append(int(new.e[j] == simplify_epsilon(w1 + w2)))
                if j == 0 and new.e[j] == simplify_epsilon(w1 + w2):
                    new.table[0][0] = 1

            const = 0
            for i in range(1, len(l1.s)):
                if all(val == 0 for val in l1.table[i]):
                    const += 1
                    continue
                if first:
                    new.table.append([])
                for j in range(len(new.e)):
                    if not first:
                        if j < len(new.table[i - const]):
                            if j == 0 and new.s[i - const] == simplify_epsilon(w1 + w2):
                                new.table[i - const][j] = 1
                            continue
                    if j == 0:
                        new.table[i - const].append(int(new.s[i - const] == simplify_epsilon(w1 + w2)))
                    else:
                        w = new.e[j]
                        if len(w) > len(w2):
                            w = w[:len(w) - len(w2)]
                            val = l1.table[i][next(k for k in range(1, len(l1.e)) if l1.e[k] == w)]
                            new.table[i - const].append(val)
                        elif len(w) == len(w2):
                            new.table[i - const].append(l1.table[i][0])
                        else:
                            new.table[i - const].append(0)

            const += 1
            for i in range(1, len(l2.s)):
                if all(val == 0 for val in l2.table[i]):
                    const += 1
                    continue
                if first:
                    new.table.append([])
                for j in range(len(new.e)):
                    if not first:
                        if j < len(new.table[i + len(l1.s) - const]):
                            if j == 0 and new.s[i + len(l1.s) - const] == simplify_epsilon(w1 + w2):
                                new.table[i + len(l1.s) - const][j] = 1
                            continue
                    if j == 0:
                        new.table[i + len(l1.s) - const].append(
                            int(new.s[i + len(l1.s) - const] == simplify_epsilon(w1 + w2)))
                    else:
                        w = new.e[j]
                        if len(w) <= len(w2):
                            val = l2.table[i][next(k for k in range(len(l2.e)) if l2.e[k] == w)]
                            new.table[i + len(l1.s) - const].append(val)
                        else:
                            new.table[i + len(l1.s) - const].append(0)

            first = 0

    return new


def kleene_star(l: L):
    """ Построение замыкания Клини (L*) для автомата """
    new = l.copy()

    final_states = []
    for i in range(len(l.table)):
        if new.table[i][0] == 1:
            final_states.append(i)

    for j in range(len(new.e)):
        if new.table[0][j] == 1:
            for f in final_states:
                new.table[f][j] = 1

    new.table[0][0] = 1

    return new


def read_parametrs(filename: str = "parameters.txt"):
    f = open(filename, 'r')
    l1 = f.readline()
    maxLenth = int(l1.strip().replace(' ', '').split('=')[1])
    l2 = f.readline()
    maxNesting = int(l2.strip().replace(' ', '').split('=')[1])

    return maxLenth, maxNesting


def main():
    global file_path, max_size
    file_path = input("Enter file path (ex. automaton.txt):  ")
    max_size, _ = read_parametrs()
    program = L()

    # Создаю свою таблицу для каждого подавтомата
    const_lbr1 = L()
    rbr1 = L()
    pattern = L()
    equal = L()
    expression = L()
    sep = L()
    eol = L()

    empty = L()
    w = eq(empty)
    while w != "True":
        # Вначале определяем алфавит для eol
        w_eol = w[len(w) - max_size:]
        w_new = w + w_eol
        while inclusion(w_new):
            w_eol = w_eol[1:]
            w_new = w + w_eol

        eol.add_word_block(w_eol, w, '')

        eol_alp = ''.join(f'{x}' for x in eol.alphabet)

        i = 0
        while w[i] in eol_alp:
            i += 1
        eol_first = i
        i = len(w) - 1
        while w[i] in eol_alp:
            i -= 1
        eol_last = i + 1

        # добавляем слово, распознающееся eol в места [eol]* для корректного разбиения на подавтоматы
        for i in range(eol_first + 1, eol_last):  # +1 для вставки в конец
            # Вставляем w_eol на позицию i
            modified_word = w[:i] + w_eol + w[i:]

            if inclusion(modified_word):
                print("Подходящее место для вставки найдено:", modified_word)
                w = modified_word
                break
        # добавляем слово, распознающееся eol в места [eol]* для корректного разбиения на подавтоматы
        for i in range(eol_last - 1, eol_first, -1):  # +1 для вставки в конец
            # Вставляем w_eol на позицию i
            modified_word = w[:i] + w_eol + w[i:]

            if inclusion(modified_word):
                print("Подходящее место для вставки найдено:", modified_word)
                w = modified_word
                break

        # Регулярное выражение для разделения строки по группам символов из алфавита eol
        p = fr'[{eol_alp}]+|[^{eol_alp}]+'
        lexemes = re.findall(p, w[eol_first:eol_last])

        # Печатаем результат
        print(lexemes)

        if len(lexemes) >= 5:  # после добавления eol должно всегда получаться разбить слово на нужные мне подслова
            w_rbr1 = lexemes[len(lexemes) - 1]
            rbr1.add_word_block(w_rbr1, w[:eol_last - len(w_rbr1)], w[eol_last:])
            w_const_lbr1 = lexemes[0]
            const_lbr1.add_word_block(w_const_lbr1, '', w[eol_first + len(w_const_lbr1):])

            sentence = lexemes[2]

            for x in eol.alphabet:
                alphabet.replace(x, '')
            for x in rbr1.alphabet:
                alphabet.replace(x, '')
            for x in const_lbr1.alphabet:
                alphabet.replace(x, '')

            x = sentence[(len(sentence)) - 1]
            alphabet.replace(x, '')
            blank_alp = ''
            equal_sep_alp = x

            if len(alphabet) > 1:
                for i in range(len(alphabet)):
                    j = 0
                    while sentence[j] != alphabet[i]:
                        j += 1

                    blank_alp = alphabet[len(alphabet) - i]
                    w_blank = ''
                    pattern = sentence[:j]
                    matches = re.findall(fr'[{blank_alp}]+', pattern)
                    if matches:
                        w_blank = min(len(match) for match in matches) * f'{blank_alp}'

                    if inclusion(w_const_lbr1 + pattern + w_blank + sentence + w_rbr1 + w[eol_last:]):
                        equal_sep_alp += alphabet[i]
                        print("good")
                        # blank = L_new(w_blank, w_const_lbr1 + pattern, sentence + w_rbr1 + w[eol_last:])
                        break
                    else:
                        print("AAAAAAAAAAAAAAAAAAAAAAAA (можно 1 раз)")
                        continue
            elif len(alphabet) == 1:
                blank_alp = alphabet

            i = 0
            stop = 1
            # тут может быть не один sentence, a много
            while stop:
                while sentence[i] not in equal_sep_alp:
                    i += 1
                w_pattern = sentence[:i]
                j = max_size
                while sentence[i + j] not in equal_sep_alp:
                    j -= 1
                j += 1
                w_equal = sentence[i:i + j]
                k = i + j
                while sentence[k] not in equal_sep_alp:
                    k += 1
                w_expression = sentence[i + j:k]
                j = max_size
                if k + j < len(sentence):
                    while sentence[k + j] not in equal_sep_alp:
                        j -= 1
                    j += 1
                    w_sep = sentence[k:k + j]
                else:
                    w_sep = sentence[k:]
                    stop = 0

                i = k + j

                pattern.add_word_block(w_pattern, w_const_lbr1, w_equal + w_expression + w_sep + w_rbr1 + w[eol_last:])
                equal.add_word_block(w_equal, w_const_lbr1 + w_pattern, w_expression + w_sep + w_rbr1 + w[eol_last:])
                expression.add_word_block(w_expression, w_const_lbr1 + w_pattern + w_equal,
                                          w_sep + w_rbr1 + w[eol_last:])
                sep.add_word_block(w_sep, w_const_lbr1 + w_pattern + w_equal + w_expression, w_rbr1 + w[eol_last:])

        sent = conc(conc(conc(pattern, equal), expression), sep)
        eol_star = kleene_star(eol)

        l1 = conc(eol_star, sent)
        l2 = kleene_star(l1)
        definition = conc(conc(conc(const_lbr1, l2), eol_star), rbr1)
        eol_p = conc(eol, eol_star)
        l3 = conc(definition, eol_p)
        l4 = conc(l3, kleene_star(l3))
        program = conc(eol_star, l4)

        w = eq(program)

    print(program)


if __name__ == "__main__":
    main()
