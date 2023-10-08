class coefficients:
    def __init__(self, name=None, kefX=None, freeKef=None):
        if kefX is not None and freeKef is not None:
            self.kefX = kefX
            self.freeKef = freeKef
        elif name is not None:
            self.kefX = ['a_1' + name, 'a_2' + name]
            self.freeKef = ['b_1' + name, 'b_2' + name]
        else:
            self.kefX = []
            self.freeKef = []

    def comp(self, f):
        res_kefX = []
        res_freeKef = []
        for i in range(len(f.kefX) - 1):
            res_kefX.append(f.kefX[i])
        res_kefX.append('(' + '* ' + self.kefX[0] + ' ' + f.kefX[len(f.kefX) - 1] + ')')
        res_kefX.append(self.kefX[len(self.kefX) - 1])

        for i in range(len(f.freeKef) - 1):
            res_freeKef.append(f.freeKef[i])
        res_freeKef.append(
            '(+ ' + '(* ' + self.kefX[0] + ' ' + f.freeKef[len(f.freeKef) - 1] + ') ' + self.freeKef[0] + ')')
        res_freeKef.append(self.freeKef[len(self.freeKef) - 1])

        return coefficients('a', res_kefX, res_freeKef)


def parse_word(w):
    tmp = coefficients(w[len(w) - 1])
    for i in range(len(w) - 2, -1, -1):
        x = coefficients(w[i])
        tmp = x.comp(tmp)
    return tmp


def remove_duplicates(input_string):
    unique_chars = ""

    for char in input_string:
        if char not in unique_chars:
            unique_chars += char

    return unique_chars


def define(name):
    s = '(declare-fun ' + 'a_1' + name + ' () Int)\n'
    s += '(declare-fun ' + 'a_2' + name + ' () Int)\n'
    s += '(declare-fun ' + 'b_1' + name + ' () Int)\n'
    s += '(declare-fun ' + 'b_2' + name + ' () Int)\n'
    s += '(assert (>= ' + 'a_1' + name + ' 0))\n'
    s += '(assert (>= ' + 'a_2' + name + ' 0))\n'
    s += '(assert (>= ' + 'b_1' + name + ' 0))\n'
    s += '(assert (>= ' + 'b_2' + name + ' 0))\n'
    return s


def greater(Lkef, Rkef):
    s = '(or'
    for i in range(len(Lkef) - 1, -1, -1):
        if i != 0:
            s += ' (and'
        s += ' (> ' + Lkef[i] + ' ' + Rkef[i] + ')'
        for j in range(i - 1, -1, -1):
            s += ' (= ' + Lkef[j] + ' ' + Rkef[j] + ')'
        if i != 0:
            s += ')'
    s += ')'
    return s


def equal(Lkef, Rkef):
    s = '(and'
    for i in range(len(Lkef)):
        s += ' (= ' + Lkef[i] + ' ' + Rkef[i] + ')'
    s += ')'
    return s


def rules(LHS, RHS):
    while len(LHS.kefX) < len(RHS.kefX):
        LHS.kefX.insert(0, str(0))
        LHS.freeKef.insert(0, str(0))
    while len(LHS.kefX) > len(RHS.kefX):
        RHS.kefX.insert(0, str(0))
        RHS.freeKef.insert(0, str(0))

    rule = '(assert (or '

    rule += '(and '
    rule += greater(LHS.kefX, RHS.kefX) + ' '
    rule += '(or '
    rule += greater(LHS.freeKef, RHS.freeKef) + ' '
    rule += equal(LHS.freeKef, RHS.freeKef) + ')) '

    rule += '(and '
    rule += equal(LHS.kefX, RHS.kefX) + ' '
    rule += greater(LHS.freeKef, RHS.freeKef) + ')'
    rule += '))'

    return rule


def main():
    with open("input.txt", "r") as input_file:
        lines = input_file.readlines()
    tmp = ''
    d = ''
    for line in lines:
        words = line.split()
        left = parse_word(words[0])
        right = parse_word(words[2])
        d += words[0] + words[2]
        tmp += rules(left, right) + '\n'
    smt = '(set-logic QF_NIA)\n'
    for name in remove_duplicates(d):
        smt += define(name)
    smt += '\n' + tmp + '\n'
    smt += '(check-sat)\n(get-model)\n(exit)'
    with open("smt.smt2", "w") as file:
        file.write(smt)


if __name__ == "__main__":
    main()
