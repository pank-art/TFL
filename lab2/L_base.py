from L_block import conc, kleene_star, L, inclusion

if __name__ == "__main__":
    aba = L()
    aba.alphabet.add('a')
    aba.alphabet.add('b')
    aba.alphabet.add('c')
    aba.expansion()  # автомат в auto.txt (переменная filepath в L_block)

    aba_star = kleene_star(aba)
    print(aba_star)
    print(aba)
    print(conc(aba, aba_star))
