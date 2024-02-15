#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <sstream>

class Domino {
public:
    std::string up;
    std::string down;

    Domino(const std::string& up, const std::string& down) : up(up), down(down) {}
};



std::vector<Domino> parseDominoes(const std::vector<std::string>& inputLines) {
    std::vector<Domino> dominoes;

    for (const auto& dominoStr : inputLines) {
        std::istringstream ss(dominoStr.substr(1));
        std::string up, down;
        std::getline(ss, up, ',');
        std::getline(ss, down, ')');
        up.erase(0, up.find_first_not_of(" "));
        up.erase(up.find_last_not_of(" ") + 1);
        down.erase(0, down.find_first_not_of(" "));
        down.erase(down.find_last_not_of(" ") + 1);
        dominoes.emplace_back(up, down);
    }

    return dominoes;
}

std::string define(int n) {
    std::string s;
    for (int i = 0; i < n; ++i) {
        s += "(declare-fun M_" + std::to_string(i) + " () Int)\n";
        s += "(assert (>= M_" + std::to_string(i) + " 0))\n";
    }
    s += "(assert (or";
    for (int i = 0; i < n; ++i) {
        s += " (> M_" + std::to_string(i) + " 0)";
    }
    s += "))\n";
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            if (i != j) {
                s += "(declare-fun N" + std::to_string(i) + std::to_string(j) + " () Int)\n";
                s += "(assert (>= N" + std::to_string(i) + std::to_string(j) + " 0))\n";
            }
        }
    }
    return s;
}

std::set<char> generateAlphabet(const std::vector<Domino>& dominoes) {
    std::set<char> alphabet;
    for (const auto& domino : dominoes) {
        for (char c : domino.up + domino.down) {
            alphabet.insert(c);            
        }
    }
    return alphabet;
}

std::string sumNin(const std::vector<Domino>& dominoes, size_t i) {
    std::string s = "(+ ";
    for (size_t j = 0; j < dominoes.size(); ++j) {
        if (i != j) {
            s += "N" + std::to_string(i) + std::to_string(j) + " ";
        }
    }
    s.pop_back();
    s += ")";
    return s;
}

std::string sumNnj(const std::vector<Domino>& dominoes, size_t j) {
    std::string s = "(+ ";
    for (size_t i = 0; i < dominoes.size(); ++i) {
        if (i != j) {
            s += "N" + std::to_string(i) + std::to_string(j) + " ";
        }
    }
    s.pop_back();
    s += ")";
    return s;
}

int n = 0;

std::vector<std::string> generateConditions(const std::vector<Domino>& dominoes, const std::set<char>& alphabet) {
    n = dominoes.size();
    std::vector<std::string> conditions;

    for (char letter : alphabet) {
        std::string sUp = "(+ ";
        std::string sDown = "(+ ";
        for (size_t i = 0; i < dominoes.size(); ++i) {
            int countUp = 0, countDown = 0;
            for (char c : dominoes[i].up) {
                if (c == letter) {
                    countUp++;
                }
            }
            sUp += "(* " + std::to_string(countUp) + " M_" + std::to_string(i) + ") ";

            for (char c : dominoes[i].down) {
                if (c == letter) {
                    countDown++;
                }
            }
            sDown += "(* " + std::to_string(countDown) + " M_" + std::to_string(i) + ") ";
        }

        sUp.pop_back();
        sDown.pop_back();
        sUp += ")";
        sDown += ")";

        conditions.push_back("(= " + sUp + " " + sDown + ")");
    }

    for (size_t i = 0; i < dominoes.size(); ++i) {
        for (size_t j = 0; j < dominoes.size(); ++j) {
            if (i != j) {
                conditions.push_back("(<= N" + std::to_string(i) + std::to_string(j) + " M_" + std::to_string(i) + ")");
                conditions.push_back("(<= N" + std::to_string(i) + std::to_string(j) + " M_" + std::to_string(j) + ")");
            }
        }
    }

    std::string s = "(or";
    for (size_t i = 0; i < dominoes.size(); ++i) {        
        for (size_t j = 0; j < dominoes.size(); ++j) {
            if (i != j && dominoes[i].up[0] == dominoes[i].down[0] && dominoes[j].up.back() == dominoes[j].down.back()) {
                std::string start = " (and (= " + sumNnj(dominoes, i) + " " +
                    "(- M_" + std::to_string(i) + " 1))";
                std::string end = " (and (= " + sumNin(dominoes, j) + " " +
                    "(- M_" + std::to_string(j) + " 1))";
                for (size_t k = 0; k < dominoes.size(); ++k) {
                    if (i != k) {
                        start += " (= " + sumNnj(dominoes, k) + " M_" + std::to_string(k) + ")";
                    }
                    if (j != k) {
                        end += " (= " + sumNin(dominoes, k) + " M_" + std::to_string(k) + ")";
                    }
                }
                start += ")";
                end += ")";

                std::string second = " ";
                if (dominoes[i].up.size() > dominoes[i].down.size()) {
                    char symbol = dominoes[i].up[dominoes[i].down.size()];
                    for (size_t k = 0; k < dominoes.size(); ++k) {
                        if (k != i) {
                            if (dominoes[k].down[0] != symbol) {
                                second += "(= N" + std::to_string(i) + std::to_string(k) + " 0) ";
                            }
                        }
                    }
                }
                else if (dominoes[i].up.size() < dominoes[i].down.size()) {
                    char symbol = dominoes[i].down[dominoes[i].up.size()];
                    for (size_t k = 0; k < dominoes.size(); ++k) {
                        if (k != i) {
                            if (dominoes[k].up[0] != symbol) {
                                second += "(= N" + std::to_string(i) + std::to_string(k) + " 0) ";
                            }
                        }
                    }
                }
                else {
                    if (dominoes[i].up == dominoes[i].down) {
                        for (size_t k = 0; k < dominoes.size(); ++k) {
                            if (k != i) {
                                if (dominoes[k].up[0] != dominoes[i].up[0] and dominoes[k].down[0] != dominoes[i].up[0]) {
                                    std::string cond = "(= N" + std::to_string(i) + std::to_string(k) + " 0)";
                                    conditions.push_back(cond);
                                }
                            }
                        }
                    }
                }
                second.pop_back();
                s += " (and" + start + end + second + ")";
            }
        }
    }

    s += ")";
    if (s == "(or)") {
        s = "false";
    }

    conditions.push_back(s);

    return conditions;
}



int main() {
    std::ifstream inputFile("input.txt");
    if (!inputFile.is_open()) {
        std::cerr << "Не удалось открыть файл input.txt" << std::endl;
        return 1;
    }
    std::vector<std::string> inputLines;
    std::string line;
    while (std::getline(inputFile, line)) {
        inputLines.push_back(line);
    }

    std::vector<Domino> dominoes = parseDominoes(inputLines);
    std::set<char> alphabet = generateAlphabet(dominoes);
    std::vector<std::string> conditions = generateConditions(dominoes, alphabet);


    std::ofstream file("smt.smt2");
    file << "(set-logic QF_NIA)\n";
    file << define(dominoes.size()) << '\n';
    for (const auto& condition : conditions) {
        file << "(assert " << condition << ")\n";
    }
    file << '\n';
    file << "(check-sat)\n(get-model)\n(exit)";

    return 0;
}

