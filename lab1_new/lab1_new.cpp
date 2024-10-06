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
            s += "(declare-fun N" + std::to_string(i) + std::to_string(j) + " () Int)\n";
            s += "(assert (>= N" + std::to_string(i) + std::to_string(j) + " 0))\n";
        }
        s += "(declare-fun Nstart" + std::to_string(i) + " () Int)\n";
        s += "(assert (or (= Nstart" + std::to_string(i) + " 0) (= Nstart" + std::to_string(i) + " 1)))\n";
        s += "(declare-fun N" + std::to_string(i) + "last" + " () Int)\n";
        s += "(assert (or (= N" + std::to_string(i) + "last" + " 0) (= N" + std::to_string(i) + "last" + " 1)))\n";
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
        s += "N" + std::to_string(i) + std::to_string(j) + " ";
    }
    s.pop_back();
    s += ")";
    return s;
}

std::string sumNnj(const std::vector<Domino>& dominoes, size_t j) {
    std::string s = "(+ ";
    for (size_t i = 0; i < dominoes.size(); ++i) {
        s += "N" + std::to_string(i) + std::to_string(j) + " ";
    }
    s.pop_back();
    s += ")";
    return s;
}

std::pair<int, int> count_pair(const std::string& pair, const std::string& up, const std::string& down) {
    int upCount = 0;
    int downCount = 0;

    for (size_t k = 0; k < up.size() - 1; ++k) {
        if (up.substr(k, 2) == pair) {
            ++upCount;
        }
    }

    for (size_t k = 0; k < down.size() - 1; ++k) {
        if (down.substr(k, 2) == pair) {
            ++downCount;
        }
    }

    return { upCount, downCount };
}

int n = 0;

std::vector<std::string> generateConditions(const std::vector<Domino>& dominoes, const std::set<char>& alphabet) {
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

    std::string one_start = "(= (+";
    std::string one_last = "(= (+";

    for (std::size_t i = 0; i < dominoes.size(); ++i) {
        //сумма смычек для каждой домино с каждой стороны равна кол-во вхождений
        std::string start = "(= (+ Nstart" + std::to_string(i);
        std::string end = "(= (+ N" + std::to_string(i) + "last";

        for (std::size_t j = 0; j < dominoes.size(); ++j) {
            start += " N" + std::to_string(j) + std::to_string(i);
            end += " N" + std::to_string(i) + std::to_string(j);
        }

        start += ") M_" + std::to_string(i) + ")";
        end += ") M_" + std::to_string(i) + ")";

        conditions.push_back(start);
        conditions.push_back(end);

        conditions.push_back("(or (<= N" + std::to_string(i) + std::to_string(i) + " (- M_" + std::to_string(i) + " 1)) (and (= 0 N" + std::to_string(i) + std::to_string(i) + ") (= 0 M_" + std::to_string(i) + ")))");

        //кол-во начальных и конечных домино = 1
        one_start += " Nstart" + std::to_string(i);
        one_last += " N" + std::to_string(i) + "last";
    }

    one_start += ") 1)";
    one_last += ") 1)";
    conditions.push_back(one_start);
    conditions.push_back(one_last);

    //тут добавил всевозможные пары букв (создание pairs)
    std::vector<std::string> pairs;
    for (std::size_t i = 0; i < dominoes.size(); ++i) {
        for (std::size_t j = 0; j < dominoes.size(); ++j) {
            std::string up = dominoes[i].up + dominoes[j].up[0];
            std::string down = dominoes[i].down + dominoes[j].down[0];

            for (std::size_t k = 0; k < up.size() - 1; ++k) {
                int c = 1;
                for (std::size_t l = 0; l < pairs.size(); ++l) {
                    if (up.substr(k, 2) == pairs[l]) {
                        c = 0;
                        break;
                    }
                }
                if (c) {
                    pairs.push_back(up.substr(k, 2));
                }
            }
 

            for (std::size_t k = 0; k < down.size() - 1; ++k) {
                int c = 1;
                for (std::size_t l = 0; l < pairs.size(); ++l) {
                    if (down.substr(k, 2) == pairs[l]) {
                        c = 0;
                        break;
                    }
                }
                if (c) {
                    pairs.push_back(down.substr(k, 2));
                }
            }
        }
    }

    //тут условия на равенство кол-во пар сверху и снизу
    for (const auto& pair : pairs) {
        std::string up_cond = "(+ 0";
        std::string down_cond = "(+ 0";

        for (std::size_t i = 0; i < dominoes.size(); ++i) {
            for (std::size_t j = 0; j < dominoes.size(); ++j) {
                // количество pair сверху и снизу в домино[i] + первая буква домино[j]
                auto [up_count, down_count] = count_pair(pair, dominoes[i].up + dominoes[j].up[0],
                    dominoes[i].down + dominoes[j].down[0]);

                if (up_count != down_count) {
                    if (up_count != 0) {
                        up_cond += " (* " + std::to_string(up_count) + " N" + std::to_string(i) + std::to_string(j) + ")";
                    }

                    if (down_count != 0) {
                        down_cond += " (* " + std::to_string(down_count) + " N" + std::to_string(i) + std::to_string(j) + ")";
                    }
                }
            }
            // количество pair сверху и снизу в домино[i]. 
            auto [up_count, down_count] = count_pair(pair, dominoes[i].up, dominoes[i].down);

            if (up_count != down_count) {
                if (up_count != 0) {
                    up_cond += " (* " + std::to_string(up_count) + " N" + std::to_string(i) + "last)";
                }

                if (down_count != 0) {
                    down_cond += " (* " + std::to_string(down_count) + " N" + std::to_string(i) + "last)";
                }
            }
        }

        std::string cond = "(= " + up_cond + ") " + down_cond + "))";
        conditions.push_back(cond);
    }

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
    file << define(int(dominoes.size())) << '\n';
    for (const auto& condition : conditions) {
        file << "(assert " << condition << ")\n";
    }
    file << '\n';
    file << "(check-sat)\n(get-model)\n(exit)";

    return 0;
}

