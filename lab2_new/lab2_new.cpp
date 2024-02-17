using namespace std;

#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <regex>
#include <set>

class FiniteAutomaton {
public:
    std::vector<std::string> states;
    std::string start_state;
    std::vector<std::string> final_states;
    //std::unordered_map<std::string, std::unordered_map<std::string, std::string>> transitions;
    std::unordered_map<std::string, std::unordered_map<std::string, std::unordered_set<std::string>>> transitions;


    FiniteAutomaton() = default;

    FiniteAutomaton copy() const {
        FiniteAutomaton new_automaton;
        new_automaton.states = states;
        new_automaton.start_state = start_state;
        new_automaton.final_states = final_states;

        for (const auto& from_state : transitions) {
            for (const auto& symbol_transitions : from_state.second) {
                std::string symbol = symbol_transitions.first;
                const auto& to_states = symbol_transitions.second;
                for (const auto& to_state : to_states) {
                    new_automaton.add_transition(from_state.first, symbol, to_state);
                }
            }
        }
        return new_automaton;
    }

    std::string end_regex() const {
        for (const auto& from_state : transitions) {
            for (const auto& symbol_transitions : from_state.second) {
                std::string symbol = symbol_transitions.first;
                const auto& to_states = symbol_transitions.second;
                for (const auto& to_state : to_states) {
                    if (to_state == "new_final") {
                        return symbol;
                    }
                }
            }           
        }
        return "";
    }

    void add_transition(const std::string& from_state, const std::string& symbol, const std::string& to_state) {
        transitions[from_state][symbol].insert(to_state);
    }

    void read_automaton(std::ifstream& file) {
        std::getline(file, start_state);
        states.push_back(start_state);

        std::string final_states_str;
        std::getline(file, final_states_str);
        final_states_str.erase(std::remove_if(final_states_str.begin(), final_states_str.end(), ::isspace), final_states_str.end());
        for (const auto& state : split(final_states_str, ',')) {
            final_states.push_back(state);
            if (std::find(states.begin(), states.end(), state) == states.end()) {
                states.push_back(state);
            }
        }

        std::string transition_input;
        while (std::getline(file, transition_input)) {
            transition_input.erase(std::remove_if(transition_input.begin(), transition_input.end(), ::isspace), transition_input.end());
            std::smatch matches;
            std::regex_match(transition_input, matches, std::regex(R"(\(([^,]+),([^)]+)\)->([^,]+))"));
            std::string from_state = matches[1];
            std::string symbol = matches[2];
            std::string to_state = matches[3];

            if (std::find(states.begin(), states.end(), to_state) == states.end()) {
                states.push_back(to_state);
            }
            if (std::find(states.begin(), states.end(), from_state) == states.end()) {
                states.push_back(from_state);
            }

            add_transition(from_state, symbol, to_state);
        }
    }

    void print_automaton() const {
        std::cout << "States:";
        for (const auto& state : states) {
            std::cout << " " << state;
        }
        std::cout << "\nStart state: " << start_state << "\nFinal states:";
        for (const auto& final_state : final_states) {
            std::cout << " " << final_state;
        }
        std::cout << "\nTransitions:\n";
        for (const auto& from_state : transitions) {
            for (const auto& symbol_transitions : from_state.second) {
                std::string symbol = symbol_transitions.first;
                const auto& to_states = symbol_transitions.second;
                for (const auto& to_state : to_states) {
                    std::cout << "(" << from_state.first << ", " << symbol << ") -> " << to_state << "\n";
                }
            }
        }
    }

    void make_uniform() {
        std::string new_start_state = "new_start";
        std::string new_final_state = "new_final";

        states.push_back(new_start_state);
        states.push_back(new_final_state);

        add_transition(new_start_state, "E", start_state);
        for (const auto& final_state : final_states) {
            add_transition(final_state, "E", new_final_state);
        }

        final_states.clear();

        start_state = new_start_state;
        final_states.push_back(new_final_state);
    }

    std::string find_symbol_for_transition(const std::string& from_state, const std::string& to_state) const {
        for (const auto& from_state_entry : transitions) {
            for (const auto& symbol_transitions : from_state_entry.second) {
                std::string symbol = symbol_transitions.first;
                const auto& to_states = symbol_transitions.second;
                for (const auto& next_state : to_states) {
                    if (from_state_entry.first == from_state && next_state == to_state) {
                        return symbol;
                    }
                }
            }
        }
        return "";
    }

    void delete_state(const std::string& state_k) {
        auto transitions_copy = transitions;

        std::string kk = "";
        for (const auto& symbol_transitions : transitions_copy[state_k]) {
            std::string symbol = symbol_transitions.first;
            const auto& to_states = symbol_transitions.second;
            for (const auto& to_state : to_states) {
                if (to_state == state_k && kk.empty()) {
                    kk = symbol;
                    transitions[state_k][symbol].erase(to_state);
                    if (transitions[state_k][symbol].empty()) {
                        transitions[state_k].erase(symbol);
                    }
                }
                else if (to_state == state_k && !kk.empty()) {
                    kk += "|" + symbol;
                    transitions[state_k][symbol].erase(to_state);
                    if (transitions[state_k][symbol].empty()) {
                        transitions[state_k].erase(symbol);
                    }
                }
            }
        }

        for (auto& from_state : transitions_copy) {
            for (const auto& symbol_transitions : from_state.second) {
                std::string symbol = symbol_transitions.first;
                const auto& to_states = symbol_transitions.second;
                for (const auto& to_state : to_states) {
                    if (to_state == state_k && from_state.first != state_k) {
                        transitions[from_state.first][symbol].erase(to_state);
                        if (transitions[from_state.first][symbol].empty()) {
                            transitions[from_state.first].erase(symbol);
                        }
                        std::string pk = symbol;

                        for (const auto& symbol_next_transitions : transitions_copy[state_k]) {
                            std::string symbol_next = symbol_next_transitions.first;
                            const auto& next_states = symbol_next_transitions.second;
                            for (const auto& next_state : next_states) {
                                if (next_state != state_k) {
                                    std::string kq = symbol_next;
                                    std::string pq = find_symbol_for_transition(from_state.first, next_state);

                                    if (!pq.empty()) {
                                        bool found = false;
                                        for (const auto& sym_transitions : transitions[from_state.first]) {
                                            std::string sym = sym_transitions.first;
                                            const auto& next_ss = sym_transitions.second;
                                            for (const auto& next_s : next_ss) {
                                                if (next_s == next_state) {
                                                    transitions[from_state.first][sym].erase(next_s);
                                                    if (transitions[from_state.first][sym].empty()) {
                                                        transitions[from_state.first].erase(sym);
                                                    }
                                                    found = true;
                                                    break;
                                                }
                                            }
                                            if (found) {
                                                break;
                                            }
                                        }
                                    }

                                    if (transitions.count(state_k) && transitions[state_k].count(symbol_next)) {
                                        for (const auto& next_s : transitions[state_k][symbol_next]) {
                                            if (next_s == next_state) {
                                                transitions[state_k][symbol_next].erase(next_s);
                                                if (transitions[state_k][symbol_next].empty()) {
                                                    transitions[state_k].erase(symbol_next);
                                                }
                                                break;
                                            }
                                        }
                                    }

                                    std::string simp;
                                    if (!pq.empty()) {
                                        simp = simplify_regex("(" + pq + ")|((" + pk + ")(" + kk + ")*(" + kq + "))");
                                    }
                                    else {
                                        simp = simplify_regex("(" + pk + ")(" + kk + ")*(" + kq + ")");
                                    }
                                    add_transition(from_state.first, simp, next_state);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

private:
    std::vector<std::string> split(const std::string& str, char delimiter) const {
        std::vector<std::string> result;
        std::stringstream ss(str);
        std::string token;
        while (std::getline(ss, token, delimiter)) {
            result.push_back(token);
        }
        return result;
    }

    std::string simplify_regex(std::string regex_str) const {
        std::regex regex;

        // Remove unnecessary parentheses around empty or repeating expressions
        regex_str = std::regex_replace(regex_str, std::regex(R"(\(\*\)|\(\|\)|\(\)\?|\(\)\*|\(None\)\|)"), "");

        // Remove double asterisks
        regex_str = std::regex_replace(regex_str, std::regex(R"(\*\*)"), "*");

        // Remove double vertical bars
        regex_str = std::regex_replace(regex_str, std::regex(R"(\|\|)"), "|");

        // Remove empty parentheses
        regex_str = std::regex_replace(regex_str, std::regex(R"(\(\))"), "");

        // Remove parentheses around single characters
        regex_str = std::regex_replace(regex_str, std::regex(R"(\((\w)\))"), "$1");

        // Remove epsilon before and after a character
        regex_str = std::regex_replace(regex_str, std::regex(R"(E(\w))"), "$1");
        regex_str = std::regex_replace(regex_str, std::regex(R"((\w)E)"), "$1");
        regex_str = std::regex_replace(regex_str, std::regex(R"(E\()"), "(");
        regex_str = std::regex_replace(regex_str, std::regex(R"(\)E)"), ")");
        regex_str = std::regex_replace(regex_str, std::regex(R"(\*E)"), "*");


        std::smatch matches;
        while (std::regex_search(regex_str, matches, std::regex(R"(\(\(([^()]+)\)\))"))) {
            regex_str = std::regex_replace(regex_str, std::regex(R"(\(\(([^()]+)\)\))"), "($1)");
        }

        return regex_str;
    }
};

int main() {
    FiniteAutomaton automaton;
    std::ifstream input_file("input.txt");
    automaton.read_automaton(input_file);
    automaton.make_uniform();

    std::vector<std::string> states;
    for (const auto& state : automaton.states) {
        if (state != "new_start" && state != "new_final") {
            states.push_back(state);
        }
    }
    std::ofstream output_file("out.txt");
    
    std::string ans = "";
    do {
        FiniteAutomaton a_copy = automaton.copy();
        for (const auto& state : states) {
            //cout << state << endl;
            a_copy.delete_state(state);
            //a_copy.print_automaton();
            //output_file << state << "\n";
        }
     
        //output_file << a_copy.end_regex() << "\n";
        if (ans.empty()) {
            ans = a_copy.end_regex();
        }
        if (a_copy.end_regex().size() < ans.size()) {
            ans = a_copy.end_regex();
        }
    } while (std::next_permutation(states.begin(), states.end()));

    output_file << "Регулярка минимальной длины, полученная при переборе всевозможных вариантов исключения состояний:\n";
    output_file << ans << "\n";

    std::map<std::string, int> delet;

    for (auto state_it = states.rbegin(); state_it != states.rend(); ++state_it) {
        const std::string& state = *state_it;
        std::set<std::string> to_states;

        for (const auto& sym_transitions : automaton.transitions[state]) {
            const auto& next_states = sym_transitions.second;
            for (const auto& next_state : next_states) {
                if (next_state != "new_final") {
                    to_states.insert(next_state);
                }
            }
        }

        delet[state] = to_states.size();
    }

    std::vector<std::pair<std::string, size_t>> delet_vector(delet.begin(), delet.end());
    std::sort(delet_vector.begin(), delet_vector.end(), [](const auto& a, const auto& b) {
        return a.second <= b.second;
        });

    for (const auto& pair : delet_vector) {
        automaton.delete_state(pair.first);
    }

    //std::cout << automaton.end_regex() << std::endl;
    output_file << "Регулярка, полученная при оптимальном порядке исключения состояний:\n";
    output_file << automaton.end_regex() << "\n";

    return 0;
}

