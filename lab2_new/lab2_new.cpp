using namespace std;

#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <regex>

class FiniteAutomaton {
public:
    std::vector<std::string> states;
    std::string start_state;
    std::vector<std::string> final_states;
    std::unordered_map<std::string, std::unordered_map<std::string, std::string>> transitions;

    FiniteAutomaton() = default;

    FiniteAutomaton copy() const {
        FiniteAutomaton new_automaton;
        new_automaton.states = states;
        new_automaton.start_state = start_state;
        new_automaton.final_states = final_states;

        for (const auto& from_state : transitions) {
            for (const auto& entry : from_state.second) {
                new_automaton.add_transition(from_state.first, entry.first, entry.second);
            }
        }

        return new_automaton;
    }

    std::string end_regex() const {
        for (const auto& entry : transitions.at("new_start")) {
            if (entry.second == "new_final") {
                return entry.first;
            }
        }
        return "";
    }

    void add_transition(const std::string& from_state, const std::string& symbol, const std::string& to_state) {
        transitions[from_state][symbol] = to_state;
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
            for (const auto& entry : from_state.second) {
                std::cout << "(" << from_state.first << ", " << entry.first << ") -> " << entry.second << "\n";
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
            for (const auto& entry : from_state_entry.second) {
                if (from_state_entry.first == from_state && entry.second == to_state) {
                    return entry.first;
                }
            }
        }
        return "";
    }

    void delete_state(const std::string& state_k) {
        auto transitions_copy = transitions;

        std::string kk = "";
        for (const auto& entry : transitions_copy[state_k]) {
            if (entry.second == state_k && kk.empty()) {
                kk = entry.first;
                transitions[state_k].erase(entry.first);
            }
            else if (entry.second == state_k && !kk.empty()) {
                kk += "|" + entry.first;
                transitions[state_k].erase(entry.first);
            }
        }

        for (auto& from_state_entry : transitions_copy) {
            for (const auto& entry : from_state_entry.second) {
                if (entry.second == state_k && from_state_entry.first != state_k) {
                    transitions[from_state_entry.first].erase(entry.first);
                    std::string pk = entry.first;

                    for (const auto& symbol_next_entry : transitions_copy[state_k]) {
                        if (symbol_next_entry.second != state_k) {
                            std::string kq = symbol_next_entry.first;
                            std::string pq = find_symbol_for_transition(from_state_entry.first, symbol_next_entry.second);
                           
                            if (!pq.empty()) {
                                for (const auto& sym_entry : transitions[from_state_entry.first]) {
                                    if (sym_entry.second == symbol_next_entry.second) {
                                        transitions[from_state_entry.first].erase(sym_entry.first);
                                        break;
                                    }
                                }
                            }

                            if (transitions.count(state_k) && transitions[state_k].count(symbol_next_entry.first)) {
                                transitions[state_k].erase(symbol_next_entry.first);
                            }

                            std::string simp;
                            if (!pq.empty()) {
                                simp = simplify_regex("(" + pq + ")|((" + pk + ")(" + kk + ")*(" + kq + "))");
                            }
                            else {
                                simp = simplify_regex("(" + pk + ")(" + kk + ")*(" + kq + ")");
                            }
                            add_transition(from_state_entry.first, simp, symbol_next_entry.second);
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

    //std::replace(ans.begin(), ans.end(), 'E', 'E');
    //std::ofstream output_file("out.txt");
    output_file << ans;

    return 0;
}

