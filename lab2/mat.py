import subprocess


def auto_inclusion(automat: str, s: str):
    try:
        # Start mat.exe process
        process = subprocess.Popen(
            ['./mat.exe'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            encoding='utf-8',
            bufsize=1
        )

        # file_path = input("Enter file path (ex. automaton.txt):  ")
        file_path = automat
        process.stdin.write(f"{file_path}\n")
        process.stdin.flush()

        option = "1"

        process.stdin.write(f"{option}\n")
        process.stdin.flush()

        test_string = s
        process.stdin.write(f"{test_string}\n")
        process.stdin.flush()
        result = process.stdout.readline().strip()
        #print(result)
        # print(f"Result: {'Accepted' if result == '1' else 'Not accepted'}")
        return result
        process.wait()


    except Exception as e:
        print(f"Error: {e}")
    finally:
        if 'process' in locals():
            process.terminate()


def auto_equivalence(automat: str, table):
    try:
        # Start mat.exe process
        process = subprocess.Popen(
            ['./mat.exe'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            encoding='utf-8',
            bufsize=1
        )

        # file_path = input("Enter file path (ex. automaton.txt):  ")
        file_path = automat
        process.stdin.write(f"{file_path}\n")
        process.stdin.flush()

        option = "2"

        process.stdin.write(f"{option}\n")
        process.stdin.flush()

        eq_table = str(table).replace("'", "\"")
        #print(eq_table)
        process.stdin.write(f"{eq_table}\n")
        process.stdin.flush()
        result = process.stdout.readline().strip()
        #print(result)
        # print(f"Result: {'Equivalent' if result == '1' else 'Not equivalent'}")
        return result
        process.wait()

    except Exception as e:
        print(f"Error: {e}")
    finally:
        if 'process' in locals():
            process.terminate()


def interact_with_mat():
    try:
        # Start mat.exe process
        process = subprocess.Popen(
            ['./mat.exe'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            bufsize=1
        )

        file_path = input("Enter file path (ex. automaton.txt):  ")
        process.stdin.write(f"{file_path}\n")
        process.stdin.flush()

        while True:
            print("\nSelect option:")
            print("1 - Check string inclusion")
            print("2 - Check automaton equivalence")
            print("3 - Visualize automaton")
            print("4 - Exit")

            option = input("Enter option: ")

            process.stdin.write(f"{option}\n")
            process.stdin.flush()

            if option == "4":
                print("Exiting program")
                break
            elif option == "1":
                test_string = input("Enter string to check: ")
                process.stdin.write(f"{test_string}\n")
                process.stdin.flush()
                result = process.stdout.readline().strip()
                print(result)
                print(f"Result: {'Accepted' if result == '1' else 'Not accepted'}")
            elif option == "2":
                eq_table = input("Enter equivalence table: ")
                process.stdin.write(f"{eq_table}\n")
                process.stdin.flush()
                result = process.stdout.readline().strip()
                print(result)
                print(f"Result: {'Equivalent' if result == '1' else 'Not equivalent'}")
            elif option == "3":
                result = process.stdout.readline().strip()
                print(result)
                # visualize_dfa(automaton, "lab2")
                print("Visualization completed")
            else:
                result = process.stdout.readline().strip()
                print(f"Error: {result}")

        process.wait()

    except Exception as e:
        print(f"Error: {e}")
    finally:
        if 'process' in locals():
            process.terminate()


if __name__ == "__main__":
    interact_with_mat()
