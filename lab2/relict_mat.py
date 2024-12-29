import json
import requests


# Глобальные переменные для URL-адресов
CHECK_WORD_URL = "http://127.0.0.1:8095/checkWord"
CHECK_TABLE_URL = "http://127.0.0.1:8095/checkTable"


def membershipQuery(word):
    if word == "":
        word = "ε"

    query_body = {
        "word": word
    }
    try:
        response = requests.post(
            CHECK_WORD_URL,
            data=json.dumps(query_body),
            headers={"Content-Type": "application/json"}
        )
        response_json = response.json()
        return response_json["response"]
    except Exception as e:
        print("Произошла ошибка при проверке на включение :-( =>", e)
        return None

def equivalenceQuery(S, S_extra, E, table):
    query_body = {
        "main_prefixes": S,
        "non_main_prefixes": S_extra,
        "suffixes": E,
        "table": table
    }
    try:
        response = requests.post(
            CHECK_TABLE_URL,
            data=json.dumps(query_body),
            headers={"Content-Type": "application/json"}
        )

    except Exception as e:
        print("Произошла ошибка при проверке на эквивалентность :-( =>", e)
        return None
    response = response.json()
    if response["type"] == True and response["response"] != None:
        return (0, response["response"])

    elif response["type"] == False:
        return (1, response["response"])
    else:
        return (2, "")

