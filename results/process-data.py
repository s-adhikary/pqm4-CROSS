import argparse
import csv
import string
import pandas as pd
import pathlib
import matplotlib.pyplot as plt


def process_table(test: str, cat: str, table: pd.DataFrame):
    print("==========================")
    print("==========PROCESS=========")
    print("==========================")
    new_cols = ["Scheme", "Version", "Problem", "Level", "Variant"]
    print(list(table.columns))
    new_table = pd.DataFrame(columns=new_cols + list(table.columns)[1:])
    # Build better table from decomposing scheme name
    for (_, row) in table.iterrows():
        details = row["Scheme"].split("-")
        new_row = []
        new_row.append("cross")
        # Version
        new_row.append(details[0][-3:])
        # Problem
        new_row.append(details[3])
        # Level
        new_row.append(details[4])
        # Variant
        new_row.append(details[5].split()[0])
        new_row.extend(row[1:])
        new_table.loc[len(new_table)] = new_row

    print(new_table)
    return new_table

def load_data(path: pathlib.Path) -> dict:
    tables = {} 
    with open(path, 'r', encoding='utf-8') as f:
        reader = csv.reader(f)
        test = ""
        category = ""
        start_row = -1
        table_sec = False
        sub_table_sec = 0
        cols = []
        for i, row in enumerate(reader):
            if table_sec:
                if row[0].startswith("Scheme"):
                    if sub_table_sec == 2:
                        table_sec = False
                    # Found sub table
                    start_row = i
                    # Get columns
                    for col in row:
                        if len(col) != 0:
                            cols.append(col)
                # This is kem/signature scheme line
                elif len(row[1]) == 0:
                    # If we've seen a sub_table, commit it
                    if sub_table_sec > 0:
                        print(f"Add table from {start_row} to {i}")
                        print(sub_table_sec)
                        table = tables.get(name, {})
                        table[category] = pd.read_csv(path, skiprows=start_row, nrows=i - start_row - 1, usecols=cols)
                        tables[name] = table
                        start_row = -1
                        cols = []
                    category = row[0]
                    sub_table_sec += 1
            if not table_sec and len(row[1]) == 0:
                if start_row != -1:
                    print(f"Add table from {start_row} to {i}")
                    table = tables.get(name, {})
                    table[category] = pd.read_csv(path, skiprows=start_row, nrows=i - start_row - 1, usecols=cols)
                    tables[name] = table
                    start_row = -1
                    cols = []
                    sub_table_sec = 0
                name = row[0]
                table_sec = True
    return tables


def main():
    #TODO: fix formatting of description in output
    parser = argparse.ArgumentParser(description='''\
                                     Process the benchmarking csv data produced by first benchmarking then
                                     running `python3 convert_benchmarks.py csv > [name].csv`.
                                     Should produce useful graphics and better sorted dataframes for ease
                                     of analysis
                                     ''')



    parser.add_argument("-f", "--file", help="The csv produced by the benchmarks.", type=pathlib.Path, required=True)

    args = parser.parse_args()
    #pd.set_option('display.max_columns', None)

    tables = load_data(args.file)

    for test, value in tables.items():
        #print(f"Table '{test}':")
        for cat, table, in value.items():
            if len(table) == 0:
                continue
            #print(f"\t{cat}:\n{table.head()}")
            new_table = process_table(test, cat, table)
            new_table.to_csv(f"{"_".join(test.split())}-{"_".join(cat.split())}.csv")


if __name__ == "__main__":
    main()
