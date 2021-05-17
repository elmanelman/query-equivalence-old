import argparse

from equivalence import db, checker

if __name__ == "__main__":
    argument_parser = argparse.ArgumentParser(
        description="SQL query equivalence checker"
    )
    argument_parser.add_argument(
        "schema", help="DDL script for the schema that queries use"
    )
    argument_parser.add_argument(
        "q1", help="the file containing the first SQL query"
    )
    argument_parser.add_argument(
        "q2", help="the file containing the second SQL query"
    )
    argument_parser.add_argument(
        "-c",
        "--connection-string",
        required=True,
        help="PostgreSQL connection string (quoted)",
    )
    arguments = argument_parser.parse_args()

    schema_filename = arguments.schema
    q1_filename = arguments.q1
    q2_filename = arguments.q2
    connection_string = arguments.connection_string

    plan_generator = db.PlanGenerator(connection_string)

    with open(schema_filename, "r") as schema_file:
        schema_script = schema_file.read()

        plan_generator.use_schema(schema_script)

    checker = checker.Checker(plan_generator)

    with open(q1_filename, "r") as q1_file:
        q1 = q1_file.read()

    with open(q2_filename, "r") as q2_file:
        q2 = q2_file.read()

    result = checker.check(q1, q2)
    answer = {
        False: "The queries are not equivalent",
        True: "The queries are equivalent",
    }

    print(answer[result])
