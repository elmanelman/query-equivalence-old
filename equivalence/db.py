import collections
import dataclasses
import secrets
import typing

import pglast
import psycopg2


@dataclasses.dataclass(frozen=True)
class ConnectionParameters:
    """Represents regular PostgreSQL connection parameters"""

    user: str
    password: str
    dbname: str
    host: str = "localhost"
    port: int = 5432


@dataclasses.dataclass(frozen=True)
class ColumnInfo:
    """Represents information about a specific column"""

    column_name: str
    column_type: str
    is_nullable: bool
    ordinal_position: int


class PlanGenerator:
    def __configure_planner(self):
        """
        Configures PostgreSQL query planner to use
        simplified (though not the most effective)
        execution plans
        """
        parameters_to_off = [
            # use sequential scans
            "enable_indexscan",
            "enable_bitmapscan",
            "enable_tidscan",
            # use nested loop joins
            "enable_hashjoin",
            "enable_mergejoin",
            # disable automatic materialization
            "enable_material",
        ]

        with self.connection.cursor() as cursor:
            for parameter in parameters_to_off:
                cursor.execute(f"set {parameter} = 'off'")

            # disable parallelism
            cursor.execute("set max_parallel_workers_per_gather = 0")

    def __init__(
            self,
            connection_parameters: typing.Union[ConnectionParameters, str],
            schema_script=None,
    ):
        if type(connection_parameters) is str:
            self.connection = psycopg2.connect(connection_parameters)
        else:
            self.connection = psycopg2.connect(
                **dataclasses.asdict(connection_parameters)
            )

        self.schema_name = "public"
        self.schema_script = schema_script
        if schema_script is not None:
            self.use_schema(schema_script)

        self.__configure_planner()

    def use_schema(self, schema_script):
        """Creates a new schema from the script

        :param schema_script: DDL script to use
        """
        if self.schema_script is not None:
            current_schema_fingerprint = pglast.fingerprint(self.schema_script)
            given_schema_fingerprint = pglast.fingerprint(schema_script)
            if current_schema_fingerprint == given_schema_fingerprint:
                return

        with self.connection.cursor() as cursor:
            self.schema_name = f"qe_{secrets.token_hex(4)}"
            self.schema_script = schema_script

            cursor.execute(f"create schema {self.schema_name}")
            cursor.execute(f"set search_path = '{self.schema_name}'")
            cursor.execute(schema_script)

    def get_schema_info(self, schema_name=None):
        """Gets information about the schema

        :param schema_name: schema name
        :return: dictionary with schema information
        """
        if schema_name is None:
            if self.schema_name is not None:
                schema_name = self.schema_name
            else:
                raise ValueError("schema name not specified")

        query = """
            select
                t.table_name,
                c.column_name,
                c.data_type,
                c.is_nullable,
                c.ordinal_position
            from information_schema.tables t
            join information_schema.columns c
                on t.table_name = c.table_name
            where t.table_schema = %(schema_name)s
            order by t.table_name, c.ordinal_position"""

        schema_info = collections.defaultdict(dict)

        with self.connection.cursor() as cursor:
            cursor.execute(query, {"schema_name": schema_name})

            schema_info_rows = cursor.fetchall()
            for row in schema_info_rows:
                (
                    table_name,
                    column_name,
                    data_type,
                    is_nullable,
                    ordinal_position,
                ) = row
                bool_map = {"NO": False, "YES": True}
                column_info = ColumnInfo(
                    column_name,
                    data_type,
                    bool_map[is_nullable],
                    ordinal_position,
                )
                schema_info[table_name][column_name] = column_info

        return dict(schema_info)

    def drop_schema(self):
        """Drops current schema"""
        with self.connection.cursor() as cursor:
            cursor.execute("set search_path = 'public'")
            cursor.execute(f"drop schema {self.schema_name} cascade")

            self.schema_name = "public"

    def get_json(self, query):
        """Requests a query execution plan from the PostgreSQL planner.

        :param query: selection query
        :return: dictionary of the execution plan tree
        """
        with self.connection.cursor() as cursor:
            explain_query = f"explain (format json, verbose) {query}"

            cursor.execute(explain_query)
            plan_row = cursor.fetchone()

            return plan_row[0][0]["Plan"]
