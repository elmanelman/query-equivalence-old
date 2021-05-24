import functools

import pglast
from pglast.enums import BoolExprType, A_Expr_Kind


def get_ast(expr):
    """Get the AST of the SQL expression by placing it within query and parsing it

    :param expr: expression string
    :return: expression AST
    """
    parsed = pglast.parse_sql(f"select {expr}")
    dict_query = (
        0,
        "RawStmt",
        "stmt",
        "SelectStmt",
        "targetList",
        0,
        "ResTarget",
        "val",
    )

    for key in dict_query:
        parsed = parsed[key]

    return parsed


def from_ast(root):
    """Construct an expression from the specified PostgreSQL parsed node

    :param root: parse tree root
    :return: expression
    """

    def traverse(node):
        if len(node.keys()) != 1:
            raise ValueError("ast node must contain exactly one key")

        node_type = (*node,)[0]

        if node_type == "BoolExpr":
            bool_expression = node["BoolExpr"]
            bool_operator = bool_expression["boolop"]
            arguments = bool_expression["args"]

            if bool_operator == BoolExprType.NOT_EXPR:
                if len(arguments) != 1:
                    msg = "not operator must take exactly one argument"
                    raise ValueError(msg)

                return Not(traverse(arguments[0]))

            expr_type_map = {
                BoolExprType.AND_EXPR: And,
                BoolExprType.OR_EXPR: Or,
            }

            op_constructor = expr_type_map[bool_operator]
            joined_args = functools.reduce(
                lambda a, b: op_constructor(a, b),
                map(traverse, arguments[1:]),
                traverse(arguments[0]),
            )

            return joined_args
        elif node_type == "ColumnRef":
            fields = node["ColumnRef"]["fields"]
            if len(fields) == 1:
                column_name = fields[0]["String"]["str"]

                return ColumnRef(column_name)
            elif len(fields) == 2:
                relation = fields[0]["String"]["str"]
                column_name = fields[1]["String"]["str"]

                return ColumnRef(column_name, relation)
            else:
                msg = "unsupported column reference with >2 fields"

                raise ValueError(msg)
        elif node_type == "A_Expr":
            a_expr = node["A_Expr"]
            kind = a_expr["kind"]

            arguments = []
            if "lexpr" in a_expr:
                arguments.append(a_expr["lexpr"])
            if "rexpr" in a_expr:
                arguments.append(a_expr["rexpr"])

            if kind == A_Expr_Kind.AEXPR_OP:
                op_name = a_expr["name"][0]["String"]["str"]
                op_name_map = {
                    # comparison
                    "=": Equal,
                    "!=": NotEqual,
                    "<>": NotEqual,
                    "<": Less,
                    "<=": LessOrEqual,
                    ">": Greater,
                    ">=": GreaterOrEqual,
                    # arithmetic
                    "+": Add,
                    "-": Subtract,
                    "*": Multiply,
                    "/": Divide,
                    "^": Power,
                }

                if op_name not in op_name_map:
                    raise NotImplementedError(f"unknown operator: {op_name}")

                return op_name_map[op_name](*map(traverse, arguments))
            else:
                raise NotImplementedError(f"unknown a_expr kind: {kind}")
        elif node_type == "A_Const":
            const_expr = node["A_Const"]
            const_type = (*const_expr["val"],)[0]

            if const_type == "Null":
                return Null()

            const_container = const_expr["val"][const_type]

            if const_type == "Integer":
                return Const(const_container["ival"])
            if const_type == "Float":
                return Const(float(const_container["str"]))
            if const_type == "String":
                return Const(const_container["str"])

            raise NotImplementedError(f"unknown const type: {const_type}")
        elif node_type == "TypeCast":
            # TODO: consider type casting

            return traverse(node["TypeCast"]["arg"])
        else:
            raise NotImplementedError(
                f"unknown expression node type: {list(node.keys())[0]}"
            )

    return traverse(root)


def from_str(s):
    if s.upper() == "FALSE":
        return Const(False)
    if s.upper() == "TRUE":
        return Const(True)

    return from_ast(get_ast(s))


class Null:
    pass


class Const:
    """Constant value of an arbitrary type"""

    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return self.value == other.value

    def __str__(self):
        if type(self.value) is bool:
            return str(self.value).lower()

        if type(self.value) is str:
            return f'"{self.value}"'

        return str(self.value)


class ColumnRef:
    """Reference to a column in a relation or subquery with alias"""

    def __init__(self, name, relation=None):
        self.name = name
        self.relation = relation

    def __str__(self):
        if self.relation is not None:
            return f"{self.relation}_{self.name}"
        else:
            return self.name


class BinOp:
    def __init__(self, left_expr, right_expr):
        self.left_expr = left_expr
        self.right_expr = right_expr

    @property
    def op(self):
        raise NotImplementedError

    def __str__(self):
        return f"({self.op} {self.left_expr} {self.right_expr})"


class And(BinOp):
    op = "and"


class Or(BinOp):
    op = "or"


class Not:
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return f"(not {self.expr})"


class Equal(BinOp):
    op = "="


class NotEqual(BinOp):
    op = "!="


class Less(BinOp):
    op = "<"


class LessOrEqual(BinOp):
    op = "<="


class Greater(BinOp):
    op = ">"


class GreaterOrEqual(BinOp):
    op = ">="


class Add(BinOp):
    op = "+"


class Subtract(BinOp):
    op = "-"


class Multiply(BinOp):
    op = "*"


class Divide(BinOp):
    op = "/"


class Power(BinOp):
    op = "^"
