from equivalence import db, expression, tree

import z3


def build_alias_context(t1: tree.Node, t2: tree.Node):
    context = {}

    def traverse(t: tree.Node):
        if isinstance(t, tree.Scan):
            if t.relation not in context:
                context[t.relation] = t
            if t.alias not in context:
                context[t.alias] = t

        for child in t.children:
            traverse(child)

    traverse(t1)
    traverse(t2)

    return context


def build_solver_program(declarations, assertions):
    declarations_str = "\n".join(declarations)
    assertions_str = "\n".join(assertions)

    return f"{declarations_str}\n{assertions_str}"


def build_values_context(relation, rows):
    declarations = set()
    type_map = {int: "Int", str: "String", bool: "Bool"}
    for i, value in enumerate(rows[0]):
        declarations.add(
            f"(declare-const {relation}_column{i + 1} {type_map[type(value)]})"
        )

    assertions = []
    for row in rows:
        row_assertions = []
        for i, value in enumerate(row):
            row_assertions.append(f"(= {relation}_column{i + 1} {value})")

        assertions.append(f"(and {' '.join(row_assertions)})")

    return declarations, {f"(assert (or {' '.join(assertions)}))"}


class Checker:
    def __init__(self, plan_generator: db.PlanGenerator):
        self.plan_generator = plan_generator
        self.solver = z3.Solver()

        self.schema_info = {}

        self.alias_context = {}
        self.column_refs = []

        self.declarations = set()
        self.assertions = set()

    def check(self, query1, query2):
        prepared_query1 = self.plan_generator.init_values_relations(query1)
        prepared_query2 = self.plan_generator.init_values_relations(query2)

        if prepared_query1 != query1:
            query1 = prepared_query1

        if prepared_query2 != query2:
            query2 = prepared_query2

        values_relations = self.plan_generator.values_relations
        for relation in values_relations:
            declarations, assertions = build_values_context(
                relation, values_relations[relation]
            )
            self.declarations = self.declarations | declarations
            self.assertions = self.assertions | assertions

        plan_dict1 = self.plan_generator.get_json(query1)
        plan_dict2 = self.plan_generator.get_json(query2)

        self.schema_info = self.plan_generator.get_schema_info()

        self.plan_generator.drop_values_relations()

        plan_tree1 = tree.from_dict(plan_dict1)
        plan_tree2 = tree.from_dict(plan_dict2)

        normalized_tree1 = tree.normalize(plan_tree1)
        normalized_tree2 = tree.normalize(plan_tree2)

        self.alias_context = build_alias_context(
            normalized_tree1, normalized_tree2
        )

        return self.compare_trees(normalized_tree1, normalized_tree2)

    def add_column_refs(self, from_expr):
        if isinstance(from_expr, expression.BinOp):
            self.add_column_refs(from_expr.left_expr)
            self.add_column_refs(from_expr.right_expr)

        if isinstance(from_expr, expression.Not):
            self.add_column_refs(from_expr.expr)

        if isinstance(from_expr, expression.ColumnRef):
            self.column_refs.append(from_expr)

    def make_declaration(self, column_ref):
        type_map = {"integer": "Int", "int": "Int", "text": "String"}

        relation = column_ref.relation

        while relation != self.alias_context[relation].relation:
            relation = self.alias_context[relation].relation

        column_type = self.schema_info[relation][column_ref.name].column_type

        return f"(declare-const {column_ref} {type_map[column_type]})"

    def compare_expressions(self, e1_str, e2_str):
        self.solver.reset()

        e1 = expression.from_str(e1_str)
        e2 = expression.from_str(e2_str)

        self.add_column_refs(e1)
        self.add_column_refs(e2)

        solver_declarations = self.declarations.copy()
        solver_assertions = self.assertions.copy()

        for column_ref in self.column_refs:
            solver_declarations.add(self.make_declaration(column_ref))

            if column_ref.relation is None:
                continue

            target_relation = self.alias_context[column_ref.relation].relation
            target_column_ref = expression.ColumnRef(
                column_ref.name, target_relation
            )
            solver_declarations.add(self.make_declaration(target_column_ref))

            assertion = f"(assert (= {column_ref} {target_column_ref}))"
            solver_assertions.add(assertion)

        # solver_assertions.add(f"(assert (not (= {e1} {e2})))")
        #
        # solver_program = " ".join(solver_declarations)
        # solver_program += " "
        # solver_program += " ".join(solver_assertions)

        # test equivalence
        program_eq = build_solver_program(
            solver_declarations,
            solver_assertions | {f"(assert (not (= {e1} {e2})))"},
        )
        self.solver.from_string(program_eq)
        if not self.solver.check() == z3.unsat:
            return False, None

        # test actual value for unsat
        program_value = build_solver_program(
            solver_declarations, solver_assertions | {f"(assert {e1})"}
        )
        self.solver.from_string(program_value)
        if self.solver.check() == z3.unsat:
            return True, True

        return True, False

    def compare_trees(self, t1: tree.Node, t2: tree.Node):
        if type(t1) is not type(t2):
            return False

        if len(t1.children) != len(t2.children):
            return False

        if isinstance(t1, tree.Scan):
            return t1 == t2

        if isinstance(t1, tree.Result):
            if len(t1.output) != len(t2.output):
                return False

            for column1, column2 in zip(t1.output, t2.output):
                expr1 = expression.from_str(column1)
                expr2 = expression.from_str(column2)

                self.solver.from_string(f"(assert (not (= {expr1} {expr2})))")

                if not self.solver.check() == z3.unsat:
                    return False

                self.solver.reset()

            return True

        if isinstance(t1, tree.Filter) and isinstance(t2, tree.Filter):
            equivalent, unsat = self.compare_expressions(
                t1.expression, t2.expression
            )

            if not equivalent:
                return False

            if unsat:
                return True

            return self.compare_trees(t1.children[0], t2.children[0])

        if isinstance(t1, tree.Limit) and isinstance(t2, tree.Limit):
            return t1.rows == t2.rows

        through_ops = (
            tree.Product,
            tree.Union,
            tree.UnionAll,
            tree.Intersect,
            tree.IntersectAll,
            tree.Except,
            tree.ExceptAll,
            tree.Aggregate,
            tree.Sort,
        )
        if isinstance(t1, through_ops):
            for child1, child2 in zip(t1.children, t2.children):
                if not self.compare_trees(child1, child2):
                    return False

            return True

        raise NotImplementedError(type(t1))
