from equivalence import db, expression, tree

import z3


def build_alias_context(t1: tree.Node, t2: tree.Node):
    context = {}

    def traverse(t1: tree.Node, t2: tree.Node):
        if type(t1) is not type(t2):
            return False

        if len(t1.children) != len(t2.children):
            return False

        if isinstance(t1, tree.Scan) and isinstance(t2, tree.Scan):
            context[t1.alias] = t1
            context[t2.alias] = t2

        for child1, child2 in zip(t1.children, t2.children):
            traverse(child1, child2)

    traverse(t1, t2)

    return context


class Checker:
    def __init__(self, plan_generator: db.PlanGenerator):
        self.plan_generator = plan_generator
        self.solver = z3.Solver()

        self.schema_info = {}

        self.alias_context = {}
        self.column_refs = []

    def check(self, query1, query2):
        self.schema_info = self.plan_generator.get_schema_info()

        plan_dict1 = self.plan_generator.get_json(query1)
        plan_dict2 = self.plan_generator.get_json(query2)

        plan_tree1 = tree.from_dict(plan_dict1)
        plan_tree2 = tree.from_dict(plan_dict2)

        normalized_tree1 = tree.normalize(plan_tree1)
        normalized_tree2 = tree.normalize(plan_tree2)

        self.alias_context = build_alias_context(normalized_tree1, normalized_tree2)

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
        type_map = {
            "integer": "Int",
            "int": "Int",
            "text": "String"
        }

        # print(column_ref.relation, column_ref.name)

        relation = column_ref.relation
        while relation != self.alias_context[relation].relation:
            relation = self.alias_context[relation].relation

        column_type = self.schema_info[relation][column_ref.name].column_type

        return f"(declare-const {column_ref} {type_map[column_type]})"

    def compare_expressions(self, e1_str, e2_str):
        e1 = expression.from_str(e1_str)
        e2 = expression.from_str(e2_str)

        self.add_column_refs(e1)
        self.add_column_refs(e2)

        solver_declarations = set()
        solver_assertions = set()

        for column_ref in self.column_refs:
            solver_declarations.add(self.make_declaration(column_ref))

            if column_ref.relation is None:
                continue

            target_relation = self.alias_context[column_ref.relation].relation
            target_column_ref = expression.ColumnRef(column_ref.name, target_relation)
            solver_declarations.add(self.make_declaration(target_column_ref))

            assertion = f"(assert (= {column_ref} {target_column_ref}))"
            solver_assertions.add(assertion)

        solver_assertions.add(f"(assert (not (= {e1} {e2})))")

        solver_program = " ".join(solver_declarations)
        solver_program += " "
        solver_program += " ".join(solver_assertions)

        # print("declarations", solver_declarations)
        # print("assertions", solver_assertions)

        self.solver.from_string(solver_program)

        # print(self.solver.sexpr())

        if not self.solver.check() == z3.unsat:
            # print(self.solver.model())
            return False

        self.solver.reset()

        return True

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

                # print(self.solver.sexpr(), self.solver.check())

                if not self.solver.check() == z3.unsat:
                    return False

                self.solver.reset()

            return True

        if isinstance(t1, tree.Filter):
            if not self.compare_expressions(t1.expression, t2.expression):
                return False

            return self.compare_trees(t1.children[0], t2.children[0])

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
