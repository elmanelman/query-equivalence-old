import copy
import uuid
from abc import abstractmethod, ABCMeta

import graphviz


class Node(metaclass=ABCMeta):
    def __init__(self, output, children=None):
        self.uuid = str(uuid.uuid4())

        self.output = output

        if children is None:
            self.children = []
        else:
            self.children = children

    def compare_structure(self, other):
        """Compare two nodes by recursively comparing nodes types only

        :param other: node to compare with
        :return: comparison result
        """
        if type(self) is not type(other):
            return False
        if len(self.children) != len(other.children):
            return False
        for child, other_child in zip(self.children, other.children):
            if not child.compare_structure(other_child):
                return False

        return True

    @abstractmethod
    def graph_label(self):
        return ""

    @abstractmethod
    def graph_node(self, graph):
        return

    def to_graph(self):
        graph = graphviz.Digraph(
            node_attr={"shape": "box"}, edge_attr={"arrowhead": "none"}
        )

        def traverse(node):
            node.graph_node(graph)
            for child in node.children:
                graph.edge(node.uuid, child.uuid)
                traverse(child)

        traverse(self)

        return graph.unflatten()


class Scan(Node):
    """Selects all rows from the relation"""

    def __init__(self, output, relation, alias=None):
        super().__init__(output)

        self.relation = relation
        self.alias = alias if alias is not None else relation

    def __eq__(self, other):
        return self.relation == other.relation

    def graph_label(self):
        if self.relation == self.alias:
            return self.relation
        else:
            return f"{self.relation} as {self.alias}"

    def graph_node(self, graph):
        graph.node(self.uuid, self.graph_label())


class Result(Node):
    """Selects a row with only constant values"""

    def __init__(self, output):
        super().__init__(output)

    def graph_label(self):
        return ", ".join(self.output)

    def graph_node(self, graph):
        graph.node(self.uuid, self.graph_label())


class Filter(Node):
    """
    Filters rows from a child node by the predicate expression
    """

    def __init__(self, output, children, expression):
        super().__init__(output, children)

        self.expression = expression

    def graph_label(self):
        return "σ" + self.expression

    def graph_node(self, graph):
        graph.node(self.uuid, self.graph_label())


class Aggregate(Node):
    """Aggregates rows from a child node by the specified key"""

    def __init__(self, output, children, key):
        super().__init__(output, children)

        self.key = key

    def graph_label(self):
        if len(self.key) == 0:
            return f"γ\n{', '.join(self.output)}"
        else:
            return f"γ({', '.join(self.key)})\n{', '.join(self.output)}"

    def graph_node(self, graph):
        graph.node(self.uuid, self.graph_label())


class Product(Node):
    """Cartesian product of some nodes"""

    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "×"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class Union(Node):
    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "∪"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class UnionAll(Node):
    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "∪ᴬᴸᴸ"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class Intersect(Node):
    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "∩"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class IntersectAll(Node):
    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "∩ᴬᴸᴸ"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class Except(Node):
    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "∖"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class ExceptAll(Node):
    def __init__(self, output, children):
        super().__init__(output, children)

    def graph_label(self):
        return "∖ᴬᴸᴸ"

    def graph_node(self, graph):
        graph.node(
            self.uuid, self.graph_label(), _attributes={"shape": "circle"}
        )


class Sort(Node):
    def __init__(self, output, children, key):
        super().__init__(output, children)

        self.key = key

    def graph_label(self):
        return f"order by\n{', '.join(self.key)}"

    def graph_node(self, graph):
        graph.node(self.uuid, self.graph_label())


def from_dict(plan_dict) -> Node:
    def get_child(node_dict):
        if len(node_dict["Plans"]) != 1:
            # print(node_dict["Node Type"], len(node_dict["Plans"]))
            raise ValueError("get_child supports only unary nodes")

        return node_dict["Plans"][0]

    def traverse(node_dict):
        node_type = node_dict["Node Type"]

        if "Output" not in node_dict:
            output = node_dict["Plans"][0]["Output"]
        else:
            output = node_dict["Output"]

        if node_type == "Seq Scan":
            relation = node_dict["Relation Name"]
            alias = node_dict["Alias"]
            scan_node = Scan(output, relation, alias)

            if "Filter" in node_dict:
                return Filter(output, [scan_node], node_dict["Filter"])

            return scan_node
        elif node_type == "Result":
            if "One-Time Filter" in node_dict:
                if node_dict["One-Time Filter"][:4] == "NULL":
                    return Filter(output, [Result(output)], "FALSE")

                return Filter(
                    output, [Result(output)], node_dict["One-Time Filter"]
                )

            return Result(output)
        elif node_type == "Subquery Scan":
            return traverse(get_child(node_dict))
        elif node_type == "Nested Loop":
            children = [traverse(d) for d in node_dict["Plans"]]

            if node_dict["Join Type"] == "Inner":
                pass
            elif node_dict["Join Type"] == "Left":
                raise NotImplementedError("left join")
            elif node_dict["Join Type"] == "Right":
                raise NotImplementedError("right join")

            if "Join Filter" in node_dict:
                filter_expression = node_dict["Join Filter"]

                return Filter(
                    output, [Product(output, children)], filter_expression
                )

            return Product(output, children)
        elif node_type == "Aggregate":
            key = node_dict["Group Key"] if "Group Key" in node_dict else []
            children = [traverse(d) for d in node_dict["Plans"]]

            return Aggregate(output, children, key)
        elif node_type == "Append":
            children = [traverse(d) for d in node_dict["Plans"]]

            return UnionAll(output, children)
        elif node_type == "Unique":
            child_dict = get_child(node_dict)
            if child_dict["Node Type"] == "Sort":
                child_child_dict = get_child(child_dict)
                if child_child_dict["Node Type"] == "Append":
                    return Union(
                        output,
                        [traverse(d) for d in child_child_dict["Plans"]],
                    )
        elif node_type == "SetOp":
            operator = node_dict["Command"]
            operator_map = {
                "Intersect": Intersect,
                "Intersect All": IntersectAll,
                "Except": Except,
                "Except All": ExceptAll,
            }

            child_dict = get_child(node_dict)
            if child_dict["Node Type"] == "Sort":
                child_dict = get_child(child_dict)

            children = [traverse(d) for d in child_dict["Plans"]]

            return operator_map[operator](output, children)
        elif node_type == "Sort":
            key = node_dict["Sort Key"]
            children = [
                traverse(child_dict) for child_dict in node_dict["Plans"]
            ]

            return Sort(output, children, key)
        else:
            # pprint(node_dict)

            raise ValueError("unknown node type: " + node_type)

    root = traverse(plan_dict)

    return root


def is_filter(node):
    return isinstance(node, Filter)


def is_product(node):
    return isinstance(node, Product)


def pull_filters(tree):
    supported_operators = (Product, Sort)

    def traverse(node):
        traversed_children = [traverse(child) for child in node.children]

        if isinstance(node, supported_operators):
            filters = []
            result_children = []

            for i, child in enumerate(traversed_children):
                if is_filter(child):
                    filters.append(child.expression)
                    result_children.append(child.children[0])
                else:
                    result_children.append(child)

            if len(filters) == 0:
                return node

            node_copy = copy.deepcopy(node)
            node_copy.children = result_children

            return Filter(node.output, [node_copy], " AND ".join(filters))
        elif is_filter(node) and is_filter(traversed_children[0]):
            return Filter(
                node.output,
                traversed_children[0].children,
                f"{node.expression} AND {traversed_children[0].expression}",
            )
        else:
            node_copy = copy.deepcopy(node)
            node_copy.children = traversed_children
            return node_copy

    traversed = traverse(tree)

    return traversed


def merge_products(tree):
    def traverse(node):
        traversed_children = [traverse(child) for child in node.children]

        if is_product(node):
            result_children = []

            for child in traversed_children:
                if is_product(child):
                    result_children += child.children
                else:
                    result_children.append(child)

            node_copy = copy.deepcopy(node)
            node_copy.children = result_children

            return node_copy
        else:
            node_copy = copy.deepcopy(node)
            node_copy.children = traversed_children
            return node_copy

    traversed = traverse(tree)

    return traversed


def normalize(tree):
    return merge_products(pull_filters(tree))
