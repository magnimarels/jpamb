#!/usr/bin/env python3
"""A very stupid syntactic analysis, that only checks for assertion errors."""

import logging
import sys
from pathlib import Path

import tree_sitter
import tree_sitter_java

import jpamb


def main():
    methodid = jpamb.getmethodid(
        "syntaxer",
        "1.0",
        "Cooked-Pikachu",
        ["syntactic", "python"],
        for_science=True,
    )

    JAVA_LANGUAGE = tree_sitter.Language(tree_sitter_java.language())
    parser = tree_sitter.Parser(JAVA_LANGUAGE)

    log = logging
    log.basicConfig(level=logging.DEBUG)

    suite, _ = jpamb.setup()

    srcfile = suite.sourcefile(methodid.classname).relative_to(Path.cwd())

    with open(srcfile, "rb") as f:
        log.debug("parse sourcefile %s", srcfile)
        tree = parser.parse(f.read())

    simple_classname = str(methodid.classname.name)

    log.debug(f"{simple_classname}")

    class_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        f"""
        (class_declaration 
            name: ((identifier) @class-name 
                   (#eq? @class-name "{simple_classname}"))) @class
    """,
    )

    for node in tree_sitter.QueryCursor(class_q).captures(tree.root_node)["class"]:
        break
    else:
        log.error(f"could not find a class of name {simple_classname} in {srcfile}")
        sys.exit(-1)

    method_name = methodid.extension.name

    method_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        f"""
        (method_declaration name: 
          ((identifier) @method-name (#eq? @method-name "{method_name}"))
        ) @method
    """,
    )

    for snode in tree_sitter.QueryCursor(method_q).captures(node)["method"]:
        if not (p := snode.child_by_field_name("parameters")):
            log.debug(f"Could not find parameteres of {method_name}")
            continue

        params = [c for c in p.children if c.type == "formal_parameter"]

        if len(params) != len(methodid.extension.params):
            continue

        for tn, t in zip(methodid.extension.params, params):
            if (tp := t.child_by_field_name("type")) is None:
                break

            if tp.text is None:
                break

            # todo check for type.
        else:
            break
    else:
        log.warning(
            f"could not find a method of name {method_name} in {simple_classname}"
        )
        sys.exit(-1)

    body = snode.child_by_field_name("body")
    assert body and body.text
    for t in body.text.splitlines():
        log.debug("line: %s", t.decode())

    body_range = (body.start_byte, body.end_byte)

    def is_top_level(n):
        return n.parent is not None and (n.parent.start_byte, n.parent.end_byte) == body_range


    assert_q = tree_sitter.Query(JAVA_LANGUAGE, """(assert_statement) @assert""")

    assert_false_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """(assert_statement (false)) @assert-false""",
    )

    assert_true_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """(assert_statement (true)) @assert-true""",
    )

    all_asserts_raw = tree_sitter.QueryCursor(assert_q).captures(body).get("assert", [])
    assert_false_nodes = tree_sitter.QueryCursor(assert_false_q).captures(body).get("assert-false", [])
    assert_true_nodes = tree_sitter.QueryCursor(assert_true_q).captures(body).get("assert-true", [])

    assert_true_ranges = {(n.start_byte, n.end_byte) for n in assert_true_nodes}
    all_asserts = [
        n for n in all_asserts_raw if (n.start_byte, n.end_byte) not in assert_true_ranges
    ]

    top_level_asserts = [n for n in all_asserts if is_top_level(n)]
    nested_asserts = [n for n in all_asserts if not is_top_level(n)]

    top_level_assert_false = [n for n in assert_false_nodes if is_top_level(n)]
    nested_assert_false = [n for n in assert_false_nodes if not is_top_level(n)]

    if top_level_assert_false:
        print("assertion error;found-assert-always")
    elif top_level_asserts:
        print("assertion error;found-assert-reachable")
    elif nested_assert_false or nested_asserts:
        print("assertion error;found-assert-conditional")
    else:
        print("assertion error;skip")


    divide_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
    (binary_expression
    operator: "/"
    ) @divide
    """,
    )

    literal_divide_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
    (binary_expression
        operator: "/"
        right: (decimal_integer_literal) @divisor
        (#eq? @divisor "0")
    ) @divide
    """,
    )

    guarded_divide_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
        (if_statement
            condition: (parenthesized_expression
                (binary_expression left: (identifier) @checked-var operator: "!="))
            consequence: (_
                (binary_expression
                    operator: "/"
                    right: (identifier) @divisor-var
                    (#eq? @checked-var @divisor-var)) @safe-divide))
        """,
    )

    all_divides = tree_sitter.QueryCursor(divide_q).captures(body).get("divide", [])
    guarded_divides = tree_sitter.QueryCursor(guarded_divide_q).captures(body).get("safe-divide", [])
    guarded_divide_ranges = {(n.start_byte, n.end_byte) for n in guarded_divides}

    guard_if_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
        (if_statement
            condition: (parenthesized_expression
                (binary_expression left: (identifier) @checked-var operator: "!="))
            consequence: (_) @guarded-block)
        """,
    )

    guarded_blocks = tree_sitter.QueryCursor(guard_if_q).captures(body).get("guarded-block", [])

    guarded_divide_ranges = set()
    for block in guarded_blocks:
        divides_in_block = tree_sitter.QueryCursor(divide_q).captures(block).get("divide", [])
        for d in divides_in_block:
            guarded_divide_ranges.add((d.start_byte, d.end_byte))

    unguarded_divides = [
        n for n in all_divides if (n.start_byte, n.end_byte) not in guarded_divide_ranges
    ]
    unguarded_divides = [
        n for n in all_divides if (n.start_byte, n.end_byte) not in guarded_divide_ranges
    ]

    any_divide_found = any(
        capture_name == "divide"
        for capture_name, _ in tree_sitter.QueryCursor(divide_q).captures(body).items()
    )

    literal_zero_divide_found = any(
        capture_name == "divide"
        for capture_name, _ in tree_sitter.QueryCursor(literal_divide_q).captures(body).items()
    )

    if literal_zero_divide_found:
        print("divide by zero;found-zero-div")
    elif unguarded_divides:
        print("divide by zero;found-unguarded-div")
    elif guarded_divides:
        print("divide by zero;skip")
    else:
        print("divide by zero;skip")


    nullptr_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
    (null_literal) @nullptr
    """,
    )

    nullptr_found = any(
        capture_name == "nullptr"
        for capture_name, _ in tree_sitter.QueryCursor(nullptr_q).captures(body).items()
    )

    if nullptr_found:
        log.debug("Found null pointer")
        print("null pointer;found-null")
    else:
        log.debug("No null pointer")
        print("null pointer;skip")


    all_access_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """(array_access index: (identifier) @idx) @access""",
    )

    guard_if_bounds_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
        (if_statement
            condition: (parenthesized_expression
                (binary_expression left: (identifier) @checked-var))
            consequence: (_) @guarded-bounds-block)
        """,
    )

    all_accesses = tree_sitter.QueryCursor(all_access_q).captures(body).get("access", [])


    guarded_bounds_blocks = tree_sitter.QueryCursor(guard_if_bounds_q).captures(body).get("guarded-bounds-block", [])

    guarded_ranges = set()
    for block in guarded_bounds_blocks:
        accesses_in_block = tree_sitter.QueryCursor(all_access_q).captures(block).get("access", [])
        for a in accesses_in_block:
            guarded_ranges.add((a.start_byte, a.end_byte))

    for_bound_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
        (for_statement
            condition: (binary_expression
                left: (identifier) @loop-var
                operator: "<"
                right: (field_access
                    field: (identifier) @length-field
                    (#eq? @length-field "length")))
            body: (_) @loop-body)
        """,
    )

    for_bound_blocks = tree_sitter.QueryCursor(for_bound_q).captures(body).get("loop-body", [])

    for block in for_bound_blocks:
        accesses_in_block = tree_sitter.QueryCursor(all_access_q).captures(block).get("access", [])
        for a in accesses_in_block:
            guarded_ranges.add((a.start_byte, a.end_byte))

    unguarded_accesses = [
        n for n in all_accesses if (n.start_byte, n.end_byte) not in guarded_ranges
    ]


    neg_literal_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
        (array_access
            index: (unary_expression
                operator: "-"
                operand: (decimal_integer_literal)) @neg-idx) @neg-access
        """,
    )
    neg_accesses = tree_sitter.QueryCursor(neg_literal_q).captures(body).get("neg-access", [])

    literal_access_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """(array_access index: (decimal_integer_literal) @lit-idx) @lit-access""",
    )
    literal_accesses = tree_sitter.QueryCursor(literal_access_q).captures(body).get("lit-access", [])

    if neg_accesses:
        log.debug("Found out of bounds")
        print("out of bounds;found-outofbounds")
    elif unguarded_accesses or literal_accesses:
        log.debug("Found out of bounds")
        print("out of bounds;found-unguarded")
    else:
        print("out of bounds;skip")


    infinite_while_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """
        (while_statement
            condition: (parenthesized_expression (true))
            body: (_) @loop-body) @infinite-while
        """,
    )

    exit_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        """[(break_statement) (return_statement)] @exit""",
    )

    loop_bodies = tree_sitter.QueryCursor(infinite_while_q).captures(body).get("loop-body", [])

    unguarded_loops = []
    for lb in loop_bodies:
        exits = tree_sitter.QueryCursor(exit_q).captures(lb).get("exit", [])
        if not exits:
            unguarded_loops.append(lb)

    recursive_call_q = tree_sitter.Query(
        JAVA_LANGUAGE,
        f"""
        (method_invocation
            name: ((identifier) @call-name (#eq? @call-name "{method_name}"))) @call
        """,
    )

    recursive_calls = tree_sitter.QueryCursor(recursive_call_q).captures(body).get("call", [])

    top_level_recursive_calls = [n for n in recursive_calls if is_top_level(n)]
    nested_recursive_calls = [n for n in recursive_calls if not is_top_level(n)]

    if unguarded_loops or top_level_recursive_calls:
        log.debug("Found likely non-termination (unguarded loop or top-level recursion)")
        print("*;found-nontermination-strong")
    elif nested_recursive_calls:
        log.debug("Found guarded recursion")
        print("*;found-nontermination-guarded")
    else:
        log.debug("No non-termination signal")
        print("*;skip")


    strong_risk_found = (
        top_level_assert_false
        or literal_zero_divide_found
        or neg_accesses
        or unguarded_loops
        or top_level_recursive_calls
    )

    if not strong_risk_found:
        log.debug("Found ok")
        print("ok;found-ok")
    else:
        log.debug("No ok")
        print("ok;skip")

    for q in jpamb.QUERIES:
        if q not in (
            "assertion error",
            "divide by zero",
            "null pointer",
            "ok",
            "out of bounds",
            "*",
        ):
            print(f"{q};skip")

    sys.exit(0)