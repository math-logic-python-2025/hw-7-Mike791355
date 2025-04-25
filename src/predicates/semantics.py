# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/semantics.py

"""Semantic analysis of predicate-logic expressions."""

from typing import FrozenSet, Generic, TypeVar

from src.logic_utils import frozendict

from src.predicates.syntax import *

from itertools import product

#: A generic type for a universe element in a model.
T = TypeVar("T")


@frozen
class Model(Generic[T]):
    """An immutable model for predicate-logic constructs.

    Attributes:
        universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
            terms can be evaluated and over which quantifications are defined.
        constant_interpretations (`~typing.Mapping`\\[`str`, `T`]): mapping from
            each constant name to the universe element to which it evaluates.
        relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each relation name to its arity, or to ``-1`` if the relation is the
            empty relation.
        relation_interpretations (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
            mapping from each n-ary relation name to argument n-tuples (of
            universe elements) for which the relation is true.
        function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each function name to its arity.
        function_interpretations (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
            mapping from each n-ary function name to the mapping from each
            argument n-tuple (of universe elements) to the universe element that
            the function outputs given these arguments.
    """

    universe: FrozenSet[T]
    constant_interpretations: Mapping[str, T]
    relation_arities: Mapping[str, int]
    relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]]
    function_arities: Mapping[str, int]
    function_interpretations: Mapping[str, Mapping[Tuple[T, ...], T]]

    def __init__(
        self,
        universe: AbstractSet[T],
        constant_interpretations: Mapping[str, T],
        relation_interpretations: Mapping[str, AbstractSet[Tuple[T, ...]]],
        function_interpretations: Mapping[str, Mapping[Tuple[T, ...], T]] = frozendict(),
    ):
        """Initializes a `Model` from its universe and constant, relation, and
        function name interpretations.

        Parameters:
            universe: the set of elements to which terms are to be evaluated
                and over which quantifications are to be defined.
            constant_interpretations: mapping from each constant name to a
                universe element to which it is to be evaluated.
            relation_interpretations: mapping from each relation name that is to
                be the name of an n-ary relation, to the argument n-tuples (of
                universe elements) for which the relation is to be true.
            function_interpretations: mapping from each function name that is to
                be the name of an n-ary function, to a mapping from each
                argument n-tuple (of universe elements) to a universe element
                that the function is to output given these arguments.
        """
        for constant in constant_interpretations:
            assert is_constant(constant)
            assert constant_interpretations[constant] in universe
        relation_arities = {}
        for relation in relation_interpretations:
            assert is_relation(relation)
            relation_interpretation = relation_interpretations[relation]
            if len(relation_interpretation) == 0:
                arity = -1  # any
            else:
                some_arguments = next(iter(relation_interpretation))
                arity = len(some_arguments)
                for arguments in relation_interpretation:
                    assert len(arguments) == arity
                    for argument in arguments:
                        assert argument in universe
            relation_arities[relation] = arity
        function_arities = {}
        for function in function_interpretations:
            assert is_function(function)
            function_interpretation = function_interpretations[function]
            assert len(function_interpretation) > 0
            some_argument = next(iter(function_interpretation))
            arity = len(some_argument)
            assert arity > 0
            assert len(function_interpretation) == len(universe) ** arity
            for arguments in function_interpretation:
                assert len(arguments) == arity
                for argument in arguments:
                    assert argument in universe
                assert function_interpretation[arguments] in universe
            function_arities[function] = arity

        self.universe = frozenset(universe)
        self.constant_interpretations = frozendict(constant_interpretations)
        self.relation_arities = frozendict(relation_arities)
        self.relation_interpretations = frozendict(
            {relation: frozenset(relation_interpretations[relation]) for relation in relation_interpretations}
        )
        self.function_arities = frozendict(function_arities)
        self.function_interpretations = frozendict(
            {function: frozendict(function_interpretations[function]) for function in function_interpretations}
        )

    def __repr__(self) -> str:
        """Computes a string representation of the current model.

        Returns:
            A string representation of the current model.
        """
        return (
            "Universe="
            + str(self.universe)
            + "; Constant Interpretations="
            + str(self.constant_interpretations)
            + "; Relation Interpretations="
            + str(self.relation_interpretations)
            + (
                "; Function Interpretations=" + str(self.function_interpretations)
                if len(self.function_interpretations) > 0
                else ""
            )
        )

    def evaluate_term(self, term: Term,
                  assignment: Mapping[str, T] = frozendict()) -> T:

        assert term.constants().issubset(self.constant_interpretations.keys())
        assert term.variables().issubset(assignment.keys())
        for function, arity in term.functions():
            assert function in self.function_interpretations and self.function_arities[function] == arity

        if not getattr(term, "arguments", None):
            if term.root in assignment:                  
                return assignment[term.root]
            else:                                        
                return self.constant_interpretations[term.root]
        args_values = []
        for a in term.arguments:
            args_values.append(self.evaluate_term(a, assignment))
        ri = self.function_interpretations[term.root]
        return ri[tuple(args_values)]

        # Task 7.7

    def evaluate_formula(self, formula: Formula, assignment: Mapping[str, T] = frozendict()) -> bool:

        assert formula.constants().issubset(self.constant_interpretations.keys())
        assert formula.free_variables().issubset(assignment.keys())
        for function, arity in formula.functions():
            assert function in self.function_interpretations and self.function_arities[function] == arity
        for relation, arity in formula.relations():
            assert relation in self.relation_interpretations and self.relation_arities[relation] in {-1, arity}
        


        if is_equality(formula.root):
            x, y = formula.arguments
            x = self.evaluate_term(x, assignment)
            y = self.evaluate_term(y, assignment)
            return (x == y)

        if is_unary(formula.root):
            first_val = self.evaluate_formula(formula.first, assignment)
            return not first_val

        if is_binary(formula.root):
            first_val = self.evaluate_formula(formula.first, assignment)
            second_val = self.evaluate_formula(formula.second, assignment)
            if formula.root == '&':
                return first_val and second_val
            if formula.root == '|':
                return first_val or second_val
        
            return not first_val or second_val


        if is_relation(formula.root):
            rg = []
            for term in formula.arguments:
                rg.append(self.evaluate_term(term, assignment))
            if tuple(rg) in self.relation_interpretations[formula.root]:
                return True
            else:
                return False

        for element in self.universe:
            na = dict(assignment)
            na[formula.variable] = element
            result = self.evaluate_formula(formula.statement, na)
            if formula.root == 'A':
                if not result:
                    return False
            else:
                if result:
                    return True
        return True if formula.root == 'A' else False


    def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
        for formula in formulas:
            assert formula.constants().issubset(self.constant_interpretations.keys())
            for function, rt in formula.functions():
                assert function in self.function_interpretations and self.function_arities[function] == rt
            for relation, rt in formula.relations():
                assert relation in self.relation_interpretations and self.relation_arities[relation] in {-1, rt}
                
        for formula in formulas:
            if not list(formula.free_variables()):
                if not self.evaluate_formula(formula):
                    return False
            else:
                for x in product(self.universe, repeat=len(list(formula.free_variables()))):
                    if not self.evaluate_formula(formula, dict(zip(list(formula.free_variables()), x))):
                        return False
        return True
