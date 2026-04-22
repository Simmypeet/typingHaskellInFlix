/// 
/// Splits a list of predicates into `(deferred, retained)`, where `deferred`
/// are the list of predicates that will be propagated out to the caller/outer
/// scope, and `retained` are the predicates that will be used to form a type
/// scheme.
///
pub def split(
    classEnvironment: ClassEnvironment,
    fixedVariables: Set[TypeVar],
    generalizedVariables: Set[TypeVar],
    predicates: List[Predicate]
): (List[Predicate], List[Predicate]) \ ContextReductionFailure = {
    let reducedPredicates = reduce(predicates, classEnvironment);

    let (deferred, retained) = List.partition(
        x -> {
            let vars = x |> Typeable.typeVars;
            vars |> List.forAll(y -> fixedVariables |> Set.memberOf(y))
        }, 
        reducedPredicates
    );

    let eliminatings = ???;
    
    (
        deferred, 
        retained |> List.filter(
            x -> eliminatings |> Set.memberOf(x)
        ))

}