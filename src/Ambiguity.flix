///
/// `Ambiguity` represents a type variable that doesn't present in both fixed 
/// and generic variables. The type variable also comes with predicates that 
/// contain the type variable.
///
pub enum Ambiguity(TypeVar, List[Predicate]) with Eq, Hash, Order, ToString


mod Ambiguity {
    pub def create(
        tyVar: TypeVar, 
        preds: List[Predicate]
    ): Ambiguity = Ambiguity(tyVar, preds)


    pub def typeVar(ambiguity: Ambiguity): TypeVar = match ambiguity {
        case Ambiguity(tyVar, _) => tyVar
    }


    pub def predicates(ambiguity: Ambiguity): List[Predicate] = match ambiguity {
        case Ambiguity(_, preds) => preds
    }


    pub def findAmbiguities(
        tyVars: Set[TypeVar],
        predicates: List[Predicate]
    ): List[Ambiguity] = {
        let allPredicatesTyVars = predicates |> Typeable.typeVars;
        let ambiguousTyVars = allPredicatesTyVars 
            |> List.filter(x -> Set.memberOf(x, tyVars));


        ambiguousTyVars |> List.map(
            x -> Ambiguity.create(
                x, 
                
                // grab all the predicates that contain the ambiguous type 
                // variable `x`
                predicates |> List.filter(p ->  {
                    let pTyVars = p |> Typeable.typeVars;
                    List.memberOf(x, pTyVars)
                })
            )
        )
    }
}
