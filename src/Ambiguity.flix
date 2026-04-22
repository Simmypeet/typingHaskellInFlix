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
            |> List.filter(x -> not Set.memberOf(x, tyVars));


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


mod Test {
    use Assert.assertEq


    def predicatesFor(
        tyVar: TypeVar,
        ambiguities: List[Ambiguity]
    ): List[Predicate] = {
        let matching = ambiguities |> List.filter(
            ambiguity -> Ambiguity.typeVar(ambiguity) == tyVar
        );

        match matching {
            case Nil => Nil
            case ambiguity :: _ => ambiguity |> Ambiguity.predicates
        }
    }


    @Test
    pub def findAmbiguitiesReturnsEmptyWhenAllVariablesAreFixed(): Unit \ Assert = {
        let predA = Predicate.num(Type.varT("a"));
        let predB = Predicate.integral(Type.varT("b"));

        let ambiguities = Ambiguity.findAmbiguities(
            (TypeVar.varT("a") :: TypeVar.varT("b") :: Nil) |> List.toSet,
            predA :: predB :: Nil
        );

        assertEq({expected = Nil}, ambiguities)
    }


    @Test
    pub def findAmbiguitiesCollectsAllPredicatesForUnfixedVariable(): Unit \ Assert = {
        let a = TypeVar.varT("a");
        let predA = Predicate.num(Type.varT("a"));
        let predB = Predicate.fractional(Type.varT("a"));

        let ambiguities = Ambiguity.findAmbiguities(
            (TypeVar.varT("b") :: Nil) |> List.toSet,
            predA :: predB :: Nil
        );

        assertEq(
            {expected = (a :: Nil) |> List.toSet},
            ambiguities |> List.map(Ambiguity.typeVar) |> List.toSet
        );

        assertEq(
            {expected = (predA :: predB :: Nil) |> List.toSet},
            ambiguities |> predicatesFor(a) |> List.toSet
        )
    }


    @Test
    pub def findAmbiguitiesIgnoresFixedVariables(): Unit \ Assert = {
        let a = TypeVar.varT("a");
        let b = TypeVar.varT("b");
        let predA = Predicate.num(Type.varT("a"));
        let predB = Predicate.integral(Type.varT("b"));

        let ambiguities = Ambiguity.findAmbiguities(
            (a :: Nil) |> List.toSet,
            predA :: predB :: Nil
        );

        assertEq(
            {expected = (b :: Nil) |> List.toSet},
            ambiguities |> List.map(Ambiguity.typeVar) |> List.toSet
        );

        assertEq(
            {expected = (predB :: Nil) |> List.toSet},
            ambiguities |> predicatesFor(b) |> List.toSet
        )
    }


    @Test
    pub def findAmbiguitiesIncludesSharedPredicatesForEachUnfixedVariable()
        : Unit \ Assert = {
        let a = TypeVar.varT("a");
        let b = TypeVar.varT("b");

        let predA = Predicate.num(Type.varT("a"));
        let predB = Predicate.integral(Type.varT("b"));
        let shared = Predicate.createIsIn(
            ClassId.eq(),
            Type.arrowApply(Type.varT("a"), Type.varT("b"))
        );

        let ambiguities = Ambiguity.findAmbiguities(
            Set.empty(),
            predA :: predB :: shared :: Nil
        );

        assertEq(
            {expected = (a :: b :: Nil) |> List.toSet},
            ambiguities |> List.map(Ambiguity.typeVar) |> List.toSet
        );

        assertEq(
            {expected = (predA :: shared :: Nil) |> List.toSet},
            ambiguities |> predicatesFor(a) |> List.toSet
        );

        assertEq(
            {expected = (predB :: shared :: Nil) |> List.toSet},
            ambiguities |> predicatesFor(b) |> List.toSet
        )
    }
}
