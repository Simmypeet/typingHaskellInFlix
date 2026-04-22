pub enum AsPattern(Variable, Pattern) with Eq, Hash, Order, ToString


mod AsPattern {
    pub def innerPattern(asPattern: AsPattern): Pattern = match asPattern {
        case AsPattern(_, pattern) => pattern
    }


    pub def variable(asPattern: AsPattern): Variable = match asPattern {
        case AsPattern(variable, _) => variable
    }
}


pub enum NPlusKPattern(Variable, Literal) with Eq, Hash, Order, ToString


mod NPlusKPattern {
    pub def variable(npk: NPlusKPattern): Variable = match npk {
        case NPlusKPattern(variable, _) => variable
    }
}


pub enum Constructor(AdtId, Scheme, List[Pattern]) with Eq, Hash, Order, ToString


mod Constructor{
    pub def innerPatterns(constructor: Constructor): List[Pattern] = match constructor {
        case Constructor(_, _, patterns) => patterns
    }


    pub def scheme(constructor: Constructor): Scheme = match constructor {
        case Constructor(_, scheme, _) => scheme
    }
}


pub enum AdtId(Id) with Eq, Hash, Order, ToString


pub enum Pattern with Eq, Hash, Order, ToString {
    case Wildcard,
    case Var(Variable),
    case As(AsPattern),
    case Literal(Literal),
    ///
    /// For pattern like `fact (n+1) = (n+1) * fact n`
    ///
    case NPlusK(NPlusKPattern),
    case Constructor(Constructor)
}


mod Pattern {
    use TypeInference.freshInstantiate
    use Pattern.typeInferenceMany

    pub def typeInference(
        pattern: Pattern
    ): (List[Predicate], List[Assumption], Type) 
        \ TypeInference + UnificationFailure = {
        let a = match pattern {
            case Pattern.Wildcard => {
                let newTyVar = Type.Var(TypeInference.newTypeVar(Kind.Star));

                (Nil, Nil, newTyVar)
            }

            case Pattern.Var(var) => {
                let newTyVar = Type.Var(TypeInference.newTypeVar(Kind.Star));

                (
                    Nil,
                    Assumption.create(
                        var, 
                        Scheme.createSimpleScheme(newTyVar)
                    ) :: Nil,
                    newTyVar
                )
            }

            case Pattern.As(asPattern) => {
                let (preds, assumptions, ty) =
                    typeInference(AsPattern.innerPattern(asPattern));

                (
                    preds,
                    Assumption.create(
                        AsPattern.variable(asPattern), 
                        Scheme.createSimpleScheme(ty)
                    ) ::
                    assumptions,
                    ty
                )
            }

            case Pattern.Literal(lit) => {
                let (predicates, ty) = Literal.typeInference(lit);

                (predicates, Nil, ty)
            }

            case Pattern.NPlusK(npk) => {
                let ty = Type.Var(TypeInference.newTypeVar(Kind.Star));

                (
                    Predicate.integral(ty) :: Nil,
                    Assumption.create(
                        NPlusKPattern.variable(npk), 
                        Scheme.createSimpleScheme(ty)
                    ) :: Nil,
                    ty
                )
            }

            case Pattern.Constructor(constructor) => {
                let (ps, assumptions, tys) = 
                    typeInferenceMany(constructor |> Constructor.innerPatterns);

                let newTy = Type.Var(TypeInference.newTypeVar(Kind.Star));

                let scheme = constructor |> Constructor.scheme;
                let freshScheme = scheme |> TypeInference.freshInstantiate;

                let constructorTy = tys 
                    |> List.foldRight(
                        (lhs, rhs) ->  Type.arrowApply(lhs, rhs),
                        newTy
                    );

                TypeInference.unifyTypes(
                    freshScheme |> Qualified.head, 
                    constructorTy
                );


                (
                    ps ++ (freshScheme |> Qualified.context),
                    assumptions,
                    newTy
                )
            }
        };

        ???
    }


    pub def typeInferenceMany(
        patterns: List[Pattern]
    ): (List[Predicate], List[Assumption], List[Type])
        \ TypeInference + UnificationFailure = {
        def iterate(
            current: List[(List[Predicate], List[Assumption], Type)]
        ): (List[Predicate], List[Assumption], List[Type]) = match current {
            case Nil => (Nil, Nil, Nil)
            case (preds,  assumptions, ty) :: rest => {
                let (restPreds, restAssumptions, restTys) = iterate(rest);
  
                (
                    preds ++ restPreds,
                    assumptions ++ restAssumptions,
                    ty :: restTys
                )  
            }
        };

        let initial = patterns |> List.map(typeInference);
        iterate(initial)
    }
}