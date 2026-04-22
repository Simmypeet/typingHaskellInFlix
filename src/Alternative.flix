pub enum Alternative(List[Pattern], Expr) with Eq, Hash, Order, ToString


mod Alternative {
    pub def create(
        patterns: List[Pattern], 
        expr: Expr
    ): Alternative = Alternative(patterns, expr)


    pub def patterns(alt: Alternative): List[Pattern] = match alt {
        case Alternative(patterns, _) => patterns
    }


    pub def expr(alt: Alternative): Expr = match alt {
        case Alternative(_, expr) => expr
    }


    pub def typeInference(
        classEnvironment: ClassEnvironment,
        assumptions: List[Assumption],
        alt: Alternative
    ): (List[Predicate], Type) \ 
        TypeInference 
        + UnificationFailure 
        + AssumptionNotFoundFailure 
    = {
        let patterns = Alternative.patterns(alt);
        let expr = Alternative.expr(alt);

        let (patternPreds, newAssumptions, patternTys) 
            = Pattern.typeInferenceMany(patterns);

        let (exprPreds, exprTy) = Expr.typeInference(
            classEnvironment,
            assumptions ++ newAssumptions,
            expr
        );

        (
            patternPreds ++ exprPreds,
            patternTys |> List.foldRight(
                (right, curr) -> Type.arrowApply(right, curr), 
                exprTy
            )
        )
    }


    pub def typeInferenceMany(
        classEnvironment: ClassEnvironment,
        assumptions: List[Assumption],
        expectedTy: Type,
        alts: List[Alternative]
    ): List[Predicate] \ 
        TypeInference 
        + UnificationFailure 
        + AssumptionNotFoundFailure 
    = {
        let results = List.map(
            alt -> Alternative.typeInference(
                classEnvironment, 
                assumptions, 
                alt
            ),
            alts
        );

        foreach ((_, ty) <- results) 
            TypeInference.unifyTypes(expectedTy, ty);

        List.flatMap(pr -> fst(pr), results)
    }
}


