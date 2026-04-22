pub enum FunctionApplication(Expr, Expr) with Eq, Hash, Order, ToString


mod FunctionApplication {
    pub def function(app: FunctionApplication): Expr = match app {
        case FunctionApplication(func, _) => func
    }


    pub def argument(app: FunctionApplication): Expr = match app {
        case FunctionApplication(_, arg) => arg
    }
}


pub enum Let(BindGroup, Expr) with Eq, Hash, Order, ToString


pub enum Expr with Eq, Hash, Order, ToString {
    case Var(Variable),
    case Literal(Literal),
    case Constant(Assumption),
    case App(FunctionApplication),
    case Let(Let)
}


mod Expr {
    pub def typeInference(
        classEnvironment: ClassEnvironment,
        assumptions: List[Assumption],
        expr: Expr
    ): (List[Predicate], Type) \ (
        TypeInference + UnificationFailure + AssumptionNotFoundFailure
    ) = {
        match expr {
            case Expr.Var(variable) => {
                let assumption = match (assumptions |> List.find(
                    x -> x |> Assumption.variable == variable
                )) {
                    case Some(assumption) => assumption
                    case None => AssumptionNotFoundFailure.notFound(variable)
                };


                let scheme = assumption |> Assumption.scheme;
                let ty = TypeInference.freshInstantiate(scheme);

                (ty |> Qualified.context, ty |> Qualified.head)
            }

            case Expr.Constant(const) => {
                let scheme = const |> Assumption.scheme;
                let ty = TypeInference.freshInstantiate(scheme);

                (ty |> Qualified.context, ty |> Qualified.head)
            }

            case Expr.Literal(lit) => {
                lit |> Literal.typeInference
            }


            case Expr.App(app) => {
                let (fnPreds, fnTy) = typeInference(
                    classEnvironment,
                    assumptions,
                    app |> FunctionApplication.function
                );

                let (argPreds, argTy) = typeInference(
                    classEnvironment,
                    assumptions,
                    app |> FunctionApplication.argument
                );

                let newVar = TypeInference.newTypeVar(Kind.Star);

                let functionType = Type.arrowApply(argTy, Type.Var(newVar));
                
                TypeInference.unifyTypes(functionType, fnTy);

                (
                    fnPreds ++ argPreds,
                    Type.Var(newVar)
                )
            }

            case _ => ???
        }
    }
}