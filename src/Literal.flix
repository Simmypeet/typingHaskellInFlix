pub enum Literal with Eq, Hash, Order, ToString {
    case Integer(Int32)
    case Char(Char)
    case Rational(Float64)
    case String(String)
}


mod Literal {
    pub def typeInference(
        lit: Literal
    ): (Predicates, Type) \ TypeInference = {
        match lit {
            case Integer(_) => {
                let tyVar = Type.Var(TypeInference.newTypeVar());

                (
                    Predicates.singleton(Predicate.num(tyVar)),
                    tyVar
                )
            }

            case Char(_) => (Predicates.empty(), Type.char())

            case String(_) => (Predicates.empty(), Type.string())

            case Rational(_) => {
                let tyVar = Type.Var(TypeInference.newTypeVar());

                (
                    Predicates.singleton(Predicate.fractional(tyVar)),
                    tyVar
                )
            }
        }
    }
}