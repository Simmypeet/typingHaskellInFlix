pub enum Literal with Eq, Hash, Order, ToString {
    case Integer(Int32)
    case Char(Char)
    case Rational(Float64)
    case String(String)
}


mod Literal {
    pub def typeInference(
        lit: Literal
    ): (List[Predicate], Type) \ TypeInference = {
        match lit {
            case Integer(_) => {
                let tyVar = Type.Var(TypeInference.newTypeVar());

                (
                    Predicate.num(tyVar) :: Nil,
                    tyVar
                )
            }

            case Char(_) => (Nil, Type.char())

            case String(_) => (Nil, Type.string())

            case Rational(_) => {
                let tyVar = Type.Var(TypeInference.newTypeVar());

                (
                    Predicate.fractional(tyVar) :: Nil,
                    tyVar
                )
            }
        }
    }
}