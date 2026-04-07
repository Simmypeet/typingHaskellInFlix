///
/// A symbolic name for a type class. For example, `Eq` a type class 
///
pub enum ClassId(Id) with Eq, Hash, Order, ToString


///
/// A predicate reprsenting that the `type` must be an instance of the 
/// `typeClases`
///
pub enum IsIn(ClassId, Type) with Eq, Hash, Order, ToString


///
/// An enumeration of predicates that can appear in the solver.
///
pub enum Predicate with Eq, Hash, Order, ToString {
    case IsIn(IsIn)
}

///
/// Represents a qualified data, which must satisfy the predicates in order to 
/// be valid. For example, `Eq a => a -> a` can be represented as a qualified 
/// type where the predicate is `IsIn (Eq, a)` and the data is `a -> a`.
///
pub enum Qualified[a](List[Predicate], a) with Eq, Hash, Order, ToString


instance Typeable[Qualified[a]] with Typeable[a] {
    pub def applySubstitution(
        subst: Substitution, 
        x: Qualified[a]
    ): Qualified[a] = 
        match x {
            case Qualified.Qualified(preds, data) => Qualified.Qualified(
                preds |> Typeable.applySubstitution(subst),
                data |> Typeable.applySubstitution(subst)
            )
        }


    pub def typeVars(x: Qualified[a]): Set[TypeVar] = 
        match x {
            case Qualified.Qualified(preds, data) => 
                Set.union(
                    Typeable.typeVars(preds), 
                    Typeable.typeVars(data)
                )
        }
}


instance Typeable[Predicate] {
    pub def applySubstitution(subst: Substitution, x: Predicate): Predicate = 
        match x {
            case Predicate.IsIn(IsIn.IsIn(tyClass, ty)) => 
                Predicate.IsIn(IsIn.IsIn(
                    tyClass, 
                    ty |> Typeable.applySubstitution(subst)
                ))
        }


    pub def typeVars(x: Predicate): Set[TypeVar] = 
        match x {
            case Predicate.IsIn(IsIn.IsIn(_, ty)) => 
                Typeable.typeVars(ty)
        }
}


instance Mgu[Predicate] {
    pub def mgu(x: Predicate, y: Predicate): Option[Substitution] = 
        match (x, y) {
            case (
                Predicate.IsIn(IsIn.IsIn(tc1, ty1)), 
                Predicate.IsIn(IsIn.IsIn(tc2, ty2))
            ) => if (tc1 == tc2) {
                Mgu.mgu(ty1, ty2)
            } else {
                None // type classes do not match, cannot unify
            }
        }
}


instance Match[Predicate] {
    pub def matches(x: Predicate, y: Predicate): Option[Substitution] = 
        match (x, y) {
            case (
                Predicate.IsIn(IsIn.IsIn(tc1, ty1)), 
                Predicate.IsIn(IsIn.IsIn(tc2, ty2))
            ) => if (tc1 == tc2) {
                Match.matches(ty1, ty2)
            } else {
                None // type classes do not match, cannot unify

            }
        }
}
