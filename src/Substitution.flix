///
/// Represents a substitution mapping type variables to types. For example, 
/// the substitution {a -> Int32} maps the type variable `a` to the type `Int32`.
///
pub enum Substitution(Map[TypeVar, Type]) with Eq, ToString


///
/// An error occurs when `Substitution.merge` is called on two substitutions 
/// that have conflicting mappings. 
///
/// It stores the variable that has conflicting mappings and the two types that 
/// are in conflict.
///
pub enum MergeConflictError(TypeVar, Type, Type)


mod Substitution {
    pub def fromMap(map: Map[TypeVar, Type]): Substitution = 
        Substitution.Substitution(map)


    pub def get(var: TypeVar, subst: Substitution): Option[Type] = {
        match subst {
            case Substitution.Substitution(map) => map |> Map.get(var)
        }
    }


    def internalMapings(subst: Substitution): Map[TypeVar, Type] = match subst {
        case Substitution.Substitution(map) => map
    }


    pub def empty(): Substitution = Substitution.Substitution(Map.empty())


    pub def singleton(var: TypeVar, ty: Type): Substitution = 
        Substitution.Substitution(Map.singleton(var, ty))


    ///
    /// Combines the substitutions `first` and `second` so that it has the same
    /// effect of like `compose(first, second)(x) == first(compose(second)(x))` 
    /// for any type `x`.
    /// 
    pub def compose(first: Substitution, second: Substitution): Substitution = {
        match (first, second) {
            case (
                Substitution.Substitution(map1), 
                Substitution.Substitution(map2)
            ) =>  {
                let newMap2 = Map.map(
                     ty -> ty |> Typeable.applySubstitution(first), 
                     map2
                );

                // Combine the two maps, with the first map taking precedence
                let combinedMap = Map.union(map1, newMap2);

                Substitution.Substitution(combinedMap)

            }
        }
    }

    ///
    /// Plainly merges two substitutions without composing them. However, it
    /// does conflic checking.
    ///
    pub def merge(
        subst1: Substitution, 
        subst2: Substitution
    ): Result[MergeConflictError, Substitution] = {
        let map1 = internalMapings(subst1);
        let map2 = internalMapings(subst2);

        // Check for conflicts
        region r {
            let iter = Map.iterator(r, map1);

            def checkConflict(): Result[MergeConflictError, Substitution] = {
                match Iterator.next(iter) {
                    case Some((var, ty)) => {
                        match map2 |> Map.get(var) {
                            case Some(ty2) => if (ty != ty2) {

                                Err(MergeConflictError.MergeConflictError(
                                    var, ty, ty2
                                ))
                            } else {
                                checkConflict() // no conflict, check next
                            },

                            case None => checkConflict()
                        }
                    }
                    
                    // no more conflict to check, we can safely merge the two
                    // substitutions
                    case None => Ok(Substitution.Substitution(
                        Map.union(map1, map2)
                    ))
                }
            };

            checkConflict()
        }
    }
}


/// 
/// Allows us to apply a substitution to a type and to get the set of type 
/// variables
///
pub trait Typeable[a] {
    pub def applySubstitution(subst: Substitution, x: a): a

    pub def typeVars(x: a): List[TypeVar]
}


instance Typeable[List[a]] with Typeable[a] {
    pub def applySubstitution(subst: Substitution, x: List[a]): List[a] = 
        List.map(elem -> elem |> Typeable.applySubstitution(subst), x)


    pub def typeVars(x: List[a]): List[TypeVar] = 
        List.foldLeft(
            (acc, elem) -> listUnion(acc, Typeable.typeVars(elem)), 
            List.empty(), 
            x
        )
}




///
/// A trait for unification. It allows us to find the most general unifier of
/// two types, which is a substitution that makes the two types equal.
///
pub trait Mgu[a] {
    ///
    /// Computes the most general unifier of `x` and `y`. If there is no unifier,
    /// it returns `None`.
    ///
    pub def mgu(x: a, y: a): Option[Substitution]
}


///
/// Similar to `Mgu`, it's a one-way unification. If finds a substitution `s` 
/// such that `applySubstitution(s, x) == y`.
///
pub trait Match[a] {
    ///
    /// Checks if `x` matches `y`, which means that there exists a substitution
    /// `s` such that `applySubstitution(s, x) == y`. If such a substitution 
    /// exists, it returns `Some(s)`, otherwise it returns `None`.
    ///
    pub def matches(x: a, y: a): Option[Substitution]
}