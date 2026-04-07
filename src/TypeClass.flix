///
/// A symbolic name for a type class. For example, `Eq` a type class 
///
pub enum ClassId(Id) with Eq, Hash, Order, ToString


///
/// A predicate reprsenting that the `type` must be an instance of the 
/// `typeClases`
///
pub enum IsIn(ClassId, Type) with Eq, Hash, Order, ToString


mod IsIn {
    pub def classId(pred: IsIn): ClassId = match pred {
        case IsIn(classId, _) => classId
    }

    
    pub def ty(pred: IsIn): Type = match pred {
        case IsIn(_, ty) => ty
    }
}


///
/// An enumeration of predicates that can appear in the solver.
///
pub enum Predicate with Eq, Hash, Order, ToString {
    case IsIn(IsIn)
}


mod Predicate {
    pub def newWith(classId: ClassId, ty: Type): Predicate = 
        Predicate.IsIn(IsIn.IsIn(classId, ty))


    def isIn(pred: Predicate): IsIn = match pred {
        case Predicate.IsIn(isIn) => isIn
    }


    pub def classId(pred: Predicate): ClassId = 
        pred |> isIn |> IsIn.classId


    pub def ty(pred: Predicate): Type = 
        pred |> isIn |> IsIn.ty
}


///
/// Represents a qualified data, which must satisfy the predicates in order to 
/// be valid. For example, `Eq a => a -> a` can be represented as a qualified 
/// type where the predicate is `IsIn (Eq, a)` and the data is `a -> a`.
///
pub enum Qualified[a](List[Predicate], a) with Eq, Hash, Order, ToString


mod Qualified  {
    pub def context(qualified: Qualified[a]): List[Predicate] = 
        match qualified {
            case Qualified(preds, _) => preds
        }

    
    pub def head(qualified: Qualified[a]): a = 
        match qualified {
            case Qualified(_, data) => data
        }

    
    pub def headClassId(qualified: Qualified[Predicate]): ClassId = 
        qualified |> head |> Predicate.classId
        
}


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


///
/// An information of the class, containing the list of its superclasses and
/// the list of available instances.
///
pub enum Class(List[ClassId], List[Instance]) with Eq, Hash, Order, ToString

mod Class {
    pub def newWithSupers(supers: List[ClassId]): Class = 
        Class(supers, List.empty())


    pub def superClasses(cls: Class): List[ClassId] = 
        match cls {
            case Class(supers, _) => supers
        }

    
    pub def instances(cls: Class): List[Instance] = 
        match cls {
            case Class(_, instances) => instances
        }

    
    pub def addInstance(inst: Instance, cls: Class): Class = 
        match cls {
            case Class(supers, instances) => 
                Class(supers, inst :: instances)
        }
}


///
/// An instance of a type class, which is a qualified predicate. 
/// For example, `instance[a: Eq] Eq (List a)` can be represented as an instance
/// where the head is `IsIn (Eq, List a)` and the predicates are 
/// `[IsIn (Eq, a)]`.
///
pub enum Instance(Qualified[Predicate]) with Eq, Hash, Order, ToString


mod Instance {
    def getQualified(inst: Instance): Qualified[Predicate] = match inst {
        case Instance(q) => q
    }


    pub def head(inst: Instance): Predicate = 
        inst |> getQualified |> Qualified.head


    pub def context(inst: Instance): List[Predicate] = 
        inst |> getQualified |> Qualified.context

    
    pub def headClassId(inst: Instance): ClassId = 
        inst |> head |> Predicate.classId


    pub def headType(inst: Instance): Type = 
        inst |> head |> Predicate.ty

}