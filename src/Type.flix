
///
/// Represents a symbolic identifier. Like a name of type.
/// 
pub enum Id(String) with Eq, Hash, Order, ToString


mod Id {
    pub def getName(id: Id): String = {
        match id {
            case Id(name) => name
        }
    }
}


///
/// Defines the kind of type. For example `Int32`` has kind Star, while 
/// `List` has kind Arrow(Star, Star).
///
pub enum Kind with Eq, Hash, Order, ToString {
    case Star,
    case Arrow(Kind, Kind)
}


///
/// Represents a type variable. For example, in `List[a]`, `a` is a type variable.
///
pub enum TypeVar(Id, Kind) with Eq, Hash, Order, ToString

mod TypeVar {
    pub def varT(name: String): TypeVar = TypeVar(Id.Id(name), Kind.Star)
}


///
/// Represents a type constructor. For example, `Int32` is a type constructor 
/// with kind Star and `List` is a type constructor with kind Arrow(Star, Star).
/// 
pub enum TypeCon(Id, Kind) with Eq, Hash, Order, ToString


///
/// Represents a type application. For example, `List[Int32]` is a type 
/// application of `List` to `Int32`.
///
pub enum TypeApp(Type, Type) with Eq, Hash, Order, ToString

mod TypeApp {
    pub def head(tapp: TypeApp): Type = match tapp {
        case TypeApp(fun, _) => fun
    }

    pub def arg(tapp: TypeApp): Type = match tapp {
        case TypeApp(_, arg) => arg
    }
}


///
/// An ADT representing a type term in the type system
///
pub enum Type with Eq, Hash, Order, ToString {
    case Var(TypeVar),
    case Con(TypeCon),
    case App(TypeApp)
    case Gen(Int32)
}

mod Type {
    pub def unit(): Type = Type.Con(
        TypeCon.TypeCon(Id.Id("Unit"), Kind.Star)
    )

    pub def list(): Type = Type.Con(
        TypeCon.TypeCon(Id.Id("List"), Kind.Arrow(Kind.Star, Kind.Star))
    )

    pub def int32(): Type = Type.Con(
        TypeCon.TypeCon(Id.Id("Int32"), Kind.Star)
    )

    pub def bool(): Type = Type.Con(
        TypeCon.TypeCon(Id.Id("Bool"), Kind.Star)
    )

    pub def varT(name: String): Type = Type.Var(
        TypeVar.TypeVar(Id.Id(name), Kind.Star)
    )

    pub def apply(func: Type, arg: Type): Type = Type.App(
        TypeApp.TypeApp(func, arg)
    )

    pub def listApply(elemType: Type): Type = Type.apply(list(), elemType)


    pub def arrowApply(left: Type, right: Type): Type = Type.apply(
        Type.apply(arrow(), left), 
        right
    )


    pub def arrow(): Type = Type.Con(
        TypeCon.TypeCon(
            Id.Id("->"), 
            Kind.Arrow(Kind.Star, Kind.Arrow(
                Kind.Star, 
                Kind.Arrow(Kind.Star, Kind.Star
            )))
        )
    )
}


///
/// A trait for getting the kind of the type.
///
pub trait GetKind[a] {
    pub def getKind(x: a): Kind
}


instance GetKind[TypeVar] {
    pub def getKind(x: TypeVar): Kind = {
        match x {
            case TypeVar.TypeVar(_, k) => k
        }
    }
}


instance GetKind[TypeCon] {
    pub def getKind(x: TypeCon): Kind = {
        match x {
            case TypeCon.TypeCon(_, k) => k
        }
    }
}


instance GetKind[TypeApp] {
    pub def getKind(x: TypeApp): Kind = {
        let kind = match x {
            case TypeApp.TypeApp(fun, _) => {
                GetKind.getKind(fun)
            }
        };

        match kind {
            case Kind.Arrow(_, result) => result
            case _ => bug!("Expected a function kind")
        }
    }
}


instance GetKind[Type] {
    pub def getKind(x: Type): Kind = {
        match x {
            case Type.Var(tvar) => GetKind.getKind(tvar)
            case Type.Con(tcon) => GetKind.getKind(tcon)
            case Type.App(tapp) => GetKind.getKind(tapp)
            case Type.Gen(_) => bug!("Generic types do not have a kind")
        }
    }
}


enum BindError {
    case OccursCheckFailed,
    case KindMismatch
}


def mostGeneralUnifier(ty1: Type, ty2: Type): Option[Substitution] = {
    match (ty1, ty2) {
        case (
            Type.App(TypeApp.TypeApp(topL, topR)),
            Type.App(TypeApp.TypeApp(botL, botR))
        ) => forM(
                s1 <- mostGeneralUnifier(topL, botL);
                s2 <- mostGeneralUnifier(
                    topR |> Typeable.applySubstitution(s1), 
                    botR |> Typeable.applySubstitution(s1)
                )
            )
            yield Substitution.compose(s2, s1)
        
        case (Type.Var(var), ty) => varBind(var, ty) |> Result.toOption

        case (ty, Type.Var(var)) => varBind(var, ty) |> Result.toOption

        case (Type.Con(con1), Type.Con(con2)) => if (con1 == con2) {
            Some(Substitution.empty())
        } else {
            None
        }

        case _ => None
    }
}

def matches(ty1: Type, ty2: Type): Option[Substitution] = 
    match (ty1, ty2) {
        case (
            Type.App(TypeApp.TypeApp(topL, topR)),
            Type.App(TypeApp.TypeApp(botL, botR))
        ) => forM(
                s1 <- matches(topL, botL);
                s2 <- matches(
                    topR |> Typeable.applySubstitution(s1), 
                    botR |> Typeable.applySubstitution(s1)
                );
                s3 <- Substitution.merge(s1, s2) |> Result.toOption
            )
            yield s3
            

        case (Type.Var(var), ty) => {
            if (GetKind.getKind(var) == GetKind.getKind(ty)) {
                Some(Substitution.singleton(var, ty))
            } else {
                None
            }
        }

        case (Type.Con(con1), Type.Con(con2)) => if (con1 == con2) {
            Some(Substitution.empty())
        } else {
            None
        }

        case _ => None
    }


def varBind(tyVar: TypeVar, ty: Type): Result[BindError, Substitution] = {
    if (ty == Type.Var(tyVar)) {
        Ok(Substitution.empty())
    } else if (Typeable.typeVars(ty) |> List.memberOf(tyVar)) {
        Err(BindError.OccursCheckFailed)
    } else if (GetKind.getKind(tyVar) != GetKind.getKind(ty)) {
        Err(BindError.KindMismatch)
    } else {
        Ok(Substitution.singleton(tyVar, ty))
    }
}


instance Mgu[Type] {
    pub def mgu(x: Type, y: Type): Option[Substitution] = 
        mostGeneralUnifier(x, y)
}


instance Match[Type] {
    pub def matches(x: Type, y: Type): Option[Substitution] = 
        matches(x, y)
}



instance Typeable[Type] {
    pub def applySubstitution(subst: Substitution, x: Type): Type = match x {
        case Type.Var(var) => match subst |> Substitution.get(var) {
            case None => x, // no mapping found, return itself
            case Some(ty) => ty
        }

        case Type.App(app) => match app {
            case TypeApp.TypeApp(t1, t2) => Type.App(
                TypeApp.TypeApp(
                    t1 |> Typeable.applySubstitution(subst),
                    t2 |> Typeable.applySubstitution(subst)
                )
            )
        }

        case Type.Con(_) => x // type constructors are unaffected by substitutions
        case Type.Gen(_) => x // generic types are unaffected by substitutions
    }

    pub def typeVars(x: Type): List[TypeVar] = match x {
        case Type.Var(var) => var :: Nil,
        case Type.App(app) => match app {
            case TypeApp.TypeApp(t1, t2) => 
                listUnion(
                    t1 |> Typeable.typeVars,
                    t2 |> Typeable.typeVars
                )
        }
        case Type.Con(_) => Nil // type constructors have no type variables
        case Type.Gen(_) => Nil // generic types have no type variables
    }
}


instance Instantiate[Type] {
    pub def instantiate(types: List[Type], template: Type): Type = 
        match template {
            case Type.Gen(index) => {
                let ty = List.get(index, types);

                ty
            }

            case Type.App(app) => match app {
                case TypeApp.TypeApp(t1, t2) => Type.App(
                    TypeApp.TypeApp(
                        t1 |> Instantiate.instantiate(types),
                        t2 |> Instantiate.instantiate(types)
                    )
                )
            }

            case x => x // Type.Var and Type.Con are unaffected by instantiation
        }
}



mod Test {
    @Test
    def basicUnification(): Unit \ Assert = {
        let ty1 = Type.listApply(Type.int32());
        let ty2 = Type.listApply(Type.varT("a"));

        let result = mostGeneralUnifier(ty1, ty2);


        Assert.assertEq(
            {
                expected = Some(
                    Substitution.singleton(TypeVar.varT("a"), Type.int32())
                )
            }, 
            result
        );

        ()
    }

    @Test
    def unificationFailure(): Unit \ Assert = {
        let ty1 = Type.listApply(Type.int32());
        let ty2 = Type.listApply(Type.bool());

        let result = mostGeneralUnifier(ty1, ty2);

        Assert.assertEq({expected = None}, result);

        ()
    }

    @Test
    def matchFailure(): Unit \ Assert = {
        let ty1 = Type.listApply(Type.int32());
        let ty2 = Type.listApply(Type.varT("a")); // appear to the right, not matchable

        let result = matches(ty1, ty2);

        Assert.assertEq({expected = None}, result);

        ()
    }
}


