use Iterator.Step
pub enum Scheme(List[Kind], Qualified[Type])


def toGenSubst(
    vars: List[TypeVar]
): Substitution = {
    def createGenSubst(
        curr: List[TypeVar], 
        index: Int32, 
        acc: Map[TypeVar, Type]
    ): Map[TypeVar, Type] = match curr {
        case Nil => acc
        case head :: tail => createGenSubst(
            tail, 
            index + 1, 
            Map.insert(head, Type.Gen(index), acc)
        )
    };

    Substitution.fromMap(createGenSubst(vars, 0, Map.empty()))
}


mod Scheme {
    pub def toScheme(ty: Type): Scheme = {
        Scheme(Nil, Qualified.newHead(ty))
    }


    pub def quantify(
        typeVars: Set[TypeVar],
        qualifiedType: Qualified[Type]
    ): Scheme = {
        let variables = qualifiedType 
            |> Typeable.typeVars
            |> List.filter(x -> Set.memberOf(x, typeVars));

        let kinds = variables |> List.map(x -> GetKind.getKind(x));
        let subst = toGenSubst(variables);

        let quantifiedType = qualifiedType 
            |> Typeable.applySubstitution(subst);

        Scheme(kinds, quantifiedType)
    }
   
 
    pub def kinds(scheme: Scheme): List[Kind] = 
        match scheme {
            case Scheme(kinds, _) => kinds
        }
   
 
    pub def qualifiedType(scheme: Scheme): Qualified[Type] = 
        match scheme {
            case Scheme(_, qualifiedType) => qualifiedType
        }
}