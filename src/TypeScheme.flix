pub enum Scheme(List[Kind], Qualified[Type]) with Eq, Hash, Order, ToString


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


instance Typeable[Scheme] {
    pub def applySubstitution(subst: Substitution, x: Scheme): Scheme = match x {
        case Scheme.Scheme(kinds, qualifiedType) => Scheme.Scheme(
            kinds, 
            qualifiedType |> Typeable.applySubstitution(subst)
        )
    }

    pub def typeVars(x: Scheme): List[TypeVar] = 
        match x {
            case Scheme.Scheme(_, qualifiedType) => 
                Typeable.typeVars(qualifiedType)
        }
}



mod Test {
    use Assert.assertEq

    @Test
    pub def testQuantify(): Unit \ Assert = {
        let tyVarA = Type.varT("a");
        let tyVarB = Type.varT("b");
        let tyVarC = Type.varT("c");
        let tyVarD = Type.varT("d");

        let aarrowb = Qualified.newHead(Type.arrowApply(tyVarA, tyVarB));
        let carrowd = Qualified.newHead(Type.arrowApply(tyVarC, tyVarD));

        let firstScheme = Scheme.quantify(
            Typeable.typeVars(aarrowb) |> List.toSet,
            aarrowb
        );

        let secondScheme = Scheme.quantify(
            Typeable.typeVars(carrowd) |> List.toSet,
            carrowd
        );


        assertEq({expected = firstScheme}, secondScheme)
    }
}