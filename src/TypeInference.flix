struct TypeInferenceState[r] {
    mut currentSubst: Substitution,
    mut counter: Int32
}


mod TypeInferenceState {
    pub def extendSubstitution(
        subst: Substitution,
        state: TypeInferenceState[r]
    ): Unit \ r = {
        state->currentSubst = Substitution.compose(subst, state->currentSubst);

        ()
    }

    pub def newTypeVar(state: TypeInferenceState[r], kind: Kind): TypeVar \ r = {
        let var = TypeVar.varK("@t" + Int32.toString(state->counter), kind);
        state->counter = state->counter + 1;
        var
    }


    pub def currentSubstitution(state: TypeInferenceState[r]): Substitution \ r = 
        state->currentSubst
}


pub eff TypeInference {
    def extendSubstitution(subst: Substitution): Unit
    def getSubstitution(): Substitution
    def newTypeVar(kind: Kind): TypeVar
}


pub enum UnificationError(Type, Type) with Eq, ToString


pub eff UnificationFailure {
    def error(error: UnificationError): Void
}


mod UnificationFailure {
    pub def toResult(f: Unit -> b \ e): Result[UnificationError, b] \ e - UnificationFailure = {
        run {
            Ok(f())
        } with handler UnificationFailure {
            def error(error, _) = Err(error)
        }
    }

    @DefaultHandler
    pub def runWithDefault(
        f: Unit -> b \ e
    ): b \ (e - UnificationFailure) + IO = {
        run {
            f()
        } with handler UnificationFailure {
            def error(error, _k) = 
                bug!("Unhandled Unification Failure effect " + error.toString())
        }
    }
}


mod TypeInference {
    use Mgu.mgu
    @DefaultHandler
    pub def runWithTypeInference(f: Unit -> b \ e): b \ (e - TypeInference) + IO = {
        region r {
            let typeInferenceState = new TypeInferenceState @ r {
                currentSubst = Substitution.empty(),
                counter = 0
            };

            run {
                f() } with handler TypeInference {
                def extendSubstitution(subst, k) = {
                    TypeInferenceState.extendSubstitution(subst, typeInferenceState);
                    k()
                }

                def getSubstitution(k) = {
                    k(TypeInferenceState.currentSubstitution(typeInferenceState))
                }

                def newTypeVar(kind, k) = {
                    let var = TypeInferenceState.newTypeVar(
                        typeInferenceState,
                        kind
                    );

                    k(var)
                }
            }
        }
    }


    pub def unifyTypes(
        ty1: Type, 
        ty2: Type
    ): Unit \ (TypeInference + UnificationFailure) = {
        let subst = TypeInference.getSubstitution();

        let ty1Subst = ty1 |> Typeable.applySubstitution(subst);
        let ty2Subst = ty2 |> Typeable.applySubstitution(subst);

        match mgu(ty1Subst, ty2Subst) {
            case Some(newSubst) => {
                TypeInference.extendSubstitution(newSubst);

                ()
            }

            case None => UnificationFailure.error(
                UnificationError.UnificationError(ty1Subst, ty2Subst)
            )
        }
    }


    pub def freshInstantiate(
        scheme: Scheme
    ): Qualified[Type] \ TypeInference = {
        let foralls = scheme 
            |> Scheme.kinds 
            |> List.map(_ -> Type.Var(TypeInference.newTypeVar(Kind.Star)));

        Qualified.create(
            scheme |> Scheme.context |> Instantiate.instantiate(foralls),
            scheme |> Scheme.head |> Instantiate.instantiate(foralls)
        )
    }
}


pub trait Instantiate[t] {
    pub def instantiate(types: List[Type], template: t): t
}


instance Instantiate[List[a]] with Instantiate[a] {
    pub def instantiate(types: List[Type], template: List[a]): List[a] = 
        List.map(elem -> elem |> Instantiate.instantiate(types), template)
}


mod Test {
    use Assert.assertEq

    @Test
    def basicTypeInferenceUnification(): Unit \ TypeInference + UnificationFailure + Assert = {
        let tvarA = Type.Var(TypeInference.newTypeVar(Kind.Star));
        let tvarB = Type.Var(TypeInference.newTypeVar(Kind.Star));
        let tvarC = Type.Var(TypeInference.newTypeVar(Kind.Star));

        let tyInt32 = Type.int32();

        assertEq({expected = ()}, TypeInference.unifyTypes(tvarA, tvarB));
        assertEq({expected = ()}, TypeInference.unifyTypes(tvarB, tvarC));
        assertEq({expected = ()}, TypeInference.unifyTypes(tvarC, tyInt32));

        // all types should be unified to int32 at this point

        let subst = TypeInference.getSubstitution();

        let tyA = tvarA |> Typeable.applySubstitution(subst);
        let tyB = tvarB |> Typeable.applySubstitution(subst);
        let tyC = tvarC |> Typeable.applySubstitution(subst);

        assertEq({expected = tyInt32}, tyA);
        assertEq({expected = tyInt32}, tyB);
        assertEq({expected = tyInt32}, tyC);

        let tyBool = Type.bool();

        assertEq(
            {
                expected = Err(
                    UnificationError.UnificationError(tyInt32, tyBool)
                )
            }, 
            run TypeInference.unifyTypes(tyA, tyBool) with UnificationFailure.toResult
        );

        ()
    }
}