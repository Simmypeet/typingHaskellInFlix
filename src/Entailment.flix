///
/// Retrieves the predicates that can be derived from a given predicate by 
/// superclass relationships.
///
def bySuper(
    classEnv: ClassEnvironment,
    pred: Predicate
): Set[Predicate] = {
    let classId = pred |> Predicate.classId;
    let superClasses = classEnv |> ClassEnvironment.getSuperClasses(classId);
    let ty = pred |> Predicate.ty;


    region r {
        let iter = superClasses |> List.iterator(r);
        
        Iterator.foldLeft(
            (set, superClassId) -> {
                let superPred = bySuper(
                    classEnv, 
                    Predicate.createIsIn(superClassId, ty)
                );

                Set.union(set, superPred)
            },
            Set.singleton(pred),
            iter
        )
    }
}


///
/// Searches for an instance that can be used to satisfy the given predicate. 
/// If such an instance is found, returns a list of predicates that must be 
/// further satisfied in order for the original predicate to be satisfied. 
///
pub def byInstance(
    pred: Predicate,
    classEnv: ClassEnvironment
): Option[List[Predicate]] = {
    let classId = pred |> Predicate.classId;
    let ty = pred |> Predicate.ty;
    let instances = classEnv |> ClassEnvironment.getInstances(classId);

    let subgoals = List.findMap(
        cand -> {
            let candPredHead = cand |> Instance.headType;

            match Match.matches(candPredHead, ty) {
                case None => None
                case Some(subst) => 
                    Some(
                        cand |> Instance.context 
                            |> Typeable.applySubstitution(subst)
                    )
            }
            
        },

        instances
    );

    subgoals
}


///
/// Given a class environment, a list of predicates (the premises) that are
/// assumed to be true, determines whether a given predicate (the conclusion) 
/// can be derived from them.
///
pub def entails(
    premises: List[Predicate],
    conclusion: Predicate,
    classEnv: ClassEnvironment
): Bool = {
    let bySuperPreds = bySuper(classEnv, conclusion);

    if (Set.memberOf(conclusion, bySuperPreds)) {
        true
    } else {
        match byInstance(conclusion, classEnv) {
            case None => false
            case Some(subgoals) => {

                List.forAll(
                    subgoal -> entails(
                        premises, 
                        subgoal,
                        classEnv 
                    ),
                    subgoals
                )
            }
        }
    }
}