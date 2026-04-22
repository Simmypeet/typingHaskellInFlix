@Tailrec
def isHnf(ty: Type): Bool =
    match ty {
        case Type.Var(_) => true,
        case Type.Con(_) => false,
        case Type.App(tapp) => {
            let head = tapp |> TypeApp.head;

            isHnf(head)
        }

        case _ => bug!("Unexpected type: " + ToString.toString(ty))
    }


pub eff ContextReductionFailure {
    def error(error: Predicate): Void
}


def toHnfs(
    predicates: List[Predicate], 
    classEnv: ClassEnvironment
):  List[Predicate] \ ContextReductionFailure = {
    def traverse(
        preds: List[Predicate], 
        acc: List[Predicate]
    ): List[Predicate] = 
        match preds {
            case Nil => acc

            case pred :: rest => {
                let hnfs = toHnf(pred, classEnv);

                traverse(rest, hnfs ++ acc)
            }
        };

    traverse(predicates, Nil)
}


def toHnf(
    predicate: Predicate, 
    classEnv: ClassEnvironment
):  List[Predicate] \ ContextReductionFailure = {
    if (predicate |> Predicate.ty |> isHnf) {
        predicate :: Nil
    } else {
        let res = classEnv |> byInstance(predicate);

        match res {
            case None => ContextReductionFailure.error(predicate)

            case Some(subgoals) => toHnfs(subgoals, classEnv)
        }
    }
}


///
/// Simplifies a list of predicates by removing any predicates that are 
/// entailed by the others. For example, if we have predicates `Eq a` and `Eq b`,
/// it is possible to remove `Eq (a, b)` since it is entailed by the other two.
///
def simplify(
    predicates: List[Predicate], 
    classEnv: ClassEnvironment
): List[Predicate] = {
    def traverse(
        pass: List[Predicate],
        remaining: List[Predicate]
    ): List[Predicate] = {
        match remaining {
            case Nil => pass,
            case h :: rest =>  {
                let entails = classEnv |> entails(pass ++ rest, h);

                // h is entailed by other predicates, unnecessary
                if (entails) {
                    traverse(pass, rest)
                } else {
                    traverse(h :: pass, rest)
                }
            }
        }
    };

    traverse(Nil, predicates)
}


///
/// Simplifies a list o predicates into a "semantically equivalent" but simpler
/// list of predicates.
///
pub def reduce(
    predicates: List[Predicate], 
    classEnv: ClassEnvironment
):  List[Predicate] \ ContextReductionFailure = {
    let hnfs = classEnv |> toHnfs(predicates);

    classEnv |> simplify(hnfs)
}