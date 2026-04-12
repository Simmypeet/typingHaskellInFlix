///
/// A new type wrapper over `Id` to represent an individual variable.
///
pub enum Variable(Id) with Eq, Hash, Order, ToString


mod Variable {
    pub def fromId(id: Id): Variable = Variable(id)


    pub def fromIdString(idStr: String): Variable = 
        Variable(Id.Id(idStr))
}


///
/// Represents a type scheme associated with a variable. For example, 
/// if we have a variable `x` with type scheme `forall a. Eq a => a -> a`, 
/// then we can represent this as an assumption where the variable is `x` and 
/// the scheme is `forall a. Eq a => a -> a`.
///               
pub enum Assumption(Variable, Scheme) with Eq, Hash, Order, ToString


mod Assumption {
    pub def variable(assumption: Assumption): Variable = match assumption {
        case Assumption(variable, _) => variable
    }


    pub def scheme(assumption: Assumption): Scheme = match assumption {
        case Assumption(_, scheme) => scheme
    }
}

///
/// A collection of assumptions, essentially a mapping from variables to their
/// type schemes. In the paper, it seems to use linear search to find the type
/// scheme for a variable for some reason, but it's more efficient to use a map.
///
pub enum Assumptions(List[Assumption]) with Eq, Hash, Order, ToString


mod Assumptions {
    pub def empty(): Assumptions = Assumptions(Nil)


    pub def add(variable: Variable, scheme: Scheme, assumptions: Assumptions): Assumptions =
        Assumptions.Assumptions(
           Assumption.Assumption(variable, scheme) :: assumptions |> assumptionList
        )


    def assumptionList(assumptions: Assumptions): List[Assumption] = 
        match assumptions {
            case Assumptions(assumps) => assumps
        } 

    
    pub def lookup(variable: Variable, assumptions: Assumptions): Option[Scheme] =
        assumptions
            |> assumptionList
            |> List.findMap(x -> {
                if (x |> Assumption.variable == variable) 
                    Some(x |> Assumption.scheme)
                else None
            })
}

