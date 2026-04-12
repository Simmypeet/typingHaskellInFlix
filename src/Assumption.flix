pub enum Variable(Id) with Eq, Hash, Order, ToString


mod Variable {
    pub def fromId(id: Id): Variable = Variable(id)


    pub def fromIdString(idStr: String): Variable = 
        Variable(Id.Id(idStr))
}


pub enum Assumption(Variable, Scheme) with Eq, Hash, Order, ToString


mod Assumption {
    pub def variable(assumption: Assumption): Variable = match assumption {
        case Assumption(variable, _) => variable
    }


    pub def scheme(assumption: Assumption): Scheme = match assumption {
        case Assumption(_, scheme) => scheme
    }
}


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

