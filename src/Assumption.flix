///
/// A new type wrapper over `Id` to represent an individual variable.
///
pub enum Variable(Id) with Eq, Hash, Order, ToString


mod Variable {
    pub def fromId(id: Id): Variable = Variable(id)


    pub def fromIdString(idStr: String): Variable = 
        Variable(Id.Id(idStr))
}

pub eff AssumptionNotFoundFailure {
    def notFound(variable: Variable): Void
}


///
/// Represents a type scheme associated with a variable. For example, 
/// if we have a variable `x` with type scheme `forall a. Eq a => a -> a`, 
/// then we can represent this as an assumption where the variable is `x` and 
/// the scheme is `forall a. Eq a => a -> a`.
///               
pub enum Assumption(Variable, Scheme) with Eq, Hash, Order, ToString


mod Assumption {
    pub def create(variable: Variable, scheme: Scheme): Assumption = 
        Assumption(variable, scheme)


    pub def variable(assumption: Assumption): Variable = match assumption {
        case Assumption(variable, _) => variable
    }


    pub def scheme(assumption: Assumption): Scheme = match assumption {
        case Assumption(_, scheme) => scheme
    }
}
