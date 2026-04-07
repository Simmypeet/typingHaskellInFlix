pub enum ClassEnvironment(
    Map[ClassId, Class],
    List[Type]
)


enum AddClassError {
    case ClassAlreadyExists,
    case UnknownSuperClass(ClassId)
}


enum AddInstanceError {
    case ClassNotFound(ClassId)
    case OverlappingInstance(Instance)
}


mod ClassEnvironment {
    pub def empty(): ClassEnvironment = 
        ClassEnvironment(Map.empty(), List.empty())


    def getClassMap(env: ClassEnvironment): Map[ClassId, Class] = match env {
        case ClassEnvironment(classMap, _) => classMap
    }


    def defaultTypes(env: ClassEnvironment): List[Type] = match env {
        case ClassEnvironment(_, types) => types
    }


    pub def getSuperClasses(
        classId: ClassId, 
        env: ClassEnvironment
    ): List[ClassId] = {
        getClassMap(env) 
            |> Map.get(classId) 
            |> Option.map(Class.superClasses)
            |> Option.getWithDefault(bug!("classId is not found"))
    }


    pub def getInstances(
        classId: ClassId, 
        env: ClassEnvironment
    ): List[Instance] = {
        getClassMap(env) 
            |> Map.get(classId) 
            |> Option.map(Class.instances)
            |> Option.getWithDefault(bug!("classId is not found"))
    }


    pub def addClass(
        classId: ClassId, 
        superClasses: List[ClassId],
        env: ClassEnvironment
    ): Result[AddClassError, ClassEnvironment] = {
        let classMap = getClassMap(env);

        if (classMap |> Map.memberOf(classId)) {
            Err(AddClassError.ClassAlreadyExists)
        } else {
            let unknownSuperClass = superClasses 
                |> List.find(x -> classMap |> Map.memberOf(x));

            match unknownSuperClass {
                case Some(unknown) => {
                    Err(AddClassError.UnknownSuperClass(unknown))
                }

                case None => {
                    let newClassMap = Map.insert(
                        classId, 
                        Class.newWithSupers(superClasses), 
                        classMap
                    );

                    match env {
                        case ClassEnvironment(_, types) => 
                            Ok(ClassEnvironment(newClassMap, types))
                    }
                }
            }
        }
    }


    pub def addInstance(
        inst: Instance, 
        env: ClassEnvironment
    ): Result[AddInstanceError, ClassEnvironment] = {
        let classMap = getClassMap(env);
        let classId = inst |> Instance.headClassId;

        match Map.get(classId, classMap) {
            case Some(cls) => {
                let existingInstances = Class.instances(cls);

                let overlappingInstance = existingInstances 
                    |> List.find(i -> {
                        let iHead = i |> Instance.head;
                        let instHead = inst |> Instance.head;

                        Mgu.mgu(iHead, instHead) 
                            |> Option.nonEmpty
                    });
                
                match overlappingInstance {
                    case Some(overlap) => Err(
                        AddInstanceError.OverlappingInstance(overlap)
                    )

                    case None => {
                        let newClassMap = Map.insert(
                            classId, 
                            Class.addInstance(inst, cls), 
                            classMap
                        );
                        let defaultTypes = defaultTypes(env);

                        Ok(ClassEnvironment(newClassMap, defaultTypes))
                    }
                }
            }

            case None => Err(AddInstanceError.ClassNotFound(classId))
        }
    }
}