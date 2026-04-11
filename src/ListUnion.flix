pub def listUnion(list1: List[a], list2: List[a]): List[a] with Eq[a] = {
    // this might not be the most efficient way
    def helper(
        remaining: List[a],
        acc: List[a]
    ) : List[a] = match remaining {
        case Nil => acc
        case head :: tail => 
            if (acc |> List.memberOf(head)) {
                helper(tail, acc)
            } else {
                helper(tail, head :: acc)
            }
    };

    let first = helper(list1, Nil);

    helper(list2, first)
}