// #Sireum #Logika
//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract(
        Requires(
            list.size > 0
        ),
        Modifies(
            list
        ),
        Ensures(
            // All (0 until list.size)(a => list(a) == In(list)(a)),
            //small <= All elements
            All (0 until list.size)(a => Res[Z] <= list(a)), //order doesn't matter on res _ list
            //Some element == small
            ∃ (0 until list.size)(a => Res[Z] == list(a))
        )
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),
            i >= 1, 
            i <= list.size,
            All (0 until i)(a => small <= list(a)), 
            ∃ (0 until i)(a => small == list(a))
        )

        if (list(i) < small) {
            small = list(i)
        }
        i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?
assert(testMin == 0)