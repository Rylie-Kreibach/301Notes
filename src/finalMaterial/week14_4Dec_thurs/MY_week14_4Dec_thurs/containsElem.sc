// #Sireum #Logika

//∀ ∃

import org.sireum._

//returns whether an element is in a sequence
//returns true/false (B is bool)
//can either write true or T, same with false
def containsElem(nums: ZS, elem: Z): B = {
    //contract?
    Contract(
        Ensures(
            Res[B] == true __>: ∃(0 until nums.size)(q => elem == nums(q)),
            //if true then one of the elements ==

            Res[B] == false __>: All(0 until nums.size)(m => elem !=nums(m)) //could be !∃(...)
            //if false then elements !=
        )
    )

    var i: Z = 0
    var found: B = false
    while (i < nums.size) {
        //invariant?
        Invariant(
            Modifies(i, found),
            i >= 0,
            i <= nums.size,
            found == true __>: ∃(0 until i)(q => elem == nums(q)),
            found == false __>: All(0 until i)(m => elem != nums(m))
        )

        if (nums(i) == elem) {
            found = true
        }
        i = i + 1
    }

    return found
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testFound: B = containsElem(test, 0)

//what should testFound be?
assert(testFound == true)

testFound = containsElem(test, 4)

//what should testFound be?
assert(testFound == false)
