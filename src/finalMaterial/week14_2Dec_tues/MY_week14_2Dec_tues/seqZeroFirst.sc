// #Sireum #Logika

import org.sireum._

//"Unit" is like a void return type
def makeFirstZero(seq: ZS): Unit = {
  Contract(
    Requires(
      seq.size > 0,
    ),
    Modifies(
      seq
    ),
    Ensures(
      seq(0) == 0,
      All(1 until seq.size)(x=> (seq(x) == In(seq)(x))) //z can be any variable
      //In(seq)(x) : old sequence
      //or ∀ ...
    )
  )

  seq(0) = 0
  //how would we write the function contract?
  //what do we want to require of seq?
  //how can we describe how seq will change?
}

///// Test code ///////////

var nums: ZS = ZS(1,2,3)
makeFirstZero(nums)

//---> what should we assert?
assert(nums == ZS(0,2,3))