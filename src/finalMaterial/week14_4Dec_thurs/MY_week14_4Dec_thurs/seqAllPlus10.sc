// #Sireum #Logika

//∀ ∃

import org.sireum._

//add 10 to all elements
def allPlus10(nums: ZS): Unit = {
  //function contract?
  Contract(
    // Requires(
    //   //size doesn't matter since while loop
    //   //nothing
    // ),
    Modifies( nums ), //only needed if a reference call is changed
    Ensures(
      All (0 until nums.size)(k => nums(k) == In(nums)(k) + 10)
    )
  )


  var i: Z = 0
  while (i < nums.size) {
    //loop invariant block?
    Invariant(
      Modifies(nums, i),
      i >= 0, 
      i <= nums.size, //bound loop counter. 
      //must be true after each interation so can't be (i <= nums.size - 1)
      
      nums.size == In(nums).size, //size doesn't change

      All (0 until i)(k => nums(k) == In(nums)(k) + 10), //what has changed?
      All (i until nums.size)(k => nums(k) == In(nums)(k)) //hasn't changed
    
    )

    nums(i) = nums(i) + 10
    i = i + 1
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

allPlus10(test)

//what do we want to assert?
assert(test == ZS(14, 11, 13, 18, 20, 12))