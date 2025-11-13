// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?
  Contract(
    Requires(y>=0),
    Ensures(Res[Z] == x * y)
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0
    Deduce(
      1 (y == 0) by Premise,
      2 (answer == 0) by Premise,
      3 (answer == x * y) by Algebra*(2, 1)
    )
    //what do we need to do here?
  } else {
    Deduce( //must prove pre-conditions for function call
      1 ( !(y == 0)) by Premise,
      2 (y != 0) by Algebra*(1), //What you're passing
      // 3 (answer == 0) by Premise, 
      4 (y >= 0) by Premise,
      5 ((y-1) >= 0) by Algebra*(2, 4) //Proved precondition
    )
    var temp: Z = mult(x, y-1) //recurse down 
    
    answer = x + temp
    Deduce(
      1 (answer == x + temp) by Premise,
      2 (temp == x * (y-1)) by Premise, //post condition
      3 (temp == x * y - x) by Algebra*(2),
      4 (answer == x + x*y - x) by Algebra*(1, 3),
      5 (answer == x * y) by Algebra*(4)
      
    )
    //what do we need to show here?
  }

  //what do we need to do here?
  Deduce(
    1 (answer == x * y) by Premise //Ensures
  )

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

Deduce(
  1 (a == 5) by Premise,
  2 (b == 4) by Premise,
  3 (b >= 0) by Algebra*(2)
)
var ans: Z = mult(a, b)
Deduce(
  1 (a == 5) by Premise,
  2 (b == 4) by Premise,
  3 (ans == a * b) by Premise,
  4 (ans == 5 * 4) by Algebra*(3,2,1),
  5 (ans == 20) by Algebra*(4)
)

assert (ans == 20)
//what do we want to assert that ans is?