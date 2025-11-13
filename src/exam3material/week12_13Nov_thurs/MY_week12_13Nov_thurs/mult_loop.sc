// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(y >= 0),
    Ensures(Res[Z] == x * y)
  )


  var total: Z = 0
  var i: Z = 0

  //what goes here?
  Deduce(
    1 (total == 0) by Premise,
    2 (i == 0) by Premise,
    3 (total == x*i) by Algebra*(1,2) //prove condition pre-loop
  )
  while (i != y) {
    Invariant(
      Modifies(i, total),
      total == x * i //Requires pre check and post iteration check
    )
    //what goes here?

    total = total + x
    Deduce(
      1 (Old(total) == x * i) by Premise, //from invariant
      2 (total == Old(total) + x) by Premise,
      3 (total == x * i + x) by Algebra*(1, 2)
    ) //2 changes requires a proof between
    i = i + 1

    Deduce(
      1 (i == Old(i) + 1) by Premise,
      2 (total == x * Old(i) + x) by Premise,
      3 (total == x * (Old(i) + 1)) by Algebra*(2),
      4 (total == x * i) by Subst_>(1, 3) //prove condition after loop
    )
    //what should we be able to assert here?
  }

  Deduce(
    1 ( !(i!= y)) by Premise,
    2 (i == y) by Algebra*(1),
    3 ( total == x * i) by Premise,
    4 (total == x * y) by Algebra*(3, 2)
  )

  //what do we need here?

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

Deduce(
  1 (a == 5) by Premise,
  2 (b == 4) by Premise,
  3 (b >= 0 ) by Algebra*(2)
)
var ans: Z = mult(a, b)
Deduce(
  1 (a == 5) by Premise,
  2 (b == 4) by Premise,
  3 (ans == a * b) by Premise,
  4 (ans == 20) by Algebra*(3, 2, 1)
)

assert(ans == 20)
//what do we want to assert that ans is?