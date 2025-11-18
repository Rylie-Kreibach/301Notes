// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
//n == 3 then 2 + 4 + 6
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(n >= 0),
    Ensures(Res[Z] == n * (n + 1))
  )


  var sum: Z = 0
  var cur: Z = 0
  Deduce(
    1 (sum == 0) by Premise,
    2 (cur == 0) by Premise,
    3 (n >= 0) by Premise,
    4 (sum == cur * (cur + 1)) by Algebra*(1, 2)
  )
  while (cur != n) {
    //what about our loop invariant?
    Invariant(
      Modifies(cur, sum),
      sum == cur * (cur + 1)
    )


    cur = cur + 1
    Deduce(
      1 (cur == Old(cur) + 1) by Premise,
      2 (sum == Old(cur) * (Old(cur) + 1)) by Premise,
      3 (Old(cur) == cur - 1) by Algebra*(1),
      4 (sum == (cur - 1) * (cur - 1 + 1)) by Algebra*(2,3),
      5 (sum == (cur - 1) * cur) by Algebra*(4)
    )
    sum = sum + 2*cur
    Deduce(
      1 (sum == Old(sum) + 2 * cur) by Premise,
      2 (Old(sum) == (cur - 1) * cur) by Premise,
      3 (sum == ((cur-1) * cur) + 2 * cur) by Algebra*(1,2),
      4 (sum == cur * (cur + 1)) by Algebra*(3)
    )
  }
  Deduce(
    1 (sum == cur * (cur + 1)) by Premise,
    2 ( !(cur != n)) by Premise,
    3 (cur == n) by Algebra*(2),
    4 (sum == n * (n +1)) by Subst_<(3, 1)
  )
  return sum
}

//////////// test code /////////

val num: Z = 5
Deduce(
  1 (num == 5) by Premise,
  2 (num >= 0) by Algebra*(1)
)
var sum5evens: Z = sumEvens(num)
Deduce(
  1 (sum5evens == num * (num + 1)) by Premise,
  2 (num == 5) by Premise,
  3 (sum5evens == 5 * (5 + 1)) by Subst_<(2, 1),
  4 (sum5evens == 30) by Algebra*(3)
)

assert (sum5evens == 30)
//sum of first 5 evens: ?
