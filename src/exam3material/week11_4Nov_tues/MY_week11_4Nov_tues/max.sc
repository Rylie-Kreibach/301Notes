// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = Z.prompt("Enter first number: ")
val y: Z = Z.prompt("Enter second number: ")

//x = 3, y = 4

//how do we assume x is bigger than y?
Assume(x > y)

val max: Z = x

Deduce(
    1 (x > y) by Premise,
    2 (max == x) by Premise,
    3 (max >= x) by Algebra*(2),
    4 (max >= y) by Algebra*(2, 1),
    5 (max == x | max == y) by OrI(2)
)


Assert(max >= x)
Assert(max >= y)
Assert(max == x | max == y)
//what can we put in a proof block here?

//how do we assert max is the biggest between our two inputs?
