// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.prompt("Enter a positive number: ")

assume(x > 0)


//orig will always be the original user input value
val orig: Z = x

//do we need a proof block here? 
Deduce(//Not necessary. There was only one variable change between this and next
    1 (x > 0) by Premise,
    2 (orig == x) by Premise,
)

x = x + 1
Deduce(
    1 (x == Old(x) + 1) by Premise,
    2 (Old(x) > 0 ) by Premise,
    3 (orig == Old(x)) by Premise,
    4 (x > 1 ) by Algebra*(1, 2), //Progress towards assert
    5 (x == orig + 1) by Subst_>(3, 1)
)

//what can we put in a proof block here?
//what should we be able to assert about x and orig?

x = x + 2


//what can we put in a proof block here?
Deduce(
    1 (Old(x) > 1 ) by Premise,
    2 (x == Old(x) + 2) by Premise,
    3 (Old(x) == orig + 1) by Premise,
    4 ( x == orig + 3) by Algebra*(2, 3),
    5 (x > 3) by Algebra*(1, 2)
    
)


//what do we want to assert? How has x changed?



//Once it is working - if x was originally positive,
//how could we assert that x was still positive at the end?
assert(x == orig + 3)
assert(x > 3)