// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


@pure def orDist1(p: B, q: B, r: B): Unit = {
  Deduce(
    (p | (q & r)) |- ( (p | q ) & (p | r) )
      Proof(
        1 ( p | (q & r) ) by Premise,
        2 SubProof(
          3 Assume (p),
          4 (p | q) by OrI1(3),
          5 (p | r) by OrI1(3),
          6 ((p | q) & (p | r)) by AndI(4, 5)
        ),
        7 SubProof(
          8 Assume (q & r),
          9 (r) by AndE2(8),
          10 (q) by AndE1(8),
          11 (p | q) by OrI2(10),
          12 (p | r) by OrI2(9),
          13 ((p | q) & (p | r)) by AndI(11, 12)
        ),
        14 ((p | q) & (p | r)) by OrE(1, 2, 7)
        
    )
  )
}