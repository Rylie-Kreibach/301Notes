// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( (p | q ) & (p | r) ) |- ( p | (q & r) )
      Proof(
        1 ((p | q ) & (p | r)) by Premise,
        2 (p | q) by AndE1(1),
        3 (p | r) by AndE2(1),
        4 SubProof(
          5 Assume (p),
          6 (p | (q & r)) by OrI1(5)
        ),
        7 SubProof(
          8 Assume(q),
          9 SubProof (
            10 Assume(p),
            11 (p | (q & r)) by OrI1(10)
          ),
          12 SubProof(
            13 Assume(r),
            14 (q & r) by AndI(8, 13),
            15 (p | (q & r)) by OrI2(14)
          ),
          16 (p | (q & r)) by OrE(3, 9, 12),
        ),
        17 SubProof(//(p | r)
          18 Assume(p),
          19 (p | (q & r)) by OrI1(5)
        ),
        18 SubProof(

        ),
        
        // 22 (p | (q & r)) by OrE(1, 4, 17)
    )
  )
}