// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not1(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p __>: !q ) |- ( !(p & q)  )
      Proof(
      1 (  p __>: !q ) by Premise,
      2 SubProof( //Proves !() because it negates
        3 Assume (p & q),
        4 (p) by AndE1(3),
        5 (q) by AndE2(3),
        6 (-q) by ImplyE(1, 4), //imply, proven true
        7 (F) by NegE(5, 6) //Proves false
        //goal (F) - contradiciton
      ),
      8 ( !(p&q)) by NegI(2)

      //If you want to proof a not statement. Assume it's true. Get a contradicition
      //Then use a NegI to assume it is NOT true
    )
  )
}