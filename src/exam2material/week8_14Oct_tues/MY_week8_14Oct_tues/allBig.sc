// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,
      4 Let ((i: T) => SubProof(
        5 SubProof(
          6 Assume(P(i) | Q(i)),
          7 SubProof(
            8 Assume (R(i)),
            9 (P(i) __>: B(i)) by AllE[T](1),
            10 (Q(i) __>: C(i)) by AllE[T](2),
            11 (R(i) __>: !B(i) & !C(i)) by AllE[T](3),
            12 (R(i) __>: !B(i)) by AndE1(11),
            13 (!C(i)) by AndE2(11),
            14 (!B(i)) by ImplyE(12, 8),
            15 SubProof(
              16 Assume(P(i)),
              17 (B(i)) by ImplyE(9, 16),
              18 (F) by NegE(17, 14),
            ),
            19 SubProof(
              20 Assume(Q(i)),
              21 (C(i)) by ImplyE(10, 20),
              22 (F) by NegE(21, 13)
            ),
            23 (F) by OrE(6, 15, 19)
          ),
          24 (!R(i)) by NegI(7)
          
        ),
        25 (P(i) | Q(i) __>: !R(i)) by ImplyI(5)

      )),
      26 (∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))) by AllI[T](4)
    )
  )
}