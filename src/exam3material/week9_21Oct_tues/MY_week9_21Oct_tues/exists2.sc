// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x (P(x) __>: ¬Q(x)) ⊢ !(∃ x (P(x) & Q(x)))

@pure def exists2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (P(x)) __>: !Q(x))
    )
    |-
    (
      !(∃((x: T) => (P(x) & Q(x))))
    )
      Proof(
      1 ( ∀((x: T) => (P(x)) __>: !Q(x)) ) by Premise,
      2 SubProof(
        3 Assume ∃((x: T) => (P(x) & Q(x))),
        4 Let((a: T) => SubProof(
          5 Assume P(a) & Q(a),
          6 (P(a)) by AndE1(5),
          7 (Q(a)) by AndE2(5),
          8 ((P(a)) __>: !Q(a)) by AllE[T](1),
          9 (!Q(a)) by ImplyE(8, 6),
          10 (F) by NegE(7, 9),
        )),
        11 (F) by ExistsE[T](3, 4)
      ),
      12 (!(∃((x: T) => (P(x) & Q(x))))) by NegI(2)
    )
  )
}