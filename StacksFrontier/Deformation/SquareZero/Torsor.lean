module

public import StacksFrontier.Deformation.SquareZero.Torsor.ObstructionClass
public import StacksFrontier.Deformation.SquareZero.Torsor.TwistCochain
public import StacksFrontier.Deformation.SquareZero.Torsor.TwistCarrier
public import StacksFrontier.Deformation.SquareZero.Torsor.IsomorphismClasses

/-!
# Choices of square-zero extensions (Stacks 08S7)

Let `A' → A` be a surjection of rings with square-zero kernel `I`, let `A → B` be a ring
map, let `N` be a `B`-module and let `c : I → N` be `A`-linear, as in **Stacks 08S4**.  If
the resulting square-zero extension problem has a solution, then its set of isomorphism
classes of solutions is a principal homogeneous space under `Ext¹_B(NL_{B/A}, N)`.

The Stacks proof runs as follows.  Writing `E = B` as a set and `A[E] → B` for the
canonical presentation with kernel `J`, freeness of `Ω_{A[E]/A} ⊗ B` identifies
`Ext¹_B(NL_{B/A}, N)` with the cokernel `conormalCokernel` of precomposition with the
conormal differential.  Given two solutions `X` and `Y`, **Stacks 08S5** produces a
conormal functional `obstructionFunctional X Y`, whose class `obstructionCokernelClass`
vanishes exactly when `X ≅ Y`; so these classes separate isomorphism classes, and they add
up along triples.  It remains to show that every class is realised.  For that, write
`J' = ker (A'[E] → B)`, let `φ : A'[E] → X.B'` be the evaluation at chosen lifts of the
variables, and let `δ : J/J² → N` represent the given class.  The solution realising `δ` is
the pushout of `A'[E]` along `ψ = φ|_{J'} + δ`.  Here that pushout is built in place:
`TwistCarrier X δ` is a copy of the ring of `X` whose addition and multiplication are
deformed by the two cochains `twistAddCochain δ` and `twistMulCochain δ` of the normalised
section `b ↦ x_b - x_0`, and `twistEval` is the induced ring map `A'[E] → TwistCarrier X δ`,
i.e. the pushout structure map.

## Main definitions

* `Stacks.Deformation.conormalCokernel`: the presentation
  `Hom_B(J/J², N) / Hom_B(Ω_{A[E]/A} ⊗ B, N)` of `Ext¹_B(NL_{B/A}, N)`.
* `Stacks.Deformation.obstructionCokernelClass`: the obstruction class of a pair of
  solutions, read in that cokernel.
* `Stacks.Deformation.TwistCarrier` and `Stacks.Deformation.twistExtension`: the twist of a
  solution by a conormal functional, the in-place form of the Stacks pushout.

## Main results

* `Stacks.Deformation.isomorphismClassesTorsor`: **Stacks 08S7**.
* `Stacks.Deformation.isomorphismClasses_vsub_eq_obstructionClass`: **Stacks 08S7**, the
  statement that the torsor difference `[Y] -ᵥ [X]` is the obstruction class of 08S5.
* `Stacks.Deformation.obstructionCokernelClass_eq_zero_iff`: the obstruction class vanishes
  exactly when the two solutions are isomorphic.
* `Stacks.Deformation.exists_obstructionCokernelClass_eq`: every class is the obstruction
  class of a twist, which is the transitivity half of the torsor statement.

## References

* [Stacks Project, Tag 08S7](https://stacks.math.columbia.edu/tag/08S7)
-/
