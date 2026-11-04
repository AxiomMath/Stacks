module

public import StacksFrontier.RingTheory.Rig.Algebraization.PerturbationStableQuotients
public import StacksFrontier.RingTheory.Rig.Algebraization.RigEtaleAlgebraization

/-!
# Algebraization of rig-smooth algebras: the G-ring and the rig-étale cases

Let `I` be an ideal of a Noetherian ring `A` and let `B` be an object of the category of
Stacks 0AL4 which is rig-smooth over `(A, I)`. Remark 0GAX of the Stacks Project records that
`B` is the `I`-adic completion of a finite type `A`-algebra, by [Gabber–Zavyalov, Theorem 1.2],
and lists partial results which that theorem supersedes. This file proves the first two of them:

1. if `A` is a G-ring, the result follows from Proposition 0GAT
   (`Rig.exists_finiteType_adicCompletion_algEquiv_of_isGRing_of_isRigSmooth`);
2. if `B` is rig-étale over `(A, I)`, the result follows from Lemma 0AKA
   (`Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigEtale`).

Proposition 0GAT produces the finite type algebra in the universe `max u v` and Lemma 0AKA in the
universe `u` of `A`; the statement below uses `max u v`, lifting the second along `ULift`.

The remaining claims of the remark — [Gabber–Zavyalov, Theorem 1.2] in general, and the principal
case [Elkik, III Theorem 7] — are proved elsewhere; the remark is registered on
`Rig.isRigSmooth_algebraization` in
`StacksFrontier/RingTheory/Rig/Algebraization/RigSmoothAlgebraizationGZ.lean`, which uses the lemma of
this file for its first two partial results.

## Main results

* `Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_of_isGRing_or_isRigEtale`

## References

* [Stacks Project, Tag 0GAX](https://stacks.math.columbia.edu/tag/0GAX)
* [Stacks Project, Tag 0GAT](https://stacks.math.columbia.edu/tag/0GAT)
* [Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
-/

@[expose] public section

universe u v

namespace Rig

/-- **Parts (1) and (2) of Stacks Remark 0GAX.** Let `I` be an ideal of a Noetherian ring `A` and
let `B` be an object of the category of Stacks 0AL4 which is rig-smooth over `(A, I)`. If `A` is
a G-ring, or if `B` is rig-étale over `(A, I)`, then there is a finite type `A`-algebra `C` and
an isomorphism `B ≅ C^∧` of `A`-algebras with the `I`-adic completion of `C`.

The first case is Proposition 0GAT, the second is Lemma 0AKA, whose algebra lies in the universe
of `A` and is lifted to `max u v`. -/
public theorem exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_of_isGRing_or_isRigEtale
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigSmooth B)
    (h : IsGRing A ∨ IsRigEtale B) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  rcases h with hA | hEt
  · exact exists_finiteType_adicCompletion_algEquiv_of_isGRing_of_isRigSmooth A hA I B hB
  · obtain ⟨C₀, _, _, hC₀, ⟨e⟩⟩ := exists_finiteType_algEquiv_adicCompletion_of_isRigEtale B hEt
    let E : C₀ ≃ₐ[A] ULift.{max u v} C₀ := ULift.algEquiv.symm
    exact ⟨ULift.{max u v} C₀, inferInstance, inferInstance, Algebra.FiniteType.equiv hC₀ E,
      ⟨e.trans (adicCompletionCongr I E)⟩⟩

end Rig

end
