module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleComposition

/-!
# Two successive admissible centres amalgamate into one

Let `Y` be a quasi-compact and quasi-separated scheme, `U ⊆ Y` an open, `I` a finitely presented
centre on `Y` supported away from `U`, and `Z'` a finitely presented centre on the blowup
`b : Bl_I(Y) ⟶ Y` supported away from `b⁻¹(U)`. There is then a single finitely presented centre
`K` on `Y`, supported away from `U`, with

* `Supp K = Supp I ∪ b(Supp Z')`, and
* the two-step blowup `Bl_{Z'}(Bl_I(Y)) ⟶ Y` isomorphic over `Y` to `Bl_K(Y) ⟶ Y`.

Those two clauses are exactly the hypotheses `hK` and `e` of [Stacks, Tag 080I], so this is the
package that every amalgamation of two successive blowups consumes: the composition of admissible
blowups, the amalgamation of two successive flattening centres, and the successive reduction of
[Stacks, Tag 080Y].

## Main results

* `Stacks.Blowup.exists_centre_of_successive`: the statement above.

## Implementation notes

The centre is the product `I · J` of [Stacks, Tag 080B], for `(d, J)` the pair supplied by
`Stacks.Blowup.SecondCentreFactorization`. That hypothesis is still carried here rather than
discharged. The only proof of it is `Stacks.Blowup.exists_factorization_blowUp` of
`StacksFrontier/AlgebraicGeometry/Blowup/SecondCentreFactorization.lean`, which is visible from
here and is what makes `Stacks.Blowup.IsAdmissibleBlowup.comp` unconditional, so this statement
could be made unconditional the same way. The named discharge
`AlgebraicGeometry.secondCentreFactorization` in
`StacksFrontier/AlgebraicGeometry/Blowup/SecondCentre.lean` delegates to that same theorem, and
cannot be used here anyway because that file imports this one.

## References

* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

/-- **Two successive admissible centres amalgamate into one.** Let `I` be a finitely presented
centre on a quasi-compact and quasi-separated scheme `Y`, supported away from an open `U`, and
let `Z'` be a finitely presented centre on the blowup of `Y` in `I`, supported away from the
inverse image of `U`. Then there is a single finitely presented centre `K` on `Y`, supported
away from `U`, whose support is `Supp I ∪ b(Supp Z')` and whose blowup is the two-step blowup
over `Y`.

The centre is the product `I · J` of [Stacks, Tag 080B], for `(d, J)` the pair supplied by
`Stacks.Blowup.SecondCentreFactorization`. The last two clauses are exactly the hypotheses `hK`
and `e` of [Stacks, Tag 080I]. -/
public theorem exists_centre_of_successive {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (factorization : SecondCentreFactorization.{u}) (U : Y.Opens)
    (I : Y.IdealSheafData) (hI : FinitePresentation I.subschemeι)
    (hUI : Disjoint (U : Set Y) (I.support : Set Y))
    (Z' : (AlgebraicGeometry.blowUp I).IdealSheafData)
    (hZ' : FinitePresentation Z'.subschemeι)
    (hUZ' : Disjoint ((AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ U :
        (AlgebraicGeometry.blowUp I).Opens) : Set (AlgebraicGeometry.blowUp I))
      (Z'.support : Set (AlgebraicGeometry.blowUp I))) :
    ∃ K : Y.IdealSheafData, FinitePresentation K.subschemeι ∧
      Disjoint (U : Set Y) (K.support : Set Y) ∧
      K.supportSet = I.supportSet ∪
          (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet ∧
        Nonempty (Over.mk (AlgebraicGeometry.blowUpToBase Z' ≫
          AlgebraicGeometry.blowUpToBase I) ≅ Over.mk (AlgebraicGeometry.blowUpToBase K)) := by
  obtain ⟨d, J, -, hJft, -, -, hcomap⟩ := factorization I hI Z' hZ'
  have hsupp : (I * J).supportSet =
      I.supportSet ∪ (AlgebraicGeometry.blowUpToBase I).base '' Z'.supportSet :=
    AlgebraicGeometry.supportSet_mul_eq_union_image I Z' d J hcomap
  refine ⟨I * J, AlgebraicGeometry.finitePresentation_mul_subschemeι I J hI hJft, ?_, hsupp,
    AlgebraicGeometry.nonempty_blowUpCompositionIso I Z' d J hcomap⟩
  show Disjoint (U : Set Y) ((I * J).supportSet)
  rw [hsupp, Set.disjoint_union_right]
  refine ⟨hUI, Set.disjoint_left.mpr ?_⟩
  rintro x hxU ⟨y, hy, rfl⟩
  exact Set.disjoint_left.mp hUZ' hxU hy

end Stacks.Blowup

end
