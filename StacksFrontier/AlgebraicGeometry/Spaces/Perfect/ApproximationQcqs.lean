module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08HP: approximation by perfect complexes on a quasi-compact quasi-separated space

**Stacks 08HP.**  Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated
algebraic space over `S`.  Then approximation by perfect complexes holds on `X`.

## The proof

This is the source's proof: the induction principle of Stacks 08GP
(`AlgebraicGeometry.Space.qcqs_induction_on_self`) applied to the property "approximation by
perfect complexes holds", whose affine case is the second assertion of Stacks 08HM
(`AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isAffineSpace`) and whose inductive
step is Stacks 08HN
(`AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isElementaryDistinguishedSquare`).
The quasi-compactness of `U ×_W V` asked for by Stacks 08HN holds because `U` is quasi-compact,
`V` is affine and `W` is quasi-separated (Stacks 073B, part (3)).

Quasi-separatedness is absolute quasi-separatedness,
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`, which is the reading of Stacks 08GP; it is
stated relative to the final object of the category of schemes, which is why that object is
assumed to lie in the big fppf site.

## Main results

* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_qcqs`: **Stacks 08HP**.

## References

* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-- **Stacks 08HP.**  Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated
algebraic space over `S`.  Then approximation by perfect complexes holds on `X`. -/
@[stacks 08HP]
theorem approximationByPerfectComplexes_of_qcqs (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ApproximationByPerfectComplexes.{u, u} B S hS X hX := by
  refine qcqs_induction_on_self B S hS hZ ⟨X, hX⟩ hXqc hXqs
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y,
      ApproximationByPerfectComplexes.{u, u} B S hS Y hY) ?_ ?_ hX
  · intro V hVaff hY
    exact approximationByPerfectComplexes_of_isAffineSpace B S hS V.1.left.1 hY hVaff
  · intro W V U f _ hsq _ hWqs hUqc hVaff hPU _ _ hW
    have hUVqc : IsQuasiCompactSpace B S hS (U.preimage f).toFunctor :=
      isQuasiCompactSpace_of_iso B S hS (Subfunctor.isPullback_preimage f U).isoPullback.symm
        (isQuasiCompactSpace_pullback B S hS hZ U.ι f hsq.isOpenSubspace.1 W.1.left.property
          hUqc hVaff.isQuasiCompactSpace hWqs)
    exact approximationByPerfectComplexes_of_isElementaryDistinguishedSquare B S hS hW U f hsq
      hUqc hVaff hUVqc (hPU hsq.isOpenSubspace.1)

end AlgebraicGeometry.Space
