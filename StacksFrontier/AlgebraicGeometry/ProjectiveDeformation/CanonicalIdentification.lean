module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistIdentification

/-!
# The canonical isomorphism `r'` and the canonical twist map `θ'` of a deformation

For an admissible deformation `(X', S', i, i', f', ℒ')` of a polarized family and a positive cut
`d₀`, the source's proof of [Stacks, Tag 0D4F] describes `r'` and `θ'` before anything else:

* `ℒ'` is ample relative to `f'` ([Stacks, Tag 0D2R]);
* the comparison `ψ : 𝒜' ⟶ ⨁_{d ≥ 0} (f')_* (ℒ')^{⊗ d}` is an isomorphism in degrees `≥ d₀`, so it
  induces an isomorphism `Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d) ⟶ Proj_{S'}(𝒜')` compatible with the Serre
  twists ([Stacks, Tag 07ZJ]);
* `r'` is the composite of the morphism `r_{ℒ', ψ} : X' ⟶ Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)` of
  [Stacks, Tag 01VJ] with that isomorphism, and
* `θ'` is the map `θ` of [Stacks, Tag 01O9] in degree one for `r_{ℒ', ψ}`, read through the map of
  Serre twists of [Stacks, Tag 07ZJ].

This file *defines* `r'` and `θ'` that way and proves that both are isomorphisms.

## Main definitions

* `…AdmissibleDeformation.canonicalProjHom`: `r' : X' ⟶ Proj_{S'}(𝒜')`.
* `…AdmissibleDeformation.canonicalTwistMap`: `θ' : (r')^* 𝒪_{Proj_{S'}(𝒜')}(1) ⟶ ℒ'`.

## Main results

* `…AdmissibleDeformation.isIso_canonicalProjHom`, `…canonicalProjHom_comp_toBase`.
* `…AdmissibleDeformation.isIso_canonicalTwistMap`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

namespace PolarizedFamily.AdmissibleDeformation

variable {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- **`ℒ'` is ample relative to `f'`**, [Stacks, Tag 0D2R]. -/
theorem isRelativelyAmple_L' : Stacks.RelativeAmple.IsRelativelyAmple D.f' D.L' :=
  relativelyAmpleLiftsAlongThickening P.X D.X' P.S D.S' P.f D.f' D.i D.i' D.isThickening
    D.isPullback D.L' P.L ⟨D.polarization⟩ P.isRelativelyAmple

/-- The comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d` is an isomorphism in every degree `d ≥ d₀`. -/
theorem isIso_sectionAlgebraComparison_app (d : ℕ) (hd : d₀ ≤ d) :
    IsIso ((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)) :=
  Stacks.AlgebraicGeometry.SectionAlgebra.isIso_tailCompApp D.laurentPushforward d₀ hd₀
    (show ¬ (d : ℤ) = 0 by omega) (show (d₀ : ℤ) ≤ (d : ℤ) by omega)
    (show (0 : ℤ) ≤ (d : ℤ) by omega)

/-- The comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d` is eventually an isomorphism, the input to the
isomorphism of relative `Proj` of [Stacks, Tag 07ZJ] used to define `r'`. -/
theorem eventually_isIso_sectionAlgebraComparison :
    ∀ᶠ d : ℕ in Filter.atTop, IsIso ((D.sectionAlgebraComparison d₀ hd₀).app (d : ℤ)) :=
  Filter.eventually_atTop.2 ⟨d₀, D.isIso_sectionAlgebraComparison_app d₀ hd₀⟩

/-- **The canonical morphism `r' : X' ⟶ Proj_{S'}(𝒜')`** of [Stacks, Tag 0D4F] (4): the morphism
`r_{ℒ', ψ}` of [Stacks, Tag 01VJ] into `Proj_{S'}(⨁_{d ≥ 0} 𝒜'_d)` followed by the isomorphism of
[Stacks, Tag 07ZJ] induced by the comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d`. -/
def canonicalProjHom : D.X' ⟶ (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).scheme :=
  D.fullSectionProjHom D.isRelativelyAmple_L' ≫
    projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
      (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)

/-- **`r'` is an isomorphism**: [Stacks, Tag 0C6J] for `r_{ℒ', ψ}` and [Stacks, Tag 07ZJ] for the
comparison of relative `Proj`. -/
instance isIso_canonicalProjHom : IsIso (D.canonicalProjHom d₀ hd₀) := by
  unfold canonicalProjHom
  infer_instance

/-- **`r'` is a morphism over `S'`.** -/
theorem canonicalProjHom_comp_toBase :
    D.canonicalProjHom d₀ hd₀ ≫ (relativeProj (D.truncatedSectionAlgebra d₀ hd₀)).toBase =
      D.f' := by
  rw [canonicalProjHom, Category.assoc, projTruncationComparison_comp_toBase]
  exact D.fullSectionProjHom_comp_toBase _

/-- **The canonical map `θ' : (r')^* 𝒪_{Proj_{S'}(𝒜')}(1) ⟶ ℒ'`** of [Stacks, Tag 0D4F] (5): the
map of Serre twists of [Stacks, Tag 07ZJ] for the comparison `𝒜' ⟶ ⨁_{d ≥ 0} 𝒜'_d`, pulled back
along `r_{ℒ', ψ}`, followed by the degree-one component of the map `θ` of [Stacks, Tag 01O9] for
`r_{ℒ', ψ}` (`Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistIso`). -/
def canonicalTwistMap :
    (Scheme.Modules.pullback (D.canonicalProjHom d₀ hd₀)).obj
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist (D.truncatedSectionAlgebra d₀ hd₀) 1) ⟶
      D.L' :=
  haveI := D.finitePresentation.quasiCompact
  haveI := D.finitePresentation.quasiSeparated
  ((Scheme.Modules.pullbackComp (D.fullSectionProjHom D.isRelativelyAmple_L')
      (projTruncationComparison (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀))).inv.app _) ≫
    (Scheme.Modules.pullback (D.fullSectionProjHom D.isRelativelyAmple_L')).map
      (projTruncationTwistIso (D.sectionAlgebraComparison d₀ hd₀)
        (D.eventually_isIso_sectionAlgebraComparison d₀ hd₀)).hom ≫
    (Stacks.RelativeAmple.TwistIdentification.relativeAmpleTwistIso D.f' D.L'
      D.isRelativelyAmple_L').hom

/-- **`θ'` is an isomorphism**: the map of Serre twists of [Stacks, Tag 07ZJ] is one, and so is the
degree-one component of `θ` by [Stacks, Tag 01QI] (2) over the base. -/
instance isIso_canonicalTwistMap : IsIso (D.canonicalTwistMap d₀ hd₀) := by
  have := D.finitePresentation.quasiCompact
  have := D.finitePresentation.quasiSeparated
  unfold canonicalTwistMap
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
  · exact ⟨_, ((Scheme.Modules.pullbackComp _ _).app _).inv_hom_id,
      ((Scheme.Modules.pullbackComp _ _).app _).hom_inv_id⟩
  · exact Functor.map_isIso _ _
  · exact ⟨_, Iso.hom_inv_id _, Iso.inv_hom_id _⟩

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
