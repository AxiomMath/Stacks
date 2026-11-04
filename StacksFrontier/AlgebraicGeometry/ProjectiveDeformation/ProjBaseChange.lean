module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.ChartDescription
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.Functoriality
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.Theta

/-!
# The morphism of relative `Proj` attached to a morphism of deformations

For a morphism `φ : D₁ ⟶ D₂` of admissible deformations over `g : S'₁ ⟶ S'₂`, pulling sections back
gives the homomorphism of graded algebras `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` (`algebraPullbackHom`), which is
an isomorphism in every degree for the cut `d₀` of [Stacks, Tag 0D4F]. This file builds the
induced morphism

`Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₁}(g^* 𝒜'(D₂)) ⟶ Proj_{S'₂}(𝒜'(D₂))`,

the morphism of [Stacks, Tag 07ZG] for `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` (an isomorphism by
[Stacks, Tag 07ZJ]) followed by the base change morphism of [Stacks, Tag 01O3], and computes it on
the charts of [Stacks, Tag 01NQ].

## Main definitions

* `…ProjectiveDeformation.projMapOfEventuallyIso`: the morphism of [Stacks, Tag 07ZG] attached
  to a homomorphism of graded algebras invertible in all large degrees, on the whole relative
  `Proj`.
* `…AdmissibleDeformation.Hom.algebraPullbackSheafHom`: `algebraPullbackHom` as a homomorphism
  `g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` of `SheafGradedAlgebra`s.
* `…AdmissibleDeformation.Hom.projBaseChangeHom`: the morphism
  `Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))`.

## Main results

* `…ProjectiveDeformation.chart_comp_projMapOfEventuallyIso`: the morphism of
  [Stacks, Tag 07ZG] on the charts.
* `…AdmissibleDeformation.Hom.chart_comp_projBaseChangeHom`: `projBaseChangeHom` on the charts.
* `…AdmissibleDeformation.Hom.isPullback_projBaseChangeHom`: `Proj_{S'₁}(𝒜'(D₁))` is the base
  change of `Proj_{S'₂}(𝒜'(D₂))` along `g`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

section General

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)
  (hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)))

/-- **`Proj_S(B)` is the domain `U(ψ)`** of [Stacks, Tag 07ZG] for a homomorphism `ψ : A ⟶ B`
invertible in all large degrees (clause (1) of [Stacks, Tag 07ZJ]): the inverse of the inclusion
of `U(ψ)`. -/
def projRetract : (relativeProj B).scheme ⟶ ψ.relativeMapDomain.toScheme :=
  (Scheme.topIso _).inv ≫ (((relativeProj B).scheme).isoOfEq
    (relativeMapDomain_eq_top_of_eventually_isIso ψ hψ).symm).hom

/-- The retract is a section of the inclusion of `U(ψ)`. -/
theorem projRetract_comp_ι : projRetract ψ hψ ≫ ψ.relativeMapDomain.ι = 𝟙 _ := by
  rw [projRetract, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]

/-- **The morphism `Proj_S(B) ⟶ Proj_S(A)` of [Stacks, Tag 07ZG]** for a homomorphism
`ψ : A ⟶ B` invertible in all large degrees, read on the whole of `Proj_S(B)`: by clause (1) of
[Stacks, Tag 07ZJ] the domain `U(ψ)` is everything. -/
def projMapOfEventuallyIso : (relativeProj B).scheme ⟶ (relativeProj A).scheme :=
  projRetract ψ hψ ≫ Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom ψ

/-- Clause (2) of [Stacks, Tag 07ZJ]: it is an isomorphism. -/
instance isIso_projMapOfEventuallyIso : IsIso (projMapOfEventuallyIso ψ hψ) := by
  have := isIso_relativeMapHom_of_eventually_isIso ψ hψ
  rw [projMapOfEventuallyIso, projRetract]
  infer_instance

/-- It is a morphism over `S`. -/
theorem projMapOfEventuallyIso_comp_toBase :
    projMapOfEventuallyIso ψ hψ ≫ (relativeProj A).toBase = (relativeProj B).toBase := by
  rw [projMapOfEventuallyIso, Category.assoc,
    Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom_comp_toBase, ← Category.assoc,
    projRetract_comp_ι, Category.id_comp]

/-- **The morphism of [Stacks, Tag 07ZG] on the chart over an affine open `V`**: the morphism of
[Stacks, Tag 01MY] for `Γ(V, A) ⟶ Γ(V, B)` followed by the chart of `Proj_S(A)`, through any
section `m` of the inclusion of its domain. -/
theorem chart_comp_projMapOfEventuallyIso (V : S.Opens) (hV : IsAffineOpen V)
    (m : (AlgebraicGeometry.Proj (B.grading V)) ⟶
      (mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).toScheme)
    (hm : m ≫ (mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).ι = 𝟙 _) :
    (relativeProj B).chart V hV ≫ projMapOfEventuallyIso ψ hψ =
      m ≫ mapHom (A.grading V) (B.grading V) (ψ.sectionHom V) ≫ (relativeProj A).chart V hV := by
  have key := Stacks.AlgebraicGeometry.Tag07ZGMorphism.chart_comp_relativeMapHom ψ ⟨V, hV⟩
  have hfac : (relativeProj B).chart V hV ≫ projRetract ψ hψ =
      m ≫ (((relativeProj B).chart V hV).isoImage
          (mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V))).hom ≫
        (relativeProj B).scheme.homOfLE
          (Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_le ψ ⟨V, hV⟩) := by
    rw [← cancel_mono ψ.relativeMapDomain.ι, Category.assoc, projRetract_comp_ι,
      Category.comp_id, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.isoImage_hom_ι, ← Category.assoc, hm, Category.id_comp]
  rw [projMapOfEventuallyIso, ← Category.assoc, hfac, Category.assoc, Category.assoc, key]

end General

namespace PolarizedFamily.AdmissibleDeformation

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂) (d₀ : ℕ)
  (hd₀ : 0 < d₀)

/-- **`algebraPullbackHom` as a homomorphism of `SheafGradedAlgebra`s**
`g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)`. -/
def algebraPullbackSheafHom :
    SheafGradedAlgebraHom ((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base)
      (D₁.truncatedSectionAlgebra d₀ hd₀) where
  app n := (algebraPullbackHom φ d₀ hd₀).app n
  app_mul i j U a b := (algebraPullbackHom φ d₀ hd₀).map_mul i j (Opposite.op U) a b
  app_one U := (algebraPullbackHom φ d₀ hd₀).map_one (Opposite.op U)

variable (hiso : ∀ n : ℤ, IsIso ((algebraPullbackHom φ d₀ hd₀).app n))

include hiso in
/-- If `algebraPullbackHom` is an isomorphism in every degree, then the components of
`algebraPullbackSheafHom` are isomorphisms in all sufficiently large degrees `d`. -/
theorem eventually_isIso_algebraPullbackSheafHom :
    ∀ᶠ d : ℕ in Filter.atTop, IsIso ((algebraPullbackSheafHom φ d₀ hd₀).app (d : ℤ)) :=
  Filter.Eventually.of_forall fun d => hiso d

/-- **The morphism `Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` attached to a morphism of
deformations**: the isomorphism `Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₁}(g^* 𝒜'(D₂))` of
[Stacks, Tag 07ZJ] induced by `algebraPullbackHom`, followed by the base change morphism
`Proj_{S'₁}(g^* 𝒜'(D₂)) ⟶ Proj_{S'₂}(𝒜'(D₂))` of [Stacks, Tag 01O3]. -/
def projBaseChangeHom :
    (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).scheme ⟶
      (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).scheme :=
  projMapOfEventuallyIso (algebraPullbackSheafHom φ d₀ hd₀)
      (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso) ≫
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base

/-- **`Proj_{S'₁}(𝒜'(D₁))` is the base change of `Proj_{S'₂}(𝒜'(D₂))` along `g`**, through
`projBaseChangeHom`: [Stacks, Tag 01O3] and the isomorphism of [Stacks, Tag 07ZJ] over `S'₁`. -/
theorem isPullback_projBaseChangeHom :
    IsPullback (projBaseChangeHom φ d₀ hd₀ hiso)
      (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).toBase
      (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).toBase φ.base := by
  have h := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.isPullback_baseChangeHom
    (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base
  refine IsPullback.of_iso h (asIso (projMapOfEventuallyIso (algebraPullbackSheafHom φ d₀ hd₀)
      (eventually_isIso_algebraPullbackSheafHom φ d₀ hd₀ hiso))).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [projBaseChangeHom]
  · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id]
    rw [IsIso.eq_inv_comp, projMapOfEventuallyIso_comp_toBase]

/-- **`projBaseChangeHom` on the charts**: for affine opens `U' ⊆ g^{-1}(U)`, the chart of
`Proj_{S'₁}(𝒜'(D₁))` over `U'` followed by `projBaseChangeHom` is the morphism of
[Stacks, Tag 01MY] for `Γ(U', g^*𝒜'(D₂)) ⟶ Γ(U', 𝒜'(D₁))`, then `Proj` of
`Γ(U, 𝒜'(D₂)) ⟶ Γ(U', g^*𝒜'(D₂))`, then the chart of `Proj_{S'₂}(𝒜'(D₂))` over `U`. -/
theorem chart_comp_projBaseChangeHom {U : D₂.S'.Opens} (hU : IsAffineOpen U) {U' : D₁.S'.Opens}
    (hU' : IsAffineOpen U') (hUU' : U' ≤ φ.base ⁻¹ᵁ U)
    (m : (AlgebraicGeometry.Proj ((D₁.truncatedSectionAlgebra d₀ hd₀).grading U')) ⟶
      (mapDomain (((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base).grading U')
        ((D₁.truncatedSectionAlgebra d₀ hd₀).grading U')
        ((algebraPullbackSheafHom φ d₀ hd₀).sectionHom U')).toScheme)
    (hm : m ≫ (mapDomain (((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base).grading U')
        ((D₁.truncatedSectionAlgebra d₀ hd₀).grading U')
        ((algebraPullbackSheafHom φ d₀ hd₀).sectionHom U')).ι = 𝟙 _) :
    (relativeProj (D₁.truncatedSectionAlgebra d₀ hd₀)).chart U' hU' ≫
        projBaseChangeHom φ d₀ hd₀ hiso =
      m ≫ mapHom (((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base).grading U')
          ((D₁.truncatedSectionAlgebra d₀ hd₀).grading U')
          ((algebraPullbackSheafHom φ d₀ hd₀).sectionHom U') ≫
        AlgebraicGeometry.Proj.map
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange
            (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU')
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.irrelevant_le_map_sectionBaseChange
            (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU') ≫
        (relativeProj (D₂.truncatedSectionAlgebra d₀ hd₀)).chart U hU := by
  rw [projBaseChangeHom, ← Category.assoc, chart_comp_projMapOfEventuallyIso _ _ U' hU' m hm]
  simp only [Category.assoc]
  exact congrArg (fun t => m ≫
      mapHom (((D₂.truncatedSectionAlgebra d₀ hd₀).pullback φ.base).grading U')
        ((D₁.truncatedSectionAlgebra d₀ hd₀).grading U')
        ((algebraPullbackSheafHom φ d₀ hd₀).sectionHom U') ≫ t)
    (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.chart_baseChangeHom
      (D₂.truncatedSectionAlgebra d₀ hd₀) φ.base ⟨U, hU⟩ ⟨U', hU'⟩ hUU')

end PolarizedFamily.AdmissibleDeformation

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
