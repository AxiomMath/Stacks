module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DeformationsOfProjectiveSchemesFunctorial
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.Generic
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0

/-!
# The transition morphism of truncated section algebras over affine bases, on the top chart

Let `φ : D₁ ⟶ D₂` be a morphism of admissible deformations of a polarized family whose deformed
bases `S'₁`, `S'₂` are affine, and fix the cut `d₀` of [Stacks, Tag 0D4F]. Over an affine base
the chart of the relative `Proj` of the truncated section algebra `𝒜'` over the whole base is an
isomorphism `Proj Γ(S', 𝒜') ≅ Proj_{S'}(𝒜')`. This file computes the morphism
`Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` of [Stacks, Tag 0D4F] (`projBaseChangeHom`) on these
charts: it is `Proj` of the graded ring map `Γ(S'₂, 𝒜'(D₂)) ⟶ Γ(S'₁, 𝒜'(D₁))` which pulls
sections back along `φ`.

## Main definitions

* `Stacks.PolarizedAlgebraization.topChart`: the chart over the whole (affine) base.
* `Stacks.PolarizedAlgebraization.sectionTransition`: the graded ring map
  `Γ(S'₂, 𝒜'(D₂)) ⟶ Γ(S'₁, 𝒜'(D₁))`.

## Main results

* `Stacks.PolarizedAlgebraization.isIso_topChart`: the top chart is an isomorphism.
* `Stacks.PolarizedAlgebraization.topChart_comp_projBaseChangeHom`: the morphism of relative
  `Proj` attached to `φ` is `Proj.map` of `sectionTransition` on the top charts.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.PolarizedAlgebraization

/-! ### The top chart and a base change on it, for an arbitrary graded algebra map -/

section General

variable {S S' : Scheme.{u}} [IsAffine S] [IsAffine S']

/-- **The chart of `Proj_S(A)` over the whole base**, for an affine base `S`:
`Proj Γ(S, A) ⟶ Proj_S(A)`. -/
abbrev topChart (A : SheafGradedAlgebra S) :
    AlgebraicGeometry.Proj (A.grading ⊤) ⟶ (relativeProj A).scheme :=
  (relativeProj A).chart ⊤ (isAffineOpen_top _)

/-- Over an affine base the top chart is an isomorphism: it is the base change of the
isomorphism `⊤ ⟶ S`. -/
instance isIso_topChart (A : SheafGradedAlgebra S) : IsIso (topChart A) := by
  have : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  exact ((relativeProj A).chart_isPullback ⊤ (isAffineOpen_top _)).isIso_fst_of_isIso

/-- The whole base, as an affine open. -/
abbrev topSite (S : Scheme.{u}) [IsAffine S] : S.AffineZariskiSite :=
  ⟨⊤, isAffineOpen_top S⟩

/-- For a morphism `g : S' ⟶ S` of affine schemes, the whole of `S'` lies in the preimage
under `g` of the whole of `S`. -/
theorem top_le_preimage_top (g : S' ⟶ S) :
    (topSite S').toOpens ≤ g ⁻¹ᵁ (topSite S).toOpens :=
  fun _ _ => trivial

variable {A : SheafGradedAlgebra S} {g : S' ⟶ S} {A' : SheafGradedAlgebra S'}
  (ψ : SheafGradedAlgebraHom (A.pullback g) A')

/-- **The transition of graded rings of global sections** `Γ(S, A) ⟶ Γ(S', A')` attached to
`ψ : g^* A ⟶ A'`: the base change of sections along `g`, followed by the map of sections of
`ψ`. -/
def sectionTransition : A.grading ⊤ →+*ᵍ A'.grading ⊤ :=
  (ψ.sectionHom ⊤).comp
    (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g (topSite _)
      (topSite _) (top_le_preimage_top g))

variable (hψ : ∀ n : ℤ, IsIso (ψ.app n))

omit [IsAffine S] [IsAffine S'] in
include hψ in
/-- The map of global sections of an isomorphism of graded algebras is surjective. -/
theorem surjective_sectionHom : Function.Surjective (ψ.sectionHom ⊤) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n b =>
    let e := @asIso _ _ _ _ (ψ.app (n : ℤ)) (hψ n)
    refine ⟨DirectSum.of _ n (e.inv.app ⊤ b), ?_⟩
    rw [Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom_of,
      Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionPieceHom_apply]
    congr 1
    exact Stacks.SheafOfModules.hom_val_app_inv_val_app e _ b
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ a b⟩

/-- The irrelevant ideal condition for the base change of sections on the whole base. -/
private theorem irrelevant_le_map_sectionBaseChange_top :
    HomogeneousIdeal.irrelevant ((A.pullback g).grading ⊤) ≤
      (HomogeneousIdeal.irrelevant (A.grading ⊤)).map
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g
          (topSite _) (topSite _) (top_le_preimage_top g)) :=
  Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.irrelevant_le_map_sectionBaseChange
    A g (topSite _) (topSite _) (top_le_preimage_top g)

include hψ in
/-- The irrelevant ideal condition for `sectionTransition`. -/
theorem irrelevant_le_map_sectionTransition :
    HomogeneousIdeal.irrelevant (A'.grading ⊤) ≤
      (HomogeneousIdeal.irrelevant (A.grading ⊤)).map (sectionTransition ψ) :=
  HomogeneousIdeal.irrelevant_le_map_comp irrelevant_le_map_sectionBaseChange_top
    (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ (surjective_sectionHom ψ hψ))

include hψ in
/-- **The base change morphism `Proj_{S'}(A') ⟶ Proj_{S'}(g^* A) ⟶ Proj_S(A)` on the top
charts**: it is `Proj.map` of the transition of graded rings of global sections. -/
theorem topChart_comp_projMap_baseChangeHom :
    topChart A' ≫ (projMapOfEventuallyIso ψ (Filter.Eventually.of_forall fun d => hψ d) ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g) =
      AlgebraicGeometry.Proj.map (sectionTransition ψ)
          (irrelevant_le_map_sectionTransition ψ hψ) ≫ topChart A := by
  have hsurj := surjective_sectionHom ψ hψ
  have hdom := Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_surjective _ _ _ hsurj
  have hirr := AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ hsurj
  let m := (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hdom.symm).hom
  have hm : m ≫ (Stacks.AlgebraicGeometry.ProjShared.mapDomain ((A.pullback g).grading ⊤)
      (A'.grading ⊤) (ψ.sectionHom ⊤)).ι = 𝟙 _ := by
    simp only [m]
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, ← Scheme.topIso_hom, Iso.inv_hom_id]
  have h1 := chart_comp_projMapOfEventuallyIso ψ (Filter.Eventually.of_forall fun d => hψ d) ⊤
    (isAffineOpen_top S') m hm
  have h2 := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.chart_baseChangeHom A g
    (topSite _) (topSite _) (top_le_preimage_top g)
  have h3 : m ≫ Stacks.AlgebraicGeometry.ProjTwistChain.mapHom ((A.pullback g).grading ⊤)
      (A'.grading ⊤) (ψ.sectionHom ⊤) = AlgebraicGeometry.Proj.map (ψ.sectionHom ⊤) hirr := by
    simp only [m]
    rw [Category.assoc]
    exact Stacks.AlgebraicGeometry.ProjBaseChange.mapHom_eq_projMap _ _ _ hirr hdom
  have h4 := AlgebraicGeometry.Proj.map_comp
    (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g (topSite _)
      (topSite _) (top_le_preimage_top g)) (ψ.sectionHom ⊤)
    irrelevant_le_map_sectionBaseChange_top hirr
  rw [reassoc_of% h1, ← Category.assoc, h3, h2]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ topChart A) h4.symm)

end General

/-! ### Morphisms of admissible deformations over affine bases -/

variable {P : PolarizedFamily.{u}} (d₀ : ℕ) (hd₀ : 0 < d₀)
  {D₁ D₂ : P.AdmissibleDeformation} (φ : AdmissibleDeformation.Hom D₁ D₂)
  [IsAffine D₁.S'] [IsAffine D₂.S']
  (hiso : ∀ n : ℤ, IsIso ((AdmissibleDeformation.algebraPullbackHom φ d₀ hd₀).app n))

include hiso in
/-- **The morphism of relative `Proj` attached to a morphism of deformations, on the top
charts**: `Proj_{S'₁}(𝒜'(D₁)) ⟶ Proj_{S'₂}(𝒜'(D₂))` is `Proj.map` of the transition of graded
rings of global sections. -/
theorem topChart_comp_projBaseChangeHom :
    topChart (D₁.truncatedSectionAlgebra d₀ hd₀) ≫
        AdmissibleDeformation.projBaseChangeHom φ d₀ hd₀ hiso =
      AlgebraicGeometry.Proj.map
          (sectionTransition (AdmissibleDeformation.algebraPullbackSheafHom φ d₀ hd₀))
          (irrelevant_le_map_sectionTransition _ hiso) ≫
        topChart (D₂.truncatedSectionAlgebra d₀ hd₀) :=
  topChart_comp_projMap_baseChangeHom _ hiso

end Stacks.PolarizedAlgebraization

end
