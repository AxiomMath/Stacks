module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleSmooth
public import StacksFrontier.CategoryTheory.Triangulated.RetractionFromBiproductSection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdditiveAnyModel

/-!
# The splitting of `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}`: reduction to the centre and the blowup

Fix a scheme `S`, a smooth morphism `f : X ⟶ S` and a closed immersion `i : Z ⟶ X` with `Z`
smooth over `S`. Write `b : X' ⟶ X` for the blowing up of `X` along `Z`, `j : E ⟶ X'` for the
exceptional divisor and `p : E ⟶ Z` for its projection onto the centre. [Stacks, Tag 0FUW] says
that, when `Z` has positive codimension everywhere, the canonical map
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a splitting in `D(X, f^{-1}𝒪_S)`.

The proof in the source consists of a formal part and two geometric inputs. This file carries
out the formal part: it reduces the existence of the splitting to

* **on the centre**, a map `τ : Rp_*Ω^•_{E/S} ⟶ Ω^•_{Z/S}` and a map
  `ν : Rp_*Ω^•_{E/S} ⟶ Rp_*W` with `c ≫ τ = 𝟙`, `c ≫ ν = 0` and `τ ≫ c + ν ≫ Rp_*θ = 𝟙`,
  where `c : Ω^•_{Z/S} ⟶ Rp_*Ω^•_{E/S}` is the canonical map and `θ : W ⟶ Ω^•_{E/S}` is a
  morphism of `D(E, (E → S)^{-1}𝒪_S)` (in the source, `θ` is the map `θ'` of Remark 0FU7 for
  `c₁^{dR}(𝒪_E(1))`, read on `W = Ω^•_{E/S}[-2]`, and `τ`, `ν` come from Remark 0FUN);
* **on the blowup**, a lift `δ : Rj_*W ⟶ Ω^•_{X'/S}` of `Rj_*θ` through the canonical map
  `Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}` (in the source, the boundary map of Lemma 0FUQ).

Given these, the map `Rb_*δ ∘ i_*ν ⊕ i_*τ` is a section of the second map of the triangle of
[Stacks, Tag 0FUV] containing the summand `i_*Ω^•_{Z/S}` in its image, and
`CategoryTheory.Pretriangulated.exists_retraction_of_distTriang_biprod` ([Stacks, Tag 05QT])
turns it into a retraction of `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}`.

## Main definitions

* `Stacks.DeRham.BlowupTriangle.centreUnit`: the canonical map `Ω^•_{Z/S} ⟶ Rp_*Ω^•_{E/S}`.
* `Stacks.DeRham.BlowupTriangle.inclusionUnit`: the canonical map `Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}`.
* `Stacks.DeRham.BlowupTriangle.exceptionalPushforwardIso`: the comparison
  `Rb_* ∘ Rj_* ≅ Ri_* ∘ Rp_*`.

## Main results

* `Stacks.DeRham.BlowupTriangle.blowUpToExceptional_eq`: the canonical map
  `Rb_*Ω^•_{X'/S} ⟶ i_*Rp_*Ω^•_{E/S}` is `Rb_*` of the canonical map followed by the comparison.
* `Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp_of_section`: the reduction.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Tag 05QT](https://stacks.math.columbia.edu/tag/05QT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

-- The statements mix the `Modules` and `ModuleSheaves` spellings of the categories of modules,
-- which agree only at default transparency; these make them agree for unification.
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage

namespace Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase f))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))]

/-- **The canonical map `Ω^•_{Z/S} ⟶ Rp_*Ω^•_{E/S}`** in `D(Z, (Z → S)^{-1}𝒪_S)`. -/
abbrev centreUnit :
    deRham (i ≫ f) ⟶
      (derivedPushforward (coefficientProjection f i)).obj
        (deRham (exceptionalStructure f i)) :=
  DerivedCategory.Q.map (chain (exceptionalProjection i) (i ≫ f)) ≫
    unit (coefficientProjection f i) (deRhamCochainComplex (exceptionalStructure f i))

/-- **The canonical map `Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}`** in `D(X', (X' → S)^{-1}𝒪_S)`. -/
abbrev inclusionUnit :
    deRham (blowupMap i ≫ f) ⟶
      (derivedPushforward (coefficientInclusion f i)).obj
        (deRham (exceptionalStructure f i)) :=
  DerivedCategory.Q.map (inclusionChain f i) ≫
    unit (coefficientInclusion f i) (deRhamCochainComplex (exceptionalStructure f i))

section Square

variable {A B C D : RingedSpace.{u, u}} [HasDerivedCategory (ModuleSheaves A)]
  [HasDerivedCategory (ModuleSheaves B)] [HasDerivedCategory (ModuleSheaves C)]
  [HasDerivedCategory (ModuleSheaves D)] {g₁ : A ⟶ B} {g₂ : B ⟶ D} {g₃ : A ⟶ C} {g₄ : C ⟶ D}

/-- **The comparison `R(g₂)_*R(g₁)_*K ≅ R(g₄)_*R(g₃)_*K`** of derived direct images along two
factorisations `g₁ ≫ g₂ = g₃ ≫ g₄` of one morphism of ringed spaces, through the comparison of a
derived direct image along a composite with the composite of derived direct images
([Stacks, Tag 0D5T]). -/
def pushforwardSquareIso (h : g₁ ≫ g₂ = g₃ ≫ g₄) (K : DerivedCategory (ModuleSheaves A)) :
    (derivedPushforward g₂).obj ((derivedPushforward g₁).obj K) ≅
      (derivedPushforward g₄).obj ((derivedPushforward g₃).obj K) where
  hom := (compIso g₁ g₂).inv.app K ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj K) h) ≫ (compIso g₃ g₄).hom.app K
  inv := (compIso g₃ g₄).inv.app K ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj K) h).symm ≫
      (compIso g₁ g₂).hom.app K
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Iso.inv_hom_id_app]
    rfl
  inv_hom_id := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Iso.inv_hom_id_app]
    rfl

/-- The comparison of derived direct images along two factorisations is natural. -/
lemma pushforwardSquareIso_hom_naturality (h : g₁ ≫ g₂ = g₃ ≫ g₄)
    {K K' : DerivedCategory (ModuleSheaves A)} (φ : K ⟶ K') :
    (derivedPushforward g₂).map ((derivedPushforward g₁).map φ) ≫
        (pushforwardSquareIso h K').hom =
      (pushforwardSquareIso h K).hom ≫
        (derivedPushforward g₄).map ((derivedPushforward g₃).map φ) := by
  have h₁ := (compIso g₁ g₂).inv.naturality φ
  have h₂ := (compIso g₃ g₄).hom.naturality φ
  have h₃ := eqToHom_naturality (fun g => (derivedPushforward g).map φ) h
  simp only [Functor.comp_map] at h₁ h₂
  simp only [pushforwardSquareIso]
  rw [reassoc_of% h₁, reassoc_of% h₃, h₂]
  simp only [Category.assoc]

end Square

/-- **The comparison `Rb_*Rj_*K ≅ i_*Rp_*K`** of derived direct images along the two
factorisations `j ≫ b = p ≫ i` of `E ⟶ X`. At `K = Ω^•_{E/S}` it is the comparison occurring in
`blowUpToExceptional`. -/
abbrev exceptionalPushforwardIso
    (K : DerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))) :=
  pushforwardSquareIso (coefficientInclusion_comp_coefficientBlowup f i) K

section Reduction

variable [Smooth f] [Smooth (i ≫ f)]

/-- **The formal part of the proof of [Stacks, Tag 0FUW].** Let `θ : W ⟶ Ω^•_{E/S}` be a morphism
of `D(E, (E → S)^{-1}𝒪_S)`. Assume

* on the centre: `τ : Rp_*Ω^•_{E/S} ⟶ Ω^•_{Z/S}` and `ν : Rp_*Ω^•_{E/S} ⟶ Rp_*W` with
  `c ≫ τ = 𝟙`, `c ≫ ν = 0` and `τ ≫ c + ν ≫ Rp_*θ = 𝟙`, for `c` the canonical map;
* on the blowup: `δ : Rj_*W ⟶ Ω^•_{X'/S}` whose composite with the canonical map
  `Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}` is `Rj_*θ`.

Then the canonical map `Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a retraction. -/
theorem exists_retraction_toBlowUp_of_section
    {W : DerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))}
    (θ : W ⟶ deRham (exceptionalStructure f i))
    (τ : (derivedPushforward (coefficientProjection f i)).obj
        (deRham (exceptionalStructure f i)) ⟶ deRham (i ≫ f))
    (ν : (derivedPushforward (coefficientProjection f i)).obj
        (deRham (exceptionalStructure f i)) ⟶
      (derivedPushforward (coefficientProjection f i)).obj W)
    (hτ : centreUnit f i ≫ τ = 𝟙 _) (hν : centreUnit f i ≫ ν = 0)
    (hτν : τ ≫ centreUnit f i + ν ≫ (derivedPushforward (coefficientProjection f i)).map θ = 𝟙 _)
    (δ : (derivedPushforward (coefficientInclusion f i)).obj W ⟶ deRham (blowupMap i ≫ f))
    (hδ : δ ≫ inclusionUnit f i = (derivedPushforward (coefficientInclusion f i)).map θ) :
    ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _ := by
  obtain ⟨w, hw⟩ := exists_distTriang f i
  exact exists_retraction_of_distTriang_of_factorisations
    (derivedPushforward (coefficientBlowup f i)) (derivedPushforward (coefficientCentre f i))
    (derivedPushforward (coefficientInclusion f i)) (derivedPushforward (coefficientProjection f i))
    (exceptionalPushforwardIso f i) (fun φ => pushforwardSquareIso_hom_naturality _ φ) _ _ _ _
    (inclusionUnit f i) (centreUnit f i) rfl rfl w hw θ τ ν hτ hν hτν δ hδ

end Reduction

end Stacks.DeRham.BlowupTriangle

end
