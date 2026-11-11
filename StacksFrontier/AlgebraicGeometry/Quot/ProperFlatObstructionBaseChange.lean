module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationObstructionGroups
public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeFieldModules

/-!
# The obstruction groups of a deformation and those of the special fibre

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over a field, and let
`x = (X ⟶ Spec A)` be a deformation of `x₀` over an object `A` of `𝒞_Λ`. For an `A`-module `I`
killed by `𝔪_A` the obstruction group `T²_{X/A}(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of
[Stacks, Remark 0D1P] is `T²_{X₀/k}(I) = Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀} ⊗_k I)`, by flat base
change of the cotangent complex ([Stacks, Tag 08QQ]) and the adjunction between derived pullback
and direct image along the thickening `X₀ ⊂ X`.

This file sets up the comparison: it makes an `A`-module killed by `𝔪_A` a `k`-module, presents
`x₀` over the chart `Spec k ⟶ S`, and records the base change comparison as the condition
`AlgebraicGeometry.ProperFlatSpaceDeformation.ObstructionGroupsEmbedInSpecialFibre`.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceDeformation.residueModule`: an `A`-module killed by `𝔪_A`,
  as a `k`-vector space.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.contains_specialFibre`,
  `AlgebraicGeometry.ProperFlatSpaceDeformation.obj_eq_specialFibre`: `x₀` lies over the chart
  `Spec k ⟶ Spec Λ ⟶ S`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.ObstructionGroupsEmbedInSpecialFibre`: for every
  deformation and every `I` killed by `𝔪_A`, `T²_{X/A}(I)` embeds in `T²_{X₀/k}(I)`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.deformationObstructionGroupsVanish_of_embed`:
  the obstruction groups of all deformations vanish once those of the special fibre vanish at
  every `k`-vector space and the comparison embeds.
* `ProperFlatSpaceDeformation.deformationObstructionGroupsVanish_of_embed_of_subsingleton`:
  the same from `T²_{X₀/k}(k) = 0` alone, given the comparison.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

/-! ### Modules killed by the maximal ideal -/

section ResidueModule

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (A : ArtinianLocalAlgCat.{u, u, u} Λ k)

/-- The residue map of an object of `𝒞_Λ` is surjective. -/
theorem residueMap_surjective_of_artinian : Function.Surjective (residueMap A) := by
  intro c
  obtain ⟨r, hr⟩ := A.residueEquiv.surjective c
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
  exact ⟨s, hr⟩

/-- The kernel of the residue map is the maximal ideal. -/
theorem ker_residueMap_eq_maximalIdeal :
    RingHom.ker (residueMap A) = IsLocalRing.maximalIdeal A :=
  IsLocalRing.ker_eq_maximalIdeal _ (residueMap_surjective_of_artinian A)

/-- `k ≃ A ⧸ 𝔪_A` through the residue map. -/
def residueRingEquiv : k ≃+* A ⧸ IsLocalRing.maximalIdeal A :=
  ((Ideal.quotEquivOfEq (ker_residueMap_eq_maximalIdeal A)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (residueMap_surjective_of_artinian A))).symm

variable {A} (I : ModuleCat.{u} A)
  (hI : ∀ r ∈ IsLocalRing.maximalIdeal A, ∀ i : I, r • i = 0)

/-- An `A`-module killed by `𝔪_A`, as a module over `A ⧸ 𝔪_A`. -/
abbrev residueQuotientModule : Module (A ⧸ IsLocalRing.maximalIdeal A) I :=
  Module.IsTorsionBySet.module (R := A) (M := I) (I := IsLocalRing.maximalIdeal A)
    fun i r => hI r.1 r.2 i

/-- **An `A`-module killed by `𝔪_A`, as a `k`-vector space**: `c : k` acts as any lift of `c`
to `A`. -/
def residueModule : ModuleCat.{u} k :=
  letI := residueQuotientModule I hI
  letI : Module k I := Module.compHom I (residueRingEquiv A).toRingHom
  ModuleCat.of k I

/-- `c : k` acts on `residueModule I hI` as `r : A` does when `r` lifts `c`. -/
theorem residueModule_smul (r : A) (i : I) :
    (residueMap A r • (show residueModule I hI from i) : residueModule I hI) =
      (show residueModule I hI from r • i) := by
  let := residueQuotientModule I hI
  change (residueRingEquiv A (residueMap A r)) • i = r • i
  have : residueRingEquiv A (residueMap A r) = Ideal.Quotient.mk _ r := by
    apply (residueRingEquiv A).symm.injective
    rw [RingEquiv.symm_apply_apply]
    simp [residueRingEquiv]
  rw [this]
  exact Module.IsTorsionBySet.mk_smul _ r i

end ResidueModule

/-! ### The special fibre over its chart -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

variable (x₀ hx₀) in
include hx₀ in
/-- The spectrum of the residue field belongs to the site. -/
theorem contains_specialFibre : B.Contains (Spec (.of k)) := by
  have h := congrArg Over.left hx₀
  change ((cartesianProperFlatProjection B S hS).obj x₀).left.obj = Spec (.of k) at h
  exact h ▸ ((cartesianProperFlatProjection B S hS).obj x₀).left.property

variable (x₀ hx₀) in
/-- `x₀` lies over the chart `Spec k ⟶ Spec Λ ⟶ S`, as an object of the site. -/
theorem obj_eq_specialFibre :
    (cartesianProperFlatProjection B S hS).obj x₀ =
      algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        (contains_specialFibre x₀ hx₀) :=
  BigFppfOver.obj_injective_post_inclusion B S hS hx₀

-- The sheafification instances at `u + 1` on the model of
-- `StacksFrontier/AlgebraicGeometry/Spaces/AlgebraExtensionPushoutQcqs.lean` are tried first and
-- fail with a universe error instead of giving way to the instances at `u`.
attribute [-instance] Space.modelHasSheafifyULift Space.modelWEqualsLocallyBijectiveULift

variable (x₀ hx₀) in
/-- **The obstruction groups of the deformations of `x₀` embed in those of `x₀`**: for every
deformation `x = (X ⟶ Spec A)` of `x₀` and every `A`-module `I` killed by `𝔪_A`,
`T²_{X/A}(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` injects into
`T²_{X₀/k}(I) = Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀} ⊗_k I)`. This is the comparison of
[Stacks, Remark 0D1P] by flat base change of the cotangent complex; it is recorded here as a
condition. -/
def ObstructionGroupsEmbedInSpecialFibre
    [HasDerivedCategory (Space.modelModules x₀.obj.obj.left)] : Prop :=
  ∀ (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀
      hx₀) (I : ModuleCat.{u} a.algebra)
    (hI : ∀ r ∈ IsLocalRing.maximalIdeal a.algebra, ∀ i : I, r • i = 0),
    letI := HasDerivedCategory.standard (Space.modelModules a.point.obj.obj.left)
    ∃ φ : (Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
        (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)).obj I →
      (Space.cotangentExtTwo
        (Space.ProperFlatLift.chartStructureMap x₀ (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
          (residueModule (A := a.algebra) I hI),
      Function.Injective φ

/-- **Vanishing of the obstruction groups from the special fibre.** If the comparison
`ObstructionGroupsEmbedInSpecialFibre` holds and `T²_{X₀/k}(V) = 0` for every `k`-vector space
`V`, the obstruction groups of all deformations of `x₀` vanish. -/
theorem deformationObstructionGroupsVanish_of_embed
    [HasDerivedCategory (Space.modelModules x₀.obj.obj.left)]
    (hemb : ObstructionGroupsEmbedInSpecialFibre x₀ hx₀)
    (hT2 : ∀ V : ModuleCat.{u} k,
      Subsingleton
      ((Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap x₀
          (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj V)) :
    DeformationObstructionGroupsVanish (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀) := by
  intro a I hI
  obtain ⟨φ, hφ⟩ := hemb a I hI
  have := hT2 (residueModule (A := a.algebra) I hI)
  exact hφ.subsingleton

/-- **Vanishing of the obstruction groups from `T²_{X₀/k}(k) = 0`.** If the comparison
`ObstructionGroupsEmbedInSpecialFibre` holds and `T²_{X₀/k}(k) = Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀})`
vanishes, the obstruction groups of all deformations of `x₀` vanish: `T²_{X₀/k}` then vanishes
at every `k`-vector space
(`AlgebraicGeometry.Space.ProperFlatLift.subsingleton_cotangentExtTwo_obj_of_subsingleton_self`). -/
theorem deformationObstructionGroupsVanish_of_embed_of_subsingleton
    [HasDerivedCategory (Space.modelModules x₀.obj.obj.left)]
    (hemb : ObstructionGroupsEmbedInSpecialFibre x₀ hx₀)
    (hT2 : Subsingleton
      ((Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap x₀
          (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
          (ModuleCat.of k k))) :
    DeformationObstructionGroupsVanish (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀) :=
  deformationObstructionGroupsVanish_of_embed hemb fun V =>
    Space.ProperFlatLift.subsingleton_cotangentExtTwo_obj_of_subsingleton_self x₀ _ hT2 V

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
