module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.MayerVietorisStep
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.ChartSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
import all StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective

/-!
# Powers of a section on degree-zero cohomology of an affine chart

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` and `A` an affine open on
which `ℒ` has a frame. Degree-zero cohomology is sections, so on `A` the annihilation and
extension properties of `Stacks.Cohomology.SectionPowerAnnihilation` in degree zero are
[Stacks, Tag 01I9] and [Stacks, Tag 01P7] for a quasi-coherent module, read on the chart.

## Main results

* `Stacks.Cohomology.SectionPowerAnnihilation.annihilates_zero_of_generator`: a degree-zero class
  over the chart vanishing on the nonvanishing open is killed by a power of `s`.
* `Stacks.Cohomology.SectionPowerAnnihilation.extends_zero_of_generator`: a power of `s` times a
  degree-zero class over the part of the chart where `s` does not vanish extends to the chart.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule
open Stacks.SheafOfModules.SectionPowerComposition (mul mul_app)

universe u

namespace Stacks.Cohomology.SectionPowerAnnihilation

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable {X : Scheme.{u}}
  {L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L] {s : L.sections}

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- Degree-zero cohomology over an open, as sections. -/
abbrev θ (T : X.Opens) (G : X.Modules) :
    Hgroup X.ringCatSheaf T 0 G ⟶ (secF X.ringCatSheaf T).obj G :=
  (HzeroIso X.ringCatSheaf T).hom.app G

/-- The inverse of the degree-zero isomorphism undoes `θ`. -/
theorem θ_inv_θ (T : X.Opens) (G : X.Modules) (a : Hgroup X.ringCatSheaf T 0 G) :
    (HzeroIso X.ringCatSheaf T).inv.app G (θ T G a) = a :=
  Iso.hom_inv_id_app_apply (HzeroIso X.ringCatSheaf T) G a

/-- `θ` undoes the inverse of the degree-zero isomorphism. -/
theorem θ_θ_inv (T : X.Opens) (G : X.Modules) (a : (secF X.ringCatSheaf T).obj G) :
    θ T G ((HzeroIso X.ringCatSheaf T).inv.app G a) = a :=
  Iso.inv_hom_id_app_apply (HzeroIso X.ringCatSheaf T) G a

/-- `θ` is injective. -/
theorem θ_injective (T : X.Opens) (G : X.Modules) : Function.Injective (θ T G) := by
  intro a b h
  have e := congrArg ((HzeroIso X.ringCatSheaf T).inv.app G) h
  rwa [θ_inv_θ, θ_inv_θ] at e

/-- `θ` is natural in the module: it commutes with the maps induced by a morphism `φ`. -/
theorem θ_map (T : X.Opens) {G G' : X.Modules} (φ : G ⟶ G') (ξ : Hgroup X.ringCatSheaf T 0 G) :
    θ T G' ((Hfunctor X.ringCatSheaf T 0).map φ ξ) = (secF X.ringCatSheaf T).map φ (θ T G ξ) := by
  have h := congrArg (fun f => f ξ)
    ((HzeroIso X.ringCatSheaf T).hom.naturality φ)
  simpa only [ConcreteCategory.comp_apply] using h

/-- `θ` commutes with restriction from `T` to a smaller open `T'`. -/
theorem θ_res {T T' : X.Opens} (h : T' ≤ T) (G : X.Modules) (ξ : Hgroup X.ringCatSheaf T 0 G) :
    θ T' G (resH h 0 G ξ) = (secRestrict X.ringCatSheaf h).app G (θ T G ξ) :=
  Hzero_Hrestrict X.ringCatSheaf h G ξ

local notation "N" => nonvanishingOpen L s

/-- Restricting a section of a module twice is restricting it once. -/
theorem map_map_of_le (G : X.Modules) {T₁ T₂ T₃ : X.Opens} (h₁₂ : T₂ ≤ T₁) (h₂₃ : T₃ ≤ T₂)
    (x : G.val.obj (op T₁)) :
    G.val.map (homOfLE h₂₃).op (G.val.map (homOfLE h₁₂).op x) =
      G.val.map (homOfLE (h₂₃.trans h₁₂)).op x := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

variable (s) in
/-- **Degree zero on an affine chart: the annihilation property.** -/
theorem annihilates_zero_of_generator {A : X.Opens} (hA : IsAffineOpen A)
    (g : GeneratorSections X.toRingedSpace L A) : Annihilates X L s A 0 := by
  intro T hT hTeq G hG ξ hξ
  subst hTeq
  obtain ⟨r, hs, hAr⟩ := exists_scalar_section_inf_eq_basicOpen X L s g
  have hle : X.basicOpen r ≤ A ⊓ N := hAr.ge
  have ht : G.val.map (homOfLE (inf_le_left : A ⊓ N ≤ A)).op (θ A G ξ) = 0 := by
    have e := θ_res (inf_le_left : A ⊓ N ≤ A) G ξ
    rw [hξ, map_zero] at e
    exact e.symm
  have ht' : G.val.map (homOfLE (X.basicOpen_le r)).op (θ A G ξ) = 0 :=
    (map_map_of_le G (inf_le_left : A ⊓ N ≤ A) hle (θ A G ξ)).symm.trans
      ((congrArg (ConcreteCategory.hom (G.val.map (homOfLE hle).op)) ht).trans (map_zero _))
  have := hG
  obtain ⟨k, hk⟩ :=
    Stacks.SheafOfModules.SectionPowerComposition.exists_tensorSectionAtOpen_eq_zero
      X L s G hA r g.val hs (θ A G ξ) ht'
  refine ⟨k, θ_injective A _ ?_⟩
  rw [θ_map, map_zero]
  exact (mul_app X L s G k A (θ A G ξ)).trans hk

variable (s) in
/-- **Degree zero on an affine chart: the extension property.** -/
theorem extends_zero_of_generator {A : X.Opens} (hA : IsAffineOpen A)
    (g : GeneratorSections X.toRingedSpace L A) : Extends X L s A 0 := by
  intro T hT hTeq G hG η
  obtain ⟨r, hs, hAr⟩ := exists_scalar_section_inf_eq_basicOpen X L s g
  obtain rfl : T = X.basicOpen r := hTeq.trans hAr
  have := hG
  obtain ⟨k, a, ha⟩ :=
    Stacks.SheafOfModules.SectionPowerComposition.exists_restrict_eq_tensorSectionAtOpen
      X L s G hA r g.val hs (θ (X.basicOpen r) G η)
  refine ⟨k, (HzeroIso X.ringCatSheaf A).inv.app _ a,
    θ_injective (X.basicOpen r) _ ?_⟩
  refine (θ_res hT _ _).trans ?_
  refine (congrArg (ConcreteCategory.hom ((secRestrict X.ringCatSheaf hT).app
    (twist X L G (k : ℤ)))) (θ_θ_inv A (twist X L G (k : ℤ)) a)).trans ?_
  refine ha.trans ?_
  exact (mul_app X L s G k (X.basicOpen r) (θ (X.basicOpen r) G η)).symm.trans
    (θ_map (X.basicOpen r) (mul X L s G k) η).symm

end Stacks.Cohomology.SectionPowerAnnihilation

end
