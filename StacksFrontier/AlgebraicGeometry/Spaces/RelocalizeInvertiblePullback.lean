module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor

/-!
# Pulled-back invertible modules along a lower-shriek extension

Let `h : W ⟶ S` be a morphism of the big fppf site, `ι : Z ⟶ Y` a representable morphism of
algebraic spaces over `W` and `L` an `𝒪_Y`-module. Let `Λ = Λ_h` be the lower-shriek extension
of Stacks 04SG and `L'` the `𝒪_{Λ Y}`-module corresponding to `L` under the equivalence of
module categories of Stacks 03I5. For an algebraic space `V` over `S` with an isomorphism
`ψ : V ≅ Λ Z`, write `g₀ = ψ ≫ Λ ι : V ⟶ Λ Y`. Then `g₀^* L'` is trivial exactly when `ι^* L`
is, and `g₀^* L'` has a nonzero section `𝒪_V ⟶ g₀^* L'` exactly when `ι^* L` has one. If `L` is
invertible, so is `L'`.

This is how the proof of Stacks 0D1R moves an invertible module on an algebraization over
`Spec R` to the base `Spec k` of the deformation problem.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_relocalize`: `L'` is invertible when `L` is.
* `AlgebraicGeometry.Space.nonempty_modulePullback_relocalize_iso_unit_iff`: triviality.
* `AlgebraicGeometry.Space.exists_unit_hom_modulePullback_relocalize_ne_zero_iff`: nonzero
  sections.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

/-! ### Fully faithful functors preserving a unit object -/

section FullyFaithful

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]
  {u : C} {u' : D} (eu : F.obj u ≅ u')

include eu in
/-- A fully faithful functor carrying `u` to `u'` detects the objects isomorphic to `u`. -/
theorem nonempty_obj_iso_iff_of_fullyFaithful (N : C) :
    Nonempty (F.obj N ≅ u') ↔ Nonempty (N ≅ u) :=
  ⟨fun ⟨i⟩ => ⟨F.preimageIso (i ≪≫ eu.symm)⟩, fun ⟨i⟩ => ⟨F.mapIso i ≪≫ eu⟩⟩

include eu in
/-- A fully faithful functor between categories with zero morphisms which preserves them and
carries `u` to `u'` detects the objects with a nonzero morphism from `u`. -/
theorem exists_hom_ne_zero_iff_of_fullyFaithful [HasZeroMorphisms C] [HasZeroMorphisms D]
    [F.PreservesZeroMorphisms] (N : C) :
    (∃ s : u' ⟶ F.obj N, s ≠ 0) ↔ ∃ t : u ⟶ N, t ≠ 0 := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨F.preimage (eu.hom ≫ s), fun h => hs ?_⟩
    have h' := congrArg F.map h
    rw [F.map_preimage, F.map_zero] at h'
    simpa using congrArg (fun φ => eu.inv ≫ φ) h'
  · rintro ⟨t, ht⟩
    refine ⟨eu.inv ≫ F.map t, fun h => ht (F.map_injective ?_)⟩
    rw [F.map_zero]
    simpa using congrArg (fun φ => eu.hom ≫ φ) h

end FullyFaithful

/-! ### Pullback along an isomorphism followed by a morphism -/

section Iso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V V' T : AlgebraicSpaces B S hS} (ψ : V ≅ V') (g : V' ⟶ T) (M : Modules.{u, u} B S hS T.1 T.2)

/-- Pullback along an isomorphism followed by `g` is trivial exactly when pullback along `g` is. -/
theorem nonempty_modulePullback_iso_comp_iso_unit_iff :
    Nonempty ((modulePullback B S hS (ψ.hom ≫ g)).obj M ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1 V.2).O))) ↔
      Nonempty ((modulePullback B S hS g).obj M ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V'.1 V'.2).O))) := by
  have := isEquivalence_modulePullback_of_iso B S hS ψ
  let c := ((modulePullbackCompIso B S hS ψ.hom g).app M).symm
  refine ⟨fun ⟨i⟩ => ?_, fun ⟨i⟩ => ?_⟩
  · exact (nonempty_obj_iso_iff_of_fullyFaithful (modulePullback B S hS ψ.hom)
      (modulePullbackUnitIso B S hS ψ.hom) _).1 ⟨c.symm ≪≫ i⟩
  · obtain ⟨j⟩ := (nonempty_obj_iso_iff_of_fullyFaithful (modulePullback B S hS ψ.hom)
      (modulePullbackUnitIso B S hS ψ.hom) _).2 ⟨i⟩
    exact ⟨c ≪≫ j⟩

/-- Pullback along an isomorphism followed by `g` has a nonzero section exactly when pullback
along `g` has one. -/
theorem exists_unit_hom_modulePullback_iso_comp_ne_zero_iff :
    (∃ s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1 V.2).O)) ⟶ (modulePullback B S hS (ψ.hom ≫ g)).obj M,
        s ≠ 0) ↔
      ∃ t : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V'.1 V'.2).O)) ⟶ (modulePullback B S hS g).obj M, t ≠ 0 := by
  have := isEquivalence_modulePullback_of_iso B S hS ψ
  let c := (modulePullbackCompIso B S hS ψ.hom g).app M
  rw [← exists_hom_ne_zero_iff_of_fullyFaithful (modulePullback B S hS ψ.hom)
    (modulePullbackUnitIso B S hS ψ.hom)]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ c.inv, fun h =>
      hs ((Iso.cancel_iso_hom_right s _ c.symm).1 (h.trans zero_comp.symm))⟩
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ c.hom, fun h =>
      hs ((Iso.cancel_iso_hom_right s _ c).1 (h.trans zero_comp.symm))⟩

end Iso

/-! ### Relocalization -/

section Relocalize

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {Y Z : AlgebraicSpaces B W hW} (ι : Z ⟶ Y)
  (hι : yoneda.relativelyRepresentable ι.hom) (L : Modules.{u, u} B W hW Y.1 Y.2)

/-- **An invertible module stays invertible on the lower-shriek extension.** -/
theorem isInvertibleModule_relocalize (hL : IsInvertibleModule Y L) :
    IsInvertibleModule (relocalizeSpace B hW hS h Y)
      ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L) :=
  (isInvertible_moduleDerelocalize_iff h Y _).1
    (isInvertible_of_iso_modules ((moduleRelocalizeEquivalence B W S hW hS h Y).counitIso.app
      L).symm hL)

/-- Reading the pullback along `Λ ι` of the module corresponding to `L` over `W` is the pullback
of `L` along `ι`. -/
def moduleDerelocalizeModulePullbackIso :
    (moduleDerelocalize B W S hW hS h Z).obj
        ((modulePullback B S hS (relocalizeHom B hW hS h ι)).obj
        ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L)) ≅
      (modulePullback B W hW ι).obj L :=
  ((modulePullbackRelocalizeIso h ι hι).app
      ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L)).symm ≪≫
    (modulePullback B W hW ι).mapIso ((moduleRelocalizeEquivalence B W S hW hS h Y).counitIso.app L)

include hι in
/-- The pullback along `Λ ι` of the module corresponding to `L` is trivial exactly when `ι^* L`
is. -/
theorem nonempty_modulePullback_relocalizeHom_iso_unit_iff :
    Nonempty ((modulePullback B S hS (relocalizeHom B hW hS h ι)).obj
        ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L) ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (relocalizeSpace B hW hS h Z).1
            (relocalizeSpace B hW hS h Z).2).O))) ↔
      Nonempty ((modulePullback B W hW ι).obj L ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B W hW Z.1 Z.2).O))) := by
  refine (nonempty_obj_iso_iff_of_fullyFaithful (moduleDerelocalize B W S hW hS h Z)
    (moduleDerelocalizeUnitIso h Z) _).symm.trans ?_
  exact ⟨fun ⟨i⟩ => ⟨(moduleDerelocalizeModulePullbackIso h ι hι L).symm ≪≫ i⟩,
    fun ⟨i⟩ => ⟨moduleDerelocalizeModulePullbackIso h ι hι L ≪≫ i⟩⟩

include hι in
/-- The pullback along `Λ ι` of the module corresponding to `L` has a nonzero section exactly
when `ι^* L` has one. -/
theorem exists_unit_hom_modulePullback_relocalizeHom_ne_zero_iff :
    (∃ s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (relocalizeSpace B hW hS h Z).1
            (relocalizeSpace B hW hS h Z).2).O)) ⟶
        (modulePullback B S hS (relocalizeHom B hW hS h ι)).obj
          ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L), s ≠ 0) ↔
      ∃ t : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B W hW Z.1 Z.2).O)) ⟶ (modulePullback B W hW ι).obj L, t ≠ 0 := by
  refine (exists_hom_ne_zero_iff_of_fullyFaithful (moduleDerelocalize B W S hW hS h Z)
    (moduleDerelocalizeUnitIso h Z) _).symm.trans ?_
  let c := moduleDerelocalizeModulePullbackIso h ι hι L
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ c.hom, fun h' =>
      hs ((Iso.cancel_iso_hom_right s _ c).1 (h'.trans zero_comp.symm))⟩
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ c.inv, fun h' =>
      hs ((Iso.cancel_iso_hom_right s _ c.symm).1 (h'.trans zero_comp.symm))⟩

variable {V : AlgebraicSpaces B S hS} (ψ : V ≅ relocalizeSpace B hW hS h Z)

include hι in
/-- **Triviality along `ψ ≫ Λ ι`**: the pullback of the module corresponding to `L` along
`ψ ≫ Λ ι` is trivial exactly when `ι^* L` is. -/
theorem nonempty_modulePullback_relocalize_iso_unit_iff :
    Nonempty ((modulePullback B S hS (ψ.hom ≫ relocalizeHom B hW hS h ι)).obj
        ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L) ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1 V.2).O))) ↔
      Nonempty ((modulePullback B W hW ι).obj L ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B W hW Z.1 Z.2).O))) :=
  (nonempty_modulePullback_iso_comp_iso_unit_iff ψ _ _).trans
    (nonempty_modulePullback_relocalizeHom_iso_unit_iff h ι hι L)

include hι in
/-- **Nonzero sections along `ψ ≫ Λ ι`**: the pullback of the module corresponding to `L` along
`ψ ≫ Λ ι` has a nonzero section exactly when `ι^* L` has one. -/
theorem exists_unit_hom_modulePullback_relocalize_ne_zero_iff :
    (∃ s : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS V.1 V.2).O)) ⟶
        (modulePullback B S hS (ψ.hom ≫ relocalizeHom B hW hS h ι)).obj
          ((moduleRelocalizeEquivalence B W S hW hS h Y).inverse.obj L), s ≠ 0) ↔
      ∃ t : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B W hW Z.1 Z.2).O)) ⟶ (modulePullback B W hW ι).obj L, t ≠ 0 :=
  (exists_unit_hom_modulePullback_iso_comp_ne_zero_iff ψ _ _).trans
    (exists_unit_hom_modulePullback_relocalizeHom_ne_zero_iff h ι hι L)

end Relocalize

end AlgebraicGeometry.Space

end
