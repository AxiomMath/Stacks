module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Colimits

/-!
# Colimits of quasi-coherent modules on a category fibred in groupoids

Let `p : 𝒳 ⥤ BigFppfOver B S hS` be an essentially small category fibred in groupoids. Whenever
quasi-coherence on the associated fppf site is closed under colimits of a shape `K` with a
`u`-small type of objects, quasi-coherent modules have colimits of shape `K` and the inclusion
into all fppf module sheaves preserves them.

## Main results

* `AlgebraicGeometry.FibredSite.hasColimitsOfShape_quasicoherentModules`: quasi-coherent
  modules have colimits of a given shape with a `u`-small type of objects, given closure of
  quasi-coherence under them.
* `AlgebraicGeometry.FibredSite.preservesColimitsOfShape_quasicoherentInclusion`: the
  inclusion into all fppf module sheaves preserves them.
* `AlgebraicGeometry.FibredSite.hasColimits_quasicoherentModules_of_smallSite` and
  `AlgebraicGeometry.FibredSite.preservesColimits_quasicoherentInclusion_of_smallSite`: for a
  fibred category whose objects form a `Type u`, the two statements above for all shapes at
  once, in the `CategoryTheory.Limits.HasColimits` and `CategoryTheory.Limits.PreservesColimits`
  forms.

## Implementation notes

The shape `K` is restricted only by `Small.{u} K`; its universe of morphisms is free. The
all-shapes forms are stated for fibred categories whose objects form a `Type u`, where the
morphisms of the ambient category of module sheaves also lie in `Type u`.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t' t w v u

namespace AlgebraicGeometry.FibredSite

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (K : Type t) [Category.{t'} K] [Small.{u} K]

/-- Quasi-coherent modules on the associated fppf site of an essentially small category fibred
in groupoids have colimits of a given shape with a `u`-small type of objects, provided
quasi-coherence is closed under them. -/
public theorem hasColimitsOfShape_quasicoherentModules
    (h : (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K) :
    HasColimitsOfShape K (quasicoherentModules.{u, v, w, u} B S hS p hp) := by
  let _ := h
  let _ := hasColimitsOfShape_sheafOfModules_ringStructureSheafCore B S hS p hp .fppf K
  infer_instance

/-- The inclusion of quasi-coherent modules into all fppf module sheaves preserves colimits of
a given shape with a `u`-small type of objects, provided quasi-coherence is closed under them. -/
public theorem preservesColimitsOfShape_quasicoherentInclusion
    (h : (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K) :
    PreservesColimitsOfShape K
      (SheafOfModules.isQuasicoherentOnSite.{v, w, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι := by
  let _ := h
  let _ := hasColimitsOfShape_sheafOfModules_ringStructureSheafCore B S hS p hp .fppf K
  infer_instance

end

section SmallSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type u} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- Quasi-coherent modules on a category fibred in groupoids whose objects form a `Type u` have
all colimits, provided quasi-coherence is closed under colimits of every shape in `Type u`. -/
public theorem hasColimits_quasicoherentModules_of_smallSite
    (h : ∀ (K : Type u) [Category.{u} K],
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K) :
    HasColimits (quasicoherentModules.{u, u, u, u} B S hS p hp) :=
  ⟨fun K _ => hasColimitsOfShape_quasicoherentModules B S hS p hp K (h K)⟩

/-- On a category fibred in groupoids whose objects form a `Type u`, the inclusion of
quasi-coherent modules into all fppf module sheaves preserves colimits, provided quasi-coherence
is closed under colimits of every shape in `Type u`. -/
public theorem preservesColimits_quasicoherentInclusion_of_smallSite
    (h : ∀ (K : Type u) [Category.{u} K],
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).IsClosedUnderColimitsOfShape K) :
    PreservesColimits
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι :=
  ⟨fun {K} _ => preservesColimitsOfShape_quasicoherentInclusion B S hS p hp K (h K)⟩

end SmallSite

end AlgebraicGeometry.FibredSite

end
