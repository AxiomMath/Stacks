module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality

/-!
# The higher direct images of a module against the flat base change property

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`. The higher direct images `Rⁱf_*` of sheaves of modules are
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`, and the flat base change property of
Stacks 0762 is `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`. Stacks 0765 says that for a
quasi-compact and quasi-separated morphism of algebraic stacks and a module which is locally
quasi-coherent (Stacks 06WJ) and has the flat base change property, each `Rⁱf_*ℱ` has the flat
base change property.

This file records what holds of that for the two functors as they stand: in degree zero the
higher direct image is the direct image, so the flat base change property of `R⁰f_*ℱ` is a
restatement of the flat base change property of `f_*ℱ` and of nothing else. **No part of Stacks
0765 is claimed here** and no tag is recorded. Stacks 0765 itself is
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_moduleSheafHigherDirectImage`, with the
flat base change property read on sheaves at section universe `u + 1`.

## Main results

* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_moduleSheafHigherDirectImage_zero_iff`: in
  degree zero, the flat base change property of the higher direct image is that of the direct
  image.

## Implementation notes

### The universes at which the two notions meet

The comparison map `c_φ` of Stacks 0761 is the mate of the direct-image comparison under the
pullback–direct image adjunction along the map of structure sheaves, and that adjunction is
supplied by `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall`, which asks the
source site to be essentially small *in the universe of the rings and of the module sections*.
The small étale site of a scheme in `Scheme.{u}` is essentially small in `u` and its structure
sheaf takes values in `RingCat.{u}`, so `AlgebraicGeometry.Stack.restrictModulePullbackComparison`
— and with it `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` — is available only for a
presheaf of modules whose sections lie in `u`.

The direct image of sheaves of modules of Stacks 06WE, on the other hand, is computed by limits
indexed by the two sites, so it is available only for modules whose sections lie in
`max u v w v' w'`, where `v`, `w`, `v'`, `w'` are the object and morphism universes of `𝒳` and
`𝒴`; the same is then true of its right derived functors.

The two therefore meet exactly when `v`, `w`, `v'` and `w'` are bounded by the universe of the
schemes, which is how the variables below are seated. That seating is not the one at which the
2-category `AlgebraicGeometry.Stack.AlgebraicStacks` is built: there the underlying category of a
stack is in `Type (u + 1)`, as the big fppf category over `S` itself is, with morphisms in
`Type u`, and the direct image then produces modules with sections in `u + 1` while the
comparison map wants `u`, so the statement of Stacks 0765 cannot be formed with it. What the
seating below does cover is the `u`-small models: the big fppf category over `S` is essentially
small in `u` by `AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver`, and so is the total
category of a category fibred in groupoids over it by
`AlgebraicGeometry.Stack.essentiallySmall_obj`, so a stack is equivalent to one seated here.

At section universe `u + 1` the flat base change property is
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`, whose module universe is free over the
universe of the schemes subject only to `UnivLE`.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe v w v' w'

variable (B : BigFppfSite.{max v w v' w'}) (E : BigEtaleSite.{max v w v' w'})
  (h : E.cutoff = B.cutoff)
  (S : Scheme.{max v w v' w'}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  [HasWeakSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{max v w v' w'}]
  [(associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{max v w v' w'}]
  [HasWeakSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{max v w v' w'}]
  [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{max v w v' w'}]

/-- In degree zero the higher direct image of a sheaf of modules is the direct image of Stacks
06WE, so it has the flat base change property of Stacks 0762 exactly when the direct image does.
-/
theorem hasFlatBaseChangeProperty_moduleSheafHigherDirectImage_zero_iff
    (M : SheafOfModules.{max v w v' w'} (ringStructureSheafCore B S hS p hp τ hτ)) :
    HasFlatBaseChangeProperty B E h S hS q hq τ hτ
        (((moduleSheafHigherDirectImage B S hS p q hp hq f hf τ hτ 0).obj M).val) ↔
      HasFlatBaseChangeProperty B E h S hS q hq τ hτ
        (((moduleSheafPushforward B S hS p q hp hq f hf τ hτ).obj M).val) := by
  have e :
      (((moduleSheafHigherDirectImage B S hS p q hp hq f hf τ hτ 0).obj M).val) ≅
        (((moduleSheafPushforward B S hS p q hp hq f hf τ hτ).obj M).val) :=
    (SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ)).mapIso
      ((moduleSheafHigherDirectImageZeroIso B S hS p q hp hq f hf τ hτ).app M)
  exact ⟨hasFlatBaseChangeProperty_of_iso B E h S hS q hq τ hτ e,
    hasFlatBaseChangeProperty_of_iso B E h S hS q hq τ hτ e.symm⟩

end AlgebraicGeometry.Stack

end
