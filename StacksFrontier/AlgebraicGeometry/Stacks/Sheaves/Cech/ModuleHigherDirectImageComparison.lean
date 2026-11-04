module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence

/-!
# Two direct images of sheaves of modules along a 1-morphism of fibred categories

A 1-morphism `f : 𝒳 ⥤ 𝒴` of categories fibred in groupoids over the big fppf category of a
scheme `S` has two direct images of sheaves of modules, both right adjoint to the same inverse
image:

* `AlgebraicGeometry.Stack.moduleSheafPushforward`, the direct image of [Stacks, Tag 06WE],
  given on underlying presheaves of modules by the functor of compatible families of
  `AlgebraicGeometry.Stack.moduleFunctoriality`; its right derived functors are the higher direct
  images `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`;
* `Stacks.RelativeCech.moduleDirectImage`, given on underlying presheaves of modules by the right
  Kan extension `PresheafOfModules.directImageObj` along `f.op`; the relative Čech spectral
  sequence `Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData` abuts to its right
  derived functors.

This file shows that the two direct images, and hence their right derived functors, are
isomorphic.

## Main results

* `AlgebraicGeometry.Stack.relativeCechModuleInverseImage_eq_modulePullback_anyUniverse`: the
  two *inverse* images agree on the nose.
* `AlgebraicGeometry.Stack.moduleDirectImageIsoModuleSheafPushforward`: the two direct images
  are isomorphic.
* `AlgebraicGeometry.Stack.moduleHigherDirectImageIso`: in every degree, the right derived
  functors of `Stacks.RelativeCech.moduleDirectImage` are the higher direct images
  `AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`.

## References

* [Stacks Project, Tag 06WD](https://stacks.math.columbia.edu/tag/06WD)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w vb wb a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type vb} [Category.{wb} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (τ : SiteKind)

/-- The inverse image of sheaves of modules `Stacks.RelativeCech.moduleInverseImage` is equal to
`AlgebraicGeometry.Stack.modulePullback`. -/
theorem relativeCechModuleInverseImage_eq_modulePullback_anyUniverse :
    Stacks.RelativeCech.moduleInverseImage.{u, v, vb, w, wb, max u v w vb wb}
        B S hS p q hp hq f hf τ =
      modulePullback.{u, v, w, max u v w vb wb, vb, wb} B S hS p q hp hq f hf
        (B.baseTopology τ) (B.baseTopology_le_topology τ) := by
  cases hf
  rfl

/-- The direct image `Stacks.RelativeCech.moduleDirectImage` is isomorphic to
`AlgebraicGeometry.Stack.moduleSheafPushforward`. -/
noncomputable def moduleDirectImageIsoModuleSheafPushforward :
    Stacks.RelativeCech.moduleDirectImage.{u, v, vb, w, wb, max u v w vb wb}
        B S hS p q hp hq f hf τ ≅
      moduleSheafPushforward.{u, v, w, u, vb, wb} B S hS p q hp hq f hf
        (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  Adjunction.rightAdjointUniq
    (Stacks.RelativeCech.moduleInverseDirectImageAdjunction.{u, v, vb, w, wb,
      max u v w vb wb} B S hS p q hp hq f hf τ)
    (Adjunction.ofNatIsoLeft
      (moduleSheafAdjunction.{u, v, w, u, vb, wb} B S hS p q hp hq f hf
        (B.baseTopology τ) (B.baseTopology_le_topology τ))
      (eqToIso (relativeCechModuleInverseImage_eq_modulePullback_anyUniverse.{u, v, w, vb, wb}
        B S hS p q hp hq f hf τ).symm))

section Derived

variable [HasWeakSheafify (associatedTopology B S hS p (B.baseTopology τ))
    AddCommGrpCat.{max u v w vb wb}]
  [(associatedTopology B S hS p (B.baseTopology τ)).WEqualsLocallyBijective
    AddCommGrpCat.{max u v w vb wb}]
  [HasWeakSheafify (associatedTopology B S hS q (B.baseTopology τ))
    AddCommGrpCat.{max u v w vb wb}]
  [(associatedTopology B S hS q (B.baseTopology τ)).WEqualsLocallyBijective
    AddCommGrpCat.{max u v w vb wb}]

/-- In every degree `n`, the `n`-th right derived functor of
`Stacks.RelativeCech.moduleDirectImage` is isomorphic to the higher direct image `Rⁿf_*` of
`AlgebraicGeometry.Stack.moduleSheafHigherDirectImage`. -/
noncomputable def moduleHigherDirectImageIso (n : ℕ) :
    letI := Stacks.RelativeCech.moduleDirectImage_additive.{u, v, vb, w, wb,
      max u v w vb wb} B S hS p q hp hq f hf τ
    letI : EnoughInjectives (SheafOfModules.{max u v w vb wb}
        (ringStructureSheafCore B S hS p hp (B.baseTopology τ)
          (B.baseTopology_le_topology τ))) :=
      enoughInjectives_moduleSheaves.{u, v, w, max u v w vb wb} B S hS p hp
        (B.baseTopology τ) (B.baseTopology_le_topology τ)
    (Stacks.RelativeCech.moduleDirectImage.{u, v, vb, w, wb, max u v w vb wb}
        B S hS p q hp hq f hf τ).rightDerived n ≅
      moduleSheafHigherDirectImage.{u, v, w, vb, wb} B S hS p q hp hq f hf
        (B.baseTopology τ) (B.baseTopology_le_topology τ) n := by
  letI := Stacks.RelativeCech.moduleDirectImage_additive.{u, v, vb, w, wb,
    max u v w vb wb} B S hS p q hp hq f hf τ
  letI : EnoughInjectives (SheafOfModules.{max u v w vb wb}
      (ringStructureSheafCore B S hS p hp (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) :=
    enoughInjectives_moduleSheaves.{u, v, w, max u v w vb wb} B S hS p hp
      (B.baseTopology τ) (B.baseTopology_le_topology τ)
  let e := moduleDirectImageIsoModuleSheafPushforward.{u, v, w, vb, wb}
    B S hS p q hp hq f hf τ
  have inner :
      (Stacks.RelativeCech.moduleDirectImage.{u, v, vb, w, wb, max u v w vb wb}
          B S hS p q hp hq f hf τ).rightDerived n ≅
        (moduleSheafPushforward.{u, v, w, u, vb, wb} B S hS p q hp hq f hf
          (B.baseTopology τ) (B.baseTopology_le_topology τ)).rightDerived n :=
    { hom := NatTrans.rightDerived e.hom n
      inv := NatTrans.rightDerived e.inv n
      hom_inv_id := by
        rw [← NatTrans.rightDerived_comp e.hom e.inv n, e.hom_inv_id,
          NatTrans.rightDerived_id]
      inv_hom_id := by
        rw [← NatTrans.rightDerived_comp e.inv e.hom n, e.inv_hom_id,
          NatTrans.rightDerived_id] }
  exact inner

end Derived

end AlgebraicGeometry.Stack

end
