module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage

/-!
# The coherent sheaves of modules on a site form a weak Serre subcategory

On an arbitrary site, with the sections of the modules in the universe of the sections of the
sheaf of rings, the sheaves of modules coherent in the sense of Stacks 03DL(8)
(`SheafOfModules.IsCoherentOnSite`) contain zero and are closed under isomorphisms, kernels and
cokernels (Stacks 01BY (3)) and extensions (Stacks 01BY (4)): they form a weak Serre subcategory
(Stacks 02MO).  The closure results are already available; this file packages them.

It also records that the preimage of a weak Serre subcategory under an equivalence of abelian
categories is a weak Serre subcategory, which is how coherence on a slice of one ringed site is
read on the corresponding slice of an equivalent one.

## Main definitions

* `SheafOfModules.isCoherentOnSite`: coherence on a site as an `ObjectProperty`.

## Main results

* `SheafOfModules.isCoherentOnSite_isWeakSerreClass` and
  `SheafOfModules.isWeakSerre_isCoherentOnSite`.
* `CategoryTheory.ObjectProperty.isWeakSerreClass_inverseImage_of_isEquivalence`.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u v w u' v'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **The preimage of a weak Serre subcategory under an equivalence of abelian categories is a
weak Serre subcategory.** -/
theorem isWeakSerreClass_inverseImage_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence]
    (P : ObjectProperty D) [P.IsWeakSerreClass] : (P.inverseImage F).IsWeakSerreClass := by
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  exact
    { exists_zero := ⟨0, isZero_zero C, P.prop_of_isZero (F.map_isZero (isZero_zero C))⟩
      of_iso := fun e h => P.prop_of_iso (F.mapIso e) h
      kernels_le := by
        rintro _ ⟨f, k, hk, h₁, h₂⟩
        exact P.prop_of_isLimit_kernelFork (KernelFork.mapIsLimit k hk F) h₁ h₂
      cokernels_le := by
        rintro _ ⟨f, k, hk, h₁, h₂⟩
        exact P.prop_of_isColimit_cokernelCofork (CokernelCofork.mapIsColimit k hk F) h₁ h₂
      prop_X₂_of_shortExact := fun hS h₁ h₃ => P.prop_X₂_of_shortExact (hS.map_of_exact F) h₁ h₃ }

end CategoryTheory.ObjectProperty

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Coherence on a site (Stacks 03DL(8)) as a property of objects of the category of sheaves of
modules. -/
abbrev isCoherentOnSite : ObjectProperty (SheafOfModules.{w} R) :=
  fun M => SheafOfModules.IsCoherentOnSite M

/-- **The coherent sheaves of modules on a site form a weak Serre subcategory**: they contain
zero and are closed under isomorphisms, kernels, cokernels (Stacks 01BY (3)) and extensions
(Stacks 01BY (4)). -/
instance isCoherentOnSite_isWeakSerreClass : (isCoherentOnSite R).IsWeakSerreClass where
  exists_zero := ⟨0, isZero_zero _, Stacks.SheafOfModules.isCoherentOnSite_zero (isZero_zero _)⟩
  of_iso e h := Stacks.SheafOfModules.isCoherentOnSite_of_iso e h
  kernels_le := by
    rintro _ ⟨f, k, hk, h₁, h₂⟩
    exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (Stacks.SheafOfModules.isCoherentOnSite_kernel h₁ h₂ f)
  cokernels_le := by
    rintro _ ⟨f, k, hk, h₁, h₂⟩
    exact Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (Stacks.SheafOfModules.isCoherentOnSite_cokernel f h₁ h₂)
  prop_X₂_of_shortExact hS h₁ h₃ := Stacks.SheafOfModules.isCoherentOnSite_X₂_of_shortExact hS h₁ h₃

/-- The coherent sheaves of modules on a site form a weak Serre subcategory in the sense of
Stacks 02MO. -/
theorem isWeakSerre_isCoherentOnSite : WeakSerre.IsWeakSerre (isCoherentOnSite R) :=
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

end SheafOfModules

end
