module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian objects in the derived category of modules on a category

Let `C` be a category viewed as a site with the chaotic topology and let `O` be a sheaf of rings
on `C`, that is a functor `O : Cᵒᵖ ⥤ RingCat`. An object `K` of `D(O)` is *cartesian* when for
every morphism `U → V` of `C` the canonical map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an
isomorphism in `D(O(U))`. The cartesian objects form the full subcategory `QC(O) ⊆ D(O)`.

Tag 0H0R expresses this condition relative to a datum
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData O`, which records, for every
restriction homomorphism `O(V) → O(U)`, the derived base change `- ⊗^L_{O(V)} O(U)`
characterized as the left adjoint of derived restriction of scalars, together with its
functoriality isomorphism. This file supplies that datum, so that the cartesian condition and the
subcategory `QC(O)` depend on `O` alone.

## Main definitions

* `Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData`: the base-change datum of
  `O`, assembled from derived extension of scalars along the restriction homomorphisms of `O`.
* `Stacks.ModulesOnACategory.CartesianObjects.IsCartesian`: an object of `D(O)` has cartesian
  derived sections.
* `Stacks.ModulesOnACategory.CartesianObjects.cartesianDerivedModules`: the full subcategory
  `QC(O) ⊆ D(O)`.

## Implementation notes

Derived base change along a ring homomorphism is the total left derived functor of extension of
scalars, which `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` builds from
K-flat resolutions, and `derivedExtensionScalarsAdjunction` exhibits as the left adjoint of
derived restriction of scalars. Both are available for homomorphisms of *commutative* rings only,
extension of scalars along a homomorphism of general rings being absent from the ambient library.
Accordingly `canonicalBaseChangeData` carries the hypothesis that every section ring `O(U)` is
commutative, which is the standing convention of the source;
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData O` itself is used verbatim,
with `O : Cᵒᵖ ⥤ RingCat` as there.

The functoriality isomorphism is not constructed by hand: derived base change along `a ≫ b` and
the composite of the derived base changes along `a` and `b` are left adjoints of derived
restriction along `a ≫ b` and of the composite of the derived restrictions, and those two right
adjoints are isomorphic because restriction of scalars along a composite of ring homomorphisms is
the composite of the restrictions. Conjugating that isomorphism of right adjoints
(`CategoryTheory.conjugateIsoEquiv`) produces the isomorphism of left adjoints. Transporting the
isomorphism of restriction functors from module categories to derived categories uses that an
exact functor's descent to derived categories is a localization lift, so two such descents with
isomorphic sources are isomorphic.

### Universes

The module universe of every object named below is the one fixed by
`StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability`:
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod O` is the derived category of
`PresheafOfModules.{max u v r w} O`, and
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.RGamma O U` lands in
`DerivedCategory (ModuleCat.{max u v r w} (O.obj U))`. So with the structure sheaf taken at
`RingCat.{0}` and the modules at `w = 0`, the coefficient module universe is `max u v`, the
maximum of the two site universes. This is why the explicit `ModuleCat.{max u v}` and
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.*.{0}` annotations appear: they name the
universes the dependency determines, and none of them is a choice made in this file.

## References

* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0H0R](https://stacks.math.columbia.edu/tag/0H0R)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryIsoOfNatIso mapDerivedCategoryCompIso
  mapDerivedCategoryCompIso_inv_app_Q)

universe r u v w

namespace Stacks.ModulesOnACategory.CartesianObjects

attribute [local instance] HasDerivedCategory.standard

section Generalities

/-- The commutative ring structure on a ring object whose multiplication is commutative. It is an
`abbrev` so that instance search sees through it when it is introduced by `letI`, and its
underlying ring structure is the given one. -/
abbrev commRingOfComm (R : RingCat.{r}) (hR : ∀ x y : R, x * y = y * x) : CommRing R :=
  { (inferInstance : Ring R) with mul_comm := hR }

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- Derived restriction of scalars along a composite is the composite of derived restrictions:
restriction of scalars along `(O.map b) ∘ (O.map a)` is restriction along `O.map b` followed by
restriction along `O.map a`, and that isomorphism descends to the derived categories. -/
def dRestrictCompIso {U V W : Cᵒᵖ} (a : W ⟶ V) (b : V ⟶ U) :
    Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DRestrict.{w} O b ⋙
      Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DRestrict.{w} O a ≅
      Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DRestrict.{w} O (a ≫ b) :=
  (mapDerivedCategoryCompIso (ModuleCat.restrictScalars.{max u v r w} (O.map b).hom)
      (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)).symm ≪≫
    (mapDerivedCategoryIsoOfNatIso _ _
      (ModuleCat.restrictScalarsComp'.{max u v r w} (O.map a).hom (O.map b).hom
        (O.map (a ≫ b)).hom (by rw [O.map_comp]; rfl))).symm

end Generalities

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{0})
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)

/-- Derived base change `- ⊗^L_{O(V)} O(U)` along the restriction homomorphism of `a : V ⟶ U`
in `Cᵒᵖ`, namely the total left derived functor of extension of scalars along `O.map a`. -/
def baseChange {U V : Cᵒᵖ} (a : V ⟶ U) :
    DerivedCategory (ModuleCat.{max u v} (O.obj V)) ⥤
      DerivedCategory (ModuleCat.{max u v} (O.obj U)) :=
  letI := commRingOfComm (O.obj U) (hO U)
  letI := commRingOfComm (O.obj V) (hO V)
  (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).functor

/-- Derived base change along `a` is left adjoint to derived restriction of scalars along `a`
(tag 0GMT), which is what characterizes it canonically. -/
def baseChangeAdj {U V : Cᵒᵖ} (a : V ⟶ U) :
    baseChange O hO a ⊣ Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DRestrict.{0} O a := by
  letI := commRingOfComm (O.obj U) (hO U)
  letI := commRingOfComm (O.obj V) (hO V)
  haveI : Functor.IsLeftDerivedFunctor
      (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).functor
      (show DerivedCategory.Q ⋙
            (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).functor ⟶
          (ModuleCat.extendScalars (O.map a).hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q from
        (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} (O.obj V)) (ComplexShape.up ℤ)) :=
    (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).isLeftDerived
  exact derivedExtensionScalarsAdjunction.{0, 0, max u v} (O.map a).hom
    (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).functor
    (totalDerivedExtensionScalars.{0, 0, max u v} (O.map a).hom).comparison

/-- **Tag 0GYV, base-change datum.** The derived extension-of-scalars functors along all
restriction homomorphisms of `O`, with their adjunctions to derived restriction of scalars and
their composition isomorphisms. The functoriality isomorphism is obtained by conjugating the
composition isomorphism of the right adjoints. -/
def canonicalBaseChangeData : Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData.{0}
  O where
  baseChange a := baseChange O hO a
  baseChangeAdj a := baseChangeAdj O hO a
  baseChangeComp a b :=
    (conjugateIsoEquiv ((baseChangeAdj O hO a).comp (baseChangeAdj O hO b))
      (baseChangeAdj O hO (a ≫ b))).symm (dRestrictCompIso O a b)

/-- An object of `D(O)` has cartesian derived sections if for every morphism `U → V` of `C` the
canonical derived base-change comparison `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an
isomorphism. -/
@[stacks 0GYV "cartesian-object condition"]
abbrev IsCartesian (K : Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod.{0} O) : Prop :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.IsQC.{0} (canonicalBaseChangeData O hO) K

/-- The full subcategory `QC(O) ⊆ D(O)` consisting of the objects with cartesian derived
sections. -/
@[stacks 0GYV "the full subcategory QC(O)"]
abbrev cartesianDerivedModules : Type _ :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.QC.{0} (canonicalBaseChangeData O hO)

end Stacks.ModulesOnACategory.CartesianObjects

end
