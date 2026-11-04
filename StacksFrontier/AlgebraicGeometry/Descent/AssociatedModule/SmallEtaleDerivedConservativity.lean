module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel

/-!
# `ε^*` is conservative on the derived category of `𝒪_S`-modules

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites
of Stacks 08H7/070R.  Its inverse image on modules is the associated-module functor
`ε^* = (𝓕 ↦ 𝓕^a)` of Stacks 03DU (4) at `τ = étale`, which this development spells
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`.  Being additive and exact, `ε^*`
induces `ε^*_D : D(𝒪_S) ⥤ D(S_étale, 𝒪)` through Mathlib's
`CategoryTheory.Functor.mapDerivedCategory`.

This file records that `ε^*_D` is *conservative* in the three senses a descent argument needs:
it commutes with taking cohomology sheaves, and the two properties of a cohomology sheaf that a
descent has to pull back along `ε` — vanishing and finite type — descend along it.

The point of all three is that they hold for an **arbitrary** object of `D(𝒪_S)`, with no
quasi-coherence hypothesis.  On `D_QCoh(𝒪_S)` the functor `ε^*_D` is an equivalence
(`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`, Stacks 071Q) and
conservativity is a triviality; off the quasi-coherent locus `ε^*` is not faithful, so the
faithful-functor route is unavailable and the input is instead the zero-detection assertion of
Stacks 08H8 for an arbitrary `𝒪_S`-module,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso`: the comparison
  `Hⁿ(ε^*_D E) ≅ ε^*(Hⁿ E)`, natural in `E : D(𝒪_S)`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_homology_of_isZero_homology_associatedModule`: `ε^*_D`
  reflects vanishing of a cohomology sheaf.
* `AlgebraicGeometry.SmallEtale.isFiniteType_homology_of_isFiniteType_homology_associatedModule`:
  finite type of a cohomology sheaf descends along `ε^*_D`.
* `AlgebraicGeometry.SmallEtale.reflectsMonomorphisms_associatedModule`: `ε^*` reflects
  monomorphisms, the left-exact companion of
  `AlgebraicGeometry.SmallEtale.reflectsEpimorphisms_associatedModule`.
* `AlgebraicGeometry.SmallEtale.reflectsIsomorphisms_associatedModule`: `ε^*` reflects
  isomorphisms of `𝒪_S`-modules.
* `AlgebraicGeometry.SmallEtale.reflectsIsomorphisms_associatedModuleDerived`: `ε^*_D` reflects
  isomorphisms of `D(𝒪_S)`.

## Implementation notes

The `HasDerivedCategory` instances are left free, as in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean`:
pinning `CategoryTheory.HasDerivedCategory.standard` would put the morphisms of `D(𝒪_S)` one
universe above its objects and make the statements unusable for the quasi-coherent development.
The two sides are allowed to carry different morphism universes, since
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` allows it.

`ε^*` is spelled `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf` throughout rather than
`AlgebraicGeometry.SmallEtale.associatedModule`.  The two are the same term — the former is an
`abbrev` for the latter — but the source is retyped from
`AlgebraicGeometry.Scheme.Modules` to `SheafOfModules.{u} S.ringCatSheaf`.  Those two types are
equal by `rfl`, yet carry separately declared `CategoryTheory.Category` and
`CategoryTheory.Abelian` instances, and instance search does not cross between them; the
`OfSheaf` spelling is the one at which exactness and additivity of `ε^*` are available as
instances, so it is the one at which `mapDerivedCategory` can be formed.  The same mismatch is
why `reflectsMonomorphisms_associatedModule` and `reflectsIsomorphisms_associatedModule` below
are restated at the `OfSheaf` spelling by a `have`, which is a definitional check rather than a
synthesis and therefore does cross, as for `AlgebraicGeometry.RingedSite.ringSheaf` versus
`AlgebraicGeometry.SmallEtale.structureSheaf`.

`isZero_of_isZero_associatedModule_general` is stated for a module over
`Stacks.Sheaves.RingedToposModules.structureRingSheaf S.zariskiRingedTopos`, a third spelling of
the same sheaf of rings; it too is `rfl`-equal to `S.ringCatSheaf`, and unifies without help.

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08WK](https://stacks.math.columbia.edu/tag/08WK)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `ε^*` reflects monomorphisms and isomorphisms of `𝒪_S`-modules -/

/-- **`ε^*` reflects monomorphisms.**  It is left exact — that is Stacks 08H8, formalized as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf` — and it detects
zero objects, by the zero-detection assertion of Stacks 08H8 for an *arbitrary* `𝒪_S`-module,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`.

This is the left-exact companion of
`AlgebraicGeometry.SmallEtale.reflectsEpimorphisms_associatedModule`, and is stated at the
`OfSheaf` retyping of `ε^*` because that is the spelling at which left exactness is an
instance. -/
theorem reflectsMonomorphisms_associatedModule :
    (associatedModuleOfSheaf B S hS).ReflectsMonomorphisms :=
  Functor.reflectsMonomorphisms_of_preservesFiniteLimits_of_reflectsZeroObjects
    (associatedModuleOfSheaf B S hS) fun F ↦ isZero_of_isZero_associatedModule_general B S hS F

/-- **`ε^*` reflects isomorphisms of `𝒪_S`-modules.**  A morphism of an abelian category that is
both a monomorphism and an epimorphism is an isomorphism, and `ε^*` reflects each of the two
by `AlgebraicGeometry.SmallEtale.reflectsMonomorphisms_associatedModule` and
`AlgebraicGeometry.SmallEtale.reflectsEpimorphisms_associatedModule`.

Note that `ε^*` is **not** faithful off the quasi-coherent locus, so this does not come from
`CategoryTheory.Functor.ReflectsIsomorphisms` for a full and faithful functor; it is exactness
plus zero detection that does the work. -/
theorem reflectsIsomorphisms_associatedModule :
    (associatedModuleOfSheaf B S hS).ReflectsIsomorphisms := by
  have hmono := reflectsMonomorphisms_associatedModule B S hS
  have hepi : (associatedModuleOfSheaf B S hS).ReflectsEpimorphisms :=
    reflectsEpimorphisms_associatedModule B S hS
  refine ⟨fun {X Y} f hf => ?_⟩
  have := hf
  have : Mono f := hmono.reflects f inferInstance
  have : Epi f := hepi.reflects f inferInstance
  exact isIso_of_mono_of_epi f

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-! ### `Hⁿ` commutes with `ε^*` on derived categories -/

/-- **`Hⁿ` commutes with `ε^*` on derived categories.**  For every `n : ℤ` there is an
isomorphism `Hⁿ(ε^*_D E) ≅ ε^*(Hⁿ E)`, natural in `E : D(𝒪_S)`.

This is `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` — an exact additive functor
commutes with the homology of the derived category — instantiated at `ε^*`.  Its three
hypotheses are instances at the `OfSheaf` spelling:
`AlgebraicGeometry.SmallEtale.additive_associatedModuleOfSheaf`,
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf` (Stacks 08H8) and
`AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleOfSheaf`. -/
def associatedModuleDerivedHomologyIso (n : ℤ) :
    (associatedModuleOfSheaf B S hS).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheaf B S hS)) n ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) n ⋙
        associatedModuleOfSheaf B S hS :=
  (associatedModuleOfSheaf B S hS).mapDerivedCategoryHomologyIso n

/-! ### Vanishing of a cohomology sheaf descends along `ε^*` -/

/-- **`ε^*_D` reflects vanishing of a cohomology sheaf.**  If `Hⁿ(ε^*_D E)` vanishes then so
does `Hⁿ E`, for an arbitrary `E : D(𝒪_S)` with no quasi-coherence hypothesis.

By `AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso` the hypothesis says that
`ε^*(Hⁿ E)` vanishes, and `ε^*` detects zero objects of an arbitrary `𝒪_S`-module by the
zero-detection assertion of Stacks 08H8,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`.

This is deliberately *not*
`KoszulLiftReflectionAudit.isZero_homology_mapDerivedCategory_iff`, which asks for `F.Faithful`:
`ε^*` is not faithful on all `𝒪_S`-modules, only on the quasi-coherent ones. -/
theorem isZero_homology_of_isZero_homology_associatedModule
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheaf B S hS)) n).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E))) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) n).obj E) :=
  isZero_of_isZero_associatedModule_general B S hS _
    (h.of_iso ((associatedModuleDerivedHomologyIso B S hS n).app E).symm)

/-! ### Finite type of a cohomology sheaf descends along `ε^*` -/

/-- **Finite type of a cohomology sheaf descends along `ε^*_D`.**  If `Hᵐ(ε^*_D E)` is of
finite type then so is `Hᵐ E`, for an arbitrary `E : D(𝒪_S)`.

The chain is: rewrite `Hᵐ(ε^*_D E) ≅ ε^*(Hᵐ E)` by
`AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso`, pass from Mathlib's
`SheafOfModules.IsFiniteType` to the categorical form 03DL (5) by
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType`, descend along `ε^*` by
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule` — the implication
(2) ⇒ (1) of Stacks 08HD — and come back by
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`. -/
theorem isFiniteType_homology_of_isFiniteType_homology_associatedModule
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ)
    (h : SheafOfModules.IsFiniteType ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheaf B S hS)) m).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E))) :
    SheafOfModules.IsFiniteType
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) m).obj E) := by
  have h1 : SheafOfModules.IsFiniteType ((associatedModuleOfSheaf B S hS).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) m).obj E)) :=
    Stacks.SheafOfModules.Site.isFiniteType_of_iso
      ((associatedModuleDerivedHomologyIso B S hS m).app E) h
  have h2 := Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ h1
  have h3 := isFiniteTypeOnSite_of_associatedModule B S hS _ h2
  exact Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ h3

/-! ### `ε^*_D` reflects isomorphisms -/

/-- **`ε^*_D` reflects isomorphisms of `D(𝒪_S)`.**  A morphism of `D(𝒪_S)` carried to an
isomorphism by `ε^*_D` is already an isomorphism, with no quasi-coherence hypothesis.

`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff` turns the hypothesis into: `ε^*`
carries each homology map of `φ` to an isomorphism.  Then
`AlgebraicGeometry.SmallEtale.reflectsIsomorphisms_associatedModule` makes each homology map of
`φ` an isomorphism, and `CategoryTheory.DerivedCategory.isIso_iff` assembles those into `φ`
being an isomorphism. -/
theorem reflectsIsomorphisms_associatedModuleDerived :
    (associatedModuleOfSheaf B S hS).mapDerivedCategory.ReflectsIsomorphisms := by
  have hiso := reflectsIsomorphisms_associatedModule B S hS
  refine ⟨fun {K L} φ hφ => ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have := ((associatedModuleOfSheaf B S hS).isIso_mapDerivedCategory_map_iff φ).mp hφ n
  exact hiso.reflects _

end Derived

end AlgebraicGeometry.SmallEtale

end
