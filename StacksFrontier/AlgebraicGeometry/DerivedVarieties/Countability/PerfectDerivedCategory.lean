module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.BoundedDerivedCategory
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Countability of the perfect and the bounded coherent derived categories

Let `X` be a scheme of finite type over a countable Noetherian ring. [Stacks, Tag 0G0W] asserts
that `D_perf(𝒪_X)` and `D^b_Coh(𝒪_X)` are countable, countability of a category being
`CategoryTheory.EssentiallyCountableCategory`: countably many morphisms between any two objects
and countably many isomorphism classes of objects, the notion of [Stacks, Section 0G0T].

The proof is the one of the source. `X` is Noetherian ([Stacks, Tag 01T6]). A perfect object of
`D(𝒪_X)` has bounded coherent cohomology ([Stacks, Tag 0FXU]), so `D_perf(𝒪_X)` is a full
subcategory of `D^b_Coh(𝒪_X)`, and countability passes to full subcategories. Next
`D^b_Coh(𝒪_X)` is equivalent to `D^b(Coh(𝒪_X))` ([Stacks, Tag 0FDB]), which is countable
because `Coh(𝒪_X)` is ([Stacks, Tag 0G0V]); countability of `Coh(𝒪_X)`, which the source omits,
is `AlgebraicGeometry.essentiallyCountable_coherentModules_of_finiteType`.

## Main results

* `CategoryTheory.EssentiallyCountableCategory.of_full_of_faithful`: a category admitting a
  fully faithful functor to an essentially countable category is essentially countable.
* `AlgebraicGeometry.essentiallyCountable_isPerfect_of_boundedCoherent`: on a Noetherian scheme
  `D_perf(𝒪_X)` is essentially countable as soon as `D^b_Coh(𝒪_X)` is.
* `DerivedCategoryB.essentiallyCountable_derivedCategoryBBounded_of_model`: essential
  countability of `D^b_B(A)` does not depend on the model of the derived category.
* `AlgebraicGeometry.essentiallyCountable_boundedCoherent_of_finiteType`: `D^b_Coh(𝒪_X)` is
  essentially countable.
* `AlgebraicGeometry.essentiallyCountable_perfect_and_boundedCoherent_of_finiteType`:
  **[Stacks, Tag 0G0W]**.

## Implementation notes

The derived category of `𝒪_X`-modules is read at an arbitrary
`CategoryTheory.HasDerivedCategory` instance, as [Stacks, Tag 0FXU] is, rather than at
`CategoryTheory.HasDerivedCategory.standard`; the modules are spelled
`StrictlyPerfect.OXMod` of the underlying ringed space, the spelling of that tag, which
is the same type as `AlgebraicGeometry.Scheme.Modules` of the scheme. [Stacks, Tag 0FDB] is
proved at the standard model, and the result is moved to an arbitrary model along the comparison
equivalence `StacksDraft.DerivedModel.modelEquiv`, which preserves cohomology.

`D^b_Coh(𝒪_X)` is `DerivedCategoryB.derivedCategoryBBounded` applied to coherence of
`𝒪_X`-modules, and `D_perf(𝒪_X)` is `AlgebraicGeometry.RingedSpace.IsPerfect`, the perfectness
of [Stacks, Tag 08CM]; both are read as full subcategories of `D(𝒪_X)` cut out by those object
properties.

## References

* [Stacks Project, Tag 0G0W](https://stacks.math.columbia.edu/tag/0G0W)
* [Stacks Project, Tag 0G0V](https://stacks.math.columbia.edu/tag/0G0V)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

open CategoryTheory

universe v v' u u' d

namespace CategoryTheory

/-- A category admitting a fully faithful functor to an essentially countable category is
itself essentially countable: the functor is injective on each morphism set, and, being fully
faithful, injective on isomorphism classes. -/
public theorem EssentiallyCountableCategory.of_full_of_faithful
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (hD : EssentiallyCountableCategory D) :
    EssentiallyCountableCategory C where
  countableHom X Y :=
    have := hD.countableHom (F.obj X) (F.obj Y)
    F.map_injective.countable
  countableSkeleton :=
    have := hD.countableSkeleton
    F.mapSkeleton_injective.countable

end CategoryTheory

namespace AlgebraicGeometry

/-- On a Noetherian scheme the perfect objects of `D(𝒪_X)` form an essentially countable
category as soon as the bounded objects with coherent cohomology do, because a perfect object
has bounded coherent cohomology ([Stacks, Tag 0FXU]) and so `D_perf(𝒪_X)` is a full subcategory
of `D^b_Coh(𝒪_X)`. -/
public theorem essentiallyCountable_isPerfect_of_boundedCoherent (X : Scheme.{u})
    [IsNoetherian X]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (hbc : EssentiallyCountableCategory
      (ObjectProperty.FullSubcategory
        (DerivedCategoryB.derivedCategoryBBounded
          (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)))) :
    EssentiallyCountableCategory
      (ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) =>
          RingedSpace.IsPerfect (X := X.toRingedSpace) K)) := by
  let P : ObjectProperty
      (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :=
    fun K => RingedSpace.IsPerfect (X := X.toRingedSpace) K
  let Q : ObjectProperty
      (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :=
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
  have hPQ : P ≤ Q := fun K hK =>
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X K hK
  exact EssentiallyCountableCategory.of_full_of_faithful (ObjectProperty.ιOfLE hPQ) hbc

/-- The perfect half of [Stacks, Tag 0G0W], reduced to its coherent half `hbc`. Let `R` be a
countable Noetherian ring and let `X` be a scheme of finite type over `R`. Then the perfect objects
of `D(𝒪_X)` form an essentially countable category, as soon as the bounded objects with coherent
cohomology do. -/
public theorem essentiallyCountable_isPerfect_of_finiteType {R : Type u} [CommRing R]
    [Countable R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]
    (hbc : EssentiallyCountableCategory
      (ObjectProperty.FullSubcategory
        (DerivedCategoryB.derivedCategoryBBounded
          (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent)))) :
    EssentiallyCountableCategory
      (ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) =>
          RingedSpace.IsPerfect (X := X.toRingedSpace) K)) :=
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  essentiallyCountable_isPerfect_of_boundedCoherent X hbc

end AlgebraicGeometry

namespace DerivedCategoryB

/-- Essential countability of `D^b_B(A)` does not depend on the chosen model of the derived
category: the comparison equivalence of two models identifies their cohomology functors, hence
their full subcategories `D^b_B(A)`. -/
public theorem essentiallyCountable_derivedCategoryBBounded_of_model {C : Type u}
    [Category.{v} C] [Abelian C] (B : ObjectProperty C) [B.IsClosedUnderIsomorphisms]
    (h₁ : HasDerivedCategory.{v'} C) (h₂ : HasDerivedCategory.{u'} C)
    (H : EssentiallyCountableCategory (@derivedCategoryBBounded C _ _ h₂ B).FullSubcategory) :
    EssentiallyCountableCategory (@derivedCategoryBBounded C _ _ h₁ B).FullSubcategory := by
  let E := StacksDraft.DerivedModel.modelEquiv h₁ h₂
  have hmem : ∀ K : (@derivedCategoryBBounded C _ _ h₁ B).FullSubcategory,
      @derivedCategoryBBounded C _ _ h₂ B (E.functor.obj K.obj) := by
    intro K
    have e := fun n => (StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso h₁ h₂ n).app K.obj
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hB⟩ := K.property
    exact ⟨⟨⟨a, fun n hn => (ha n hn).of_iso (e n)⟩, ⟨b, fun n hn => (hb n hn).of_iso (e n)⟩⟩,
      fun n => B.prop_of_iso (e n).symm (hB n)⟩
  exact EssentiallyCountableCategory.of_full_of_faithful
    ((@derivedCategoryBBounded C _ _ h₂ B).lift
      ((@derivedCategoryBBounded C _ _ h₁ B).ι ⋙ E.functor) hmem) H

end DerivedCategoryB

namespace AlgebraicGeometry

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- On a Noetherian scheme whose category of coherent modules is essentially countable,
`D^b_Coh(𝒪_X)` is essentially countable, at the standard model of the derived category: it is
equivalent to `D^b(Coh(𝒪_X))` by [Stacks, Tag 0FDB], which is essentially countable by
[Stacks, Tag 0G0V]. -/
public theorem essentiallyCountable_boundedCoherent_standard (X : Scheme.{u}) [IsNoetherian X]
    [EssentiallyCountableCategory (SheafOfModules.CoherentModules X.ringCatSheaf)] :
    EssentiallyCountableCategory
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory :=
  EssentiallyCountableCategory.of_full_of_faithful
    (coherentToModulesDerivedBoundedEquivalence X).inverse inferInstance

end Standard

/-- **`D^b_Coh(𝒪_X)` is essentially countable** for a scheme `X` of finite type over a countable
Noetherian ring, at any model of the derived category. -/
public theorem essentiallyCountable_boundedCoherent_of_finiteType {R : Type u} [CommRing R]
    [Countable R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [h : HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)] :
    EssentiallyCountableCategory
      (ObjectProperty.FullSubcategory
        (DerivedCategoryB.derivedCategoryBBounded
          (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent))) :=
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have := essentiallyCountable_coherentModules_of_finiteType f
  DerivedCategoryB.essentiallyCountable_derivedCategoryBBounded_of_model (coherentInModules X) h
    (HasDerivedCategory.standard _) (essentiallyCountable_boundedCoherent_standard X)

/-- **Stacks Project, Tag 0G0W.** Let `X` be a scheme of finite type over a countable Noetherian
ring `R`. Then the categories `D_perf(𝒪_X)` and `D^b_Coh(𝒪_X)` are countable: each has
countably many morphisms between any two objects and countably many isomorphism classes of
objects, which is `CategoryTheory.EssentiallyCountableCategory`, the notion of countability of
[Stacks, Section 0G0T]. Both are read as full subcategories of `D(𝒪_X)`, at any model of the
derived category.

As in the source: `X` is Noetherian, `D_perf(𝒪_X)` is a full subcategory of `D^b_Coh(𝒪_X)`
([Stacks, Tag 0FXU]), `D^b_Coh(𝒪_X) = D^b(Coh(𝒪_X))` ([Stacks, Tag 0FDB]), and the bounded
derived category of the countable abelian category `Coh(𝒪_X)`
(`AlgebraicGeometry.essentiallyCountable_coherentModules_of_finiteType`) is countable
([Stacks, Tag 0G0V]). -/
@[stacks 0G0W "D_perf(O_X) and D^b_Coh(O_X) are countable categories"]
public theorem essentiallyCountable_perfect_and_boundedCoherent_of_finiteType {R : Type u}
    [CommRing R] [Countable R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)] :
    EssentiallyCountableCategory
        (ObjectProperty.FullSubcategory
          (fun K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) =>
            RingedSpace.IsPerfect (X := X.toRingedSpace) K)) ∧
      EssentiallyCountableCategory
        (ObjectProperty.FullSubcategory
          (DerivedCategoryB.derivedCategoryBBounded
            (fun M : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace => M.IsCoherent))) :=
  have hbc := essentiallyCountable_boundedCoherent_of_finiteType f
  ⟨essentiallyCountable_isPerfect_of_finiteType f hbc, hbc⟩

end AlgebraicGeometry

end
