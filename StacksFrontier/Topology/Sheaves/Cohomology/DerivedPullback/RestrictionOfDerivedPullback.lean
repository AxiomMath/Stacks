module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.RingedSpace.RestrictMorphism

/-!
# Derived pullback commutes with restriction to an open subspace

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `V ⊆ Y` be open. Write
`f|_{f⁻¹V} : (f⁻¹V, 𝒪_X|_{f⁻¹V}) ⟶ (V, 𝒪_Y|_V)` for the restriction of `f`. Then

`(Lf^* M)|_{f⁻¹V} ≅ L(f|_{f⁻¹V})^* (M|_V)`,

naturally in `M`. This is the derived form of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesPullbackCompIso`, and it is
the step an argument that replaces `Y` by an open subspace needs in order to carry a derived
pullback along.

Nothing is proved about pullback itself. Restriction to an open subspace *is* pullback along the
open immersion of that subspace, already on derived categories
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`), so both sides are
derived pullbacks along a composite of two morphisms of ringed spaces; the composition formula of
[Stacks, Tag 0D5S] identifies each with the derived pullback along the composite, and the two
composites are the same morphism, by
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion`.

## Main definitions

* `Stacks.Cohomology.DerivedRestrictionPullback.derivedPullbackRestrictCompIso`: the
  identification with both restrictions written as derived pullbacks along the two open
  immersions, which is the form the composition formula produces.
* `Stacks.Cohomology.DerivedRestrictionPullback.derivedRestrictPullbackIso`: the same with both
  restrictions written as `Stacks.Cohomology.HigherDirectImage.moduleRestriction` on derived
  categories, which is the form a consumer restricting a complex to an open has.

## Main results

* `Stacks.Cohomology.DerivedRestrictionPullback.restrictHom_eq_restrictedMorphism`: the two
  spellings of the restriction of a morphism of ringed spaces to an open subspace of its target
  that this library carries are *the same morphism*, by `rfl`.

## Implementation notes

Both isomorphisms are isomorphisms of functors, so naturality in the complex is automatic, and
neither carries a hypothesis: the composition formula of [Stacks, Tag 0D5S] is unconditional for
the canonical derived pullbacks, as
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` records.

*Why the existence instances below are declared.* Writing `derivedPullback g` needs
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy` at
`g`, and instance search does not find it when the source of `g` is an open subspace written as
`Stacks.Cohomology.HigherDirectImage.restrictToOpen`: that spelling and
`AlgebraicGeometry.SheafedSpace.restrict` reach the derived category of modules on the subspace
by different routes, and the universe of the derived category is left unsolved by the failed
match. Applied to the morphism explicitly the general instance elaborates, so the two instances
below are it, at the shapes the definitions here present search with. The binder they discharge
is `Prop`-valued and hence proof-irrelevant, so seating them does not produce a second derived
pullback functor; this is the precedent of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.pullbackRestrictedMorphism_additive`.

Restriction on derived categories is
`(Stacks.Cohomology.HigherDirectImage.moduleRestriction X U).mapDerivedCategory` rather than a
left derived functor: restriction is exact, and
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso` is exactly the
identification of the derived pullback along the open immersion with it.

## References

* [Stacks Project, Lemma 20.28.5 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Lemma 26.4.5 (Tag 01E5)](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Lemma 20.28.2 (Tag 06YJ)](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.HigherDirectImage
open Stacks.DerivedPullback.Composition

namespace Stacks.Cohomology.DerivedRestrictionPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The two spellings of a restricted morphism -/

/-- **The two restrictions of a morphism of ringed spaces to an open subspace of its target that
this library carries are the same morphism.**

`AlgebraicGeometry.RingedSpace.restrictHom` writes the map of structure sheaves as a composite of
whiskerings and `Stacks.Cohomology.HigherDirectImage.restrictedMorphism` writes out its
components; the components of the first reduce to the components of the second, and the two
identifications of opens of the source that they are built from are two proofs of one equation,
so the two morphisms are definitionally equal.

In particular the commuting square `j_{f⁻¹V} ≫ f = f|_{f⁻¹V} ≫ j_V`, which the implementation
notes of `StacksFrontier/Topology/Sheaves/RingedSpace/RestrictMorphism.lean` record as not being
available there, is available for `AlgebraicGeometry.RingedSpace.restrictHom` as well: it is
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion` read along
this equality. -/
theorem restrictHom_eq_restrictedMorphism {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y) :
    AlgebraicGeometry.RingedSpace.restrictHom f V = restrictedMorphism f V :=
  rfl

/-! ### The existence of the derived pullbacks that occur below -/

/-- **[Stacks, Tag 06YJ] out of an open subspace**, seated so that the derived pullbacks below
can be written down; see the implementation notes of this file.

The source of the morphism is an open subspace in the
`Stacks.Cohomology.HigherDirectImage.restrictToOpen` spelling, which is the shape every derived
pullback in this file has: the open immersion `j_U : X|_U ⟶ X`, the restricted morphism
`f|_{f⁻¹V} : X|_{f⁻¹V} ⟶ Y|_V`, and the two composites out of `X|_{f⁻¹V}`. -/
instance hasLeftDerivedFunctor_outOfRestrictToOpen {X Y : RingedSpace.{u, u}} (W : Opens X)
    (m : restrictToOpen X W ⟶ Y) :
    (pullbackOnHomotopy m).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy m

/-- **[Stacks, Tag 06YJ] at a restricted morphism.** The same instance as
`hasLeftDerivedFunctor_outOfRestrictToOpen`, stated at the restricted morphism itself: with the
target an open subspace as well, the universe of its derived category of modules is fixed by the
statement rather than left to the match, and search needs the goal's shape. -/
instance hasLeftDerivedFunctor_restrictedMorphism {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y) :
    (pullbackOnHomotopy (restrictedMorphism f V)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V)))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (restrictedMorphism f V)

/-! ### Derived pullback and restriction to an open -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- **Derived pullback commutes with restriction to an open subspace**, with both restrictions
written as derived pullbacks along the open immersions `j_{f⁻¹V}` and `j_V`:

`Lf^* ⋙ Lj_{f⁻¹V}^* ≅ Lj_V^* ⋙ L(f|_{f⁻¹V})^*`.

Both sides are identified by [Stacks, Tag 0D5S] with the derived pullback along a composite, and
the two composites `j_{f⁻¹V} ≫ f` and `f|_{f⁻¹V} ≫ j_V` are equal. -/
def derivedPullbackRestrictCompIso :
    derivedPullback f ⋙ derivedPullback (openSubspaceInclusion X (preimageOpen f V)) ≅
      derivedPullback (openSubspaceInclusion Y V) ⋙
        derivedPullback (restrictedMorphism f V) :=
  derivedPullbackCompIsoCanonical (openSubspaceInclusion X (preimageOpen f V)) f ≪≫
    eqToIso (congrArg (fun m : restrictToOpen X (preimageOpen f V) ⟶ Y => derivedPullback m)
      (restrictedMorphism_comp_openSubspaceInclusion f V)) ≪≫
    (derivedPullbackCompIsoCanonical (restrictedMorphism f V)
      (openSubspaceInclusion Y V)).symm

/-- **Derived pullback commutes with restriction to an open subspace.**

`(Lf^* M)|_{f⁻¹V} ≅ L(f|_{f⁻¹V})^* (M|_V)`, naturally in `M`.

This is `Stacks.Cohomology.DerivedRestrictionPullback.derivedPullbackRestrictCompIso` with the
derived pullbacks along the two open immersions rewritten as ordinary restriction of modules,
which is what they are by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`. -/
def derivedRestrictPullbackIso :
    derivedPullback f ⋙ (moduleRestriction X (preimageOpen f V)).mapDerivedCategory ≅
      (moduleRestriction Y V).mapDerivedCategory ⋙
        derivedPullback (restrictedMorphism f V) :=
  Functor.isoWhiskerLeft (derivedPullback f)
      (derivedPullbackModuleRestrictionIso X (preimageOpen f V)).symm ≪≫
    derivedPullbackRestrictCompIso f V ≪≫
    Functor.isoWhiskerRight (derivedPullbackModuleRestrictionIso Y V)
      (derivedPullback (restrictedMorphism f V))

end Stacks.Cohomology.DerivedRestrictionPullback

end
