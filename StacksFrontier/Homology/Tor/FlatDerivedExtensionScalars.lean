module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Derived extension of scalars when extension of scalars is exact

Let `f : R → S` be a homomorphism of commutative rings and let `G : Mod R ⥤ Mod S` be an *exact*
functor isomorphic to `ModuleCat.extendScalars f`. Then `G` acts on unbounded derived categories
degreewise, by `CategoryTheory.Functor.mapDerivedCategory`, and that degreewise action already
inverts the quasi-isomorphisms; so it is a total left derived functor of degreewise extension of
scalars, and therefore canonically isomorphic to
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars f`:

`- ⊗ᴸ_R S  ≅  G`.

The case `G = ModuleCat.extendScalars f` itself applies exactly when `f` is flat, and is recorded
separately. The general shape is what consumers want: a functor arising geometrically — the stalk
of an associated sheaf, say — is presented as exact and only *isomorphic* to extension of scalars,
never equal to it, and forcing it through the flat case first would need the isomorphism anyway.

The model of the derived category is free: the statements take `[HasDerivedCategory.{w} ·]` for
the two module categories as binders rather than fixing `HasDerivedCategory.standard`. A
statement proved for one model says nothing about another, the two derived categories being
merely equivalent and not equal, and both the locally small model with morphisms in `Type u` and
the standard model with morphisms in `Type (u + 1)` are wanted by the consumers of this file.

## Main results

* `RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory`: an exact
  functor isomorphic to extension of scalars is, on derived categories, derived extension of
  scalars.
* `RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors`:
  the isomorphism is the one compatible with the two comparisons with degreewise extension of
  scalars, which is what pins it down.
* `RingTheory.TorIndependence.flatDerivedExtensionScalarsIso`: the flat case, `G` being extension
  of scalars itself.

## Implementation notes

Both functors are total left derived functors of degreewise extension of scalars followed by
localization: the derived one by `TotalDerivedExtensionScalars.isLeftDerived`, the degreewise one
because an exact functor inverts quasi-isomorphisms, which is
`CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts` applied to
`CategoryTheory.Functor.mapDerivedCategoryFactors`. So the isomorphism is the uniqueness of a
left derived functor, `CategoryTheory.Functor.leftDerivedNatIso` at the given isomorphism read
degreewise, and the compatibility statement is
`CategoryTheory.Functor.leftDerivedNatTrans_app`.

This is the unbounded, model-free form of the step that
`StacksFrontier.Homology.Tor.FlatBaseChangeHomology` performs for its own purposes with a `private`
declaration fixed at `HasDerivedCategory.standard`, and it is the functor-level companion of
`StacksDraft.DerivedHom.HomModuleBaseChange.isIso_comparison_of_flat`, which says instead that
the comparison of *any* left derived functor of extension of scalars along a flat map is
invertible.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace RingTheory.TorIndependence

variable {R S : Type u} [CommRing R] [CommRing S]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

section

variable (f : R →+* S) (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (e : G ≅ ModuleCat.extendScalars.{u, u, u} f)

/-- The degreewise comparison transported along `e`: degreewise extension of scalars followed by
localization is `G` applied degreewise followed by localization. -/
def mapHomologicalComplexIsoOfExtendScalars :
    CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u} f ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e.symm (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- The degreewise action of an exact functor on derived categories is a total left derived
functor of the degreewise functor followed by localization: it inverts the quasi-isomorphisms.

This is not made an instance: its conclusion is keyed on `IsLeftDerivedFunctor` for an arbitrary
exact functor of module categories, so as a global instance it would be attempted on every
unrelated search for a left derived functor. It is seated with `haveI` where it is wanted. -/
theorem isLeftDerivedFunctor_mapDerivedCategory :
    G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    G.mapDerivedCategory G.mapDerivedCategoryFactors

/-- **An exact functor isomorphic to extension of scalars is derived extension of scalars.**
For `G : Mod R ⥤ Mod S` exact and `e : G ≅ ModuleCat.extendScalars f`, the degreewise action of
`G` on unbounded derived categories is the total derived extension-of-scalars functor along `f`.

Both sides are total left derived functors of degreewise extension of scalars followed by
localization — the right-hand side because an exact functor inverts quasi-isomorphisms — so this
is the uniqueness of a left derived functor. -/
def totalDerivedExtensionScalarsIsoMapDerivedCategory :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor ≅
      G.mapDerivedCategory :=
  haveI := isLeftDerivedFunctor_mapDerivedCategory (R := R) (S := S) G
  Functor.leftDerivedNatIso
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor
    G.mapDerivedCategory
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).comparison
    G.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (mapHomologicalComplexIsoOfExtendScalars f G e)

/-- **The comparison is the one compatible with the two factorizations.** At a cochain complex,
`totalDerivedExtensionScalarsIsoMapDerivedCategory` followed by the comparison of the degreewise
functor with the localization is the comparison of the derived functor with degreewise extension
of scalars, read through `e`. This is what pins the isomorphism down. -/
theorem totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalarsIsoMapDerivedCategory f G e).hom.app
          (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          f).comparison.app P ≫
        (mapHomologicalComplexIsoOfExtendScalars f G e).hom.app P :=
  have := isLeftDerivedFunctor_mapDerivedCategory (R := R) (S := S) G
  Functor.leftDerivedNatTrans_app
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor
    G.mapDerivedCategory
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).comparison
    G.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (mapHomologicalComplexIsoOfExtendScalars f G e).hom P

end

/-- **Derived extension of scalars along a flat ring map is the degreewise functor.** For
`f : R → S` flat, extension of scalars is exact, so its degreewise action on derived categories
already inverts quasi-isomorphisms and is therefore its own total left derived functor; it is
hence isomorphic to `totalDerivedExtensionScalars f`. -/
def flatDerivedExtensionScalarsIso (f : R →+* S) (hf : f.Flat) :
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).functor ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory :=
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  totalDerivedExtensionScalarsIsoMapDerivedCategory f
    (ModuleCat.extendScalars.{u, u, u} f) (Iso.refl _)

end RingTheory.TorIndependence

end
