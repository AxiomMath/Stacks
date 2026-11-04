module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism

/-!
# The two spellings of the stalk of a sheaf of modules on a scheme

The stalk at a point `x` of a scheme `X` of a sheaf of `𝒪_X`-modules is taken in two
different spellings, and they land in two different categories of modules:

* `AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x` takes modules over the
  `RingCat`-valued stalk of the sheaf of rings.  This is the spelling the stalkwise criterion
  for invertibility in the derived category
  (`Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso`) and the computation of
  the derived stalk of a pushforward along a closed immersion
  (`Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIso`) are stated in.
* `Stacks.ModuleSkyscraper.modulesStalkFunctor X x` takes modules over the local ring
  `𝒪_{X,x}`, the ring `AlgebraicGeometry.Scheme.Hom.stalkMap` and `ModuleCat.extendScalars` are
  stated over.  This is the spelling the derived stalk of a derived pullback
  (`AlgebraicGeometry.derivedPullbackStalkIso`) and everything about Tor independence are
  stated in.

The two differ by restriction of scalars along the ring isomorphism
`AlgebraicGeometry.ringCatStalkRingEquiv`.  This file records that as an isomorphism of
*functors*, and derives from it that the two derived stalks of a morphism of the derived
category of `𝒪_X`-modules are invertible together.

## Main definitions

* `AlgebraicGeometry.restrictScalarsStalkFunctorIso`: the comparison of the two stalk functors,
  as an isomorphism of functors.

## Main results

* `AlgebraicGeometry.isEquivalence_restrictScalarsStalk`: restriction of scalars along
  `AlgebraicGeometry.ringCatStalkRingEquiv` is an equivalence of categories, being restriction
  along a ring isomorphism.
* `AlgebraicGeometry.isIso_stalkFunctor_map_iff`: a morphism of sheaves of `𝒪_X`-modules has
  invertible stalk at `x` in one spelling exactly when it has in the other.
* `AlgebraicGeometry.isIso_derivedStalkFunctor_map_iff`: a morphism of the derived category of
  `𝒪_X`-modules has invertible derived stalk at `x` in one spelling exactly when it has in the
  other.  This is the form the two halves of Stacks 0E23 have to be joined in.

## Implementation notes

*Which bridge this is, and why it is not a duplicate.*  There is already a one-directional
bridge for zero objects,
`Stacks.Cohomology.ClosedImmersionBaseChange.isZero_derivedStalkFunctor_of_isZero`, which
crosses from the `RingCat` spelling to the local-ring spelling degreewise through
`AlgebraicGeometry.restrictScalarsStalkObjIso`.  That one is about a single object and in one
direction only.  Recorded here is the comparison of the *functors*, from which the object-level
statements follow in both directions, and the resulting statement about a *morphism*, which is
what a claim about a base change map needs: the off-image half of Stacks 0E23
(`Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedStalk_derivedBaseChangeMap`) is
stated in the local-ring spelling, while the stalkwise criterion that has to consume it is
stated in the `RingCat` one.  The existing object-level lemma is kept exactly as it stands; it
is a candidate for being re-proved from the ingredients here rather than deleted.

*Why restriction of scalars here is an equivalence.*  `AlgebraicGeometry.ringCatStalkRingEquiv`
is a ring *isomorphism*, so `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` applies.  That
single fact supplies additivity, exactness and reflection of isomorphisms, so none of them has
to be proved by hand from the fact that restriction of scalars leaves the underlying abelian
group alone.

*Why the derived statement is about a morphism and not an isomorphism of functors.*  The
derived comparison of the two derived stalk *functors* would be this underived comparison
carried along `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso`, after
splitting a composite with `...mapDerivedCategoryCompIso`.  Those two helpers ask for
`CategoryTheory.Functor.Additive` of their arguments relative to the `Preadditive` structure
their own `Abelian` instance binder supplies, and that demand is not met here even though each
additivity instance is found on its own: `X.Modules` and
`SheafOfModules X.ringCatSheaf` are one category in two spellings carrying two `Abelian`
instances, and `Functor.Additive` of the stalk functor is available for one spelling, of
`Stacks.ModuleSkyscraper.modulesStalkFunctor` for the other.  The route taken instead asks for
no instance on a composite at all: invertibility in a derived category is tested degreewise on
homology, which `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff` supplies on the
local-ring side and the already-constructed
`AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso` on the `RingCat` side, and in each
degree the two stalks are compared by `isIso_stalkFunctor_map_iff`.

*Why the underived comparison of morphisms goes through abelian groups.*  Both stalks of a
morphism have the same underlying map of abelian groups, and `forget₂` to `AddCommGrpCat`
reflects isomorphisms, so after reflecting both sides the two statements are literally the same
one.  Reflecting through restriction of scalars instead would be the same argument one step
later and runs into the instance-spelling obstruction above.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} (x : X)

/-! ### Restriction of scalars along the comparison of stalk rings -/

/-- **Restriction of scalars along `ringCatStalkRingEquiv` is an equivalence of categories.**
It is restriction of scalars along a ring isomorphism, so
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv` applies. -/
instance isEquivalence_restrictScalarsStalk :
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv x).symm.toRingHom).IsEquivalence :=
  inferInstanceAs
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ringCatStalkRingEquiv x).symm).functor.IsEquivalence)

/-- Restriction of scalars along `ringCatStalkRingEquiv` is additive.  It is an equivalence, so
it preserves binary coproducts, and a functor between additive categories that preserves binary
biproducts is additive. -/
instance additive_restrictScalarsStalk :
    (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom)
  Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction of scalars along `ringCatStalkRingEquiv` reflects isomorphisms: it is the
functor of an equivalence, hence fully faithful. -/
instance reflectsIsomorphisms_restrictScalarsStalk :
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv x).symm.toRingHom).ReflectsIsomorphisms :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ringCatStalkRingEquiv x).symm).fullyFaithfulFunctor.reflectsIsomorphisms

/-! ### The comparison of the two stalk functors -/

/-- **The two stalk functors differ by restriction of scalars.**  Taking the stalk at `x` over
the `RingCat`-valued stalk of the sheaf of rings and then restricting scalars along
`AlgebraicGeometry.ringCatStalkRingEquiv` is taking the stalk at `x` over the local ring
`𝒪_{X,x}`.

The components are `AlgebraicGeometry.restrictScalarsStalkObjIso`, which is the identity on
underlying abelian groups.  Naturality is therefore the statement that the two stalk maps of a
morphism of sheaves of modules have the same underlying map of abelian groups, and they do by
construction: both are `TopCat.Presheaf.stalkFunctor AddCommGrpCat x` applied to the underlying
morphism of presheaves of abelian groups, so naturality holds by `rfl`. -/
def restrictScalarsStalkFunctorIso :
    AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
        ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x :=
  NatIso.ofComponents (restrictScalarsStalkObjIso x) (fun _ => rfl)

/-- The two stalks of a morphism of sheaves of modules are invertible together: the stalk over
the local ring `𝒪_{X,x}` is an isomorphism exactly when the stalk over the `RingCat`-valued
stalk of the sheaf of rings is.

This is `restrictScalarsStalkFunctorIso` together with the fact that restriction of scalars
along a ring isomorphism, being an equivalence, reflects isomorphisms. -/
theorem isIso_stalkFunctor_map_iff {M N : X.Modules} (φ : M ⟶ N) :
    IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map φ) ↔
      IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map φ) := by
  rw [← isIso_iff_of_reflects_iso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map φ)
      (forget₂ (ModuleCat.{u} (ToType (X.presheaf.stalk x))) AddCommGrpCat.{u}),
    ← isIso_iff_of_reflects_iso ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        X.ringCatSheaf x).map φ)
      (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x))
        AddCommGrpCat.{u})]
  exact Iff.rfl

/-! ### The derived consequence -/

/-- **The two derived stalks of a morphism are invertible together.**  For a morphism `φ` of the
unbounded derived category of sheaves of `𝒪_X`-modules, the derived stalk of `φ` at `x` taken
over the local ring `𝒪_{X,x}` is an isomorphism exactly when the derived stalk taken over the
`RingCat`-valued stalk of the sheaf of rings is.

Invertibility in a derived category is tested degreewise on homology, and in each degree the
two derived stalks are the two stalks of the map of cohomology sheaves — by
`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff` on the local-ring side and by
`AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso` on the `RingCat` side — so
`isIso_stalkFunctor_map_iff` compares them. -/
theorem isIso_derivedStalkFunctor_map_iff
    {E F : DerivedCategory X.Modules} (φ : E ⟶ F) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor x).map φ) ↔
      IsIso ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x).map φ) :=
  (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).isIso_mapDerivedCategory_map_iff φ).trans
      (forall_congr' fun n =>
        (isIso_stalkFunctor_map_iff x
            ((DerivedCategory.homologyFunctor X.Modules n).map φ)).trans
          (NatIso.isIso_map_iff
            (AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso
              X.ringCatSheaf x n) φ).symm)).trans
    (DerivedCategory.isIso_iff _ ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
      X.ringCatSheaf x).map φ)).symm

end AlgebraicGeometry

end

end
