module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingBridge
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat

/-!
# The derived stalk of a derived associated sheaf is derived base change along the germ

Let `A` be a commutative ring and `y` a point of `Spec A`. Degreewise sheafification `M ↦ M̃` is
exact, and so is the stalk at `y`, so their composite acts on unbounded derived categories
degreewise. This file identifies that action with derived base change along the germ map
`A ⟶ 𝒪_{Spec A, y}`:

`(M^•)~_y  ≅  M^• ⊗ᴸ_A 𝒪_{Spec A, y}`.

Over the abelian categories this is Stacks 01HV, read over the local ring `𝒪_{Spec A, y}`: the
stalk at `y` of `M̃` is `𝒪_{Spec A, y} ⊗_A M`, naturally in `M`.

## Main definitions

* `AlgebraicGeometry.specGermRingHom`: the germ map `A ⟶ 𝒪_{Spec A, y}`, namely the inverse of
  the global sections isomorphism of Stacks 01HR followed by the germ at `y`.

## Main results

* `ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv`: restriction of scalars along a ring
  isomorphism is extension of scalars along its inverse.
* `AlgebraicGeometry.ringCatStalkRingEquiv_comp_specStalkRingHom`: the two germ maps — into the
  `RingCat`-valued stalk and into the local ring — agree through
  `AlgebraicGeometry.ringCatStalkRingEquiv`.
* `AlgebraicGeometry.tildeModulesStalkIso`: the stalk at `y` of `M̃` is `𝒪_{Spec A, y} ⊗_A M`,
  naturally in `M`.
* `AlgebraicGeometry.derivedTildeStalkIso`: derived sheafification followed by the derived stalk at
  `y` is derived base change along the germ map.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u w

namespace ModuleCat

/-- Restriction of scalars along the inverse of a ring isomorphism `e` is extension of scalars
along `e`. -/
def restrictScalarsIsoExtendScalarsOfRingEquiv {T O : Type u} [CommRing T] [CommRing O]
    (e : T ≃+* O) :
    ModuleCat.restrictScalars.{u, u, u} e.symm.toRingHom ≅
      ModuleCat.extendScalars.{u, u, u} e.toRingHom :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} e.symm).toAdjunction.leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} e.toRingHom)

/-- The isomorphism between the extension-of-scalars functors along two equal ring maps. -/
def extendScalarsFunctorCongr {R S : Type u} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : f = g) :
    ModuleCat.extendScalars.{u, u, u} f ≅ ModuleCat.extendScalars.{u, u, u} g :=
  eqToIso (congrArg ModuleCat.extendScalars.{u, u, u} h)

end ModuleCat

namespace AlgebraicGeometry

variable (A : CommRingCat.{u}) (y : (Spec A).carrier)

/-- The germ map `A ⟶ 𝒪_{Spec A, y}`: the inverse of the global sections isomorphism of Stacks 01HR
followed by the germ at `y` of the structure sheaf, read over the local ring. -/
def specGermRingHom : A →+* ToType ((Spec A).presheaf.stalk y) :=
  (((Spec A).presheaf.germ ⊤ y trivial).hom).comp (Scheme.ΓSpecIso A).inv.hom

/-- The germ into the `RingCat`-valued stalk of the sheaf of rings, followed by the identification
`ringCatStalkRingEquiv` of that stalk with the local ring, is the germ into the local ring. -/
theorem ringCatStalkRingEquiv_comp_specStalkRingHom :
    letI := Stacks.RingedSpace.structureStalkCommRing (Spec A).toRingedSpace y
    ((ringCatStalkRingEquiv y).toRingHom).comp (Stacks.TildeStalk.specStalkRingHom A y) =
      specGermRingHom A y := by
  ext a
  exact SemilinearStalk.commStalkRingEquiv_germ (Spec A).presheaf y ⊤ trivial _

/-- Extension of scalars along the germ into the `RingCat`-valued stalk, followed by restriction of
scalars along `ringCatStalkRingEquiv`, is extension of scalars along the germ into the local ring.
-/
def tildeStalkBaseChangeIso :
    letI := Stacks.RingedSpace.structureStalkCommRing (Spec A).toRingedSpace y
    Stacks.TildeStalk.tildeStalkBaseChange A y ⋙
        ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv y).symm.toRingHom ≅
      ModuleCat.extendScalars.{u, u, u} (specGermRingHom A y) :=
  letI := Stacks.RingedSpace.structureStalkCommRing (Spec A).toRingedSpace y
  Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv.{u}
      (ringCatStalkRingEquiv y)) ≪≫
    (ModuleCat.extendScalarsComp.{u, u} (Stacks.TildeStalk.specStalkRingHom A y)
      (ringCatStalkRingEquiv y).toRingHom).symm ≪≫
    ModuleCat.extendScalarsFunctorCongr.{u} (ringCatStalkRingEquiv_comp_specStalkRingHom A y)

/-- The stalk at `y` of the sheaf associated to an `A`-module is the base change of that module
along the germ map `A ⟶ 𝒪_{Spec A, y}`, naturally in the module:

`~ ⋙ (-)_y ≅ 𝒪_{Spec A, y} ⊗_A -`. -/
def tildeModulesStalkIso :
    tilde.functor A ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A) y ≅
      ModuleCat.extendScalars.{u, u, u} (specGermRingHom A y) :=
  Functor.isoWhiskerLeft (tilde.functor A)
      (AlgebraicGeometry.restrictScalarsStalkFunctorIso (X := Spec A) y).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.TildeStalk.tildeStalkFunctorIso A y) _ ≪≫
    tildeStalkBaseChangeIso A y

/-- Degreewise sheafification followed by the derived stalk at `y`, both read on unbounded derived
categories, is the total derived extension of scalars along the germ map `A ⟶ 𝒪_{Spec A, y}`:

`(M^•)~_y ≅ M^• ⊗ᴸ_A 𝒪_{Spec A, y}`. -/
def derivedTildeStalkIso [HasDerivedCategory.{w} (Spec A).Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} ((Spec A).presheaf.stalk y))] :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom A y)).functor ≅
      (tilde.functor A).mapDerivedCategory ⋙ derivedStalkFunctor y :=
  RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory
      (specGermRingHom A y) _ (tildeModulesStalkIso A y) ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso (tilde.functor A)
      (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A) y)).symm

end AlgebraicGeometry

end
