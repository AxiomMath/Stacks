module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom

/-!
# The composition isomorphism of Stacks 0D5S of a factorisation, read on complexes

The composition isomorphism `Stacks.DerivedPullback.schemeFactorIso` attached to a factorisation
`f ≫ g = k` of morphisms of schemes (Stacks 0D5S on the Zariski sites) is characterized by its
composite with the comparison of the derived pullback with degreewise pullback: on a complex `K`
it is the comparison along `g` pushed by `Lf^*`, then the comparison along `f`, then the
localization of the underived compositor of the inverse images of modules on ringed spaces
(`AlgebraicGeometry.Space.schemeFactorIso_hom_app_fac`).

## Main definitions

* `AlgebraicGeometry.Space.ringedSpaceFactorModulePullbackIso`,
  `AlgebraicGeometry.Space.schemeFactorModulePullbackIso`: the underived compositor
  `g^* ⋙ f^* ≅ k^*` of a factorisation.
* `AlgebraicGeometry.Space.schemeModulePullbackHomotopy`,
  `AlgebraicGeometry.Space.schemeDerivedPullbackComparison`: degreewise inverse image on
  homotopy categories and the comparison of the derived pullback with it.
* `AlgebraicGeometry.Space.schemeFactorMapHomotopyIso`: the underived compositor on homotopy
  categories.

## Main results

* `AlgebraicGeometry.Space.schemeFactorMapHomotopyIso_hom_app_quotient`: at the image of a
  complex, `schemeFactorMapHomotopyIso` is the underived compositor applied degreewise.
* `AlgebraicGeometry.Space.schemeFactorIso_hom_app_fac`: the characterization of
  `Stacks.DerivedPullback.schemeFactorIso` on complexes.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

section Zariski

variable {X Y Z : Scheme.{u}}

/-- The underived compositor `g^* ⋙ f^* ≅ k^*` of inverse images of modules attached to a
factorisation `f ≫ g = k` of morphisms of ringed spaces. -/
def ringedSpaceFactorModulePullbackIso {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ (k : X ⟶ Z), f ≫ g = k →
      (RingedSpaceModuleAdjunction.modulePullback g ⋙ RingedSpaceModuleAdjunction.modulePullback f ≅
        RingedSpaceModuleAdjunction.modulePullback k)
  | _, rfl => Stacks.DerivedPullback.Composition.modulePullbackComp f g

/-- The underived compositor `g^* ⋙ f^* ≅ k^*` of inverse images of modules along the morphisms
of ringed spaces underlying a factorisation `f ≫ g = k` of morphisms of schemes. -/
def schemeFactorModulePullbackIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom ⋙
        RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ≅
      RingedSpaceModuleAdjunction.modulePullback k.toLRSHom.toShHom :=
  ringedSpaceFactorModulePullbackIso f.toLRSHom.toShHom g.toLRSHom.toShHom k.toLRSHom.toShHom
    (congrArg (fun m : X ⟶ Z ↦ m.toLRSHom.toShHom) h)

/-- Degreewise inverse image of complexes of modules along the morphism of ringed spaces
underlying a morphism of schemes, on the unbounded homotopy categories. -/
abbrev schemeModulePullbackHomotopy (g : Y ⟶ Z) :=
  (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).mapHomotopyCategory
    (ComplexShape.up ℤ)

/-- The comparison `Lg^* ⟶ g^*` of the derived pullback along the morphism of ringed spaces
underlying a morphism of schemes with degreewise pullback, with its target spelled through
`AlgebraicGeometry.Space.schemeModulePullbackHomotopy`. -/
abbrev schemeDerivedPullbackComparison (g : Y ⟶ Z) :
    DerivedCategory.Qh ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom ⟶
      schemeModulePullbackHomotopy g ⋙ DerivedCategory.Qh :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g.toLRSHom.toShHom

/-- The derived pullback is a left derived functor for the comparison
`AlgebraicGeometry.Space.schemeDerivedPullbackComparison`. -/
instance isLeftDerivedFunctor_schemeDerivedPullbackComparison (g : Y ⟶ Z) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).IsLeftDerivedFunctor (schemeDerivedPullbackComparison g)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  inferInstanceAs ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).IsLeftDerivedFunctor
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))

/-- `AlgebraicGeometry.Space.schemeFactorModulePullbackIso` read on the unbounded homotopy
categories. -/
def schemeFactorMapHomotopyIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    schemeModulePullbackHomotopy g ⋙ schemeModulePullbackHomotopy f ≅
      schemeModulePullbackHomotopy k :=
  Functor.mapHomotopyCategoryCompIso (schemeFactorModulePullbackIso f g k h) (ComplexShape.up ℤ)

/-- At the image of a complex, `AlgebraicGeometry.Space.schemeFactorMapHomotopyIso` is the image
of the underived compositor applied degreewise. -/
theorem schemeFactorMapHomotopyIso_hom_app_quotient (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ℤ) :
    (schemeFactorMapHomotopyIso f g k h).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
        (schemeFactorModulePullbackIso f g k h).hom (ComplexShape.up ℤ)).app N) := by
  show (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
    ((Functor.mapHomologicalComplexCompIso (schemeFactorModulePullbackIso f g k h)
      (ComplexShape.up ℤ)).hom.app N) = _
  congr 1

/-- **The composition isomorphism of Stacks 0D5S of a factorisation, on complexes.** At the
image of a complex `K`, `Stacks.DerivedPullback.schemeFactorIso` followed by the comparison of
`Lk^*` with degreewise pullback is the comparison along `g` pushed by `Lf^*`, then the comparison
along `f`, then the localization of the underived compositor
`AlgebraicGeometry.Space.schemeFactorMapHomotopyIso`. -/
theorem schemeFactorIso_hom_app_fac (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.schemeFactorIso f g k h).hom.app (DerivedCategory.Qh.obj K) ≫
        (schemeDerivedPullbackComparison k).app K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).map ((schemeDerivedPullbackComparison g).app K) ≫
        (schemeDerivedPullbackComparison f).app ((schemeModulePullbackHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((schemeFactorMapHomotopyIso f g k h).hom.app K) := by
  subst h
  have e₂ : schemeFactorMapHomotopyIso f g (f ≫ g) rfl =
      Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f.toLRSHom.toShHom
        g.toLRSHom.toShHom :=
    rfl
  rw [e₂]
  exact Functor.leftDerived_fac_app _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      (f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom))
    (HomotopyCategory.quasiIso _ _) _ _ K

end Zariski

end AlgebraicGeometry.Space

end
