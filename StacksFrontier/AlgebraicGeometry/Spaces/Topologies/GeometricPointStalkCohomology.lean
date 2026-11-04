module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerivedOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Stalks of higher direct images of algebraic spaces at a geometric point, from base change

Let `T` be a big étale site of algebraic spaces over a scheme `S`, `f : Y ⟶ X` a morphism of its
objects and `x̄ : Spec Ω ⟶ X` a geometric point, with geometric fibre `Y_x̄ = Y ×_X Spec Ω` and
projections `g' : Y_x̄ ⟶ Y`, `f' : Y_x̄ ⟶ Spec Ω`. For an object `E` of the unbounded derived
category of abelian sheaves on the spaces-étale site of `Y` there is a chain of canonical
identifications

`(Hⁿ(Rf_* E))_x̄ ≅ (x̄⁻¹ Hⁿ(Rf_* E))_{can} ≅ Hⁿ(x̄⁻¹ Rf_* E)_{can}`
`  ≅ Hⁿ(Rf'_* (g')⁻¹ E)_{can} ≅ Hⁿ(RΓ(Y_x̄, (g')⁻¹ E))`

in which the third step is the base change map of Stacks 0DG3 for the cartesian square of the
geometric fibre and every other step holds for every morphism `f`. So as soon as that base change
map is invertible at `E`, the stalk at `x̄` of the `n`-th cohomology sheaf of `Rf_* E` is the
`n`-th étale hypercohomology of the fibre. This file proves exactly that; the two parts of
[Stacks, Tag 0DG4], for `f` proper, are in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkProperBaseChange`, after
Stacks 0DG3.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleAbelianAdjunction`: the adjunction
  `f⁻¹ ⊣ f_*` on abelian sheaves on the spaces-étale sites.
* `AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberIsoInverseImageSheafFiber`: the stalk at
  `x̄` of an abelian sheaf is the stalk of its inverse image along `x̄` at the canonical point of
  `Spec Ω` (Stacks 04K2, part (4)).
* `AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberCompPushforwardIsoGamma`: the stalk at the
  canonical point of `Spec Ω` of a direct image along `f' : Y' ⟶ Spec Ω` is global sections on
  `Y'`.
* `AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberMapDerivedCategoryDerivedPushforwardIso`:
  `(Rf'_* L)_{can} ≅ RΓ(Y', L)` on the whole unbounded derived category.
* `AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberHomologyDerivedPushforwardIsoOfIsIso`:
  **the stalk at `x̄` of `Hⁿ(Rf_* E)` is `Hⁿ(RΓ(Y_x̄, (g')⁻¹ E))`**, granted that the base change
  map of the geometric fibre square is invertible at `E`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.hasTorsionCohomology_singleFunctor`: a torsion abelian
  sheaf placed in degree `0` has torsion cohomology sheaves.

## Implementation notes

The stalk at a geometric point is the fibre functor of
`AlgebraicGeometry.Space.spacesEtaleSitePoint`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkSections`. Its exactness on
abelian sheaves is transported from the universe lift of the point, whose fibre functor is the
same (`CategoryTheory.GrothendieckTopology.Point.uliftSheafFiberIso`) and lives at the universe of
the coefficients, where filtered colimits of abelian groups are exact.

The derived base change map is `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleDerivedBaseChange`,
the map of Stacks 0DG3; its invertibility at `E` is the hypothesis of
`AlgebraicGeometry.BigEtaleSpaceSite.abelianSheafFiberHomologyDerivedPushforwardIsoOfIsIso`.

## References

* [Stacks Project, Tag 0DG4](https://stacks.math.columbia.edu/tag/0DG4)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DG2](https://stacks.math.columbia.edu/tag/0DG2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The slice-category smallness instances `CategoryTheory.small_over` and
-- `CategoryTheory.locallySmall_over` send the searches for the sheaf pullback's left Kan
-- extensions here into a typeclass timeout, so they are switched off in this file.
attribute [-instance] CategoryTheory.small_over CategoryTheory.locallySmall_over
open Stacks.Homology.DerivedSquare (totalRightDerived totalRightDerivedUnit)
open AlgebraicGeometry.Space

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive

/-! ### The abelian adjunction on the spaces-étale sites -/

/-- The adjunction `f⁻¹ ⊣ f_*` of abelian sheaves on the spaces-étale sites, for a morphism
`f : Y ⟶ X` of algebraic spaces of the big étale site: the adjunction of the morphism of topoi of
Stacks 0DF6 on commutative group objects, with the direct image identified with restriction of
abelian sheaves along base change. -/
def smallEtaleAbelianAdjunction {X Y : T.Spaces} (f : Y ⟶ X) :
    CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f) ⊣
      smallEtalePushforward T f :=
  letI := (smallEtaleMorphism T f).preservesFiniteLimits
  letI : PreservesLimitsOfSize.{0, 0} (smallEtaleMorphism T f).pushforward :=
    (smallEtaleMorphism T f).adj.rightAdjoint_preservesLimits
  letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
  (ProEtale.mapAbelianSheafAdjunction (smallEtaleMorphism T f).adj).ofNatIsoRight
    (ProEtale.mapAbelianSheafRestrictionIso.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor)

/-! ### Exactness of the stalk functors -/

section Exactness

variable {Z : T.Spaces} (z : Space.GeometricPoint T.fppfSite S T.fppf_mem Z.1)

/-- The stalk functor at a geometric point on abelian sheaves on the spaces-étale site is left
exact: it is the fibre functor of the universe lift of the point, a filtered colimit at the
universe of the coefficients. -/
instance preservesFiniteLimits_spacesEtaleSitePoint_sheafFiber :
    PreservesFiniteLimits ((spacesEtaleSitePoint z).sheafFiber (A := Ab.{u + 1})) :=
  preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft (sheafToPresheaf _ Ab.{u + 1})
      (GrothendieckTopology.Point.uliftPresheafFiberIso.{u + 1} (spacesEtaleSitePoint z)))

/-- The stalk functor at a geometric point on abelian sheaves on the spaces-étale site is right
exact, being a left adjoint. -/
instance preservesFiniteColimits_spacesEtaleSitePoint_sheafFiber :
    PreservesFiniteColimits ((spacesEtaleSitePoint z).sheafFiber (A := Ab.{u + 1})) :=
  inferInstance

/-- The stalk functor at a geometric point on abelian sheaves on the spaces-étale site is
additive, being left exact. -/
instance additive_spacesEtaleSitePoint_sheafFiber :
    ((spacesEtaleSitePoint z).sheafFiber (A := Ab.{u + 1})).Additive :=
  Functor.additive_of_preserves_binary_products _

end Exactness

/-! ### Torsion sheaves in degree zero -/

/-- A torsion abelian sheaf placed in degree `0` has torsion cohomology sheaves: its cohomology
sheaf in degree `0` is the sheaf, and the others vanish. -/
theorem hasTorsionCohomology_singleFunctor {Y : T.Spaces}
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) F) :
    HasTorsionCohomology T ((DerivedCategory.singleFunctor _ 0).obj F) := by
  intro i
  rcases lt_trichotomy i 0 with h | rfl | h
  · exact ObjectProperty.prop_of_isZero _ (DerivedCategory.isZero_of_isGE _ 0 i h)
  · exact ObjectProperty.prop_of_iso _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · exact ObjectProperty.prop_of_isZero _ (DerivedCategory.isZero_of_isLE _ 0 i h)

/-! ### The stalk at a geometric point through the field spectrum -/

/-- Global sections of abelian sheaves on a spaces-étale site form an additive functor: it is a
right adjoint, so it preserves binary products. -/
local instance additive_globalSections_spacesEtale (Z : T.Spaces) :
    (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) Ab.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

section FibreStalk

variable {X : T.Spaces} (x : Space.GeometricPoint T.fppfSite S T.fppf_mem X.1)

/-- **The stalk of an abelian sheaf at a geometric point `x̄` is the stalk of its inverse image
along `x̄` at the canonical point of the field spectrum** (Stacks 04K2, part (4), for abelian
sheaves on the spaces-étale sites). -/
def abelianSheafFiberIsoInverseImageSheafFiber :
    (spacesEtaleSitePoint x).sheafFiber (A := Ab.{u + 1}) ≅
      CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (geometricPointHom x)) ⋙
        (spacesEtaleSitePoint (geometricPointSpaceBase x)).sheafFiber :=
  letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem
    (geometricPointHom x)).isContinuous
  eqToIso (congrArg (fun z : Space.GeometricPoint T.fppfSite S T.fppf_mem X.1 ↦
      (spacesEtaleSitePoint z).sheafFiber (A := Ab.{u + 1}))
      (geometricPointMap_geometricPointSpaceBase x).symm) ≪≫
    (spacesEtaleSheafFiberInverseImageIso (geometricPointHom x) (geometricPointSpaceBase x)
      Ab.{u + 1}).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.sheafAdjunctionContinuous _ Ab.{u + 1} _ _).leftAdjointUniq
        (smallEtaleAbelianAdjunction T (geometricPointHom x))) _

variable {Y' : T.Spaces} (f' : Y' ⟶ geometricPointSpace x)

/-- **The stalk at the canonical point of the field spectrum of a direct image along
`f' : Y' ⟶ Spec Ω` is the group of global sections on `Y'`**: the stalk there is global sections
on `Spec Ω`, and global sections of a direct image are global sections upstairs. -/
def abelianSheafFiberCompPushforwardIsoGamma :
    smallEtalePushforward T f' ⋙
        (spacesEtaleSitePoint (geometricPointSpaceBase x)).sheafFiber (A := Ab.{u + 1}) ≅
      Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') Ab.{u + 1} :=
  Functor.isoWhiskerLeft _ (spacesEtaleBaseSheafFiberIsoGamma x Ab.{u + 1}) ≪≫
    spacesPushforwardGammaIso f' Ab.{u + 1}

/-- **`(Rf'_* L)_{can} ≅ RΓ(Y', L)` for `f' : Y' ⟶ Spec Ω`**, naturally in `L` on the unbounded
derived category: the stalk at the canonical point is exact, so it passes through the derived
direct image, and the composite of the stalk with `f'_*` is global sections on `Y'`. -/
def abelianSheafFiberMapDerivedCategoryDerivedPushforwardIso :
    totalRightDerived (smallEtalePushforward T f') ⋙
        ((spacesEtaleSitePoint (geometricPointSpaceBase x)).sheafFiber
          (A := Ab.{u + 1})).mapDerivedCategory ≅
      totalRightDerived (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
        Ab.{u + 1}) :=
  Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIsoOfIso
    (smallEtalePushforward T f')
    ((spacesEtaleSitePoint (geometricPointSpaceBase x)).sheafFiber (A := Ab.{u + 1}))
    (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') Ab.{u + 1})
    (abelianSheafFiberCompPushforwardIsoGamma T x f')

end FibreStalk

/-! ### Stalks of derived direct images at a geometric point -/

section Stalk

variable {X Y : T.Spaces} (f : Y ⟶ X) (x : Space.GeometricPoint T.fppfSite S T.fppf_mem X.1)

/-- **The stalk at a geometric point of a cohomology sheaf of a derived direct image, granted
base change.** Let `f : Y ⟶ X` be a morphism of algebraic spaces of the big étale site,
`x̄ : Spec Ω ⟶ X` a geometric point and `Y_x̄ = Y ×_X Spec Ω` the geometric fibre, with projection
`g' : Y_x̄ ⟶ Y`. If the base change map `x̄⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` of Stacks 0DG3 for the
cartesian square of the fibre is invertible at an object `E` of the unbounded derived category of
abelian sheaves on the spaces-étale site of `Y`, then `(Hⁿ(Rf_* E))_x̄ ≅ Hⁿ(RΓ(Y_x̄, (g')⁻¹ E))`
for every `n`. -/
def abelianSheafFiberHomologyDerivedPushforwardIsoOfIsIso
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}))
    (hbc : IsIso ((spacesEtaleDerivedBaseChange T f (geometricPointHom x)
      (pullback.fst f (geometricPointHom x)) (pullback.snd f (geometricPointHom x))
      (IsPullback.of_hasPullback f (geometricPointHom x))).app E)) (n : ℤ) :
    ((spacesEtaleSitePoint x).sheafFiber (A := Ab.{u + 1})).obj
      ((DerivedCategory.homologyFunctor
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) n).obj
          ((totalRightDerived (smallEtalePushforward T f)).obj E)) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((totalRightDerived (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
          (pullback f (geometricPointHom x))) Ab.{u + 1})).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (smallEtaleMorphism T (pullback.fst f (geometricPointHom x)))).mapDerivedCategory.obj
            E)) :=
  let Sb := (spacesEtaleSitePoint (geometricPointSpaceBase x)).sheafFiber (A := Ab.{u + 1})
  (abelianSheafFiberIsoInverseImageSheafFiber T x).app _ ≪≫
    Sb.mapIso (((CategoryTheory.Sites.abelianInverseImage
      (smallEtaleMorphism T (geometricPointHom x))).mapDerivedCategoryHomologyIso n).app
        ((totalRightDerived (smallEtalePushforward T f)).obj E)).symm ≪≫
    Sb.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso (asIso
      ((spacesEtaleDerivedBaseChange T f (geometricPointHom x)
        (pullback.fst f (geometricPointHom x)) (pullback.snd f (geometricPointHom x))
        (IsPullback.of_hasPullback f (geometricPointHom x))).app E))) ≪≫
    ((Sb.mapDerivedCategoryHomologyIso n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((abelianSheafFiberMapDerivedCategoryDerivedPushforwardIso T x
        (pullback.snd f (geometricPointHom x))).app _)

end Stalk

end AlgebraicGeometry.BigEtaleSpaceSite

end
