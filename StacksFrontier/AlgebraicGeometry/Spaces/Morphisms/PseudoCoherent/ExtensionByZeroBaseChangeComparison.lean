module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryOfNatIsoRightUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentLocalization
public import StacksFrontier.CategoryTheory.Adjunction.MateComparison

/-!
# The derived base change map for extension by zero, computed on complexes

Let

```
T' --u'--> T
|t'        |t
v          v
U  --u-->  Z
```

be a commutative square of algebraic spaces with `u` and `u'` étale.  The base change map
`u'_!(Lt'^*A) ⟶ Lt^*(u_!A)` of
`AlgebraicGeometry.Space.DerivedPullbackComposition.extensionByZeroBaseChange` is the mate, under
`u_! ⊣ Lu^*` and `u'_! ⊣ Lu'^*`, of the identification `Lu^* ⋙ Lt'^* ≅ Lt^* ⋙ Lu'^*` of the
square.  For the canonical pseudofunctoriality of derived pullback
(`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`) this file computes it at the image
of a complex: read through the comparison maps `Lf^* ⟶ f^*`, it is the *degreewise* base change
map of the square, the mate under the adjunctions of degreewise extension by zero of the degreewise
identification `u^* ⋙ t'^* ≅ t^* ⋙ u'^*` on homotopy categories.

## Main definitions

* `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso`: the degreewise
  identification `g^* ⋙ f^* ≅ k^*` attached to a factorisation `f ≫ g = k`.
* `AlgebraicGeometry.Space.etaleLowerShriekHomotopyAdjunction`: degreewise extension by zero is
  left adjoint to degreewise pullback along an étale morphism, on homotopy categories.
* `AlgebraicGeometry.Space.extensionByZeroBaseChangeHomotopy`: the degreewise base change map
  `t'^* ⋙ u'_! ⟶ u_! ⋙ t^*` on homotopy categories.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp`: the identification
  `Lg^* ⋙ Lf^* ≅ Lk^*` read through the comparison maps is the degreewise one.
* `AlgebraicGeometry.Space.squareIso_canonical_hom_app_comp`: so is the identification of a
  square.
* `AlgebraicGeometry.Space.etaleDerivedLowerShriekAdjunction_unit_app_comp`: the unit of
  `u_! ⊣ Lu^*` read through the comparison maps is the degreewise one.
* `AlgebraicGeometry.Space.extensionByZeroBaseChange_canonical_app_comp`: the derived base change
  map read through the comparison maps is the degreewise one.
* `AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app`: the derived base change
  map is invertible at a complex at which the two comparison maps involved and the degreewise base
  change map are.

## Implementation notes

The derived categories of the modules of the small étale topoi enter through two routes, the
derived pullback of `Stacks.Cohomology.DerivedPullbackOfToposHom` and the localization functor
`DerivedCategory.Qh`, and the second reads the preadditive structure of the modules off their
abelian structure.  The local instances below fix the abelian structure to be
`SheafOfModules.instAbelian` and the preadditive structure to be the one it induces, so that every
statement here spells these instances the way `DerivedCategory.Qh` does; the comparison of the
derived pullback with degreewise pullback (`smallEtaleDerivedModulePullbackComparison'`) and
degreewise pullback itself (`smallEtaleModulePullbackMapHomotopy`) are restated as abbreviations
whose types are elaborated with them.  The calculus is done once, for abstract functors, in
`CategoryTheory.Adjunction.mateEquiv_symm_app_comp_of_eq`,
`CategoryTheory.Iso.hom_inv_app_comp_eq_of_comparisons` and
`CategoryTheory.mapDerivedCategoryAdjunction_ofNatIsoRight_unit_app_Qh`, and instantiated here with
definitions identified with the abstract data by `rfl` at the level of natural transformations and
adjunctions.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

namespace AlgebraicGeometry.Space

universe u

/- The derived pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` is stated for
the standard model of the derived category, so the declarations below are stated at it too; the
abelian and preadditive structures of the modules are fixed as explained in the implementation
notes. -/
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The identifications of factorisations on homotopy categories -/

/-- Degreewise pullback of complexes of modules along a morphism of algebraic spaces, on
homotopy categories. -/
abbrev smallEtaleModulePullbackMapHomotopy {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) :=
  Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The comparison `Lf^* ⟶ f^*` of a morphism of algebraic spaces, with its target written as
the composite of degreewise pullback and localization. -/
abbrev smallEtaleDerivedModulePullbackComparison' {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ smallEtaleDerivedModulePullback B S hS f ⟶
      smallEtaleModulePullbackMapHomotopy f ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  derivedPullbackComparison' (X := smallEtaleRingedTopos B S hS X)
    (Z := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The degreewise identification `g^* ⋙ f^* ≅ k^*` of pullbacks on homotopy categories attached
to a factorisation `f ≫ g = k` of morphisms of algebraic spaces: the compositor of Stacks 03D6
followed by the 2-isomorphism of Stacks 03G8 comparing the composite of the morphisms of small
étale ringed topoi with that of the composite. -/
def smallEtalePullbackMapHomotopyFactorIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    smallEtaleModulePullbackMapHomotopy g ⋙ smallEtaleModulePullbackMapHomotopy f ≅
      smallEtaleModulePullbackMapHomotopy k :=
  haveI := RingedToposHom.pullbackModules_additive
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))
  pullbackMapHomotopyCompIso (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) ≪≫
    Stacks.Homology.mapHomotopyCategoryIso
      (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso (ComplexShape.up ℤ) ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z ↦ smallEtaleModulePullbackMapHomotopy m) h)

/-- **The identification `Lg^* ⋙ Lf^* ≅ Lk^*` is the degreewise one on complexes**: read through
the comparison maps `L(-)^* ⟶ (-)^*`, it is
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso`. -/
theorem smallEtaleDerivedPullbackFactorIso_hom_app_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedPullbackFactorIso B S hS f g k h).hom.app (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullbackComparison' k).app M =
      (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedModulePullbackComparison' g).app M) ≫
        (smallEtaleDerivedModulePullbackComparison' f).app
          ((smallEtaleModulePullbackMapHomotopy g).obj M) ≫
        DerivedCategory.Qh.map ((smallEtalePullbackMapHomotopyFactorIso f g k h).hom.app M) := by
  subst h
  have h₁ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app'
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) M
  have h₂ := derivedPullbackIsoOfTwoIso_hom_fac (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom_compTwoIso B S hS f g) M
  have e : (smallEtaleDerivedPullbackFactorIso B S hS f g (f ≫ g) rfl).hom.app
      (DerivedCategory.Qh.obj M) =
      (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f g).hom.app (DerivedCategory.Qh.obj M) := by
    simp [smallEtaleDerivedPullbackFactorIso]
  rw [e, smallEtaleDerivedPullbackCompIsoOfTwoIso_hom_app, Category.assoc]
  dsimp only [smallEtaleDerivedModulePullbackComparison', smallEtaleModulePullbackMapHomotopy]
  rw [h₂, reassoc_of% h₁]
  simp only [smallEtalePullbackMapHomotopyFactorIso, pullbackMapHomotopyCompIso, Iso.trans_hom,
    NatTrans.comp_app, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    CategoryTheory.Functor.map_comp, Stacks.Homology.mapHomotopyCategoryIso]

/-! ### The identification of a square -/

/-- The components of `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso`. -/
theorem DerivedPullbackComposition.squareIso_hom_app (P : DerivedPullbackComposition B S hS)
    {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z)
    (h : u' ≫ t = t' ≫ u)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (P.squareIso u' t t' u h).hom.app M =
      (P.iso t' u (u' ≫ t) h.symm).hom.app M ≫ (P.iso u' t (u' ≫ t) rfl).inv.app M :=
  rfl

/-- The identifications of factorisations of the canonical pseudofunctoriality datum. -/
theorem canonical_iso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k) :
    (DerivedPullbackComposition.canonical B S hS).iso f g k h =
      smallEtaleDerivedPullbackFactorIso B S hS f g k h := rfl

/-- `AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` for the
identifications of the canonical pseudofunctoriality datum. -/
theorem canonical_iso_hom_app_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    ((DerivedPullbackComposition.canonical B S hS).iso f g k h).hom.app
          (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullbackComparison' k).app M =
      (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedModulePullbackComparison' g).app M) ≫
        (smallEtaleDerivedModulePullbackComparison' f).app
          ((smallEtaleModulePullbackMapHomotopy g).obj M) ≫
        DerivedCategory.Qh.map ((smallEtalePullbackMapHomotopyFactorIso f g k h).hom.app M) :=
  smallEtaleDerivedPullbackFactorIso_hom_app_comp f g k h M


/-- **The identification of a square is the degreewise one on complexes**: for the canonical
pseudofunctoriality datum, the identification `Lu^* ⋙ Lt'^* ≅ Lt^* ⋙ Lu'^*` of a commutative
square, read through the comparison maps, is the degreewise identification
`u^* ⋙ t'^* ≅ t^* ⋙ u'^*`. -/
theorem squareIso_canonical_hom_app_comp {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (h : u' ≫ t = t' ≫ u)
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    ((DerivedPullbackComposition.canonical B S hS).squareIso u' t t' u h).hom.app
          (DerivedCategory.Qh.obj N) ≫
        (smallEtaleDerivedModulePullback B S hS u').map
          ((smallEtaleDerivedModulePullbackComparison' t).app N) ≫
        (smallEtaleDerivedModulePullbackComparison' u').app
          ((smallEtaleModulePullbackMapHomotopy t).obj N) =
      (smallEtaleDerivedModulePullback B S hS t').map
          ((smallEtaleDerivedModulePullbackComparison' u).app N) ≫
        (smallEtaleDerivedModulePullbackComparison' t').app
          ((smallEtaleModulePullbackMapHomotopy u).obj N) ≫
        DerivedCategory.Qh.map
          (((smallEtalePullbackMapHomotopyFactorIso t' u (u' ≫ t) h.symm).hom ≫
            (smallEtalePullbackMapHomotopyFactorIso u' t (u' ≫ t) rfl).inv).app N) := by
  rw [DerivedPullbackComposition.squareIso_hom_app]
  exact Iso.hom_inv_app_comp_eq_of_comparisons _ _ _ _ _ _
    (smallEtaleDerivedModulePullbackComparison' (u' ≫ t)) _ _ N
    (canonical_iso_hom_app_comp t' u (u' ≫ t) h.symm N)
    (canonical_iso_hom_app_comp u' t (u' ≫ t) rfl N)

/-! ### Extension by zero and its adjunction on homotopy categories -/

/-- **Degreewise extension by zero is left adjoint to degreewise pullback along an étale
morphism**, on homotopy categories: the adjunction of Stacks 03DJ induced on homotopy categories,
read through the identification of pullback with étale restriction of Stacks 03LW. -/
def etaleLowerShriekHomotopyAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    (etaleExtensionByZero B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      smallEtaleModulePullbackMapHomotopy f :=
  (Adjunction.mapHomotopyCategoryAdjunction (G := etaleExtensionByZero B S hS f hf)
      (F := etaleRestriction B S hS f hf) (etaleModuleLowerShriekAdjunction B S hS f hf)
      (ComplexShape.up ℤ)).ofNatIsoRight
    (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
      (pullbackModulesIsoEtaleRestriction B S hS f hf) (ComplexShape.up ℤ)).symm

/-- The two spellings of the comparison `Lf^* ⟶ f^*` agree. -/
theorem smallEtaleDerivedModulePullbackComparison'_eq {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    smallEtaleDerivedModulePullbackComparison' f =
      smallEtaleDerivedModulePullbackComparison B S hS f :=
  rfl

/-- The identification of `Lf^*` along an étale morphism with the functor induced by étale
restriction, read through the comparison maps. -/
theorem smallEtaleDerivedModulePullbackIsoOfIsEtale_hom_app_comp {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS f hf).hom.app (DerivedCategory.Qh.obj N) ≫
        (etaleRestriction B S hS f hf).mapDerivedCategoryFactorsh.hom.app N =
      (smallEtaleDerivedModulePullbackComparison B S hS f).app N ≫
        DerivedCategory.Qh.map ((Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
          (pullbackModulesIsoEtaleRestriction B S hS f hf) (ComplexShape.up ℤ)).hom.app N) := by
  let := Functor.isLeftDerivedFunctor_of_inverts (smallEtaleModuleQuasiIso B S hS Y)
    (etaleRestriction B S hS f hf).mapDerivedCategory
    (etaleRestriction B S hS f hf).mapDerivedCategoryFactorsh
  exact Functor.leftDerivedNatTrans_app (smallEtaleDerivedModulePullback B S hS f)
    (etaleRestriction B S hS f hf).mapDerivedCategory
    (smallEtaleDerivedModulePullbackComparison B S hS f)
    (etaleRestriction B S hS f hf).mapDerivedCategoryFactorsh.hom
    (smallEtaleModuleQuasiIso B S hS Y)
    (Functor.isoWhiskerRight
      (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
        (pullbackModulesIsoEtaleRestriction B S hS f hf) (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom N

/-- `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoOfIsEtale_hom_app_comp` with the
comparison spelled as in `AlgebraicGeometry.Space.etaleLowerShriekHomotopyAdjunction`. -/
theorem smallEtaleDerivedModulePullbackIsoOfIsEtale_hom_app_comp' {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS f hf).hom.app (DerivedCategory.Qh.obj N) ≫
        (etaleRestriction B S hS f hf).mapDerivedCategoryFactorsh.hom.app N =
      (smallEtaleDerivedModulePullbackComparison' f).app N ≫
        DerivedCategory.Qh.map ((Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
          (pullbackModulesIsoEtaleRestriction B S hS f hf)
            (ComplexShape.up ℤ)).symm.inv.app N) := by
  rw [smallEtaleDerivedModulePullbackComparison'_eq, Iso.symm_inv]
  exact smallEtaleDerivedModulePullbackIsoOfIsEtale_hom_app_comp f hf N

/-- **The unit of `u_! ⊣ Lu^*` is the degreewise one on complexes**: at the image of a complex,
read through the comparison maps of `u_!` and `Lu^*`, it is the image of the unit of the degreewise
adjunction `AlgebraicGeometry.Space.etaleLowerShriekHomotopyAdjunction`. -/
theorem etaleDerivedLowerShriekAdjunction_unit_app_comp {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (etaleDerivedLowerShriekAdjunction B S hS f hf).unit.app (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          ((etaleExtensionByZero B S hS f hf).mapDerivedCategoryFactorsh.hom.app M) ≫
        (smallEtaleDerivedModulePullbackComparison' f).app
          (((etaleExtensionByZero B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      DerivedCategory.Qh.map ((etaleLowerShriekHomotopyAdjunction f hf).unit.app M) :=
  mapDerivedCategoryAdjunction_ofNatIsoRight_unit_app_Qh (F := etaleExtensionByZero B S hS f hf)
    (G := etaleRestriction B S hS f hf) (hG := smallEtaleModulePullbackMapHomotopy f)
    (etaleModuleLowerShriekAdjunction B S hS f hf)
    (smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS f hf)
    (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso
      (pullbackModulesIsoEtaleRestriction B S hS f hf) (ComplexShape.up ℤ)).symm
    (smallEtaleDerivedModulePullbackComparison' f)
    (smallEtaleDerivedModulePullbackIsoOfIsEtale_hom_app_comp' f hf)
    (etaleDerivedLowerShriekAdjunction B S hS f hf) rfl
    (etaleLowerShriekHomotopyAdjunction f hf) rfl M

/-- **The comparison map `Lf^* ⟶ f^*` is invertible along an étale morphism**, at every complex. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison'_app {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    IsIso ((smallEtaleDerivedModulePullbackComparison' f).app N) := by
  exact IsIso.of_isIso_fac_right
    (smallEtaleDerivedModulePullbackIsoOfIsEtale_hom_app_comp' f hf N).symm

/-- **The comparison map `Lf^* ⟶ f^*` is invertible along an étale morphism.** -/
theorem isIso_smallEtaleDerivedModulePullbackComparison' {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    IsIso (smallEtaleDerivedModulePullbackComparison' f) :=
  have := isIso_smallEtaleDerivedModulePullbackComparison'_app f hf
  NatIso.isIso_of_isIso_app _

/-! ### The base change map -/

/-- **The degreewise base change map for extension by zero**, `t'^* ⋙ u'_! ⟶ u_! ⋙ t^*` on
homotopy categories: the mate, under the adjunctions of degreewise extension by zero, of the
degreewise identification `u^* ⋙ t'^* ≅ t^* ⋙ u'^*` of a commutative square. -/
def extensionByZeroBaseChangeHomotopy {T T' U Z : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u) :
    smallEtaleModulePullbackMapHomotopy t' ⋙
        (etaleExtensionByZero B S hS u' hu').mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (etaleExtensionByZero B S hS u hu).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        smallEtaleModulePullbackMapHomotopy t :=
  ((mateEquiv (etaleLowerShriekHomotopyAdjunction u hu)
    (etaleLowerShriekHomotopyAdjunction u' hu')).symm
      (TwoSquare.mk _ _ _ _ ((smallEtalePullbackMapHomotopyFactorIso t' u (u' ≫ t) h.symm).hom ≫
        (smallEtalePullbackMapHomotopyFactorIso u' t (u' ≫ t) rfl).inv)))

/-- **The derived base change map for extension by zero is the degreewise one on complexes**: for
the canonical pseudofunctoriality datum, at the image of a complex `M`, the base change map
`u'_!(Lt'^*M) ⟶ Lt^*(u_!M)` read through the comparison maps is the image of the degreewise base
change map `u'_!(t'^*M) ⟶ t^*(u_!M)`. -/
theorem extensionByZeroBaseChange_canonical_app_comp {T T' U Z : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))
      (ComplexShape.up ℤ)) :
    ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu'
          h).app (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullback B S hS t).map
          ((etaleExtensionByZero B S hS u hu).mapDerivedCategoryFactorsh.hom.app M) ≫
        (smallEtaleDerivedModulePullbackComparison' t).app
          (((etaleExtensionByZero B S hS u hu).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      (etaleExtensionByZero B S hS u' hu').mapDerivedCategory.map
          ((smallEtaleDerivedModulePullbackComparison' t').app M) ≫
        (etaleExtensionByZero B S hS u' hu').mapDerivedCategoryFactorsh.hom.app
          ((smallEtaleModulePullbackMapHomotopy t').obj M) ≫
        DerivedCategory.Qh.map ((extensionByZeroBaseChangeHomotopy u' t t' u hu hu' h).app M) := by
  have := isIso_smallEtaleDerivedModulePullbackComparison' u' hu'
  exact Adjunction.mateEquiv_symm_app_comp_of_eq (etaleDerivedLowerShriekAdjunction B S hS u hu)
    (etaleDerivedLowerShriekAdjunction B S hS u' hu')
    (etaleLowerShriekHomotopyAdjunction u hu) (etaleLowerShriekHomotopyAdjunction u' hu')
    (smallEtaleDerivedModulePullbackComparison' t') (smallEtaleDerivedModulePullbackComparison' t)
    (smallEtaleDerivedModulePullbackComparison' u) (smallEtaleDerivedModulePullbackComparison' u')
    (etaleExtensionByZero B S hS u hu).mapDerivedCategoryFactorsh
    (etaleExtensionByZero B S hS u' hu').mapDerivedCategoryFactorsh
    ((DerivedPullbackComposition.canonical B S hS).squareIso u' t t' u h).hom
    ((smallEtalePullbackMapHomotopyFactorIso t' u (u' ≫ t) h.symm).hom ≫
      (smallEtalePullbackMapHomotopyFactorIso u' t (u' ≫ t) rfl).inv)
    ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu' h)
    rfl (extensionByZeroBaseChangeHomotopy u' t t' u hu hu' h) rfl
    (etaleDerivedLowerShriekAdjunction_unit_app_comp u hu)
    (etaleDerivedLowerShriekAdjunction_unit_app_comp u' hu')
    (squareIso_canonical_hom_app_comp u' t t' u h) M

/-- **The derived base change map for extension by zero is invertible at a complex** `M` at which
the comparison maps of `Lt'^*` at `M` and of `Lt^*` at `u_!M`, and the degreewise base change map,
are invertible. -/
theorem isIso_extensionByZeroBaseChange_canonical_app {T T' U Z : AlgebraicSpaces B S hS}
    (u' : T' ⟶ T) (t : T ⟶ Z) (t' : T' ⟶ U) (u : U ⟶ Z) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) (h : u' ≫ t = t' ≫ u)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS U))
      (ComplexShape.up ℤ))
    [IsIso ((smallEtaleDerivedModulePullbackComparison' t').app M)]
    [IsIso ((smallEtaleDerivedModulePullbackComparison' t).app
      (((etaleExtensionByZero B S hS u hu).mapHomotopyCategory (ComplexShape.up ℤ)).obj M))]
    [IsIso ((extensionByZeroBaseChangeHomotopy u' t t' u hu hu' h).app M)] :
    IsIso (((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu
      hu' h).app (DerivedCategory.Qh.obj M)) := by
  exact IsIso.of_isIso_fac_right (extensionByZeroBaseChange_canonical_app_comp u' t t' u hu hu' h M)

end AlgebraicGeometry.Space
