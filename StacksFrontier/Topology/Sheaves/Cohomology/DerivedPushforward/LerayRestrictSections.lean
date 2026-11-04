module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections

/-!
# Restriction of derived sections to a smaller open

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `W ⊆ V ⊆ Y` be opens.
Sections over `V` restrict to sections over `W`, but the two functors
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` take values in modules over *different*
rings, `Γ(V, 𝒪_Y)` and `Γ(W, 𝒪_Y)`.  Restriction is therefore not a transformation between them:
it is a transformation

`Γ(V, -) ⟶ Γ(W, -) ∘ res`,

where `res` is restriction of scalars along `Γ(V, 𝒪_Y) ⟶ Γ(W, 𝒪_Y)`, and a section of the
right-hand side is a section over `W` read as a `Γ(V, 𝒪_Y)`-module.  Restriction of scalars is
exact, so it descends to derived categories, and the same shape describes the derived restriction

`RΓ(V, -) ⟶ RΓ(W, -) ∘ res`

obtained from the universal property of the total right derived functor of `Γ(V, -)`.  This file
builds these transformations for sections over an open and for sections over the inverse image of
an open, and proves that the Leray comparison of
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison` ([Stacks, Tag 0D5W]) commutes with them.
That compatibility is what conclusion (c) of [Stacks, Tag 0EX3] uses when it compares derived
sections over nested opens.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.sectionsRingRestrict` and
  `Stacks.Cohomology.DerivedSectionsLeray.sectionsRestrictScalars` — the restriction map
  `Γ(V, 𝒪_X) ⟶ Γ(W, 𝒪_X)` of the structure sheaf, and restriction of scalars along it.
* `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrictLE` and
  `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrictLE` — the degreewise restriction
  transformations for sections over an open and for sections over the inverse image of an open.
* `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrictUnit` and
  `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrictUnitLE` — the transformations
  into `Qh ⋙ (RΓ(W, -) ∘ res)` that the universal property of the derived functor consumes.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrictLE` and
  `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrictLE` — the derived
  restriction transformations.

## Main results

* Exactness of restriction of scalars, which is what makes
  `CategoryTheory.Functor.mapDerivedCategory` available for it, is **not** stated here: it is
  Mathlib's `ModuleCat.restrictScalars_map_exact` and the two instances that file derives from
  it.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrictLE_fac_app` and
  `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrictLE_fac_app` — the
  factorizations through the derived-functor units that characterize the two derived restrictions.
* `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_restrict` — **the compatibility of the
  Leray comparison with restriction to a smaller open**.

## Implementation notes

*Why the degreewise maps are already available.*  Restriction for sections over an open of `X` is
`CategoryTheory.PresheafOfModules.restriction`, which is exactly a transformation into restriction
of scalars.  Restriction for sections over an inverse image needs the commutation of `f^♯` with
restriction, and that is free here: sections over `f⁻¹ V` read over `Γ(V, 𝒪_Y)` *are* sections
over `V` of the direct image, as `pushforwardPreimageSectionsIso` records, so the second
transformation is the first one for `Y` applied to a direct image.

*Where the content of the compatibility sits.*  Both sides of
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_restrict` are transformations out of the
total right derived functor `RΓ(f⁻¹ V, -)`, so
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` reduces the statement to the
composites with the derived-functor unit.  Each of those collapses, by the characterizing
factorizations, to a composite of degreewise units, and the two results are matched by naturality
of the derived restriction, naturality of the comparison `Qh ⋙ res ≅ res ⋙ Qh` of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, and the identity of the degreewise
restrictions, which holds on the nose.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of restriction of scalars

Nothing is stated here. Mathlib's `Mathlib/Algebra/Category/ModuleCat/ChangeOfRingsExact.lean`,
which this file imports, proves `ModuleCat.restrictScalars_map_exact` for a homomorphism
`f : R →+* S` of **commutative** rings and derives from it the two instances
`PreservesFiniteLimits (ModuleCat.restrictScalars f)` and
`PreservesFiniteColimits (ModuleCat.restrictScalars f)` that make
`CategoryTheory.Functor.mapDerivedCategory` available below.

Those instances do apply to the ring maps of this file even though `sectionsRingRestrict` is
valued in `RingCat`: the sections of the structure sheaf of a ringed space are a `CommRingCat`
read through `forget₂ CommRingCat RingCat`, so their carrier still carries the `CommRing`
instance Mathlib's instances ask for. The lemma and the instances are deliberately not restated
for possibly noncommutative rings: nothing here needs that generality, and a second pair of
instances would give synthesis two unrelated paths to the same goal. -/

/-! ### Restriction of sections to a smaller open -/

/-- **The restriction map of the structure sheaf.**  For opens `U' ⊆ U` of a ringed space `X`, the
ring homomorphism `Γ(U, 𝒪_X) ⟶ Γ(U', 𝒪_X)`. -/
abbrev sectionsRingRestrict (X : RingedSpace.{u, u}) {U U' : Opens X.carrier} (h : U' ≤ U) :
    (structureSheafRing X).obj.obj (op U) →+* (structureSheafRing X).obj.obj (op U') :=
  ((structureSheafRing X).obj.map (homOfLE h).op).hom

/-- **Restriction of scalars along the restriction map of the structure sheaf.**  It turns a
`Γ(U', 𝒪_X)`-module into a `Γ(U, 𝒪_X)`-module, and it is the functor through which restriction of
sections from `U` to `U'` is a natural transformation. -/
abbrev sectionsRestrictScalars (X : RingedSpace.{u, u}) {U U' : Opens X.carrier} (h : U' ≤ U) :
    ModuleCat.{u} ((structureSheafRing X).obj.obj (op U')) ⥤
      ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)) :=
  ModuleCat.restrictScalars (sectionsRingRestrict X h)

/-- **Restriction of sections to a smaller open.**  For opens `U' ⊆ U` of a ringed space `X`, the
restriction maps `ℱ(U) ⟶ ℱ(U')` of a sheaf of `𝒪_X`-modules, assembled into a transformation into
restriction of scalars: each component is `Γ(U, 𝒪_X)`-linear once the target is read over
`Γ(U, 𝒪_X)` along `sectionsRingRestrict X h`. -/
def sectionsOverOpenRestrictLE (X : RingedSpace.{u, u}) {U U' : Opens X.carrier} (h : U' ≤ U) :
    sectionsOverOpen X U ⟶ sectionsOverOpen X U' ⋙ sectionsRestrictScalars X h :=
  Functor.whiskerLeft (SheafOfModules.forget (structureSheafRing X))
    (PresheafOfModules.restriction (structureSheafRing X).obj (homOfLE h).op)

/-- **Restriction of sections over an inverse image to a smaller open.**  For opens `W ⊆ V` of `Y`
and a morphism `f : X ⟶ Y` of ringed spaces, the restriction maps
`ℱ(f⁻¹ V) ⟶ ℱ(f⁻¹ W)` of a sheaf of `𝒪_X`-modules, as a transformation of functors valued in
`Γ(V, 𝒪_Y)`-modules.

Nothing new has to be checked: sections over `f⁻¹ V` read over `Γ(V, 𝒪_Y)` are sections over `V`
of the direct image (`pushforwardPreimageSectionsIso`), so this is `sectionsOverOpenRestrictLE` for
`Y` applied to a direct image, and the commutation of `f^♯` with the restriction maps is part of
`f^♯` being a morphism of sheaves of rings. -/
def preimageSectionsRestrictLE {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V W : Opens Y.carrier}
    (h : W ≤ V) :
    preimageSections f V ⟶ preimageSections f W ⋙ sectionsRestrictScalars Y h :=
  Functor.whiskerLeft (modulePushforward f) (sectionsOverOpenRestrictLE Y h)

/-! ### The derived restriction for sections over an open -/

/-- Restriction of scalars commutes with passing to the derived category: sections over `U'`
followed by restriction of scalars, read on the homotopy category and then localized, is sections
over `U'` localized and then followed by the derived functor of restriction of scalars. -/
def sectionsRestrictHomotopyIso (X : RingedSpace.{u, u}) {U U' : Opens X.carrier}
    (h : U' ≤ U) :
    (sectionsOverOpen X U' ⋙ sectionsRestrictScalars X h).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (sectionsOverOpen X U').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ (sectionsRestrictScalars X h).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (sectionsOverOpen X U' ⋙ sectionsRestrictScalars X h)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft ((sectionsOverOpen X U').mapHomotopyCategory (ComplexShape.up ℤ))
      (sectionsRestrictScalars X h).mapDerivedCategoryFactorsh.symm

/-- The canonical transformation from termwise sections over `U` to
`RΓ(U', -)` followed by restriction of scalars: the degreewise restriction maps, read on the
homotopy category, followed by the unit of `RΓ(U', -)`.  Its universal factorization is the derived
restriction `derivedSectionsOverOpenRestrictLE`. -/
def sectionsOverOpenRestrictUnit (X : RingedSpace.{u, u}) {U U' : Opens X.carrier} (h : U' ≤ U) :
    homotopySectionsOverOpen X U ⟶
      DerivedCategory.Qh ⋙
        (derivedSectionsOverOpen X U' ⋙ (sectionsRestrictScalars X h).mapDerivedCategory) :=
  Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (sectionsOverOpenRestrictLE X h) (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    (sectionsRestrictHomotopyIso X h).hom ≫
    Functor.whiskerRight (derivedSectionsOverOpenUnit X U')
      (sectionsRestrictScalars X h).mapDerivedCategory

/-- **The derived restriction for sections over an open** `RΓ(U, -) ⟶ RΓ(U', -) ∘ res`, the
transformation induced by `sectionsOverOpenRestrictUnit` through the universal property of the
right derived functor of sections over `U`.  By `derivedSectionsOverOpenRestrictLE_fac_app` its
composite with the derived-functor unit is `sectionsOverOpenRestrictUnit`, and that equation
determines it. -/
def derivedSectionsOverOpenRestrictLE (X : RingedSpace.{u, u}) {U U' : Opens X.carrier}
    (h : U' ≤ U) :
    derivedSectionsOverOpen X U ⟶
      derivedSectionsOverOpen X U' ⋙ (sectionsRestrictScalars X h).mapDerivedCategory :=
  (derivedSectionsOverOpen X U).rightDerivedDesc (derivedSectionsOverOpenUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (sectionsOverOpenRestrictUnit X h)

/-- The equation characterizing the derived restriction for sections over an open, pointwise:
composing it with the unit of `RΓ(U, -)` recovers `sectionsOverOpenRestrictUnit`. -/
theorem derivedSectionsOverOpenRestrictLE_fac_app (X : RingedSpace.{u, u})
    {U U' : Opens X.carrier} (h : U' ≤ U)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedSectionsOverOpenUnit X U).app K ≫
        (derivedSectionsOverOpenRestrictLE X h).app (DerivedCategory.Qh.obj K) =
      (sectionsOverOpenRestrictUnit X h).app K :=
  (derivedSectionsOverOpen X U).rightDerived_fac_app (derivedSectionsOverOpenUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (sectionsOverOpenRestrictUnit X h) K

/-- `derivedSectionsOverOpenRestrictLE_fac_app` with a further morphism appended, the form in which
a rewrite inside a longer composite uses it. -/
theorem derivedSectionsOverOpenRestrictLE_fac_app_comp (X : RingedSpace.{u, u})
    {U U' : Opens X.carrier} (h : U' ≤ U)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)))}
    (g : (derivedSectionsOverOpen X U' ⋙ (sectionsRestrictScalars X h).mapDerivedCategory).obj
      (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedSectionsOverOpenUnit X U).app K ≫
        (derivedSectionsOverOpenRestrictLE X h).app (DerivedCategory.Qh.obj K) ≫ g =
      (sectionsOverOpenRestrictUnit X h).app K ≫ g := by
  rw [← Category.assoc, derivedSectionsOverOpenRestrictLE_fac_app]

/-! ### The derived restriction for sections over an inverse image -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V W : Opens Y.carrier} (h : W ≤ V)

/-- Restriction of scalars commutes with passing to the derived category, for sections over the
inverse image of an open. -/
def preimageSectionsRestrictHomotopyIso :
    (preimageSections f W ⋙ sectionsRestrictScalars Y h).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (preimageSections f W).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ (sectionsRestrictScalars Y h).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (preimageSections f W ⋙ sectionsRestrictScalars Y h)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft ((preimageSections f W).mapHomotopyCategory (ComplexShape.up ℤ))
      (sectionsRestrictScalars Y h).mapDerivedCategoryFactorsh.symm

/-- The canonical transformation from termwise sections over `f⁻¹ V` to `RΓ(f⁻¹ W, -)` followed by
restriction of scalars: the degreewise restriction maps, read on the homotopy category, followed by
the unit of `RΓ(f⁻¹ W, -)`. -/
def preimageSectionsRestrictUnitLE :
    homotopyPreimageSections f V ⟶
      DerivedCategory.Qh ⋙
        (derivedPreimageSections f W ⋙ (sectionsRestrictScalars Y h).mapDerivedCategory) :=
  Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (preimageSectionsRestrictLE f h) (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    (preimageSectionsRestrictHomotopyIso f h).hom ≫
    Functor.whiskerRight (derivedPreimageSectionsUnit f W)
      (sectionsRestrictScalars Y h).mapDerivedCategory

/-- **The derived restriction for sections over an inverse image**
`RΓ(f⁻¹ V, -) ⟶ RΓ(f⁻¹ W, -) ∘ res`, the transformation induced by
`preimageSectionsRestrictUnitLE` through the universal property of the right derived functor of
sections over `f⁻¹ V`. -/
def derivedPreimageSectionsRestrictLE :
    derivedPreimageSections f V ⟶
      derivedPreimageSections f W ⋙ (sectionsRestrictScalars Y h).mapDerivedCategory :=
  (derivedPreimageSections f V).rightDerivedDesc (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsRestrictUnitLE f h)

/-- The equation characterizing the derived restriction for sections over an inverse image,
pointwise: composing it with the unit of `RΓ(f⁻¹ V, -)` recovers
`preimageSectionsRestrictUnitLE`. -/
theorem derivedPreimageSectionsRestrictLE_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit f V).app K ≫
        (derivedPreimageSectionsRestrictLE f h).app (DerivedCategory.Qh.obj K) =
      (preimageSectionsRestrictUnitLE f h).app K :=
  (derivedPreimageSections f V).rightDerived_fac_app (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (preimageSectionsRestrictUnitLE f h) K

/-- `derivedPreimageSectionsRestrictLE_fac_app` with a further morphism appended, the form in which
a rewrite inside a longer composite uses it. -/
theorem derivedPreimageSectionsRestrictLE_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))}
    (g : (derivedPreimageSections f W ⋙ (sectionsRestrictScalars Y h).mapDerivedCategory).obj
      (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit f V).app K ≫
        (derivedPreimageSectionsRestrictLE f h).app (DerivedCategory.Qh.obj K) ≫ g =
      (preimageSectionsRestrictUnitLE f h).app K ≫ g := by
  rw [← Category.assoc, derivedPreimageSectionsRestrictLE_fac_app]

/-! ### The two routes written out degreewise -/

/-- The first route, expanded: the Leray unit for `f` at `V` followed by the derived restriction to
`W` is the identification of degreewise sections, the restriction unit for sections over `W`, and
then the unit of `Rf_*`.  Naturality of the derived restriction moves it past the image of the
pushforward unit, and the characterizing factorization then collapses the unit of `RΓ(V, -)`
followed by the derived restriction into `sectionsOverOpenRestrictUnit`. -/
private theorem lerayUnit_comp_derivedSectionsOverOpenRestrict_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (lerayUnit f V).app K ≫
        (derivedSectionsOverOpenRestrictLE Y h).app
          ((derivedPushforward f).obj (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (sectionsOverOpenRestrictUnit Y h).app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (sectionsRestrictScalars Y h).mapDerivedCategory.map
            ((derivedSectionsOverOpen Y W).map ((derivedPushforwardUnit f).app K)) := by
  have hnat : (derivedSectionsOverOpen Y V).map ((derivedPushforwardUnit f).app K) ≫
        (derivedSectionsOverOpenRestrictLE Y h).app
          ((derivedPushforward f).obj (DerivedCategory.Qh.obj K)) =
      (derivedSectionsOverOpenRestrictLE Y h).app
          (DerivedCategory.Qh.obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (sectionsRestrictScalars Y h).mapDerivedCategory.map
          ((derivedSectionsOverOpen Y W).map ((derivedPushforwardUnit f).app K)) :=
    (derivedSectionsOverOpenRestrictLE Y h).naturality ((derivedPushforwardUnit f).app K)
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [hnat, derivedSectionsOverOpenRestrictLE_fac_app_comp]

/-- The second route, expanded: the restriction unit for sections over `f⁻¹ V` followed by the
Leray comparison for `f` at `W` is the degreewise restriction, the comparison of restriction of
scalars with localization, the identification of degreewise sections, the unit of `RΓ(W, -)`, and
then the unit of `Rf_*`. -/
private theorem preimageSectionsRestrictUnitLE_comp_lerayComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (preimageSectionsRestrictUnitLE f h).app K ≫
        (sectionsRestrictScalars Y h).mapDerivedCategory.map
          ((lerayComparison f W).app (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (preimageSectionsRestrictLE f h)
            (ComplexShape.up ℤ)).app K) ≫
        (preimageSectionsRestrictHomotopyIso f h).hom.app K ≫
          (sectionsRestrictScalars Y h).mapDerivedCategory.map
              (DerivedCategory.Qh.map
                ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f W)
                  (ComplexShape.up ℤ)).inv.app K)) ≫
            (sectionsRestrictScalars Y h).mapDerivedCategory.map
                ((derivedSectionsOverOpenUnit Y W).app
                  (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
              (sectionsRestrictScalars Y h).mapDerivedCategory.map
                ((derivedSectionsOverOpen Y W).map ((derivedPushforwardUnit f).app K)) := by
  dsimp only [preimageSectionsRestrictUnitLE, NatTrans.comp_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← (sectionsRestrictScalars Y h).mapDerivedCategory.map_comp, lerayComparison_fac_app f W K]
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp]

/-- The two expanded routes agree.  Naturality of the comparison of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` moves the identification of degreewise sections
over `W` to the front, and the degreewise restrictions then compose to one another on the nose:
restriction for sections over `f⁻¹ W` is by construction restriction for sections over `W`
evaluated at a direct image. -/
private theorem sectionsOverOpenRestrictUnit_pushforward_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (sectionsOverOpenRestrictUnit Y h).app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (sectionsRestrictScalars Y h).mapDerivedCategory.map
            ((derivedSectionsOverOpen Y W).map ((derivedPushforwardUnit f).app K)) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (preimageSectionsRestrictLE f h)
            (ComplexShape.up ℤ)).app K) ≫
        (preimageSectionsRestrictHomotopyIso f h).hom.app K ≫
          (sectionsRestrictScalars Y h).mapDerivedCategory.map
              (DerivedCategory.Qh.map
                ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f W)
                  (ComplexShape.up ℤ)).inv.app K)) ≫
            (sectionsRestrictScalars Y h).mapDerivedCategory.map
                ((derivedSectionsOverOpenUnit Y W).app
                  (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
              (sectionsRestrictScalars Y h).mapDerivedCategory.map
                ((derivedSectionsOverOpen Y W).map ((derivedPushforwardUnit f).app K)) := by
  have hnat : (sectionsRestrictScalars Y h).mapDerivedCategoryFactorsh.inv.app
          (((preimageSections f W).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (sectionsRestrictScalars Y h).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f W)
              (ComplexShape.up ℤ)).inv.app K)) =
      DerivedCategory.Qh.map
          (((sectionsRestrictScalars Y h).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f W)
              (ComplexShape.up ℤ)).inv.app K)) ≫
        (sectionsRestrictScalars Y h).mapDerivedCategoryFactorsh.inv.app
          (((sectionsOverOpen Y W).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    ((sectionsRestrictScalars Y h).mapDerivedCategoryFactorsh.inv.naturality
      ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f W)
        (ComplexShape.up ℤ)).inv.app K)).symm
  dsimp only [sectionsOverOpenRestrictUnit, sectionsRestrictHomotopyIso,
    preimageSectionsRestrictHomotopyIso, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.comp_obj]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  rfl

/-! ### The compatibility of the Leray comparison with restriction -/

/-- **The Leray comparison is compatible with restriction to a smaller open.**  For a morphism
`f : X ⟶ Y` of ringed spaces and opens `W ⊆ V` of `Y`, the Leray comparison at `V` followed by the
derived restriction of sections over `V` to sections over `W` equals the derived restriction of
sections over `f⁻¹ V` to sections over `f⁻¹ W` followed by the Leray comparison at `W`.  Both
sides are transformations
`RΓ(f⁻¹ V, -) ⟶ Rf_* ⋙ RΓ(W, -) ⋙ res` of functors `D(𝒪_X) ⥤ D(Γ(V, 𝒪_Y))`, where `res` is
restriction of scalars along `Γ(V, 𝒪_Y) ⟶ Γ(W, 𝒪_Y)`.

This is the compatibility that conclusion (c) of [Stacks, Tag 0EX3] uses, and it holds with no
hypothesis on `f`.  Both sides come out of the total right derived functor `RΓ(f⁻¹ V, -)`, so
`lerayComparison_ext` reduces the statement to the composites with the derived-functor unit, and
those are compared degreewise. -/
theorem lerayComparison_restrict :
    lerayComparison f V ≫
        Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrictLE Y h) =
      derivedPreimageSectionsRestrictLE f h ≫
        Functor.whiskerRight (lerayComparison f W)
          (sectionsRestrictScalars Y h).mapDerivedCategory := by
  apply (derivedPreimageSections f V).rightDerived_ext (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [lerayComparison_fac_app_comp f V K, derivedPreimageSectionsRestrictLE_fac_app_comp f h K]
  exact (lerayUnit_comp_derivedSectionsOverOpenRestrict_app f h K).trans
    ((sectionsOverOpenRestrictUnit_pushforward_app f h K).trans
      (preimageSectionsRestrictUnitLE_comp_lerayComparison_app f h K).symm)

end Stacks.Cohomology.DerivedSectionsLeray

end
