module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap

/-!
# `A`-linear derived sections over an open

Let `(X, 𝒪_X)` be a ringed space and let `A = Γ(X, 𝒪_X)`.  For an open `W ⊆ X` the sections
`ℱ(W)` of a sheaf of `𝒪_X`-modules form a module over `Γ(W, 𝒪_X)`, hence a module over `A` by
restriction of scalars along the restriction homomorphism `A ⟶ Γ(W, 𝒪_X)`.  This file
constructs the resulting additive functor and its unbounded total right derived functor

`RΓ(W, -) : D(𝒪_X) ⥤ D(A)`,

together with the restriction transformations `RΓ(W, -) ⟶ RΓ(Z, -)` attached to an inclusion
`Z ⊆ W` of opens, and identifies it with the derived sections over `W` of Tag 0F16 followed by
restriction of scalars.

## Main definitions

* `Stacks.Cohomology.LinearDerivedSections.fromTop` — the restriction homomorphism
  `A = Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_X)`.
* `Stacks.Cohomology.LinearDerivedSections.linearSections` — sections over `W` as `A`-modules,
  with `Stacks.Cohomology.LinearDerivedSections.linearRestriction` the restriction map between
  them.
* `Stacks.Cohomology.LinearDerivedSections.derivedLinearSections` — the unbounded total right
  derived functor `RΓ(W, -) : D(𝒪_X) ⥤ D(A)`, with its unit
  `Stacks.Cohomology.LinearDerivedSections.derivedLinearSectionsUnit` and its restriction
  transformations `Stacks.Cohomology.LinearDerivedSections.derivedLinearRestriction`.
* `Stacks.Cohomology.LinearDerivedSections.derivedRestrictScalars` — restriction of scalars
  along `fromTop X W`, as a functor between derived categories of modules.
* `Stacks.Cohomology.LinearDerivedSections.mapHomotopyCategoryIso` — an isomorphism of additive
  functors, read on homotopy categories of complexes.

## Main results

* `Stacks.Cohomology.LinearDerivedSections.linearRestriction_id`,
  `Stacks.Cohomology.LinearDerivedSections.linearRestriction_comp` and their derived
  counterparts `Stacks.Cohomology.LinearDerivedSections.derivedLinearRestriction_id`,
  `Stacks.Cohomology.LinearDerivedSections.derivedLinearRestriction_comp`: the restriction
  transformations are functorial in the inclusion of opens.
* `Stacks.Cohomology.LinearDerivedSections.derivedLinearSectionsTopIso` — over `W = X` the
  functor is isomorphic to the derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` of the base.
* `Stacks.Cohomology.LinearDerivedSections.derivedLinearSectionsIso` — `RΓ(W, -)` is the
  derived sections over `W` followed by restriction of scalars along `A ⟶ Γ(W, 𝒪_X)`.
* `Stacks.Cohomology.LinearDerivedSections.derivedLinearSections_isTriangulated` — `RΓ(W, -)`
  is a triangulated functor.

## Implementation notes

Sections over `W` are taken with scalars restricted to `A = Γ(X, 𝒪_X)`, rather than left over
`Γ(W, 𝒪_X)`, because the comparisons one wants to make run between different opens.  With this
choice the derived sections over `U`, over `V`, over `U ∩ V` and over `X` are all objects of the
single category `D(A)`: the restriction maps of a Mayer--Vietoris situation `X = U ∪ V` are
morphisms of that one category, so they can be compared with one another and all four can be
tensored against a fixed object of `D(A)` such as `RΓ(X, K)`.  Over `Γ(W, 𝒪_X)` none of this is
available, the four rings being different; and forgetting the module structure does not help,
since `D(A) ⥤ D(ℤ)` is not an equivalence.

Restriction of scalars along a ring homomorphism is exact and leaves the underlying additive
group of a module unchanged.  Hence `linearSections` is additive, which is what allows it to be
applied to complexes at all, and the comparison `derivedLinearSectionsIso` holds: a right
derived functor computed by K-injective resolutions remains one after postcomposition with any
functor, which is `isRightDerivedFunctor_of_isIso_app_isKInjective`.

Over `W = X` the restriction homomorphism is the identity of `A`, but restriction of scalars
along the identity is only isomorphic to the identity functor, not equal to it; so the
comparison with the derived global sections of the base is an isomorphism of functors rather
than an equality.

## References

* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (exists_quasiIso_isKInjective isRightDerivedFunctor_of_isIso_app_isKInjective)

universe u

namespace Stacks.Cohomology.LinearDerivedSections

attribute [local instance] HasDerivedCategory.standard

/-- An isomorphism of additive functors induces an isomorphism between the functors they induce
on homotopy categories of homological complexes. -/
def mapHomotopyCategoryIso {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] {ι : Type*} {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-! ### `A`-linear sections over an open -/

/-- Restriction of functions from `X` to an open `W ⊆ X`, the ring map along which sections
over `W` become modules over `A = Γ(X, 𝒪_X)`. -/
abbrev fromTop (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)) ⟶
      (structureSheafRing X).obj.obj (op W) :=
  (structureSheafRing X).obj.map (homOfLE (le_top : W ≤ ⊤)).op

/-- **Sections over an open, as `A`-modules.**  Sections over `W ⊆ X` of a sheaf of
`𝒪_X`-modules, regarded as a module over `A = Γ(X, 𝒪_X)` by restriction of scalars. -/
abbrev linearSections (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    SheafOfModules.{u} (structureSheafRing X) ⥤ ModuleCat.{u} (baseRing X) :=
  sectionsOverOpen X W ⋙ ModuleCat.restrictScalars (fromTop X W).hom

variable (X : RingedSpace.{u, u})

/-- Restricting functions to `Z ⊆ W ⊆ X` in two steps. -/
lemma fromTop_comp {Z W : Opens X.carrier} (h : Z ≤ W) :
    (fromTop X Z).hom =
      ((structureSheafRing X).obj.map (homOfLE h).op).hom.comp (fromTop X W).hom := by
  have hmap : fromTop X Z = fromTop X W ≫ (structureSheafRing X).obj.map (homOfLE h).op := by
    rw [← (structureSheafRing X).obj.map_comp]
    congr 1
  rw [hmap]
  rfl

/-- **Restriction of sections, `A`-linearly.**  The restriction map `ℱ(W) ⟶ ℱ(Z)` for
`Z ⊆ W ⊆ X`, read as a morphism of `A`-modules for `A = Γ(X, 𝒪_X)`. -/
def linearRestriction {Z W : Opens X.carrier} (h : Z ≤ W) :
    linearSections X W ⟶ linearSections X Z :=
  Functor.whiskerRight
      (Functor.whiskerLeft (SheafOfModules.forget (structureSheafRing X))
        (PresheafOfModules.restriction (structureSheafRing X).obj (homOfLE h).op))
      (ModuleCat.restrictScalars (fromTop X W).hom) ≫
    Functor.whiskerLeft (SheafOfModules.evaluation (structureSheafRing X) (op Z))
      (ModuleCat.restrictScalarsComp' (fromTop X W).hom
        ((structureSheafRing X).obj.map (homOfLE h).op).hom (fromTop X Z).hom
        (fromTop_comp X h)).inv

/-- `A`-linear sections over an open form an additive functor: addition of sections is
computed open by open and restriction of scalars does not change the underlying group. -/
instance linearSections_additive (W : Opens X.carrier) : (linearSections X W).Additive where
  map_add := rfl

/-- The value of the `A`-linear restriction map on a section: it is the restriction map of the
underlying presheaf of modules. -/
lemma linearRestriction_app_apply {Z W : Opens X.carrier} (h : Z ≤ W)
    (M : SheafOfModules.{u} (structureSheafRing X)) (x : (M.val.obj (op W) : Type u)) :
    ((linearRestriction X h).app M).hom x = M.val.map (homOfLE h).op x :=
  rfl

/-- Restriction of `A`-linear sections along the identity inclusion is the identity. -/
lemma linearRestriction_id (W : Opens X.carrier) :
    linearRestriction X (le_refl W) = 𝟙 (linearSections X W) := by
  ext M x
  show M.val.map (𝟙 (op W)) x = x
  simp only [PresheafOfModules.map_id]
  rfl

/-- Restriction of `A`-linear sections is functorial in the inclusion of opens: restricting from
`W` to `Z` and then to `Y` is restricting from `W` to `Y`. -/
lemma linearRestriction_comp {Y Z W : Opens X.carrier} (h : Y ≤ Z) (h' : Z ≤ W) :
    linearRestriction X h' ≫ linearRestriction X h = linearRestriction X (h.trans h') := by
  ext M x
  show M.val.map (homOfLE h).op (M.val.map (homOfLE h').op x) =
    M.val.map (homOfLE (h.trans h')).op x
  exact (PresheafOfModules.map_comp_apply M.val (homOfLE h').op (homOfLE h).op x).symm

/-! ### Derived sections over an open, `A`-linearly -/

/-- The quasi-isomorphisms of complexes of `𝒪_X`-modules, with respect to which the derived
sections functors below are derived. -/
abbrev quasiIsos :=
  HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)

/-- `A`-linear sections over `W ⊆ X` read on the homotopy category of cochain complexes of
`𝒪_X`-modules, with values in `D(A)`. -/
abbrev homotopyLinearSections (W : Opens X.carrier) :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing X)) :=
  (linearSections X W).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **`A`-linear derived sections over an open**, `RΓ(W, -) : D(𝒪_X) ⥤ D(A)`. -/
abbrev derivedLinearSections (W : Opens X.carrier) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing X)) :=
  (homotopyLinearSections X W).totalRightDerived DerivedCategory.Qh (quasiIsos X)

/-- The canonical comparison from `A`-linear termwise sections over `W` to their right derived
functor. -/
abbrev derivedLinearSectionsUnit (W : Opens X.carrier) :
    homotopyLinearSections X W ⟶ DerivedCategory.Qh ⋙ derivedLinearSections X W :=
  (homotopyLinearSections X W).totalRightDerivedUnit DerivedCategory.Qh (quasiIsos X)

/-- **The restriction map on `A`-linear derived sections**, `RΓ(W, -) ⟶ RΓ(Z, -)` for
`Z ⊆ W ⊆ X`: the right-derived transformation of `linearRestriction`. -/
def derivedLinearRestriction {Z W : Opens X.carrier} (h : Z ≤ W) :
    derivedLinearSections X W ⟶ derivedLinearSections X Z :=
  (derivedLinearSections X W).rightDerivedNatTrans (derivedLinearSections X Z)
    (derivedLinearSectionsUnit X W) (derivedLinearSectionsUnit X Z) (quasiIsos X)
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (linearRestriction X h) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- Restriction of `A`-linear derived sections along the identity inclusion is the identity. -/
lemma derivedLinearRestriction_id (W : Opens X.carrier) :
    derivedLinearRestriction X (le_refl W) = 𝟙 (derivedLinearSections X W) := by
  rw [derivedLinearRestriction, linearRestriction_id, NatTrans.mapHomotopyCategory_id,
    Functor.whiskerRight_id', Functor.rightDerivedNatTrans_id]

/-- Restriction of `A`-linear derived sections is functorial in the inclusion of opens:
restricting from `W` to `Z` and then to `Y` is restricting from `W` to `Y`. -/
lemma derivedLinearRestriction_comp {Y Z W : Opens X.carrier} (h : Y ≤ Z) (h' : Z ≤ W) :
    derivedLinearRestriction X (h.trans h') =
      derivedLinearRestriction X h' ≫ derivedLinearRestriction X h := by
  rw [derivedLinearRestriction, derivedLinearRestriction, derivedLinearRestriction,
    Functor.rightDerivedNatTrans_comp, ← Functor.whiskerRight_comp,
    ← NatTrans.mapHomotopyCategory_comp, linearRestriction_comp]

/-! ### Derived sections over all of `X` -/

/-- Restriction of functions from `X` to `X` itself is the identity homomorphism of
`A = Γ(X, 𝒪_X)`. -/
lemma fromTop_top :
    (fromTop X ⊤).hom = RingHom.id ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) := by
  have h : (homOfLE (le_top : (⊤ : Opens X.carrier) ≤ ⊤)).op = 𝟙 (op (⊤ : Opens X.carrier)) := rfl
  show ((structureSheafRing X).obj.map (homOfLE (le_top : (⊤ : Opens X.carrier) ≤ ⊤)).op).hom = _
  rw [h, (structureSheafRing X).obj.map_id]
  rfl

/-- Over `X` itself, restriction of scalars along `fromTop` is the identity functor: the
scalars are already those of `A = Γ(X, 𝒪_X)`. -/
def restrictScalarsTopIso :
    ModuleCat.restrictScalars.{u} (fromTop X ⊤).hom ≅
      𝟭 (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) :=
  ModuleCat.restrictScalarsId' (fromTop X ⊤).hom (fromTop_top X)

/-- The derived global sections of the base, read as a functor to `D(A)`, are a right derived
functor of the termwise sections: this is the universal property that characterizes them. -/
instance isRightDerivedFunctor_baseSections :
    (baseSections X).IsRightDerivedFunctor (derivedSectionsOverOpenUnit X ⊤) (quasiIsos X) :=
  (inferInstance : (derivedSectionsOverOpen X ⊤).IsRightDerivedFunctor
    (derivedSectionsOverOpenUnit X ⊤) (quasiIsos X))

/-- **`A`-linear sections over all of `X` are the sections over `X`.**  Restricting scalars
along the identity of `A = Γ(X, 𝒪_X)` changes nothing. -/
def linearSectionsTopIso :
    sectionsOverOpen X ⊤ ⋙ ModuleCat.restrictScalars.{u} (fromTop X ⊤).hom ≅
      sectionsOverOpen X ⊤ :=
  Functor.isoWhiskerLeft (sectionsOverOpen X ⊤) (restrictScalarsTopIso X) ≪≫
    (sectionsOverOpen X ⊤).rightUnitor

/-- The comparison of `linearSectionsTopIso` on homotopy categories of complexes. -/
def homotopyLinearSectionsTopIso :
    homotopyLinearSections X ⊤ ≅ homotopySectionsOverOpen X ⊤ :=
  Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (sectionsOverOpen X ⊤ ⋙
          ModuleCat.restrictScalars.{u} (fromTop X ⊤).hom)) (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso (linearSectionsTopIso X) (ComplexShape.up ℤ))
    DerivedCategory.Qh

/-- **`A`-linear derived sections over all of `X` are the derived global sections of the base**,
`RΓ(X, -) : D(𝒪_X) ⥤ D(A)`: both are right derived functors of the same functor. -/
def derivedLinearSectionsTopIso : derivedLinearSections X ⊤ ≅ baseSections X :=
  Functor.rightDerivedNatIso (derivedLinearSections X ⊤) (baseSections X)
    (derivedLinearSectionsUnit X ⊤) (derivedSectionsOverOpenUnit X ⊤) (quasiIsos X)
    (homotopyLinearSectionsTopIso X)

/-! ### Comparison with the derived sections over `Γ(W, 𝒪_X)` -/

/-- Restriction of scalars preserves finite limits: a limit of modules is computed on the
underlying additive groups, which restriction of scalars does not change. -/
instance restrictScalars_preservesFiniteLimits {R S : Type u} [Ring R] [Ring S] (r : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} r) :=
  ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩

/-- Restriction of scalars preserves finite colimits: a colimit of modules is computed on the
underlying additive groups, which restriction of scalars does not change. -/
instance restrictScalars_preservesFiniteColimits {R S : Type u} [Ring R] [Ring S] (r : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} r) :=
  ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩

/-- Restriction of scalars along `fromTop X W`, read on derived categories of modules:
restriction of scalars is exact, so it descends to a triangulated functor
`D(Γ(W, 𝒪_X)) ⥤ D(A)`. -/
abbrev derivedRestrictScalars (W : Opens X.carrier) :
    DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op W))) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing X)) :=
  (ModuleCat.restrictScalars.{u} (fromTop X W).hom).mapDerivedCategory

/-- At the level of homotopy categories, `A`-linear sections over `W` are sections over `W`
followed by restriction of scalars along `A ⟶ Γ(W, 𝒪_X)`. -/
def homotopyLinearSectionsIso (W : Opens X.carrier) :
    homotopyLinearSections X W ≅ homotopySectionsOverOpen X W ⋙ derivedRestrictScalars X W :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (sectionsOverOpen X W ⋙
          ModuleCat.restrictScalars.{u} (fromTop X W).hom)) (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((sectionsOverOpen X W).mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{u} (fromTop X W).hom).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The comparison transformation exhibiting the derived sections over `W` with scalars
restricted to `A` as a right derived functor of the `A`-linear termwise sections. -/
def linearComparison (W : Opens X.carrier) :
    homotopyLinearSections X W ⟶
      DerivedCategory.Qh ⋙ (derivedSectionsOverOpen X W ⋙ derivedRestrictScalars X W) :=
  (homotopyLinearSectionsIso X W).hom ≫
    Functor.whiskerRight (derivedSectionsOverOpenUnit X W) (derivedRestrictScalars X W) ≫
    (Functor.associator _ _ _).hom

/-- The derived sections over `W` with scalars restricted to `A` are a right derived functor of
the `A`-linear termwise sections: the unit of `RΓ(W, -)` is invertible at every K-injective
complex, and restriction of scalars carries that isomorphism to an isomorphism. -/
instance isRightDerivedFunctor_linearComparison (W : Opens X.carrier) :
    (derivedSectionsOverOpen X W ⋙ derivedRestrictScalars X W).IsRightDerivedFunctor
      (linearComparison X W) (quasiIsos X) := by
  apply isRightDerivedFunctor_of_isIso_app_isKInjective (homotopyLinearSections X W)
    (exists_quasiIso_isKInjective X)
  intro I hI
  have hunit :
      IsIso ((derivedSectionsOverOpenUnit X W).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopySectionsOverOpen X W) (exists_quasiIso_isKInjective X)).2 DerivedCategory.Qh
      (derivedSectionsOverOpen X W) (derivedSectionsOverOpenUnit X W) I hI
  dsimp only [linearComparison, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- **`A`-linear derived sections over `W` are the derived sections over `W` with scalars
restricted along `A = Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_X)`.**  This is the statement that justifies the
name: the only difference from the derived sections of Tag 0F16 is the ring of scalars. -/
def derivedLinearSectionsIso (W : Opens X.carrier) :
    derivedLinearSections X W ≅ derivedSectionsOverOpen X W ⋙ derivedRestrictScalars X W :=
  Functor.rightDerivedUnique (derivedLinearSections X W)
    (derivedSectionsOverOpen X W ⋙ derivedRestrictScalars X W) (derivedLinearSectionsUnit X W)
    (linearComparison X W) (quasiIsos X)

/-! ### Exactness -/

/-- **`A`-linear derived sections over an open are triangulated.**  Every object of `D(𝒪_X)` is
represented by a K-injective complex and the unit is an isomorphism there, so a distinguished
triangle may be completed inside the K-injective complexes. -/
theorem derivedLinearSections_isTriangulated (W : Opens X.carrier) :
    letI := Functor.IsRightDerivedFunctor.commShift (derivedLinearSections X W)
      (derivedLinearSectionsUnit X W) (quasiIsos X) ℤ
    (derivedLinearSections X W).IsTriangulated := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (linearSections X W)
    (derivedLinearSections X W) (derivedLinearSectionsUnit X W)

end Stacks.Cohomology.LinearDerivedSections

end
