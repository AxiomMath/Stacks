module

public import StacksFrontier.AlgebraicGeometry.Quot.LeftDerivedPullbackData
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackExists
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsOfToposHom
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The pseudofunctoriality of the derived pullback on algebraic spaces

Stacks 08JX considers the functors `(g : T → B) ↦ H⁰(T, Lg^*K)` on the test schemes over an
algebraic space `B`.  Their restriction maps are derived inverse images read through the
composition comparison `L(f ≫ g)^* ≅ Lg^* ∘ Lf^*` of Stacks 0D6D, and their functor laws are the
coherence of that comparison.  This file constructs these data, the structure
`AlgebraicGeometry.Space.DerivedPullbackCoherence`.

## Main definitions

* `AlgebraicGeometry.Space.toposModulePullbackData` and
  `AlgebraicGeometry.Space.toposPullbackData`: the inverse image of `𝒪`-modules of Stacks 03LU,
  in the spelling of the direct-image adjunction and in the spelling the derived pullback is built
  from, as pullback pseudofunctor data.
* `AlgebraicGeometry.Space.homotopyPullbackData`: the same, degreewise on the homotopy categories
  of complexes.
* `AlgebraicGeometry.Space.toposDerivedPullbackData`: the derived pullbacks, with the
  comparisons induced by their universal property.
* `AlgebraicGeometry.Space.derivedPullbackCoherence`: the inhabitant of
  `AlgebraicGeometry.Space.DerivedPullbackCoherence`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedComp`: Stacks 0D6D for the derived pullback
  of algebraic spaces, the comparison `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` being invertible.
* `AlgebraicGeometry.Space.toposDerivedPullbackData_isCoherent`: the comparisons are
  associative and unital.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso`: `Lf^*𝒪_Y ≅ 𝒪_X`.

## Implementation notes

The underived inverse image of the derived pullback is
`AlgebraicGeometry.RingedToposHom.toModulesHom` of the morphism of small étale ringed topoi,
while the coherences of Stacks 03LU are stated for
`AlgebraicGeometry.Space.modulePullback`, whose spelling goes through
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`.  The two are equal, and the coherent
datum is transported along that equality by `CategoryTheory.PullbackData.transport`.

The general instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off: with
it in scope the abelian structure of the sheaves of modules is sought at a universe left
undetermined, which stalls elaboration of the localization functors.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaves of modules on the small étale ringed topos of an algebraic space, in the spelling
the derived pullback is built in. -/
abbrev toposModules (X : AlgebraicSpaces B S hS) : Type (u + 1) :=
  SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)

/-- The derived category of `𝒪`-modules on the small étale ringed topos of an algebraic space, in
the spelling the derived pullback is built in. -/
abbrev toposDerived (X : AlgebraicSpaces B S hS) : Type (u + 1) :=
  DerivedCategory (toposModules B S hS X)

/-- The inverse image of `𝒪`-modules along morphisms of algebraic spaces, with the comparisons of
Stacks 03LU, as a pullback pseudofunctor datum. -/
def toposModulePullbackData : PullbackData (AlgebraicSpaces B S hS) (toposModules B S hS) where
  pull f := modulePullback B S hS f
  idIso X := (modulePushforwardCoherence B S hS).modulePullbackIdIso X
  compIso f g := (modulePullbackCompIso B S hS f g).symm

/-- The inverse image of `𝒪`-modules is a coherent pullback pseudofunctor datum: Stacks 03LU with
its coherences. -/
theorem toposModulePullbackData_isCoherent : (toposModulePullbackData B S hS).IsCoherent where
  triangle_id _ hk := (modulePushforwardCoherence B S hS).modulePullbackTriangle_id hk
  triangle_comp hk hq hr hkr :=
    (modulePushforwardCoherence B S hS).modulePullbackTriangle_comp hk hq hr hkr

variable {B S hS} in
/-- The inverse image of modules along the morphism of small étale ringed topoi, in the spelling
the derived pullback is built from, is the inverse image of modules of Stacks 03LU. -/
def toposPullbackModulesIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ≅
      (toposModulePullbackData B S hS).pull f :=
  eqToIso (congrArg (fun h => h.pullbackModules)
    (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom (smallEtaleRingedToposHom B S hS f)))

variable {B S hS} in
/-- The inverse image of modules along the morphism of small étale ringed topoi is additive, at
the universes of the small étale ringed topoi. -/
instance toposPullbackModules_additive {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

variable {B S hS} in
/-- The inverse image of modules is additive. -/
instance toposModulePullbackData_additive {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((toposModulePullbackData B S hS).pull f).Additive :=
  Functor.additive_of_iso (toposPullbackModulesIso f)

/-- The inverse image of `𝒪`-modules along the morphisms of small étale ringed topoi, with the
comparisons of Stacks 03LU, as a coherent pullback pseudofunctor datum. -/
abbrev toposPullbackData : PullbackData (AlgebraicSpaces B S hS) (toposModules B S hS) :=
  (toposModulePullbackData B S hS).transport
    (fun f => (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules)
    (fun f => toposPullbackModulesIso f)

/-- The inverse image of `𝒪`-modules along the morphisms of small étale ringed topoi is a coherent
pullback pseudofunctor datum. -/
theorem toposPullbackData_isCoherent : (toposPullbackData B S hS).IsCoherent :=
  PullbackData.transport_isCoherent _ _ _ (toposModulePullbackData_isCoherent B S hS)

/-- The underived inverse image of complexes of `𝒪`-modules, on the homotopy categories, as a
coherent pullback pseudofunctor datum. -/
abbrev homotopyPullbackData :
    PullbackData (AlgebraicSpaces B S hS)
      (fun X => HomotopyCategory (toposModules B S hS X) (ComplexShape.up ℤ)) :=
  (toposPullbackData B S hS).toHomotopy

/-- The underived inverse image of complexes of `𝒪`-modules on the homotopy categories is a
coherent pullback pseudofunctor datum. -/
theorem homotopyPullbackData_isCoherent : (homotopyPullbackData B S hS).IsCoherent :=
  PullbackData.toHomotopy_isCoherent _ (toposPullbackData_isCoherent B S hS)

variable {B S hS}

/-- The localization of the homotopy category at the quasi-isomorphisms, into `D(𝒪_X)`, in the
spelling of the derived pullback. -/
abbrev toposQh (X : AlgebraicSpaces B S hS) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ) ⥤
        DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  DerivedCategory.Qh

/-- The derived pullback is a left derived functor of the degreewise inverse image, with the
comparison of Stacks 06YY. -/
instance isLeftDerivedFunctor_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    (smallEtaleDerivedModulePullback B S hS f).IsLeftDerivedFunctor
      (smallEtaleDerivedModulePullbackComparison B S hS f) (smallEtaleModuleQuasiIso B S hS Y) :=
  inferInstanceAs (((smallEtaleModulePullbackOnHomotopy B S hS f).totalLeftDerived
    DerivedCategory.Qh (smallEtaleModuleQuasiIso B S hS Y)).IsLeftDerivedFunctor
    ((smallEtaleModulePullbackOnHomotopy B S hS f).totalLeftDerivedCounit DerivedCategory.Qh
      (smallEtaleModuleQuasiIso B S hS Y)) (smallEtaleModuleQuasiIso B S hS Y))

/-- A natural transformation out of `D(𝒪_X)` is an isomorphism as soon as its components at the
K-flat complexes with flat terms are. -/
theorem isIso_of_isIso_app_isKFlat {X : AlgebraicSpaces B S hS} {E : Type*} [Category E]
    {F G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ⥤ E}
    (α : F ⟶ G)
    (h : ∀ K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ),
      IsKFlat (Y := smallEtaleRingedTopos B S hS X) K → IsIso (α.app ((toposQh X).obj K))) :
    IsIso α := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α fun D => ?_
  have : (toposQh X).EssSurj := Localization.essSurj _ (smallEtaleModuleQuasiIso B S hS X)
  obtain ⟨K, hK, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.hasResolutions_isKFlat'
      (Y := smallEtaleRingedTopos B S hS X) ((toposQh X).objPreimage D)
  have : IsIso ((toposQh X).map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
  let e : (toposQh X).obj K ≅ D := asIso ((toposQh X).map s) ≪≫ (toposQh X).objObjPreimageIso D
  have hα : α.app D = F.map e.inv ≫ α.app ((toposQh X).obj K) ≫ G.map e.hom := by
    rw [← α.naturality, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]
  have := h K hK
  rw [hα]
  infer_instance

/-- The comparison of Stacks 06YY is invertible at a K-flat complex with flat terms. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ))
    (hK : IsKFlat (Y := smallEtaleRingedTopos B S hS Y) K) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app K) :=
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.isIso_derivedPullbackComparison_app_isKFlat
    (smallEtaleRingedToposHom B S hS f) K hK

variable (B S hS)

/-- The comparison `L g ⋙ L f ⟶ L (f ≫ g)` of the derived pullbacks induced by the universal
property of `L (f ≫ g)`. -/
abbrev smallEtaleDerivedComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  PullbackData.derivedComp (H := fun X => HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
    (D := fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (homotopyPullbackData B S hS) (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f) f g

/-- The comparison `𝟭 ⟶ L (𝟙 X)` induced by the universal property of `L (𝟙 X)`. -/
abbrev smallEtaleDerivedIdLift (X : AlgebraicSpaces B S hS) :=
  PullbackData.derivedIdLift (H := fun X => HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
    (D := fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (homotopyPullbackData B S hS) (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f) X

variable {B S hS}

/-- At the image of a complex `K` on `Z`, the comparison `L g ⋙ L f ⟶ L (f ≫ g)` followed by the
comparison `L (f ≫ g) ∘ Q ⟶ Q ∘ (f ≫ g)^*` is the composite of the comparisons for `g` and `f`
with the inverse of the composition comparison of the underived inverse images. -/
theorem smallEtaleDerivedComp_fac {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedComp B S hS f g).app ((toposQh Z).obj K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (f ≫ g)).app K =
      (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedModulePullbackComparison B S hS g).app K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS f).app
          (((homotopyPullbackData B S hS).pull g).obj K) ≫
        (toposQh X).map (((homotopyPullbackData B S hS).compIso f g).inv.app K) :=
  PullbackData.derivedComp_fac (H := fun X => HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
    (D := fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (homotopyPullbackData B S hS) (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f) f g K

/-- At the image of a complex `K` on `X`, the comparison `𝟭 ⟶ L (𝟙 X)` followed by the comparison
`L (𝟙 X) ∘ Q ⟶ Q ∘ (𝟙 X)^*` is the image of the inverse of the unit comparison of the underived
inverse image. -/
theorem smallEtaleDerivedIdLift_fac (X : AlgebraicSpaces B S hS)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedIdLift B S hS X).app ((toposQh X).obj K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (𝟙 X)).app K =
      (toposQh X).map (((homotopyPullbackData B S hS).idIso X).inv.app K) :=
  PullbackData.derivedIdLift_fac (H := fun X => HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
    (D := fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (homotopyPullbackData B S hS) (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f) X K

/-- Stacks 0D6D for the inverse images of Stacks 03LU: the comparison
`L g ⋙ L f ⟶ L (f ≫ g)` is invertible. -/
instance isIso_smallEtaleDerivedComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (smallEtaleDerivedComp B S hS f g) := by
  refine isIso_of_isIso_app_isKFlat _ fun K hK => ?_
  have h₁ := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat (f ≫ g) K hK
  have h₂ := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat g K hK
  have h₃ := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f _
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
      (smallEtaleRingedToposHom B S hS g) K hK)
  have hQ : IsIso ((toposQh X).map (((homotopyPullbackData B S hS).compIso f g).inv.app K)) :=
    ((toposQh X).mapIso (((homotopyPullbackData B S hS).compIso f g).symm.app K)).isIso_hom
  have : IsIso ((smallEtaleDerivedComp B S hS f g).app ((toposQh Z).obj K) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS (f ≫ g)).app K) := by
    rw [smallEtaleDerivedComp_fac]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h₃ hQ)
  exact IsIso.of_isIso_comp_right _
    ((smallEtaleDerivedModulePullbackComparison B S hS (f ≫ g)).app K)

/-- The unit law of the derived pullbacks: the comparison `𝟭 ⟶ L (𝟙 X)` is invertible. -/
instance isIso_smallEtaleDerivedIdLift (X : AlgebraicSpaces B S hS) :
    IsIso (smallEtaleDerivedIdLift B S hS X) := by
  refine isIso_of_isIso_app_isKFlat _ fun K hK => ?_
  have h₁ := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat (𝟙 X) K hK
  have hQ : IsIso ((toposQh X).map (((homotopyPullbackData B S hS).idIso X).inv.app K)) :=
    ((toposQh X).mapIso (((homotopyPullbackData B S hS).idIso X).symm.app K)).isIso_hom
  have : IsIso ((smallEtaleDerivedIdLift B S hS X).app ((toposQh X).obj K) ≫
      (smallEtaleDerivedModulePullbackComparison B S hS (𝟙 X)).app K) := by
    rw [smallEtaleDerivedIdLift_fac]
    exact hQ
  exact IsIso.of_isIso_comp_right _ ((smallEtaleDerivedModulePullbackComparison B S hS (𝟙 X)).app K)

variable (B S hS)

/-- The derived pullbacks on algebraic spaces, with the composition comparison of Stacks 0D6D and
the unit law, as a pullback pseudofunctor datum. -/
abbrev toposDerivedPullbackData :
    PullbackData (AlgebraicSpaces B S hS)
      (fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  PullbackData.leftDerived (H := fun X => HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
    (D := fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (homotopyPullbackData B S hS) (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
    (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
    (hid := fun X => isIso_smallEtaleDerivedIdLift X)

/-- The derived pullbacks on algebraic spaces form a coherent pullback pseudofunctor datum: the
composition comparison of Stacks 0D6D is associative and unital. -/
theorem toposDerivedPullbackData_isCoherent :
    (toposDerivedPullbackData B S hS).IsCoherent :=
  PullbackData.leftDerived_isCoherent (H := fun X => HomotopyCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
    (D := fun X => DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (fun X => toposQh X) (fun X => smallEtaleModuleQuasiIso B S hS X)
    (homotopyPullbackData B S hS) (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
    (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
    (hid := fun X => isIso_smallEtaleDerivedIdLift X) (homotopyPullbackData_isCoherent B S hS)

variable {B S hS}

/-- The structure sheaf placed in degree zero, as an object of the homotopy category. -/
abbrev unitComplex (X : AlgebraicSpaces B S hS) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj
    (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))

/-- The derived pullback of the structure sheaf is the structure sheaf: `Lf^*𝒪_Y ≅ 𝒪_X`. -/
def smallEtaleDerivedPullbackUnitComplexIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleDerivedModulePullback B S hS f).obj ((toposQh Y).obj (unitComplex Y)) ≅
      (toposQh X).obj (unitComplex X) :=
  haveI := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isKFlat f (unitComplex Y)
    (Stacks.Cohomology.LerayOfToposHom.isKFlat_single_unit (smallEtaleRingedTopos B S hS Y))
  asIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app (unitComplex Y)) ≪≫
    (toposQh X).mapIso ((HomotopyCategory.quotient _ _).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
          ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules) _ 0).app _ ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso
          ((toposPullbackModulesIso f).app _ ≪≫ modulePullbackUnitIso B S hS f)))

variable (B S hS)

/-- The pseudofunctoriality of the derived pullback of `𝒪`-modules on algebraic spaces: the unit
law, the composition comparison of Stacks 0D6D, the identification `Lf^*𝒪_Y ≅ 𝒪_X`, and the
coherence of the first two. -/
def derivedPullbackCoherence :
    DerivedPullbackCoherence B S hS (fun _ => inferInstance) where
  idIso X := (toposDerivedPullbackData B S hS).idIso X
  compIso f g := (toposDerivedPullbackData B S hS).compIso f g
  unitPullIso {_ _} f :=
    (smallEtaleDerivedModulePullback B S hS f).mapIso
        ((DerivedCategory.singleFunctorIsoCompQh _ 0).app _) ≪≫
      smallEtaleDerivedPullbackUnitComplexIso f ≪≫
      ((DerivedCategory.singleFunctorIsoCompQh _ 0).app _).symm
  isCoherent := toposDerivedPullbackData_isCoherent B S hS

end AlgebraicGeometry.Space
