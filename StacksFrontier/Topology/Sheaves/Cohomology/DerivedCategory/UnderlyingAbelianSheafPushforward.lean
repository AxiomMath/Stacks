module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
import StacksCore.Tactic.StacksAttribute

/-!
# The derived pushforward of the underlying abelian sheaf

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K` be an object of the
unbounded derived category `D(𝒪_X)`.  Writing `K_ab` for the image of `K` in the unbounded
derived category of abelian sheaves on `X`, the canonical comparison

`Rf_* K ⟶ Rf_*(K_ab)`

is an isomorphism in `D(Ab_Y)`.  This is [Stacks, Tag 0D5Y] part (2); part (1), the statement
for derived sections over an open, is
`Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetComparison_isIso`.

The construction of the right-hand side is unconditional.  Abelian sheaves on a topological
space form a Grothendieck abelian category, so every complex of abelian sheaves receives a
quasi-isomorphism from a K-injective one and the total right derived functor of degreewise
pushforward exists; this is
`Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.hasRightDerivedFunctor_abelianSheaves`,
applied here to degreewise abelian pushforward followed by localization.

## Main definitions

* `derivedAbelianPushforward`: the unbounded derived pushforward of abelian sheaves
  `Rf_* : D(Ab_X) ⥤ D(Ab_Y)`, with its canonical comparison
  `derivedAbelianPushforwardUnit`.
* `pushforwardForgetUnit`: the comparison on homotopy categories, built from the underived
  identity `f_* ∘ forget = forget ∘ f_*` and the comparison of `Rf_*` on abelian sheaves.
* `pushforwardForgetComparison`: the canonical map `Rf_* K ⟶ Rf_*(K_ab)`, as a morphism of
  functors `D(𝒪_X) ⥤ D(Ab_Y)`.

## Main results

* `abelianPushforward_hasRightDerivedFunctor`: the abelian derived pushforward exists,
  unconditionally.
* `isIso_derivedAbelianPushforwardUnit_app_of_isKInjective`: K-injective complexes of abelian
  sheaves compute `Rf_*`.
* `abelianPushforward_map_quasiIso_of_kInjectiveModule`: the abelian pushforward takes a
  K-injective resolution of the underlying abelian complex of a K-injective complex of
  `𝒪_X`-modules to a quasi-isomorphism.
* `pushforwardForgetComparison_isIso` (Tag 0D5Y, part (2)): the comparison is an isomorphism.

## Implementation notes

`pushforwardForgetComparison` is produced by the universal property of the right derived
functor, as the comparison of derived sections in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafCohomology` is.
The source `Rf_* ∘ forget` is a right derived functor of `f_* ∘ forget`, because the comparison
of `Rf_*` is invertible on K-injective complexes of `𝒪_X`-modules and stays so after applying
any functor; the target carries `pushforwardForgetUnit`; and `rightDerivedDesc` compares them.
The underived input is `ModulePushforwardComparison.modulePushforwardCompToSheafIso`, which is
`Iso.refl`: the underlying abelian sheaf of `f_* F` is `f_*` of the underlying abelian sheaf of
`F` on the nose, both being `V ↦ F(f⁻¹ V)`.

Invertibility is then the statement that the comparison is invertible on K-injective complexes
of `𝒪_X`-modules, and the content there is
`abelianPushforward_map_quasiIso_of_kInjectiveModule`.  That is where part (1) enters, and it
enters open by open: quasi-isomorphy of a morphism of complexes of abelian sheaves is detected
on the underlying complexes of presheaves, so on sections over each open `V ⊆ Y`, where
`(f_* C)(V) = C(f⁻¹ V)` holds by definition and part (1) — in the single-complex form
`Stacks.Cohomology.SupportedComplexes.abelianSections_map_quasiIso_of_kInjectiveModule` —
applies at the open `f⁻¹ V` of `X`.  No analogue of [Stacks, Tag 0BKJ] for abelian sheaves is
needed, and the source's route through the cohomology sheaves of Tag 0D5X is not taken.

**The derived categories.** The derived categories of `𝒪_X`-, `𝒪_Y`-modules and of abelian
sheaves on `X` and `Y` are taken at `CategoryTheory.HasDerivedCategory.standard`, the
localization of the homotopy category at the quasi-isomorphisms, installed as a file-level local
instance, as in part (1). `f` is a morphism of `AlgebraicGeometry.RingedSpace.{u, u}`.

## References

* [Stacks Project, Tag 0D5Y](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.ModulePushforwardComparison (abelianPushforward
  modulePushforwardCompToSheafIso)
open Stacks.Cohomology.SupportedComplexes (sheafQuasiIso_of_presheafQuasiIso
  abelianSections_map_quasiIso_of_kInjectiveModule)
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport (AbelianSheavesOnSpace
  abelianSheaves_isGrothendieckAbelian hasRightDerivedFunctor_abelianSheaves
  hasRightDerivedFunctor_moduleSheaves)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (pushforwardToDerivedCategory
  derivedPushforward derivedPushforwardUnit isIso_derivedPushforwardUnit_app_of_isKInjective
  isRightDerivedFunctor_of_isIso_app_isKInjective exists_quasiIso_isKInjective)

namespace Stacks.Cohomology.UnderlyingAbelianPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The derived pushforward of abelian sheaves -/

/-- Degreewise pushforward of complexes of abelian sheaves, followed by localization to the
derived category. -/
abbrev abelianPushforwardToDerived :
    HomotopyCategory (AbelianSheavesOnSpace X) (ComplexShape.up ℤ) ⥤
      DerivedCategory (AbelianSheavesOnSpace Y) :=
  (abelianPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **The abelian derived pushforward exists, unconditionally.**  Abelian sheaves on a space
form a Grothendieck abelian category, the site of opens being essentially small, so every
complex receives a quasi-isomorphism from a K-injective one and the total right derived functor
of degreewise pushforward exists. -/
instance abelianPushforward_hasRightDerivedFunctor :
    (abelianPushforwardToDerived f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor_abelianSheaves X _

/-- **The unbounded derived pushforward of abelian sheaves** `Rf_* : D(Ab_X) ⥤ D(Ab_Y)`, the
total right derived functor of degreewise pushforward followed by localization. -/
abbrev derivedAbelianPushforward :
    DerivedCategory (AbelianSheavesOnSpace X) ⥤ DerivedCategory (AbelianSheavesOnSpace Y) :=
  (abelianPushforwardToDerived f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))

/-- The canonical comparison from degreewise pushforward of abelian sheaves to the derived
pushforward. -/
abbrev derivedAbelianPushforwardUnit :
    abelianPushforwardToDerived f ⟶ DerivedCategory.Qh ⋙ derivedAbelianPushforward f :=
  (abelianPushforwardToDerived f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))

/-- A K-injective complex of abelian sheaves computes the abelian derived pushforward: on it
the canonical comparison `f_* I ⟶ Rf_* I` is invertible. -/
theorem isIso_derivedAbelianPushforwardUnit_app_of_isKInjective
    (I : CochainComplex (AbelianSheavesOnSpace X) ℤ) [I.IsKInjective] :
    IsIso ((derivedAbelianPushforwardUnit f).app
      ((HomotopyCategory.quotient (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)).obj I)) := by
  have := abelianSheaves_isGrothendieckAbelian X
  exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (C := AbelianSheavesOnSpace X) (H := DerivedCategory (AbelianSheavesOnSpace Y))
    (abelianPushforwardToDerived f) (derivedAbelianPushforward f)
    (derivedAbelianPushforwardUnit f) I

/-! ### The abelian pushforward of a K-injective resolution -/

/-- **The abelian pushforward takes a K-injective resolution of an underlying abelian complex
to a quasi-isomorphism.**  Let `I` be a K-injective complex of `𝒪_X`-modules, let `J` be a
K-injective complex of abelian sheaves on `X` and let `q : I_ab ⟶ J` be a quasi-isomorphism.
Then `f_* q` is a quasi-isomorphism.

Quasi-isomorphy of a morphism of complexes of abelian sheaves is detected on the underlying
complexes of presheaves, hence open by open; over an open `V ⊆ Y` the pushforward is sections
over `f⁻¹ V`, and there the claim is [Stacks, Tag 0D5Y] part (1) in the single-complex form
`Stacks.Cohomology.SupportedComplexes.abelianSections_map_quasiIso_of_kInjectiveModule`. -/
lemma abelianPushforward_map_quasiIso_of_kInjectiveModule
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective]
    (J : CochainComplex (AbelianSheavesOnSpace X) ℤ) [J.IsKInjective]
    (q : ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso q] :
    QuasiIso (((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  have hM (U : Opens X.carrier) :
      (homotopySectionsOnOpen (structureSheafRing X) U).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) :=
    hasRightDerivedFunctor_moduleSheaves X _
  have hA (U : Opens X.carrier) :
      (homotopyAbelianSectionsOnOpen X.carrier U).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)) :=
    hasRightDerivedFunctor_abelianSheaves X _
  apply sheafQuasiIso_of_presheafQuasiIso (Opens.grothendieckTopology Y.carrier)
    (((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  exact fun V => abelianSections_map_quasiIso_of_kInjectiveModule (structureSheafRing X)
    ((opensMap f).obj (unop V)) I J q

/-- The underlying abelian complex of a K-injective complex of `𝒪_X`-modules computes the
abelian derived pushforward, even though it is not itself K-injective.  Both it and its
K-injective resolution are carried to isomorphic objects by degreewise pushforward, by
`abelianPushforward_map_quasiIso_of_kInjectiveModule`. -/
lemma isIso_derivedAbelianPushforwardUnit_app_of_moduleKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((derivedAbelianPushforwardUnit f).app
      (((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I))) := by
  have := abelianSheaves_isGrothendieckAbelian X
  let A := AbelianSheavesOnSpace X
  let F := abelianPushforwardToDerived f
  let RF := derivedAbelianPushforward f
  let α := derivedAbelianPushforwardUnit f
  let K := ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  obtain ⟨J, q, _, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives K
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hαJ : IsIso (α.app (Q.obj J)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective F RF α J
  have hqD : IsIso (DerivedCategory.Qh.map (Q.map q)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Q.map q) ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).mpr hq)
  have hqF : IsIso (F.map (Q.map q)) := by
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (AbelianSheavesOnSpace Y) (ComplexShape.up ℤ)).map
        (((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map q)))
    exact (DerivedCategory.isIso_Qh_map_iff _).mpr
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
        (abelianPushforward_map_quasiIso_of_kInjectiveModule f I J q))
  have : IsIso ((DerivedCategory.Qh ⋙ RF).map (Q.map q)) := by
    change IsIso (RF.map (DerivedCategory.Qh.map (Q.map q)))
    infer_instance
  have hcomp : IsIso (α.app (Q.obj K) ≫ (DerivedCategory.Qh ⋙ RF).map (Q.map q)) := by
    rw [← α.naturality (Q.map q)]
    infer_instance
  exact ((isIso_comp_right_iff _ _).mp hcomp : IsIso (α.app (Q.obj K)))

/-! ### The comparison with the derived pushforward of sheaves of modules -/

/-- The comparison on homotopy categories: degreewise pushforward of a complex of
`𝒪_X`-modules, with the module structure forgotten, maps canonically to the abelian derived
pushforward of the underlying abelian complex.  It is the comparison of the abelian derived
pushforward, read through the identity `f_* ∘ forget = forget ∘ f_*`. -/
def pushforwardForgetUnit :
    pushforwardToDerivedCategory f ⋙ underlyingDerivedSheaf (structureSheafRing Y) ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf (structureSheafRing X) ⋙
        derivedAbelianPushforward f) :=
  (Functor.associator ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (underlyingDerivedSheaf (structureSheafRing Y))).hom ≫
    Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((SheafOfModules.toSheaf (structureSheafRing Y)).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardCompToSheafIso f)
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f))
          (ComplexShape.up ℤ)).symm).hom DerivedCategory.Qh ≫
    (Functor.associator
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
      ((abelianPushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedAbelianPushforwardUnit f) ≫
    (Functor.associator
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedAbelianPushforward f)).inv ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv
      (derivedAbelianPushforward f) ≫
    (Functor.associator DerivedCategory.Qh (underlyingDerivedSheaf (structureSheafRing X))
      (derivedAbelianPushforward f)).hom

/-- The comparison map of the derived pushforward of sheaves of modules, read in the derived
category of abelian sheaves on `Y`. -/
abbrev pushforwardForgetSourceUnit :
    pushforwardToDerivedCategory f ⋙ underlyingDerivedSheaf (structureSheafRing Y) ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward f ⋙ underlyingDerivedSheaf (structureSheafRing Y)) :=
  Functor.whiskerRight (derivedPushforwardUnit f) (underlyingDerivedSheaf (structureSheafRing Y)) ≫
    (Functor.associator DerivedCategory.Qh (derivedPushforward f)
      (underlyingDerivedSheaf (structureSheafRing Y))).hom

/-- `Rf_* ∘ forget` is a right derived functor of `f_* ∘ forget`: the comparison of `Rf_*` is
invertible on K-injective complexes of `𝒪_X`-modules, and stays so after applying any
functor. -/
instance isRightDerivedFunctor_pushforwardForgetSource :
    (derivedPushforward f ⋙ underlyingDerivedSheaf (structureSheafRing Y)).IsRightDerivedFunctor
      (pushforwardForgetSourceUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    (pushforwardToDerivedCategory f ⋙ underlyingDerivedSheaf (structureSheafRing Y))
    (exists_quasiIso_isKInjective X) DerivedCategory.Qh _ _ (fun I hI => ?_)
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  dsimp only [pushforwardForgetSourceUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app]
  rw [Category.comp_id]
  infer_instance

/-- **The canonical comparison of [Stacks, Tag 0D5Y] part (2)**, `Rf_* K ⟶ Rf_*(K_ab)`: the map
of functors `D(𝒪_X) ⥤ D(Ab_Y)` induced, through the universal property of `Rf_* ∘ forget` as a
right derived functor, by `pushforwardForgetUnit`. -/
def pushforwardForgetComparison :
    derivedPushforward f ⋙ underlyingDerivedSheaf (structureSheafRing Y) ⟶
      underlyingDerivedSheaf (structureSheafRing X) ⋙ derivedAbelianPushforward f :=
  (derivedPushforward f ⋙ underlyingDerivedSheaf (structureSheafRing Y)).rightDerivedDesc
    (pushforwardForgetSourceUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ (pushforwardForgetUnit f)

/-- **Stacks 0D5Y, part (2).**  The unbounded derived pushforward of a complex of
`𝒪_X`-modules, with the module structure forgotten, agrees canonically and naturally with the
unbounded derived pushforward of the underlying complex of abelian sheaves:
`Rf_* K ⟶ Rf_*(K_ab)` is an isomorphism in `D(Ab_Y)`.

The morphism `f` of ringed spaces is the only argument: there is no `HasRightDerivedFunctor`
precondition here, both derived pushforwards being supplied by the proved instances
`abelianPushforward_hasRightDerivedFunctor` and
`isRightDerivedFunctor_pushforwardForgetSource` above. -/
@[stacks 0D5Y "part (2)"]
theorem pushforwardForgetComparison_isIso :
    IsIso (Stacks.Cohomology.UnderlyingAbelianPushforward.pushforwardForgetComparison f) := by
  let Q := HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
    (ComplexShape.up ℤ)
  let γ := pushforwardForgetUnit f
  have hγ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
      IsIso (γ.app (Q.obj I)) := by
    have := isIso_derivedAbelianPushforwardUnit_app_of_moduleKInjective f I
    dsimp only [γ, pushforwardForgetUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (derivedPushforward f ⋙ underlyingDerivedSheaf (structureSheafRing Y))
    (pushforwardForgetSourceUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ γ).mp
    (Stacks.Cohomology.Localization.rightDerived_of_kInjectives
      (pushforwardToDerivedCategory f ⋙ underlyingDerivedSheaf (structureSheafRing Y))
      (underlyingDerivedSheaf (structureSheafRing X) ⋙ derivedAbelianPushforward f) γ hγ)

end Stacks.Cohomology.UnderlyingAbelianPushforward

end
