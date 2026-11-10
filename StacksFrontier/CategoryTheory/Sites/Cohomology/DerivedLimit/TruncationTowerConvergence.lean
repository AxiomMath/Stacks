module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExistsKInjectiveResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLeffler
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim
public import StacksCore.Tactic.StacksAttribute

/-! # Convergence of the truncation tower on a ringed site

Let `(C, O)` be a ringed site and let `E` be an object of the derived category of `O`-modules.
Suppose a subset `B` of the objects of `C` is large enough to cover every object, and that each
`V ∈ B` carries a function `p(V, -) : ℤ → ℤ` and a cofinal system of coverings of `V` on whose
members `H^p(V_i, H^{m - p}(E)) = 0` whenever `p > p(V, m)`. Then the canonical map from `E` to
the derived limit of its truncation tower `n ↦ τ_{≥ -n} E` is an isomorphism.

The argument is local and degreewise. Fix `m`. For `n ≥ -m` the map `E ⟶ τ_{≥ -n} E` is already an
isomorphism on `H^m`, so it suffices to find, for each `V ∈ B`, a stage `n(V) ≥ -m` at which
`H^m(R lim τ_{≥ -n} E)(V) ⟶ H^m(τ_{≥ -n(V)} E)(V)` is injective: the composite through it is then
bijective, forcing `H^m(E) ⟶ H^m(R lim τ_{≥ -n} E)` to be an isomorphism on sections over a
covering family, hence an isomorphism. Injectivity at the stage
`n(V) = 1 + max {-m, p(V, m-1) - m, -1 + p(V, m) - m, -2 + p(V, m+1) - m}`
comes from the distinguished triangles `H^{-n-1}(E)[n+1] ⟶ τ_{≥ -(n+1)} E ⟶ τ_{≥ -n} E` of
Derived Categories, Remark 08J5: the choice of `n(V)` makes the three cohomology groups
`H^{m+n}(V_i, H^{-n-1}(E))`, `H^{m+n+1}(V_i, H^{-n-1}(E))` and `H^{m+n+2}(V_i, H^{-n-1}(E))`
vanish, so the tower is constant on `H^{m-1}` and `H^m` over every member of every distinguished
covering of `V`.

## Main results

* `Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower`: the convergence result.

## Implementation notes

The structure sheaf may be any sheaf of rings: the argument uses only the abelian category of its
modules. The site objects, site morphisms, rings, and modules have independent universes, as in
`Stacks.Cohomology.moduleCohomology`. Covering families are indexed in the maximum of the two site
universes, as in `Stacks.Cohomology.CofinalCoveringSystem`.

A covering family is represented by a `PreZeroHypercover`, and is a covering exactly when the
sieve it generates lies in the topology. Cofinality is stated directly as cofinality under
refinement, matching the fields of `Stacks.Cohomology.CofinalCoveringSystem`; the three hypotheses
`Cov`, `Cov_isCover` and `Cov_cofinal` are that structure unbundled, and are reassembled into it
where the sheafification argument needs it. Cohomology over an object is
`Stacks.Cohomology.moduleCohomology`; the vanishing hypothesis quantifies only over natural
numbers `p`, since cohomology in negative degrees vanishes anyway, which makes the hypothesis
weaker than the source's and so the statement stronger.

The truncation tower is `Stacks.DerivedLimit.truncGETower`. A derived limit is presented by its
defining distinguished triangle — the unfolding of
`CategoryTheory.Pretriangulated.IsDerivedLimit` — rather than by that predicate, so that the
comparison map `c` can be named; `hc` then requires `c` to have the canonical truncation maps
`truncGEπ` as all of its components, which pins it to the canonical map of Remark 0H72 rather
than to an arbitrary map to an arbitrary derived limit. This records both the construction and
its canonical compatibility.

Sheaves of modules on the site are compared with presheaves of modules, and the right derived
functors of evaluation with those of the presheaf-level sections functor, because the vanishing
hypothesis is about the former while the Mittag-Leffler and `R^1 lim` input is about the latter.
The comparison isomorphisms for an exact functor on homotopy categories are taken from
`Stacks.Cohomology.SiteCohomologyPresheaf` (Tag 0BKV), which is opened below for them.

## References

* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u wRing wModule w

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

open SiteCohomologyPresheaf
open Stacks.Homology (mapHomotopyCategoryIso homotopyHomologyIso)

/-- For an injective resolution `I` of `M`, the degree-`n` cohomology of the image in the derived
category of `F` applied degreewise to `I` is the classical right derived functor `Rⁿ F M`. -/
private def homologyDerivedImageResolutionIso
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).obj (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (injectiveResolution M).cochainComplex)) ≅
      (F.rightDerived n).obj M := by
  let I := injectiveResolution M
  exact (DerivedCategory.homologyFunctorFactors B (n : ℤ)).app _ ≪≫
    (HomologicalComplex.homologyFunctor B (.up ℤ) (n : ℤ)).mapIso
      (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat I.cocomplex) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (by rfl) ≪≫
    (I.isoRightDerivedObj F n).symm

/-- For an object `M` placed in degree `0`, the degree-`n` cohomology of the right derived functor
of `F` on the bounded-below derived category is the classical right derived functor `Rⁿ F M`. -/
private def rightDerivedFunctorPlusSingleIso
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (M : A) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≅
      (F.rightDerived n).obj M := by
  let I := injectiveResolution M
  let K : HomotopyCategory.Plus A :=
    (HomotopyCategory.Plus.quotient A).obj ⟨I.cochainComplex, 0, inferInstance⟩
  have : ∀ i : ℤ, Injective (K.obj.as.X i) := by
    intro i
    change Injective (I.cochainComplex.X i)
    infer_instance
  let e : (DerivedCategory.Plus.singleFunctor A 0).obj M ≅ DerivedCategory.Plus.Qh.obj K :=
    DerivedCategory.Plus.ι.preimageIso
      (((DerivedCategory.singleFunctorIsoCompQ A 0).app M) ≪≫
        asIso (DerivedCategory.Q.map I.ι') ≪≫
        ((DerivedCategory.quotientCompQhIso A).app I.cochainComplex).symm)
  let e' : DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
    DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso e) ≪≫
      (DerivedCategory.Plus.ι.mapIso (asIso (F.rightDerivedFunctorPlusUnith.app K))).symm ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app I.cochainComplex) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  exact (DerivedCategory.homologyFunctor B (n : ℤ)).mapIso e' ≪≫
    homologyDerivedImageResolutionIso F M n

/-- For a right derived functor `RF` of `F` on the unbounded derived category, in the presence of
`K`-injective resolutions, the degree-`n` cohomology of `RF` applied to an object `M` placed in
degree `0` is the classical right derived functor `Rⁿ F M`. -/
private def rightDerivedSingleIso
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).obj
      (RF.obj ((DerivedCategory.singleFunctor A 0).obj M)) ≅ (F.rightDerived n).obj M := by
  let I := injectiveResolution M
  let K := (HomotopyCategory.quotient A (.up ℤ)).obj I.cochainComplex
  have hI : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  have : IsIso (α.app K) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) hres).2
        DerivedCategory.Qh RF α I.cochainComplex hI
  let e : (DerivedCategory.singleFunctor A 0).obj M ≅ DerivedCategory.Qh.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ A 0).app M ≪≫
      asIso (DerivedCategory.Q.map I.ι') ≪≫
      ((DerivedCategory.quotientCompQhIso A).app I.cochainComplex).symm
  let e' : RF.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
    RF.mapIso e ≪≫ (asIso (α.app K)).symm ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app I.cochainComplex) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  exact (DerivedCategory.homologyFunctor B (n : ℤ)).mapIso e' ≪≫
    homologyDerivedImageResolutionIso F M n

/-- For an object `M` placed in degree `a`, the degree-`m` cohomology of the right derived functor
of `F` on the bounded-below derived category is `Rⁿ F M`, where `n = m - a`. -/
private def rightDerivedFunctorPlusSingleShiftIso
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (M : A) (a m : ℤ)
    (n : ℕ) (hn : m - a = n) :
    (DerivedCategory.Plus.homologyFunctor B m).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A a).obj M)) ≅
      (F.rightDerived n).obj M := by
  let R := F.rightDerivedFunctorPlus
  letI := Functor.IsRightDerivedFunctor.commShift R F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) ℤ
  let e : (DerivedCategory.Plus.singleFunctor A a).obj M ≅
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)⟦-a⟧ :=
    ((DerivedCategory.Plus.singleFunctors A).shiftIso (-a) a 0 (by omega)).symm.app M
  exact (DerivedCategory.Plus.homologyFunctor B m).mapIso
      (R.mapIso e ≪≫ (R.commShiftIso (-a)).app _) ≪≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso (-a) m (n : ℤ) (by omega)).app _ ≪≫
    rightDerivedFunctorPlusSingleIso F M n

/-- Postcomposition with an exact functor commutes with right derived functors:
`G (Rⁿ F M) ≅ Rⁿ (F ⋙ G) M`. -/
@[sga "4 V 2.5.2" "partial"]
noncomputable def rightDerivedExactPostcompositionIso
    {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    {B : Type*} [Category* B] [Abelian B]
    {D : Type*} [Category* D] [Abelian D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (M : A) (n : ℕ) :
    G.obj ((F.rightDerived n).obj M) ≅ ((F ⋙ G).rightDerived n).obj M := by
  let I := injectiveResolution M
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  exact G.mapIso (I.isoRightDerivedObj F n) ≪≫
    G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ n).app K) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ n).app
      ((G.mapHomologicalComplex _).obj K)).symm ≪≫
    (I.isoRightDerivedObj (F ⋙ G) n).symm

/-- An isomorphism of additive functors induces an isomorphism of their degree-`n` right derived
functors. -/
noncomputable def rightDerivedIsoOfFunctorIso
    {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
    {B : Type*} [Category* B] [Abelian B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n := by
  let R := injectiveResolutions A
  let e₀ : F.mapHomotopyCategory (ComplexShape.up ℕ) ≅
      G.mapHomotopyCategory (ComplexShape.up ℕ) := {
    hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℕ)
    inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℕ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
      NatTrans.mapHomotopyCategory_id] }
  let e' := Functor.isoWhiskerLeft R e₀
  simpa [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory, R] using
    Functor.isoWhiskerRight e' (HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) n)

/-! The two vanishing statements for an eventually constant tower of abelian groups are not
restated here: `isZero_firstDerivedLimit_of_eventually_iso` and
`isZero_cokernel_difference_of_eventually_iso` of
`StacksFrontier/Homology/DerivedCategory/InverseSystem/MonoHomologyProjection.lean` are the
same statements, public, and that module is already a `public import` of this file. -/

/-- Evaluation of sheaves of `O`-modules at an object `U` of the site, as a functor to modules over
the ring `O(U)`. -/
private abbrev moduleEvaluation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    (U : C) :
    CategoryTheory.Functor (SheafOfModules.{wModule} O)
      (ModuleCat.{wModule} (O.obj.obj (.op U))) :=
  SheafOfModules.evaluation O (.op U)

/-- Evaluation of sheaves of `O`-modules at an object of the site is an additive functor. -/
private lemma moduleEvaluation_additive
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] (U : C) :
    (moduleEvaluation O U).Additive := by
  dsimp [moduleEvaluation, SheafOfModules.evaluation]
  infer_instance

attribute [local instance] moduleEvaluation_additive

/-- Evaluation of sheaves of `O`-modules at `U`, viewed as a functor to abelian groups by lifting
universes and forgetting the module structure. -/
private abbrev moduleEvaluationToAddCommGrp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] (U : C) :
    CategoryTheory.Functor (SheafOfModules.{wModule} O)
      AddCommGrpCat.{max wRing wModule} :=
  moduleEvaluation O U ⋙
    ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
    forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
      AddCommGrpCat.{max wRing wModule}

/-- The functor from the homotopy category of complexes of sheaves of `O`-modules to the derived
category of abelian groups given by evaluating at `U` degreewise and localizing. -/
private abbrev homotopySectionsOverObject
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] (U : C) :
    HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{max wRing wModule} :=
  (moduleEvaluationToAddCommGrp O U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Degreewise evaluation at `U` admits a right derived functor with respect to the
quasi-isomorphisms, the category of sheaves of `O`-modules being Grothendieck abelian. -/
private lemma homotopySectionsOverObject_hasRightDerivedFunctor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [IsGrothendieckAbelian (SheafOfModules.{wModule} O)] (U : C) :
    (homotopySectionsOverObject O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck (SheafOfModules.{wModule} O)
    (homotopySectionsOverObject O U)

attribute [local instance] homotopySectionsOverObject_hasRightDerivedFunctor

/-- The total right derived functor of degreewise evaluation at `U`, from the derived category of
sheaves of `O`-modules to the derived category of abelian groups. -/
private noncomputable abbrev derivedSectionsOverObject
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    [IsGrothendieckAbelian (SheafOfModules.{wModule} O)] (U : C) :
    DerivedCategory (SheafOfModules.{wModule} O) ⥤
      DerivedCategory AddCommGrpCat.{max wRing wModule} :=
  (homotopySectionsOverObject O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))

/-- The abelian group underlying the cohomology module `Hⁿ(U, M)` of a sheaf of `O`-modules is the
degree-`n` right derived functor of evaluation at `U` with values in abelian groups. -/
private noncomputable def moduleCohomologyToUnderlyingRightDerivedIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (U : C) (M : SheafOfModules.{wModule} O) (n : ℕ) :
    ((ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
      forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
        AddCommGrpCat.{max wRing wModule}).obj)
      (moduleCohomology O U n M) ≅
      ((moduleEvaluationToAddCommGrp O U).rightDerived n).obj M := by
  let G : CategoryTheory.Functor (ModuleCat.{wModule} (O.obj.obj (.op U)))
      AddCommGrpCat.{max wRing wModule} :=
    ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
      forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
        AddCommGrpCat.{max wRing wModule}
  letI : G.Additive := by dsimp [G]; infer_instance
  simpa [moduleCohomology, moduleEvaluationToAddCommGrp,
    moduleEvaluation, G] using
    (rightDerivedExactPostcompositionIso (moduleEvaluation O U) G M n)

/-- Evaluation of presheaves of `O`-modules at an object `U`, viewed as a functor to abelian groups
by lifting universes and forgetting the module structure. -/
private abbrev presheafModuleEvaluationToAddCommGrp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing}) (U : C) :
    PresheafOfModules.{wModule} O.obj ⥤
      AddCommGrpCat.{max wRing wModule} :=
  PresheafOfModules.evaluation.{wModule, v, u, wRing} O.obj (.op U) ⋙
    (ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
      forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
        AddCommGrpCat.{max wRing wModule})

/-- The sections over `U` of the degree-`n` right derived functor of the forgetful functor from
sheaves to presheaves of `O`-modules form, as an abelian group, the cohomology `Hⁿ(U, M)`. -/
private noncomputable def moduleCohomologyToPresheafRightDerivedIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (U : C) (M : SheafOfModules.{wModule} O) (n : ℕ) :
    (presheafModuleEvaluationToAddCommGrp O U).obj
        (((SheafOfModules.forget O).rightDerived n).obj M) ≅
      (ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
        forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
          AddCommGrpCat.{max wRing wModule}).obj
        (moduleCohomology O U n M) := by
  let F := SheafOfModules.forget O
  let G := presheafModuleEvaluationToAddCommGrp O U
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : G.Additive := by dsimp [G, presheafModuleEvaluationToAddCommGrp]; infer_instance
  let E := PresheafOfModules.evaluation O.obj (.op U)
  let H := ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U))
  let K := forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
    AddCommGrpCat.{max wRing wModule}
  let eComp : moduleEvaluationToAddCommGrp O U ≅ F ⋙ G :=
    (Functor.associator (F ⋙ E) H K) ≪≫ Functor.associator F E (H ⋙ K)
  have hFG :
      G.obj ((F.rightDerived n).obj M) ≅
        ((F ⋙ G).rightDerived n).obj M := by
    simpa [F, G, presheafModuleEvaluationToAddCommGrp] using
      (rightDerivedExactPostcompositionIso F G M n)
  exact (hFG.trans ((rightDerivedIsoOfFunctorIso eComp.symm n).app M)).trans
    (moduleCohomologyToUnderlyingRightDerivedIso O U M n).symm

/-- The sections over `U` of the degree-`n` right derived functor of the forgetful functor from
sheaves to presheaves of `O`-modules form the cohomology module `Hⁿ(U, M)`. -/
private noncomputable def moduleCohomologyToPresheafModuleRightDerivedIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (U : C) (M : SheafOfModules.{wModule} O) (n : ℕ) :
    (PresheafOfModules.evaluation O.obj (.op U)).obj
        (((SheafOfModules.forget O).rightDerived n).obj M) ≅
      moduleCohomology O U n M := by
  let F := SheafOfModules.forget O
  let G := PresheafOfModules.evaluation O.obj (.op U)
  let E := moduleEvaluation O U
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : G.Additive := by dsimp [G]; infer_instance
  let e : E ≅ F ⋙ G := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl
  exact (rightDerivedExactPostcompositionIso F G M n).trans
    ((rightDerivedIsoOfFunctorIso e.symm n).app M)

/-- If the cohomology module `Hⁿ(U, M)` vanishes, then so does the degree-`n` right derived functor
of evaluation at `U` with values in abelian groups, applied to `M`. -/
private lemma isZero_moduleEvaluationRightDerived_of_isZero_moduleCohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (U : C) (M : SheafOfModules.{wModule} O) (n : ℕ)
    (h : IsZero (moduleCohomology O U n M)) :
    IsZero (((moduleEvaluationToAddCommGrp O U).rightDerived n).obj M) := by
  let G : CategoryTheory.Functor (ModuleCat.{wModule} (O.obj.obj (.op U)))
      AddCommGrpCat.{max wRing wModule} :=
    ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
      forget₂ (ModuleCat.{max wModule (wRing)} (O.obj.obj (.op U)))
        AddCommGrpCat.{max wRing wModule}
  exact (G.map_isZero h).of_iso (moduleCohomologyToUnderlyingRightDerivedIso O U M n).symm

/-- The functor from the homotopy category of complexes of sheaves of `O`-modules to the derived
category of presheaves of `O`-modules induced degreewise by the forgetful functor. -/
private abbrev moduleHomotopySectionsPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] :
    HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (PresheafOfModules.{wModule} O.obj) :=
  (SheafOfModules.forget O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The degreewise forgetful functor to complexes of presheaves of `O`-modules admits a right
derived functor with respect to the quasi-isomorphisms. -/
private lemma moduleHomotopySectionsPresheaf_hasRightDerivedFunctor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [IsGrothendieckAbelian (SheafOfModules.{wModule} O)] :
    (moduleHomotopySectionsPresheaf O).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck
    (SheafOfModules.{wModule} O) (moduleHomotopySectionsPresheaf O)

attribute [local instance] moduleHomotopySectionsPresheaf_hasRightDerivedFunctor

/-- The total right derived functor of the forgetful functor from sheaves of `O`-modules to
presheaves of `O`-modules, between the two derived categories. -/
private noncomputable abbrev moduleDerivedSectionsPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    [IsGrothendieckAbelian (SheafOfModules.{wModule} O)] :
    DerivedCategory (SheafOfModules.{wModule} O) ⥤
      DerivedCategory (PresheafOfModules.{wModule} O.obj) :=
  (moduleHomotopySectionsPresheaf O).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))

/-- Sheafifying the degree-`q` cohomology presheaf of a complex of sheaves of `O`-modules, computed
in the derived category of presheaves, recovers its degree-`q` cohomology sheaf; an isomorphism of
functors on the homotopy category. -/
private noncomputable def moduleHomotopySheafificationHomologyIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] (q : ℤ) :
    (moduleHomotopySectionsPresheaf O ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q) ⋙
        PresheafOfModules.sheafification (𝟙 O.obj) ≅
      HomotopyCategory.homologyFunctor (SheafOfModules.{wModule} O)
        (ComplexShape.up ℤ) q := by
  let A := SheafOfModules.{wModule} O
  let P := PresheafOfModules.{wModule} O.obj
  let c := ComplexShape.up ℤ
  let F := SheafOfModules.forget O
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let HqP := DerivedCategory.homologyFunctor P q
  let hP := HomotopyCategory.homologyFunctor P c q
  let hA := HomotopyCategory.homologyFunctor A c q
  haveI : PreservesFiniteColimits a := by
    have hbig :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).leftAdjoint_preservesColimits
    constructor
    intro K _ _
    exact hbig.preservesColimitsOfShape
  haveI : a.Additive := by
    have : a.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_preserves_terminal_object
    have hbp : PreservesBinaryBiproducts a :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts a
    exact Functor.additive_of_preservesBinaryBiproducts a
  haveI : PreservesFiniteLimits a := by infer_instance
  let Fmap := F.mapHomotopyCategory c
  let amap := a.mapHomotopyCategory c
  let eL : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ a ≅
      Fmap ⋙ ((DerivedCategory.Qh ⋙ HqP) ⋙ a) :=
    Functor.isoWhiskerRight (Functor.associator Fmap DerivedCategory.Qh HqP) a ≪≫
      Functor.associator Fmap (DerivedCategory.Qh ⋙ HqP) a
  let eFactor : (DerivedCategory.Qh ⋙ HqP) ⋙ a ≅ hP ⋙ a :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh P q) a
  let eH : Fmap ⋙ (hP ⋙ a) ≅ Fmap ⋙ (amap ⋙ hA) :=
    Functor.isoWhiskerLeft Fmap (by simpa [amap, hP, hA, c] using homotopyHomologyIso a q)
  let eComp : Fmap ⋙ (amap ⋙ hA) ≅ (F ⋙ a).mapHomotopyCategory c ⋙ hA :=
    (Functor.associator Fmap amap hA).symm ≪≫
      (by
        simpa [Fmap, amap] using
          Functor.isoWhiskerRight
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ a)) c) hA)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  have hCounit : IsIso adj.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    exact Adjunction.instIsIsoAppCounitOfFullOfFaithful adj G
  letI : IsIso adj.counit := hCounit
  let eF : F ⋙ a ≅ 𝟭 A := @asIso _ _ _ _ adj.counit hCounit
  let eHF : (F ⋙ a).mapHomotopyCategory c ⋙ hA ≅ hA := by
    let eId : (F ⋙ a).mapHomotopyCategory c ≅ (𝟭 A).mapHomotopyCategory c :=
      mapHomotopyCategoryIso eF c
    let idIso : (𝟭 A).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory A c) := by
      refine NatIso.ofComponents (fun K => Iso.refl K) ?_
      intro K L f
      obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨L₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
      obtain ⟨f₀, rfl⟩ := (HomotopyCategory.quotient A c).map_surjective f
      rw [Functor.mapHomotopyCategory_map]
      have hf : ((𝟭 A).mapHomologicalComplex c).map f₀ = f₀ := by
        ext i
        rfl
      rw [hf]
      change (HomotopyCategory.quotient A c).map f₀ ≫ 𝟙 _ =
        𝟙 _ ≫ (HomotopyCategory.quotient A c).map f₀
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    exact Functor.isoWhiskerRight eId hA ≪≫
      Functor.isoWhiskerRight idIso hA ≪≫ Functor.leftUnitor hA
  have hmain : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ a ≅ hA :=
    eL ≪≫ Functor.isoWhiskerLeft Fmap eFactor ≪≫ eH ≪≫ eComp ≪≫ eHF
  simpa [moduleHomotopySectionsPresheaf, Fmap, HqP, hP, hA, F, A, P, c] using hmain

/-- Composing the total right derived functor of `F` with degree-`q` cohomology and an arbitrary
functor `G` computes the total right derived functor of `F ⋙ H^q ⋙ G`. -/
private noncomputable def moduleTotalDerivedHomologyPostcompIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [IsGrothendieckAbelian (SheafOfModules.{wModule} O)]
    {B : Type*} [Category B] [Abelian B] {D : Type*} [Category D]
    (F : HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory B)
    (G : B ⥤ D) (q : ℤ) :
    (F.totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ⋙
      DerivedCategory.homologyFunctor B q ⋙ G) ≅
      (F ⋙ DerivedCategory.homologyFunctor B q ⋙ G).totalRightDerived
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) := by
  let A := SheafOfModules.{wModule} O
  let c := ComplexShape.up ℤ
  let W := HomotopyCategory.quasiIso A c
  let Hq := DerivedCategory.homologyFunctor B q
  let S : HomotopyCategory A c ⥤ D := F ⋙ Hq ⋙ G
  let R := F.totalRightDerived DerivedCategory.Qh W
  let T : DerivedCategory A ⥤ D := R ⋙ Hq ⋙ G
  let R0 := S.totalRightDerived DerivedCategory.Qh W
  let α0 := S.totalRightDerivedUnit DerivedCategory.Qh W
  let αF := F.totalRightDerivedUnit DerivedCategory.Qh W
  let β : S ⟶ DerivedCategory.Qh ⋙ T :=
    (Functor.associator F Hq G).hom ≫
      Functor.whiskerRight αF (Hq ⋙ G) ≫
      (Functor.associator DerivedCategory.Qh R (Hq ⋙ G)).hom
  have hpt :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      S (Stacks.Injectives.exists_kInjective_resolution_of_grothendieck (C := A))
  have hptF :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      F (Stacks.Injectives.exists_kInjective_resolution_of_grothendieck (C := A))
  let t := R0.rightDerivedDesc α0 W T β
  have ht : ∀ Y : DerivedCategory A, IsIso (t.app Y) := by
    intro Y
    let K := DerivedCategory.Qh.objPreimage Y
    obtain ⟨K₀, hK₀⟩ := HomotopyCategory.quotient_obj_surjective K
    let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj K₀
    let f := (Stacks.Injectives.kInjectiveResolutionInclusion A).app K₀
    have hI : I.IsKInjective := by infer_instance
    have hf : QuasiIso f := by infer_instance
    have hW : W ((HomotopyCategory.quotient A c).map f) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
    have hq : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A c).map f)) :=
      (Localization.inverts DerivedCategory.Qh W) _ hW
    have eK : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj K₀) ≅ Y := by
      rw [hK₀]
      exact DerivedCategory.Qh.objObjPreimageIso Y
    let eY : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I) ≅ Y :=
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A c).map f))).symm ≪≫ eK
    have hα0 : IsIso (α0.app ((HomotopyCategory.quotient A c).obj I)) :=
      hpt.2 DerivedCategory.Qh R0 α0 I hI
    have hαF : IsIso (αF.app ((HomotopyCategory.quotient A c).obj I)) :=
      hptF.2 DerivedCategory.Qh R αF I hI
    have hmap : IsIso ((Hq ⋙ G).map
        (αF.app ((HomotopyCategory.quotient A c).obj I))) := by
      apply Functor.map_isIso
    have hβ : IsIso (β.app ((HomotopyCategory.quotient A c).obj I)) := by
      dsimp [β]
      let : IsIso (𝟙 (G.obj (Hq.obj
          (F.obj ((HomotopyCategory.quotient A c).obj I))))) := Iso.isIso_hom (Iso.refl _)
      let : IsIso (𝟙 (G.obj (Hq.obj
          (R.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I)))))) :=
        Iso.isIso_hom (Iso.refl _)
      have hm : IsIso
          (G.map (Hq.map (αF.app ((HomotopyCategory.quotient A c).obj I))) ≫ 𝟙 _) :=
        (isIso_comp_right_iff _ _).2 hmap
      exact (isIso_comp_left_iff _ _).2 hm
    have hfac := R0.rightDerived_fac_app α0 W T β ((HomotopyCategory.quotient A c).obj I)
    have htI : IsIso (t.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A c).obj I))) := by
      have hcomp : IsIso
          (α0.app ((HomotopyCategory.quotient A c).obj I) ≫
            t.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I))) := by
        rw [hfac]
        exact hβ
      exact (isIso_comp_left_iff (α0.app _) _).mp hcomp
    have hnat := t.naturality eY.hom
    have hcomp : IsIso
        (t.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A c).obj I)) ≫
          T.map eY.hom) := by infer_instance
    rw [← hnat] at hcomp
    exact (isIso_comp_left_iff _ _).mp hcomp
  haveI : IsIso t := NatIso.isIso_of_isIso_app t
  exact (asIso t).symm

/-- Sheafifying the degree-`q` cohomology presheaf of the total right derived forgetful functor
recovers the degree-`q` cohomology functor on the derived category of sheaves of `O`-modules. -/
private noncomputable def moduleSheafificationCohomologyPresheafIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    [IsGrothendieckAbelian (SheafOfModules.{wModule} O)] (q : ℤ) :
    (moduleDerivedSectionsPresheaf O ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q) ⋙
        PresheafOfModules.sheafification (𝟙 O.obj) ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q := by
  let A := SheafOfModules.{wModule} O
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let F := moduleHomotopySectionsPresheaf O
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let HqP := DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q
  let S := F ⋙ HqP ⋙ a
  let hA := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) q
  let HqA := DerivedCategory.homologyFunctor A q
  let αA := (DerivedCategory.homologyFunctorFactorsh A q).inv
  letI : S.HasRightDerivedFunctor W :=
    Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck A S
  letI : hA.HasRightDerivedFunctor W :=
    Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck A hA
  letI : HqA.IsRightDerivedFunctor αA W := by
    simpa [W] using (Functor.isRightDerivedFunctor_iff_of_inverts HqA αA
      (HomotopyCategory.homologyFunctor_inverts_quasiIso A (ComplexShape.up ℤ) q)).2
      (by infer_instance)
  let e₁ := moduleTotalDerivedHomologyPostcompIso O F a q
  let R₁ := S.totalRightDerived DerivedCategory.Qh W
  let α₁ := S.totalRightDerivedUnit DerivedCategory.Qh W
  let RA := hA.totalRightDerived DerivedCategory.Qh W
  let αhA := hA.totalRightDerivedUnit DerivedCategory.Qh W
  let eSource := moduleHomotopySheafificationHomologyIso O q
  let e₂ := Functor.rightDerivedNatIso R₁ RA α₁ αhA W eSource
  let e₃ := Functor.rightDerivedNatIso RA HqA αhA αA W (Iso.refl hA)
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- For a distinguished triangle `T` in the derived category and an exact functor `F`, if `F`
annihilates `H^m(T.obj₁)` and `H^{m+1}(T.obj₁)`, then it sends the map induced by `T.mor₂` on `H^m`
to an isomorphism. -/
private lemma isIso_homology_eval_of_isZero
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (m : ℤ)
    (h₀ : IsZero (F.obj ((DerivedCategory.homologyFunctor A m).obj T.obj₁)))
    (h₁ : IsZero (F.obj ((DerivedCategory.homologyFunctor A (m + 1)).obj T.obj₁))) :
    IsIso (F.map ((DerivedCategory.homologyFunctor A m).map T.mor₂)) := by
  have : Mono (F.map ((DerivedCategory.homologyFunctor A m).map T.mor₂)) :=
    (ShortComplex.exact_iff_mono _ (h₀.eq_of_src _ _)).1
      ((DerivedCategory.HomologySequence.exact₂ T hT m).map F)
  have : Epi (F.map ((DerivedCategory.homologyFunctor A m).map T.mor₂)) :=
    (ShortComplex.exact_iff_epi _ (h₁.eq_of_tgt _ _)).1
      ((DerivedCategory.HomologySequence.exact₃ T hT m (m + 1)).map F)
  exact isIso_of_mono_of_epi _

/-- For `a ≤ m`, the canonical map `E ⟶ τ_{≥ a} E` induces an isomorphism on `H^m`. -/
private lemma isIso_homologyMap_truncGEπ
    {A : Type*} [Category* A] [Abelian A]
    (E : DerivedCategory A) (a m : ℤ) (ham : a ≤ m) :
    IsIso ((DerivedCategory.homologyFunctor A m).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E)) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLTGE a).obj E
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished a E
  have hzero (i : ℤ) (hi : a ≤ i) :
      IsZero ((DerivedCategory.homologyFunctor A i).obj T.obj₁) := by
    have hle : T.obj₁.IsLE (a - 1) := t.isLE_truncLT_obj E a (a - 1) (by omega)
    exact DerivedCategory.isZero_of_isLE T.obj₁ (a - 1) i (by omega)
  have : Mono ((DerivedCategory.homologyFunctor A m).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT m).2
      ((hzero m ham).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor A m).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT m (m + 1)).2
      ((hzero (m + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor A m).map T.mor₂)

/-- For `m < a`, the canonical map `τ_{< a} E ⟶ E` induces an isomorphism on `H^m`. -/
private lemma isIso_homologyMap_truncLTι
    {A : Type*} [Category* A] [Abelian A]
    (E : DerivedCategory A) (a m : ℤ) (ham : m < a) :
    IsIso ((DerivedCategory.homologyFunctor A m).map
      ((DerivedCategory.TStructure.t.truncLTι a).app E)) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLTGE a).obj E
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished a E
  have hzero (i : ℤ) (hi : i < a) :
      IsZero ((DerivedCategory.homologyFunctor A i).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE T.obj₃ a i hi
  have : Epi ((DerivedCategory.homologyFunctor A m).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT m).2
      ((hzero m ham).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor A m).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (m - 1) m).2
      ((hzero (m - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor A m).map T.mor₁)

/-- Two successive stages of the truncation tower sit in a distinguished triangle whose first
object is `H^a(E)` placed in degree `a` and whose second map is the canonical
`τ_{≥ a} E ⟶ τ_{≥ a+1} E`. -/
private lemma exists_successive_truncation_triangle
    {A : Type*} [Category* A] [Abelian A] (E : DerivedCategory A) (a : ℤ) :
    ∃ (f : (DerivedCategory.singleFunctor A a).obj
      ((DerivedCategory.homologyFunctor A a).obj E) ⟶
        (DerivedCategory.TStructure.t.truncGE a).obj E)
      (δ : (DerivedCategory.TStructure.t.truncGE (a + 1)).obj E ⟶
        ((DerivedCategory.singleFunctor A a).obj
          ((DerivedCategory.homologyFunctor A a).obj E))⟦(1 : ℤ)⟧),
      Triangle.mk f
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a (a + 1) (by omega)).app E)
        δ ∈ distTriang (DerivedCategory A) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let K := (t.truncGE a).obj E
  -- The truncation triangle of `K` at `a + 1`, with its three objects and three maps written
  -- out rather than left as projections of `t.triangleLTGE`. Writing them out is what lets the
  -- steps below see `K` as the middle object: the projections of a `Triangle.mk` reduce by
  -- structure projection, whereas those of `t.triangleLTGE` would need `t.truncGE` unfolded,
  -- and `TStructure.truncGE` is not exposed.
  let T := Triangle.mk ((t.truncLTι (a + 1)).app K) ((t.truncGEπ (a + 1)).app K)
    ((t.truncGEδLT (a + 1)).app K)
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished (a + 1) K
  have : T.obj₁.IsGE a := by
    change t.IsGE ((t.truncLTGE a (a + 1)).obj E) a
    exact t.isGE_of_iso ((t.truncGELTIsoLTGE a (a + 1)).app E) a
  have : T.obj₁.IsLE a := by
    change t.IsLE ((t.truncLT (a + 1)).obj K) a
    exact t.isLE_truncLT_obj K (a + 1) a (by omega)
  obtain ⟨M, ⟨eM⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₁ a
  let H := DerivedCategory.homologyFunctor A a
  have hι : IsIso (H.map ((t.truncLTι (a + 1)).app K)) :=
    isIso_homologyMap_truncLTι K (a + 1) a (by omega)
  have hπ := isIso_homologyMap_truncGEπ E a a le_rfl
  let eH : H.obj T.obj₁ ≅ H.obj E :=
    asIso (H.map ((t.truncLTι (a + 1)).app K)) ≪≫
      (asIso (H.map ((t.truncGEπ a).app E))).symm
  let eX : T.obj₁ ≅ (DerivedCategory.singleFunctor A a).obj (H.obj E) :=
    eM ≪≫ (DerivedCategory.singleFunctor A a).mapIso
      ((H.mapIso eM ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso A a).app M).symm ≪≫ eH)
  have hZ := t.isIso_truncGE_map_truncGEπ_app (a + 1) a (by omega) E
  let eZ : T.obj₃ ≅ (t.truncGE (a + 1)).obj E :=
    (asIso ((t.truncGE (a + 1)).map ((t.truncGEπ a).app E))).symm
  have hw : T.mor₂ ≫ eZ.hom = (t.natTransTruncGEOfLE a (a + 1) (by omega)).app E := by
    have : t.IsGE ((t.truncGE (a + 1)).obj E) a :=
      t.isGE_of_ge _ a (a + 1) (by omega)
    apply t.from_truncGE_obj_ext
    change (t.truncGEπ a).app E ≫ (t.truncGEπ (a + 1)).app K ≫
      inv ((t.truncGE (a + 1)).map ((t.truncGEπ a).app E)) = _
    rw [← Category.assoc, ← t.truncGEπ_naturality, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, t.π_natTransTruncGEOfLE_app]
    rfl
  refine ⟨eX.inv ≫ T.mor₁, eZ.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map eX.hom, ?_⟩
  apply isomorphic_distinguished _ hT _
  refine Triangle.isoMk _ _ eX.symm (Iso.refl _) eZ.symm ?_ ?_ ?_
  · simp
  · dsimp
    rw [← hw, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · simp

/-- If the quotient to the homotopy category followed by `G` preserves the product of a countable
family of cochain complexes, then `G` preserves the product of their images in the homotopy
category. -/
private lemma preserves_homotopy_product
    {A B : Type*} [Category* A] [Abelian A] [Category* B]
    [HasCountableProducts A] (G : HomotopyCategory A (.up ℤ) ⥤ B)
    (I : ℕ → CochainComplex A ℤ)
    [PreservesLimit (Discrete.functor I) (HomotopyCategory.quotient A (.up ℤ) ⋙ G)] :
    PreservesLimit (Discrete.functor (fun n => (HomotopyCategory.quotient A (.up ℤ)).obj (I n)))
      G := by
  let Q := HomotopyCategory.quotient A (.up ℤ)
  let c := Fan.mk (∏ᶜ I) (fun n => Pi.π I n)
  let d := Fan.mk (Q.obj (∏ᶜ I)) (fun n => Q.map (Pi.π I n))
  have hd : IsLimit d := Stacks.Injectives.KInjectiveProduct.productHomotopyIsLimit I
  apply preservesLimit_of_preserves_limit_cone hd
  apply (Fan.isLimitMapConeEquiv G _ d).symm.toFun
  exact (Fan.isLimitMapConeEquiv (Q ⋙ G) I c)
    (isLimitOfPreserves (Q ⋙ G) (productIsProduct I))

/-- An additive functor preserving countable products induces, degreewise on homotopy categories
and followed by degree-`m` homology, a functor preserving countable products of images of cochain
complexes. -/
private lemma preserves_homotopy_evaluation_homology_product
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (I : ℕ → CochainComplex A ℤ) (m : ℤ) :
    PreservesLimit (Discrete.functor (fun n => (HomotopyCategory.quotient A (.up ℤ)).obj (I n)))
      (F.mapHomotopyCategory (.up ℤ) ⋙ HomotopyCategory.homologyFunctor B (.up ℤ) m) := by
  let QA := HomotopyCategory.quotient A (.up ℤ)
  let QB := HomotopyCategory.quotient B (.up ℤ)
  let H := HomotopyCategory.homologyFunctor B (.up ℤ) m
  let FC := F.mapHomologicalComplex (.up ℤ)
  let FH := F.mapHomotopyCategory (.up ℤ)
  let HC := HomologicalComplex.homologyFunctor B (.up ℤ) m
  have : PreservesLimitsOfShape (Discrete ℕ) HC :=
    Stacks.DerivedProducts.preservesLimitsOfShape_homologyFunctor m
  let e : QA ⋙ FH ⋙ H ≅ FC ⋙ HC :=
    (Functor.associator QA FH H).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) H ≪≫
      Functor.associator FC QB H ≪≫
      Functor.isoWhiskerLeft FC (HomotopyCategory.homologyFunctorFactors B (.up ℤ) m)
  have : PreservesLimitsOfShape (Discrete ℕ) (QA ⋙ FH ⋙ H) :=
    preservesLimitsOfShape_of_natIso e.symm
  exact preserves_homotopy_product (FH ⋙ H) I

/-- The image in the derived category of a countable product of `K`-injective cochain complexes is
a product of their images. -/
private def derivedProductIsLimit
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (I : ℕ → CochainComplex A ℤ) (hI : ∀ n, (I n).IsKInjective) :
    IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ I))
      (fun n => DerivedCategory.Q.map (Pi.π I n))) := by
  let e (X : DerivedCategory A) := DerivedCategory.Q.objObjPreimageIso X
  let b (X : DerivedCategory A) := Stacks.Injectives.KInjectiveProduct.product_repr_derived I hI
    (DerivedCategory.Q.objPreimage X)
  let lift (s : Fan (fun n => DerivedCategory.Q.obj (I n))) :=
    (e s.pt).inv ≫ ((b s.pt).surjective (fun n => (e s.pt).hom ≫ s.proj n)).choose
  have fac (s : Fan (fun n => DerivedCategory.Q.obj (I n))) (n : ℕ) :
      lift s ≫ DerivedCategory.Q.map (Pi.π I n) = s.proj n := by
    have h := congrFun ((b s.pt).surjective (fun n => (e s.pt).hom ≫ s.proj n)).choose_spec n
    dsimp only [Stacks.Injectives.KInjectiveProduct.derivedHomComparison] at h
    dsimp only [lift]
    rw [Category.assoc, h, Iso.inv_hom_id_assoc]
  refine Fan.IsLimit.mk _ lift fac ?_
  intro s f hf
  change ∀ j, f ≫ DerivedCategory.Q.map (Pi.π I j) = s.proj j at hf
  apply (cancel_epi (e s.pt).hom).1
  apply (b s.pt).injective
  funext n
  change ((e s.pt).hom ≫ f) ≫ _ = ((e s.pt).hom ≫ lift s) ≫ _
  rw [Category.assoc, Category.assoc, hf, fac]

/-- The localization functor from the homotopy category to the derived category preserves the
product of a countable family of `K`-injective cochain complexes. -/
private lemma preserves_kInjective_product
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (I : ℕ → CochainComplex A ℤ) (hI : ∀ n, (I n).IsKInjective) :
    PreservesLimit (Discrete.functor (fun n => (HomotopyCategory.quotient A (.up ℤ)).obj (I n)))
      DerivedCategory.Qh := by
  let c := Fan.mk (∏ᶜ I) (fun n => Pi.π I n)
  have : PreservesLimit (Discrete.functor I) (DerivedCategory.Q (C := A)) :=
    preservesLimit_of_preserves_limit_cone (productIsProduct I)
      ((Fan.isLimitMapConeEquiv DerivedCategory.Q I c).symm (derivedProductIsLimit I hI))
  have : PreservesLimit (Discrete.functor I)
      (HomotopyCategory.quotient A (.up ℤ) ⋙ DerivedCategory.Qh) :=
    preservesLimit_of_natIso _ (DerivedCategory.quotientCompQhIso A).symm
  exact preserves_homotopy_product DerivedCategory.Qh I

/-- Let `L` be a derived limit of an inverse system `K`, presented by the distinguished triangle
built from the difference map. If `R ⋙ H^r ⋙ F` preserves the product and inverts the one-step
transition maps beyond the stage `N` for `r = m - 1` and `r = m`, then it sends the map
`L ⟶ K N` to a monomorphism. -/
private lemma mono_homology_projection_of_eventually_iso
    {D A : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [Category* A] [Abelian A]
    (R : D ⥤ DerivedCategory A) [R.CommShift ℤ] [R.IsTriangulated]
    (F : A ⥤ AddCommGrpCat.{w}) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => K.obj ⟨n⟩]
    {L : D} (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang D)
    (m : ℤ) (N : ℕ)
    (hpres : ∀ r : ℤ, m - 1 ≤ r → r ≤ m →
      PreservesLimit (Discrete.functor (fun n : ℕ => K.obj ⟨n⟩))
        (R ⋙ DerivedCategory.homologyFunctor A r ⋙ F))
    (hiso : ∀ r : ℤ, m - 1 ≤ r → r ≤ m → ∀ n : ℕ, N ≤ n →
      IsIso ((R ⋙ DerivedCategory.homologyFunctor A r ⋙ F).map
        (K.map (homOfLE (Nat.le_succ n)).op))) :
    Mono ((R ⋙ DerivedCategory.homologyFunctor A m ⋙ F).map (p ≫ Pi.π _ N)) := by
  let T := Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) δ
  let H₀ := R ⋙ DerivedCategory.homologyFunctor A (m - 1) ⋙ F
  let H₁ := R ⋙ DerivedCategory.homologyFunctor A m ⋙ F
  have : PreservesLimit (Discrete.functor (fun n : ℕ => K.obj ⟨n⟩)) H₀ :=
    hpres _ (by omega) (by omega)
  have : PreservesLimit (Discrete.functor (fun n : ℕ => K.obj ⟨n⟩)) H₁ :=
    hpres _ (by omega) (by omega)
  have hz := isZero_cokernel_difference_of_eventually_iso (K ⋙ H₀) N
    (hiso _ (by omega) (by omega))
  have hep : Epi (H₀.map T.mor₂) := epi_map_difference K H₀ hz
  have : Epi (F.map ((DerivedCategory.homologyFunctor A (m - 1)).map
      (R.mapTriangle.obj T).mor₂)) := hep
  have hmono : Mono (H₁.map p) :=
    _root_.mono_homology_eval_of_epi F (R.mapTriangle.obj T) (R.map_distinguished T hT) m
  apply mono_projection_of_difference K p (comp_distTriang_mor_zero₁₂ T hT) H₁ N
  intro n hn
  have : IsIso (H₁.map (K.map (homOfLE hn).op)) :=
    _root_.isIso_map_to_of_successive_isIso (K ⋙ H₁) N
    (hiso _ (by omega) (by omega)) n hn
  infer_instance

/-- For `F` additive and `G` exact, computing degree-`m` cohomology in the derived category after
`F` and then applying `G` agrees with degree-`m` homology on the homotopy category of `F ⋙ G`. -/
private def homotopyCohomologyEvaluationIso
    {A P D : Type*} [Category* A] [Abelian A] [Category* P] [Abelian P]
    [Category* D] [Abelian D]
    (F : A ⥤ P) [F.Additive] (G : P ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (m : ℤ) :
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor P m ⋙ G ≅
      (F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ HomotopyCategory.homologyFunctor D (.up ℤ) m := by
  let FH := F.mapHomotopyCategory (.up ℤ)
  let GH := G.mapHomotopyCategory (.up ℤ)
  let H := DerivedCategory.homologyFunctor P m
  let H' := HomotopyCategory.homologyFunctor D (.up ℤ) m
  exact
    Functor.associator FH DerivedCategory.Qh (H ⋙ G) ≪≫
      Functor.isoWhiskerLeft FH
        ((Functor.associator DerivedCategory.Qh H G).symm ≪≫
          Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh P m) G ≪≫
          homotopyHomologyIso G m) ≪≫
      (Functor.associator FH GH H').symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) H'

/-- When `G` is exact and `F ⋙ G` preserves countable products, the functor computing
`G (H^m (-))` through the derived category preserves countable products of images of cochain
complexes in the homotopy category. -/
private lemma preserves_homotopy_cohomology_evaluation_product
    {A P D : Type*} [Category* A] [Abelian A] [Category* P] [Abelian P]
    [Category* D] [Abelian D] [HasCountableProducts A] [HasCountableProducts D]
    [HasExactLimitsOfShape (Discrete ℕ) D]
    (F : A ⥤ P) [F.Additive] (G : P ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesLimitsOfShape (Discrete ℕ) (F ⋙ G)]
    (I : ℕ → CochainComplex A ℤ) (m : ℤ) :
    PreservesLimit (Discrete.functor (fun n => (HomotopyCategory.quotient A (.up ℤ)).obj (I n)))
      ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor P m ⋙ G) := by
  have := preserves_homotopy_evaluation_homology_product (F ⋙ G) I m
  exact preservesLimit_of_natIso _ (homotopyCohomologyEvaluationIso F G m).symm

/-- Sending a morphism to a monomorphism is invariant under an isomorphism of functors. -/
private lemma mono_map_of_natIso
    {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    (e : F ≅ G) {X Y : A} (f : X ⟶ Y) (hf : Mono (F.map f)) : Mono (G.map f) := by
  have : Mono (e.hom.app X ≫ G.map f) := by rw [← e.hom.naturality f]; infer_instance
  exact (mono_comp_iff_of_isIso _ _).1 this

/-- If a natural transformation `α : F ⟶ G` is an isomorphism at `X` and at `Y` and `G f` is an
isomorphism for `f : X ⟶ Y`, then `F f` is an isomorphism. -/
private lemma isIso_map_of_naturality
    {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    (α : F ⟶ G) {X Y : A} (f : X ⟶ Y)
    [IsIso (α.app X)] [IsIso (α.app Y)] [IsIso (G.map f)] : IsIso (F.map f) := by
  have : IsIso (F.map f ≫ α.app Y) := by rw [α.naturality f]; infer_instance
  exact (isIso_comp_right_iff _ _).1 this

/-- For a map of bounded-below homotopy classes of complexes with injective terms, if the
degree-`m` cohomology of the right derived functor of `F` inverts it, then so does the degreewise
application of `F` followed by degree-`m` homology. -/
private lemma isIso_homotopy_homology_of_rightDerived
    {A D : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    [Category* D] [Abelian D] (F : A ⥤ D) [F.Additive]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L)
    [∀ i : ℤ, Injective (K.obj.as.X i)] [∀ i : ℤ, Injective (L.obj.as.X i)] (m : ℤ)
    (h : IsIso ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D m).map
      (DerivedCategory.Plus.Qh.map f))) :
    IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙
      HomotopyCategory.homologyFunctor D (.up ℤ) m).map f.hom) := by
  let H := DerivedCategory.Plus.homologyFunctor D m
  let α := Functor.whiskerRight F.rightDerivedFunctorPlusUnith H
  have : IsIso (((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus) ⋙ H).map f) := h
  have : IsIso (α.app K) := by dsimp [α]; infer_instance
  have : IsIso (α.app L) := by dsimp [α]; infer_instance
  have h' := isIso_map_of_naturality α f
  let e := Functor.isoWhiskerLeft (F.mapHomotopyCategory (.up ℤ))
    (DerivedCategory.homologyFunctorFactorsh D m)
  exact (NatIso.isIso_map_iff e f.hom).1 h'

/-- Every object of the bounded-below derived category is isomorphic to the image of a
bounded-below complex all of whose terms are injective. -/
private lemma exists_injective_homotopy_representative
    {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    (X : DerivedCategory.Plus A) :
    ∃ I : HomotopyCategory.Plus A, (∀ i : ℤ, Injective (I.obj.as.X i)) ∧
      Nonempty (DerivedCategory.Plus.Qh.obj I ≅ X) := by
  obtain ⟨a, ha⟩ := X.property
  have : X.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff X a).1 ha
  obtain ⟨J, hJ, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X a
  let I := (HomotopyCategory.Plus.quotient A).obj
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj J)
  refine ⟨I, fun i => inferInstance, ⟨?_⟩⟩
  exact DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.quotientCompQhIso A).app _ ≪≫ DerivedCategory.Plus.ι.mapIso e)

/-- A bounded-below complex all of whose terms are injective, viewed in the homotopy category, is
`K`-injective. -/
private lemma isKInjective_of_injective_homotopyPlus
    {A : Type*} [Category* A] [Abelian A] (I : HomotopyCategory.Plus A)
    (h : ∀ i : ℤ, Injective (I.obj.as.X i)) : CochainComplex.IsKInjective I.obj.as := by
  obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff _).1 I.property
  exact CochainComplex.isKInjective_of_injective _ a

/-- Every inverse system indexed by `ℕ` in the bounded-below derived category is isomorphic to the
image of a system of bounded-below complexes with injective terms in the homotopy category. -/
private lemma exists_injective_homotopy_tower
    {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    (K : ℕᵒᵖ ⥤ DerivedCategory.Plus A) :
    ∃ I : ℕᵒᵖ ⥤ HomotopyCategory.Plus A,
      (∀ (n : ℕ) (i : ℤ), Injective ((I.obj ⟨n⟩).obj.as.X i)) ∧
      Nonempty (I ⋙ DerivedCategory.Plus.Qh ≅ K) := by
  choose J hJ e using fun n : ℕ => exists_injective_homotopy_representative (K.obj ⟨n⟩)
  let e' (n : ℕ) := (e n).some
  have hInj (n : ℕ) : CochainComplex.IsKInjective (J n).obj.as :=
    isKInjective_of_injective_homotopyPlus (J n) (hJ n)
  choose t ht using fun n : ℕ =>
    (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective (J (n + 1)) (J n) (hInj n)).surjective
      ((e' (n + 1)).hom ≫ K.map (homOfLE (Nat.le_succ n)).op ≫ (e' n).inv)
  let I := Functor.ofOpSequence t
  let α : I ⋙ DerivedCategory.Plus.Qh ⟶ K :=
    NatTrans.ofOpSequence (fun n => (e' n).hom) (fun n => by
      -- `ht n` is substituted by `congrArg` rather than by `rw`: the morphisms `t n` live in
      -- the full subcategory `HomotopyCategory.Plus A`, so the goal is type-correct only once
      -- that subtype is unfolded, and a rewrite declines to act on it.
      have h₁ : DerivedCategory.Plus.Qh.map (t n) ≫ (e' n).hom =
          ((e' (n + 1)).hom ≫ K.map (homOfLE (Nat.le_succ n)).op ≫ (e' n).inv) ≫
            (e' n).hom := congrArg (fun g => g ≫ (e' n).hom) (ht n)
      simp only [Functor.comp_map, I, Functor.ofOpSequence_map_homOfLE_succ]
      refine h₁.trans ?_
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)
  have : ∀ X, IsIso (α.app X) := fun X => (e' X.unop).isIso_hom
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨I, hJ, ⟨asIso α⟩⟩

/-- A derived limit triangle for an inverse system `K` in the derived category lifts along an
isomorphism `I ⋙ Qh ≅ K` to the homotopy category: there is an object `M` fitting into the
analogous triangle over `I`, together with an isomorphism `Qh M ≅ L` compatible with all the
projections. -/
private lemma exists_homotopy_derivedLimit_triangle
    {A : Type*} [Category* A] [Abelian A]
    (I : ℕᵒᵖ ⥤ HomotopyCategory A (.up ℤ))
    [HasProduct fun n : ℕ => I.obj ⟨n⟩]
    [PreservesLimit (Discrete.functor (fun n : ℕ => I.obj ⟨n⟩)) DerivedCategory.Qh]
    (K : ℕᵒᵖ ⥤ DerivedCategory A) (e : I ⋙ DerivedCategory.Qh ≅ K)
    [HasProduct fun n : ℕ => K.obj ⟨n⟩]
    (L : DerivedCategory A) (q : L ⟶ ∏ᶜ fun n : ℕ => K.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk q (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang _) :
    ∃ (M : HomotopyCategory A (.up ℤ)) (p : M ⟶ ∏ᶜ fun n : ℕ => I.obj ⟨n⟩)
      (d : (∏ᶜ fun n : ℕ => I.obj ⟨n⟩) ⟶ M⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => I.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => I.obj ⟨n⟩) (n + 1) ≫ I.map (homOfLE (Nat.le_succ n)).op) d ∈
        distTriang _ ∧
      ∃ eM : DerivedCategory.Qh.obj M ≅ L, ∀ n : ℕ,
        DerivedCategory.Qh.map (p ≫ Pi.π _ n) ≫ e.hom.app ⟨n⟩ = eM.hom ≫ q ≫ Pi.π _ n := by
  let F := DerivedCategory.Qh (C := A)
  have : HasProduct (fun n : ℕ => F.obj (I.obj ⟨n⟩)) :=
    hasLimit_of_iso (F := Discrete.functor (fun n : ℕ => K.obj ⟨n⟩))
      (Discrete.natIso (fun ⟨n⟩ => (e.app ⟨n⟩).symm))
  let eP : F.obj (∏ᶜ fun n : ℕ => I.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ => K.obj ⟨n⟩ :=
    asIso (piComparison F _) ≪≫ HasLimit.isoOfNatIso (Discrete.natIso (fun ⟨n⟩ => e.app ⟨n⟩))
  have heP (n : ℕ) : eP.hom ≫ Pi.π _ n = F.map (Pi.π _ n) ≫ e.hom.app ⟨n⟩ := by
    dsimp [eP]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
    simp only [Discrete.natIso_hom_app, Iso.app_hom, ← Category.assoc, piComparison_comp_π]
  let s := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => I.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => I.obj ⟨n⟩) (n + 1) ≫ I.map (homOfLE (Nat.le_succ n)).op
  let T := Triangle.mk q (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫ K.map (homOfLE (Nat.le_succ n)).op) δ
  obtain ⟨M, p, d, hS⟩ := distinguished_cocone_triangle₁ s
  let S := Triangle.mk p s d
  have he : F.map s ≫ eP.hom = eP.hom ≫ T.mor₂ := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, heP, ← Category.assoc, ← F.map_comp]
    simp only [s, Pi.lift_comp_π, F.map_sub, F.map_comp, Preadditive.sub_comp]
    dsimp [T]
    conv_rhs =>
      rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, heP n]
      rw [← Category.assoc, heP (n + 1)]
    simp only [Category.assoc]
    have hn := e.hom.naturality (homOfLE (Nat.le_succ n)).op
    change F.map (I.map (homOfLE (Nat.le_succ n)).op) ≫ e.hom.app ⟨n⟩ =
      e.hom.app ⟨n + 1⟩ ≫ K.map (homOfLE (Nat.le_succ n)).op at hn
    rw [hn]
  obtain ⟨a, ha, hd⟩ := complete_distinguished_triangle_morphism₁
    (F.mapTriangle.obj S) T (F.map_distinguished S hS) hT eP.hom eP.hom he
  let φ : F.mapTriangle.obj S ⟶ T :=
    { hom₁ := a, hom₂ := eP.hom, hom₃ := eP.hom, comm₁ := ha, comm₂ := he, comm₃ := hd }
  have hiso : IsIso a := isIso₁_of_isIso₂₃ φ (F.map_distinguished S hS) hT
    (by change IsIso eP.hom; infer_instance) (by change IsIso eP.hom; infer_instance)
  refine ⟨M, p, d, hS, @asIso _ _ _ _ a hiso, ?_⟩
  intro n
  have h := congrArg (fun f => f ≫ Pi.π (fun n : ℕ => K.obj ⟨n⟩) n) ha
  change (F.map p ≫ eP.hom) ≫ Pi.π _ n = (a ≫ q) ≫ Pi.π _ n at h
  rw [Category.assoc, heP, ← Category.assoc, ← F.map_comp] at h
  change DerivedCategory.Qh.map (p ≫ Pi.π _ n) ≫ e.hom.app ⟨n⟩ = a ≫ q ≫ Pi.π _ n
  simpa only [F, Category.assoc] using h

/-- The truncation `τ_{≥ a} E`, regarded as an object of the bounded-below derived category. -/
private abbrev truncGEPlus {A : Type*} [Category* A] [Abelian A]
    (E : DerivedCategory A) (a : ℤ) : DerivedCategory.Plus A :=
  ⟨(DerivedCategory.TStructure.t.truncGE a).obj E, a, inferInstance⟩

/-- For `a ≤ b`, the canonical map `τ_{≥ a} E ⟶ τ_{≥ b} E` in the bounded-below derived
category. -/
private abbrev truncGEPlusMap {A : Type*} [Category* A] [Abelian A]
    (E : DerivedCategory A) (a b : ℤ) (hab : a ≤ b) :
    truncGEPlus E a ⟶ truncGEPlus E b :=
  ObjectProperty.homMk ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b hab).app E)

/-- The truncation tower `n ↦ τ_{≥ -n} E` as an inverse system indexed by `ℕ` in the bounded-below
derived category. -/
private def truncGETowerPlus {A : Type*} [Category* A] [Abelian A]
    (E : DerivedCategory A) : ℕᵒᵖ ⥤ DerivedCategory.Plus A :=
  Functor.ofOpSequence (X := fun n => truncGEPlus E (-(n : ℤ)))
    (fun n => truncGEPlusMap E (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega))

/-- The truncation tower in the bounded-below derived category becomes, after the inclusion into
the derived category, the truncation tower `Stacks.DerivedLimit.truncGETower`. -/
private def truncGETowerPlusIso {A : Type*} [Category* A] [Abelian A]
    (E : DerivedCategory A) :
    truncGETowerPlus E ⋙ DerivedCategory.Plus.ι ≅ Stacks.DerivedLimit.truncGETower A E := by
  let α : truncGETowerPlus E ⋙ DerivedCategory.Plus.ι ⟶ Stacks.DerivedLimit.truncGETower A E :=
    NatTrans.ofOpSequence (fun n => 𝟙 _) (fun n => by
      simp only [Functor.comp_map, truncGETowerPlus, Stacks.DerivedLimit.truncGETower,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have : ∀ X, IsIso (α.app X) := fun X => inferInstanceAs (IsIso (𝟙 _))
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- If the right derived functor of `F` applied to `H^a(E)` placed in degree `a` has vanishing
cohomology in degrees `m` and `m + 1`, then it sends the canonical map `τ_{≥ a} E ⟶ τ_{≥ a+1} E`
to an isomorphism on degree-`m` cohomology. -/
private lemma isIso_rightDerived_truncGEPlusMap
    {A D : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    [Category* D] [Abelian D] (F : A ⥤ D) [F.Additive]
    (E : DerivedCategory A) (a b m : ℤ) (hab : a + 1 = b)
    (h₀ : IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A a).obj
        ((DerivedCategory.homologyFunctor A a).obj E)))))
    (h₁ : IsZero ((DerivedCategory.Plus.homologyFunctor D (m + 1)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A a).obj
        ((DerivedCategory.homologyFunctor A a).obj E))))) :
    IsIso ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D m).map
      (truncGEPlusMap E a b (by omega))) := by
  subst b
  let R := F.rightDerivedFunctorPlus
  let α := F.rightDerivedFunctorPlusUnith
  let := Functor.IsRightDerivedFunctor.commShift R α (HomotopyCategory.Plus.quasiIso A) ℤ
  let : R.IsTriangulated :=
    Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F R α
  obtain ⟨f, d, hT⟩ := exists_successive_truncation_triangle E a
  let S := (DerivedCategory.Plus.singleFunctor A a).obj
    ((DerivedCategory.homologyFunctor A a).obj E)
  let T : Triangle (DerivedCategory.Plus A) :=
    Triangle.mk (ObjectProperty.homMk f : S ⟶ truncGEPlus E a)
      (truncGEPlusMap E a (a + 1) (by omega))
      (ObjectProperty.homMk (d ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app S))
  -- The comparison `ι.mapTriangle.obj T = Triangle.mk f _ d` comes down to cancelling the
  -- commutation isomorphism of `ι` against its inverse on the third map. It is proved in term
  -- mode: as a tactic goal it carries the subtype coercion `DerivedCategory.Plus.ι` and so is
  -- type-correct only after that is unfolded, which a rewrite declines to do.
  have hd : (d ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app S) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app S = d :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => d ≫ g)
        ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv_hom_id_app S)).trans
          (Category.comp_id d))
  have hT' : T ∈ distTriang _ := by
    apply (DerivedCategory.Plus.ι.map_distinguished_iff T).1
    convert hT using 1
    dsimp [T, truncGEPlusMap, Functor.mapTriangle]
    congr 1
  let G := R ⋙ DerivedCategory.Plus.ι
  exact isIso_homology_eval_of_isZero (𝟭 D) (G.mapTriangle.obj T)
    (G.map_distinguished T hT') m h₀ h₁

/-- A map of sheaves of `O`-modules that is an isomorphism on sections over every object of a
subset `B` large enough to cover every object of the site is an isomorphism. -/
private lemma isIso_of_basis_evaluation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}] [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    {M N : SheafOfModules.{wModule} O} (f : M ⟶ N) (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (hf : ∀ V, B V → IsIso ((SheafOfModules.evaluation O (.op V)).map f)) :
    IsIso f := by
  let F := SheafOfModules.toSheaf O
  let g := F.map f
  have hbij (V : C) (hV : B V) : Function.Bijective (g.hom.app (.op V)) := by
    have := hf V hV
    exact (ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation O (.op V)).map f))
  have : Presheaf.IsLocallyInjective J g.hom := by
    constructor
    intro U x y hxy
    obtain ⟨𝒰, h𝒰, hB𝒰⟩ := basisCover U.unop
    refine J.superset_covering ?_ h𝒰
    intro W f hf
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    rw [Presheaf.equalizerSieve_apply]
    have hi : (F.obj M).obj.map (𝒰.f i).op x = (F.obj M).obj.map (𝒰.f i).op y := by
      apply (hbij _ (hB𝒰 i)).1
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hi]
  have : Presheaf.IsLocallySurjective J g.hom := by
    constructor
    intro U s
    obtain ⟨𝒰, h𝒰, hB𝒰⟩ := basisCover U
    refine J.superset_covering ?_ h𝒰
    intro W f hf
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    exact (Presheaf.imageSieve g.hom s).downward_closed
      ((hbij _ (hB𝒰 i)).2 ((F.obj N).obj.map (𝒰.f i).op s)) a
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).1 ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso f F

/-- Let `c : E ⟶ L` be compatible with maps `p n : L ⟶ τ_{≥ -n} E`, in the sense that each
`c ≫ p n` is the canonical truncation map. If for every degree `m` and every `V ∈ B` some stage `n`
with `-n ≤ m` makes `H^m(p n)` injective on sections over `V`, then `c` is an isomorphism. -/
private lemma isIso_of_mono_truncation_projections
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}] [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    {E L : DerivedCategory (SheafOfModules.{wModule} O)} (c : E ⟶ L) (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (p : ∀ n : ℕ, L ⟶ (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)
    (hc : ∀ n, c ≫ p n = (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
    (hp : ∀ (m : ℤ) (V : C), B V → ∃ n : ℕ, -(n : ℤ) ≤ m ∧
      Mono ((SheafOfModules.evaluation O (.op V)).map
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) m).map (p n)))) :
    IsIso c := by
  rw [DerivedCategory.isIso_iff]
  intro m
  apply isIso_of_basis_evaluation O _ B basisCover
  intro V hV
  obtain ⟨n, hn, hp⟩ := hp m V hV
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) m ⋙
    SheafOfModules.evaluation O (.op V)
  have hπ := isIso_homologyMap_truncGEπ E (-(n : ℤ)) m hn
  have hcomp : IsIso (H.map c ≫ H.map (p n)) := by
    rw [← H.map_comp, hc n]
    exact (SheafOfModules.evaluation O (.op V)).map_isIso _
  have : Mono (H.map (p n)) := hp
  have : Epi (H.map (p n)) := epi_of_epi (H.map c) (H.map (p n))
  have : IsIso (H.map (p n)) := isIso_of_mono_of_epi _
  exact (isIso_comp_right_iff (H.map c) (H.map (p n))).1 hcomp

/-- **Stacks Project, Tag 0D6M.** Under local, eventually vanishing cohomology bounds, the
canonical map from a derived object to any derived limit of its truncations from below is an
isomorphism. -/
@[stacks 0D6M,
  stacks 0D6N "the constant-bound case, by taking the degree bound at V to be max d_V m"]
theorem isIso_to_isDerivedLimit_truncationGETower
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{wRing})
    [HasSheafify J AddCommGrpCat.{wModule}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
    [EnoughInjectives (SheafOfModules.{wModule} O)]
    (E : DerivedCategory (SheafOfModules.{wModule} O))
    (B : Set C)
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (degreeBound : ∀ V : C, B V → ℤ → ℤ)
    (Cov : ∀ V : C, B V → Set (PreZeroHypercover.{max u v} V))
    (Cov_isCover : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → 𝒰.sieve₀ ∈ J V)
    (Cov_cofinal : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      𝒰.sieve₀ ∈ J V →
        ∃ 𝒱 : PreZeroHypercover.{max u v} V, Cov V hV 𝒱 ∧ Nonempty (𝒱.Hom 𝒰))
    (vanishing : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{max u v} V),
      Cov V hV 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ) (m : ℤ),
        degreeBound V hV m < (p : ℤ) →
          IsZero (moduleCohomology O (𝒰.X i) p
            ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O)
              (m - (p : ℤ))).obj E)))
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} O))
    (c : E ⟶ L)
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk q (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).map
            (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} O)))
    (hc : ∀ n : ℕ, c ≫ q ≫
      Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  apply isIso_of_mono_truncation_projections O c B basisCover
    (fun n => q ≫ Pi.π _ n) hc
  intro m V hV
  let b := degreeBound V hV
  let N : ℕ := (max (-m) (max (b (m - 1) - m)
    (max (b m - m) (b (m + 1) - m)))).toNat + 1
  have hN : -(N : ℤ) ≤ m := by dsimp [N]; omega
  refine ⟨N, hN, ?_⟩
  have hv : ∀ (𝒰 : PreZeroHypercover.{max u v} V), Cov V hV 𝒰 →
      ∀ (i : 𝒰.I₀) (n : ℕ), N ≤ n → ∀ k : ℤ, 0 ≤ k → k ≤ 2 →
        IsZero (moduleCohomology O (𝒰.X i) (m + n + k).toNat
          ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O)
            (-(n : ℤ) - 1)).obj E)) := by
    intro 𝒰 h𝒰 i n hn k hk₀ hk₂
    have hp : 0 ≤ m + n + k := by omega
    have hb : b (m + k - 1) < m + n + k := by
      dsimp [N] at hn
      have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl | rfl
      · simp only [add_zero]
        omega
      · simp only [add_sub_cancel_right]
        omega
      · rw [show m + 2 - 1 = m + 1 by omega]
        omega
    have h := vanishing V hV 𝒰 h𝒰 i (m + n + k).toNat (m + k - 1)
      (by simpa only [Int.toNat_of_nonneg hp] using hb)
    convert h using 2
    congr 2
    all_goals omega
  have hhyper : ∀ (𝒰 : PreZeroHypercover.{max u v} V), Cov V hV 𝒰 →
      ∀ (i : 𝒰.I₀) (n : ℕ), N ≤ n → ∀ k : ℤ, 0 ≤ k → k ≤ 2 →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (ModuleCat.{wModule} (O.obj.obj (.op (𝒰.X i)))) (m + k - 1)).obj
          ((moduleEvaluation O (𝒰.X i)).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{wModule} O)
              (-(n : ℤ) - 1)).obj
              ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O)
                (-(n : ℤ) - 1)).obj E)))) := by
    intro 𝒰 h𝒰 i n hn k hk₀ hk₂
    exact (hv 𝒰 h𝒰 i n hn k hk₀ hk₂).of_iso
      (rightDerivedFunctorPlusSingleShiftIso (moduleEvaluation O (𝒰.X i)) _
        (-(n : ℤ) - 1) (m + k - 1) (m + n + k).toNat (by omega))
  have hstep : ∀ (𝒰 : PreZeroHypercover.{max u v} V), Cov V hV 𝒰 →
      ∀ (i : 𝒰.I₀) (n : ℕ), N ≤ n → ∀ r : ℤ, m - 1 ≤ r → r ≤ m →
        IsIso (((moduleEvaluation O (𝒰.X i)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ r).map
            (truncGEPlusMap E (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega))) := by
    intro 𝒰 h𝒰 i n hn r hr₀ hr₁
    exact isIso_rightDerived_truncGEPlusMap (moduleEvaluation O (𝒰.X i)) E
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) r (by omega)
      (by simpa only [show m + (r - m + 1) - 1 = r by omega,
          show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by omega] using
        hhyper 𝒰 h𝒰 i n hn (r - m + 1) (by omega) (by omega))
      (by simpa only [show m + (r - m + 2) - 1 = r + 1 by omega,
          show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 by omega] using
        hhyper 𝒰 h𝒰 i n hn (r - m + 2) (by omega) (by omega))
  let A := SheafOfModules.{wModule} O
  let P := PresheafOfModules.{wModule} O.obj
  let K := Stacks.DerivedLimit.truncGETower A E
  let Kplus := truncGETowerPlus E
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_injective_homotopy_tower Kplus
  let Ih := I ⋙ HomotopyCategory.Plus.ι A
  let Ic (n : ℕ) : CochainComplex A ℤ := (I.obj ⟨n⟩).obj.as
  have hJI (n : ℕ) : (Ic n).IsKInjective :=
    isKInjective_of_injective_homotopyPlus (I.obj ⟨n⟩) (hI n)
  have : HasProduct (fun n : ℕ => Ih.obj ⟨n⟩) :=
    HasLimit.mk ⟨_, Stacks.Injectives.KInjectiveProduct.productHomotopyIsLimit Ic⟩
  have : PreservesLimit (Discrete.functor (fun n : ℕ => Ih.obj ⟨n⟩)) DerivedCategory.Qh :=
    preserves_kInjective_product Ic hJI
  let e : Ih ⋙ DerivedCategory.Qh ≅ K :=
    Functor.associator I (HomotopyCategory.Plus.ι A) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft I (DerivedCategory.Plus.QhCompιIsoιCompQh A).symm ≪≫
      (Functor.associator I DerivedCategory.Plus.Qh DerivedCategory.Plus.ι).symm ≪≫
      Functor.isoWhiskerRight eI DerivedCategory.Plus.ι ≪≫ truncGETowerPlusIso E
  obtain ⟨M, p, d, hMd, eM, hp⟩ := exists_homotopy_derivedLimit_triangle Ih K e L q δ hL
  let R := moduleHomotopySectionsPresheaf O
  let H (r : ℤ) := DerivedCategory.homologyFunctor P r
  let ev (U : C) := PresheafOfModules.evaluation O.obj (.op U)
  have hloc : ∀ (𝒰 : PreZeroHypercover.{max u v} V), Cov V hV 𝒰 →
      ∀ i : 𝒰.I₀, Mono (((R ⋙ H m).map (p ≫ Pi.π _ N)).app (.op (𝒰.X i))) := by
    intro 𝒰 h𝒰 i
    let U := 𝒰.X i
    let forgetM := ModuleCat.uliftFunctor.{wRing} (O.obj.obj (.op U)) ⋙
      forget₂ (ModuleCat.{max wRing wModule} (O.obj.obj (.op U))) AddCommGrpCat.{max wRing wModule}
    have : PreservesLimitsOfSize.{0, 0}
        (ModuleCat.uliftFunctor.{wRing, wModule} (O.obj.obj (.op U))) :=
      preservesLimitsOfSize_shrink _
    let F := ev U ⋙ forgetM
    have hmono : Mono ((R ⋙ H m ⋙ F).map (p ≫ Pi.π _ N)) := by
      apply mono_homology_projection_of_eventually_iso R F Ih p d hMd m N
      · intro r hr₀ hr₁
        exact preserves_homotopy_cohomology_evaluation_product (SheafOfModules.forget O) F Ic r
      · intro r hr₀ hr₁ n hn
        let G := (moduleEvaluation O U).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ r
        have hk : IsIso ((Kplus ⋙ G).map (homOfLE (Nat.le_succ n)).op) := by
          change IsIso (G.map ((Functor.ofOpSequence _).map _))
          rw [Functor.ofOpSequence_map_homOfLE_succ]
          exact hstep 𝒰 h𝒰 i n hn r hr₀ hr₁
        have hi : IsIso (G.map (DerivedCategory.Plus.Qh.map
            (I.map (homOfLE (Nat.le_succ n)).op))) :=
          (NatIso.isIso_map_iff (Functor.isoWhiskerRight eI G) (homOfLE (Nat.le_succ n)).op).2 hk
        have : ∀ j, Injective ((I.obj ⟨n⟩).obj.as.X j) := hI n
        have : ∀ j, Injective ((I.obj ⟨n + 1⟩).obj.as.X j) := hI (n + 1)
        have hih := isIso_homotopy_homology_of_rightDerived (moduleEvaluation O U)
          (I.map (homOfLE (Nat.le_succ n)).op) r hi
        have : IsIso ((R ⋙ H r ⋙ ev U).map (Ih.map (homOfLE (Nat.le_succ n)).op)) :=
          (NatIso.isIso_map_iff (homotopyCohomologyEvaluationIso
            (SheafOfModules.forget O) (ev U) r) _).2 hih
        exact forgetM.map_isIso ((R ⋙ H r ⋙ ev U).map
          (Ih.map (homOfLE (Nat.le_succ n)).op))
    exact forgetM.mono_of_mono_map hmono
  let CS : CofinalCoveringSystem J V :=
    { cov := Cov V hV, isCover := Cov_isCover V hV, cofinal := Cov_cofinal V hV }
  have hsheaf := sheafification_eval_mono O V CS ((R ⋙ H m).map (p ≫ Pi.π _ N)) hloc
  let T := DerivedCategory.homologyFunctor A m ⋙ SheafOfModules.evaluation O (.op V)
  let η := moduleHomotopySheafificationHomologyIso O m ≪≫
    (DerivedCategory.homologyFunctorFactorsh A m).symm
  have hm : Mono (T.map (DerivedCategory.Qh.map (p ≫ Pi.π _ N))) :=
    mono_map_of_natIso (Functor.isoWhiskerRight η (SheafOfModules.evaluation O (.op V)))
      (p ≫ Pi.π _ N) hsheaf
  have hm' : Mono (T.map (DerivedCategory.Qh.map (p ≫ Pi.π _ N) ≫ e.hom.app ⟨N⟩)) := by
    rw [T.map_comp]
    infer_instance
  rw [hp N, T.map_comp] at hm'
  exact (mono_comp_iff_of_isIso (T.map eM.hom) (T.map (q ≫ Pi.π _ N))).1 hm'

end Stacks.Cohomology
