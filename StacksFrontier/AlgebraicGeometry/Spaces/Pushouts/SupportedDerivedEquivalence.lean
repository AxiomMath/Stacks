module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedCounitAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedPullbackKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.CategoryTheory.Triangulated.AdjunctionRestrictedEquivalenceCounit

/-!
# `Rf_*` and `Lf^*` on complexes supported over a closed subspace (Stacks 0AFJ)

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and `T ⊆ |X|` a closed
subset, for instance `T = |Z|` for a closed subspace `Z`. Write `D_{QCoh,T}(𝒪_X)` for the objects
of `D(𝒪_X)` with quasi-coherent cohomology sheaves supported on `T`. Stacks 0AFJ says that, in
Situation 0AEV, `Rf_*` induces an equivalence `D_{QCoh,|f⁻¹Z|}(𝒪_Y) ≌ D_{QCoh,|Z|}(𝒪_X)` with
quasi-inverse `Lf^*`. The source's proof is: `Rf_*` and `Lf^*` preserve the two subcategories
(Stacks 08FA and 08F4, together with the preservation of supports), the counit
`Lf^*Rf_*Q ⟶ Q` is invertible on `D_{QCoh,|f⁻¹Z|}(𝒪_Y)` (Stacks 0AEU), and `Lf^*` has zero
kernel on `D_{QCoh,|Z|}(𝒪_X)`; the dual of Stacks 09J1 then concludes.

The deduction uses the following steps:

* `Lf^*` preserves quasi-coherence (Stacks 08F4):
  `AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`;
* `Rf_*` carries supports on `|f|⁻¹T` to supports on `T` for closed `T`:
  `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_derivedPushforward`, read for the
  derived direct image of the ringed topoi by
  `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_smallEtaleDerivedPushforward`;
* the objects supported on `T` form a triangulated subcategory `D_T(𝒪_X)`:
  `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_isTriangulated`;
* the dual of Stacks 09J1 inside subcategories, with the cone of the unit taken in `D_T(𝒪_X)`:
  `Stacks.Triangulated.restrictedEquivalenceOfIsIsoCounit`;
* Stacks 0AEU,
  `AlgebraicGeometry.Space.supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison`, read
  off for the counit of `Lf^* ⊣ Rf_*` on `D_{QCoh,|f⁻¹Z|}(𝒪_Y)` by
  `AlgebraicGeometry.Space.isIso_derivedAdjunction_counit_app_of_supportedDerivedCounitIsIso`;
* the zero kernel of `Lf^*` on `D_{|Z|}(𝒪_X)`, from the flatness of `f` along `f⁻¹Z` and the
  surjectivity of `f⁻¹Z ⟶ Z` on geometric points:
  `AlgebraicGeometry.Space.isZero_of_isZero_smallEtaleDerivedModulePullback` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.exists_geometricPointMap_eq_of_mem`.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedObjects`: the objects of `D(𝒪_X)` with
  quasi-coherent cohomology, for any model of `D(𝒪_X)`.
* `AlgebraicGeometry.Space.supportedQuasicoherentDerived`: `D_{QCoh,T}(𝒪_X)`.
* `AlgebraicGeometry.Space.supportedQuasicoherentDerivedEquivalence`: the equivalence
  `D_{QCoh,|f|⁻¹T}(𝒪_Y) ≌ D_{QCoh,T}(𝒪_X)` with functor `Rf_*` and inverse `Lf^*`, from its
  inputs, for any models of the derived categories.
* `AlgebraicGeometry.Space.DerivedPushforwardQcohDerivedStatement`: Stacks 08FA, part (1), as a
  proposition in the shape of the result that proves it.
* `AlgebraicGeometry.Space.FormalGlueingSituation.supportedDerivedEquivalence`: the equivalence
  in Situation 0AEV, at the standard models, for the derived adjunction of Stacks 07A6.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedAdjunction_counit_app_of_supportedDerivedCounitIsIso`:
  Stacks 0AEU in the shape the equivalence consumes.
* `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_smallEtaleDerivedPushforward`: the
  derived direct image of the ringed topoi preserves supports over a closed subset.

## Implementation notes

`AlgebraicGeometry.Space.FormalGlueingSituation.supportedDerivedEquivalence` takes three
propositions as hypotheses, each written in the shape of the result that proves it:

* `AlgebraicGeometry.Space.DerivedPullbackStalkComparisonStatement` (the stalk formula for
  derived pullbacks, from `AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap_fac`);
* `AlgebraicGeometry.Space.DerivedPullbackCohomologySupportedOnStatement` (proved by
  `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback`);
* `AlgebraicGeometry.Space.DerivedPushforwardQcohDerivedStatement` (Stacks 08FA, part (1), proved
  by `AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj`).

The triangulated structure of `D_QCoh(𝒪_X)` (Stacks 06WK) is not needed: the cone of the unit is
taken in the triangulated subcategory `D_{|Z|}(𝒪_X)`, on which `Lf^*` already has zero kernel.

In `AlgebraicGeometry.Space.supportedQuasicoherentDerivedEquivalence`, `Rf_*` and `Lf^*` enter as
any adjoint pair, for any models of the derived categories, with the preservation statements as
hypotheses; in Situation 0AEV they are the derived functors of the morphism of small étale ringed
topoi, which pins them up to unique isomorphism.

## References

* [Stacks Project, Tag 0AFJ](https://stacks.math.columbia.edu/tag/0AFJ)
* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The subcategories `D_{QCoh,T}` -/

section Subcategories

variable (X : AlgebraicSpaces B S hS) [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]

/-- The objects of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent, for any model of the
derived category. At the standard model these are the objects of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`. -/
abbrev quasicoherentDerivedObjects :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- `D_{QCoh,T}(𝒪_X)`: the objects of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent and
supported on `T` (Stacks 08GF). -/
abbrev supportedQuasicoherentDerived (T : Set (points B S hS X.1)) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  quasicoherentDerivedObjects B S hS X ⊓
    DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T)

/-- `D_{QCoh,T}(𝒪_X)` is closed under isomorphisms. -/
theorem supportedQuasicoherentDerived_isClosedUnderIsomorphisms (T : Set (points B S hS X.1)) :
    (supportedQuasicoherentDerived B S hS X T).IsClosedUnderIsomorphisms := by
  have : (quasicoherentDerivedObjects B S hS X).IsClosedUnderIsomorphisms :=
    ⟨fun e hE n => (inferInstance : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).IsClosedUnderIsomorphisms).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hE n)⟩
  have := derivedCategoryB_supportedModules_isClosedUnderIsomorphisms B S hS X T
  infer_instance

end Subcategories

/-! ### The equivalence -/

section Equivalence

variable {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2)]
  (T : Set (points B S hS X.1))
  (Lf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) [Lf.CommShift ℤ] [Lf.IsTriangulated]
  (Rf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (adj : Lf ⊣ Rf)
  (hRfQ : ∀ E, quasicoherentDerivedObjects B S hS Y E →
    quasicoherentDerivedObjects B S hS X (Rf.obj E))
  (hLfQ : ∀ E, quasicoherentDerivedObjects B S hS X E →
    quasicoherentDerivedObjects B S hS Y (Lf.obj E))
  (hLfS : ∀ E, DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) E →
    DerivedCategoryB.derivedCategoryB
      (supportedModules B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T)) (Lf.obj E))
  (hRfS : ∀ E, DerivedCategoryB.derivedCategoryB
      (supportedModules B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T)) E →
    DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) (Rf.obj E))
  (hcounit : ∀ E, supportedQuasicoherentDerived B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T) E →
    IsIso (adj.counit.app E))
  (hker : ∀ E, DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) E →
    IsZero (Lf.obj E) → IsZero E)

/-- **The equivalence of Stacks 0AFJ, from its inputs.** `Rf_*` restricts to an equivalence
`D_{QCoh,|f|⁻¹T}(𝒪_Y) ≌ D_{QCoh,T}(𝒪_X)` with quasi-inverse the restriction of `Lf^*`, given that
`Rf_*` and `Lf^*` preserve quasi-coherence and supports, that the counit `Lf^*Rf_*Q ⟶ Q` is
invertible on `D_{QCoh,|f|⁻¹T}(𝒪_Y)` (Stacks 0AEU) and that `Lf^*` has zero kernel on the objects
of `D(𝒪_X)` supported on `T`. The deduction is the dual of Stacks 09J1,
`Stacks.Triangulated.restrictedEquivalenceOfIsIsoCounit`, run with the triangulated subcategory
`D_T(𝒪_X)` (`AlgebraicGeometry.Space.derivedCategoryB_supportedModules_isTriangulated`) in which
the cone of the unit at an object of `D_{QCoh,T}(𝒪_X)` lies. -/
def supportedQuasicoherentDerivedEquivalence :
    (supportedQuasicoherentDerived B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T)).FullSubcategory ≌
      (supportedQuasicoherentDerived B S hS X T).FullSubcategory :=
  haveI := derivedCategoryB_supportedModules_isTriangulated B S hS X T
  haveI := derivedCategoryB_supportedModules_isClosedUnderIsomorphisms B S hS X T
  (Stacks.Triangulated.restrictedEquivalenceOfIsIsoCounit adj
    (supportedQuasicoherentDerived B S hS X T)
    (supportedQuasicoherentDerived B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T))
    (DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T)) (fun _ hE => hE.2)
    (fun E hE => ⟨hLfQ E hE.1, hLfS E hE.2⟩)
    (fun E hE => ⟨hRfQ E hE.1, hRfS E hE.2⟩)
    hcounit hker).symm

/-- The functor of `AlgebraicGeometry.Space.supportedQuasicoherentDerivedEquivalence` is `Rf_*`. -/
theorem supportedQuasicoherentDerivedEquivalence_functor_obj_obj
    (E : (supportedQuasicoherentDerived B S hS Y
      (pointsMap B S hS Y.1 f.hom ⁻¹' T)).FullSubcategory) :
    ((supportedQuasicoherentDerivedEquivalence B S hS f T Lf Rf adj hRfQ hLfQ hLfS hRfS hcounit
      hker).functor.obj E).obj = Rf.obj E.obj :=
  rfl

/-- The inverse of `AlgebraicGeometry.Space.supportedQuasicoherentDerivedEquivalence` is
`Lf^*`. -/
theorem supportedQuasicoherentDerivedEquivalence_inverse_obj_obj
    (E : (supportedQuasicoherentDerived B S hS X T).FullSubcategory) :
    ((supportedQuasicoherentDerivedEquivalence B S hS f T Lf Rf adj hRfQ hLfQ hLfS hRfS hcounit
      hker).inverse.obj E).obj = Lf.obj E.obj :=
  rfl

end Equivalence

/-! ### Stacks 0AEU in the shape of the counit hypothesis -/

section Counit

open Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance] isGrothendieckAbelian_ringedToposModules

/-- **Stacks 0AEU, read on `D_{QCoh,|f⁻¹Z|}(𝒪_Y)`.** At the standard model, the statement
`AlgebraicGeometry.Space.SupportedDerivedCounitIsIso` of Stacks 0AEU gives, for `f : Y ⟶ X` and a
finitely presented closed subspace `Z` with `f⁻¹Z ⟶ Z` an isomorphism and `f` flat at the points of
`f⁻¹Z`, that the counit of `Lf^* ⊣ Rf_*` is invertible at every object of
`D_{QCoh,|f|⁻¹|Z|}(𝒪_Y)`. This is the hypothesis `hcounit` of
`AlgebraicGeometry.Space.supportedQuasicoherentDerivedEquivalence`; the only translation is
`|f⁻¹Z| = |f|⁻¹|Z|` (`AlgebraicGeometry.Space.subspacePointSet_preimage`). -/
theorem isIso_derivedAdjunction_counit_app_of_supportedDerivedCounitIsIso
    (h0AEU : SupportedDerivedCounitIsIso B S hS) {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
    (hZfp : IsFinitePresentation B S hS Z.ι) (hiso : IsIso (Z.fromPreimage f.hom))
    (hflat : ∀ y : points B S hS (Z.preimage f.hom).toFunctor,
      IsFlatAt B S hS f.hom
        (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι y)) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
    ∀ E, supportedQuasicoherentDerived B S hS Y
        (pointsMap B S hS Y.1 f.hom ⁻¹' subspacePointSet B S hS X.1 Z) E →
      IsIso ((derivedAdjunction (smallEtaleRingedToposHom B S hS f)).counit.app E) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  intro E hE
  refine h0AEU f Z hZ hZfp hiso hflat ⟨E, hE.1⟩ ?_
  have h := hE.2
  rw [← subspacePointSet_preimage] at h
  exact h

end Counit

/-! ### Situation 0AEV -/

section Situation

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward

attribute [local instance] isGrothendieckAbelian_ringedToposModules
  hasLeftDerivedFunctor_pullbackOnHomotopy

/-- **Stacks 08FA, part (1), as a proposition**: for a quasi-compact and quasi-separated morphism
`f : X ⟶ Y` of algebraic spaces, the derived direct image `Rf_*` of the morphism of small étale
ringed topoi carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`, at the standard models. It is written so
that `AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj` proves it:
there `Rf_*` is `AlgebraicGeometry.Space.derivedModulePushforward`, an abbreviation of the
functor written out here. -/
def DerivedPushforwardQcohDerivedStatement : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsQuasiCompact B S hS f.hom →
    IsQuasiSeparated B S hS f.hom →
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
    ∀ E, QcohDerived B S hS X E → QcohDerived B S hS Y
      ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj E)

/-- **The derived direct image of the morphism of small étale ringed topoi preserves supports over
a closed subset**, at the standard models: if every cohomology sheaf of `E ∈ D(𝒪_Y)` is supported
on `|f|⁻¹T` for a closed `T ⊆ |X|`, then every cohomology sheaf of `Rf_*E` is supported on `T`.
This is `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_derivedPushforward` for the
total right derived functor of the direct image of the ringed topoi, which is a right derived
functor of `AlgebraicGeometry.Space.modulePushforward`, the two direct images being equal
(`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`). -/
theorem derivedCategoryB_supportedModules_smallEtaleDerivedPushforward
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (T : Set (points B S hS X.1))
    (hT : @IsClosed _ (pointTopology B S hS X.1) T) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
    let Rf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
      derivedPushforward (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS f)
    ∀ E, DerivedCategoryB.derivedCategoryB
        (supportedModules B S hS Y (pointsMap B S hS Y.1 f.hom ⁻¹' T)) E →
      DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) (Rf.obj E) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  intro Rf
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O))
  let φ := smallEtaleRingedToposHom B S hS f
  let F₀ : HomotopyCategory (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y)
      (Y := smallEtaleRingedTopos B S hS X) φ
  have hEq : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh = F₀ := by
    have key : ∀ (G : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2),
        φ.pushforwardModules = G → ∀ [G.Additive],
          G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh = F₀ := by
      intro G hG _
      subst hG
      rfl
    exact key _ (pushforwardModules_eq_modulePushforward B S hS f)
  have gen : ∀ (F' : HomotopyCategory (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2)), F' = F₀ →
      ∃ α : F' ⟶ DerivedCategory.Qh ⋙ Rf,
        Rf.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) := by
    intro F' hF'
    subst hF'
    have hI : (derivedPushforward (X := smallEtaleRingedTopos B S hS Y)
        (Y := smallEtaleRingedTopos B S hS X) φ).IsRightDerivedFunctor
          ((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y)
            (Y := smallEtaleRingedTopos B S hS X) φ).totalRightDerivedUnit DerivedCategory.Qh
              (HomotopyCategory.quasiIso (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O))
                (ComplexShape.up ℤ)))
          (HomotopyCategory.quasiIso (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O))
            (ComplexShape.up ℤ)) :=
      inferInstance
    exact ⟨_, hI⟩
  obtain ⟨αf, hαf⟩ := gen _ hEq
  exact fun E hE => derivedCategoryB_supportedModules_derivedPushforward B S hS f T hT Rf αf E hE

/-- **Stacks 0AFJ in Situation 0AEV, from three statements.** In Situation 0AEV
(`AlgebraicGeometry.Space.FormalGlueingSituation`), at the standard models of the derived
categories and with `Lf^* ⊣ Rf_*` the derived adjunction of the morphism of small étale ringed
topoi of `f` (Stacks 07A6), `Rf_*` restricts to an equivalence
`D_{QCoh,|f⁻¹Z|}(𝒪_Y) ≌ D_{QCoh,|Z|}(𝒪_X)` with quasi-inverse `Lf^*`.

The three hypotheses are Stacks 08FA, 08F4 and the stalk formula for derived pullbacks, each
written in the shape of the result that proves it:

* `H : AlgebraicGeometry.Space.DerivedPullbackStalkComparisonStatement`: the stalk at `x̄'` of
  the comparison `Lg^*P ⟶ g^*P` is invertible where derived base change along
  `𝒪_{X,g(x̄')} ⟶ 𝒪_{X',x̄'}` is computed termwise at `P_{g(x̄')}`; a consequence of
  `AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap_fac`. It gives Stacks 0AEU
  (`AlgebraicGeometry.Space.supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison`) and
  the zero kernel of `Lf^*` on `D_{|Z|}(𝒪_X)`
  (`AlgebraicGeometry.Space.isZero_of_isZero_smallEtaleDerivedModulePullback`).
* `hLfS : AlgebraicGeometry.Space.DerivedPullbackCohomologySupportedOnStatement`: `Lg^*` carries
  supports on `T` to supports on `|g|⁻¹T`; proved by
  `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback`.
* `hRfQ : AlgebraicGeometry.Space.DerivedPushforwardQcohDerivedStatement`: Stacks 08FA, part (1);
  proved by `AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj`. -/
def FormalGlueingSituation.supportedDerivedEquivalence (D : FormalGlueingSituation B S hS)
    (H : DerivedPullbackStalkComparisonStatement B S hS)
    (hLfS : DerivedPullbackCohomologySupportedOnStatement B S hS)
    (hRfQ : DerivedPushforwardQcohDerivedStatement B S hS) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2)
    (supportedQuasicoherentDerived B S hS D.spaceY
        (subspacePointSet B S hS D.Y (D.Z.preimage D.f))).FullSubcategory ≌
      (supportedQuasicoherentDerived B S hS D.spaceX
        (subspacePointSet B S hS D.X D.Z)).FullSubcategory := by
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2)
  have hT : @IsClosed _ (pointTopology B S hS D.X) (subspacePointSet B S hS D.X D.Z) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS D.algebraicSpace_X D.Z.ι D.closed_Z.2
  let Lf : DerivedCategory (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) :=
    smallEtaleDerivedModulePullback B S hS D.ambientMorphism
  let Rf : DerivedCategory (Modules.{u, u} B S hS D.spaceY.1 D.spaceY.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :=
    derivedPushforward (X := smallEtaleRingedTopos B S hS D.spaceY)
      (Y := smallEtaleRingedTopos B S hS D.spaceX)
      (smallEtaleRingedToposHom B S hS D.ambientMorphism)
  letI : Lf.CommShift ℤ := commShift_smallEtaleDerivedModulePullback B S hS D.ambientMorphism
  haveI : Lf.IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS D.ambientMorphism
  rw [subspacePointSet_preimage]
  exact supportedQuasicoherentDerivedEquivalence B S hS D.ambientMorphism
    (subspacePointSet B S hS D.X D.Z)
    Lf Rf (derivedAdjunction (smallEtaleRingedToposHom B S hS D.ambientMorphism))
    (hRfQ D.ambientMorphism D.quasiCompact_f D.quasiSeparated_f)
    (fun E hE => derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS D.ambientMorphism E hE)
    (fun E hE => hLfS D.ambientMorphism E hE)
    (derivedCategoryB_supportedModules_smallEtaleDerivedPushforward B S hS D.ambientMorphism _ hT)
    (isIso_derivedAdjunction_counit_app_of_supportedDerivedCounitIsIso B S hS
      (supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison B S hS H)
      D.ambientMorphism D.Z D.closed_Z D.finitePresentation_Z D.iso_over_Z D.flat_at_preimage_Z)
    (isZero_of_isZero_smallEtaleDerivedModulePullback B S hS D.ambientMorphism H _
      (D.exists_geometricPointMap_eq_of_mem))

end Situation

end AlgebraicGeometry.Space

end
