module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianSupportedEndoModelFactors
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetIdentity
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomologyCompare

/-!
# Stacks 0G74 part (2) in degree `c`: the two readings agree

`Stacks.Perfect.SupportedEndoForgetIdentity.forgetComparison_eq` identifies the two readings of
[Stacks, Tag 0G74] part (2) — the one on the closed subset `T` and the one with the direct image
`i_*` folded in — as transformations of derived functors.
`Stacks.Perfect.AbelianSupportedEndoModelFactors.forgetIsoApp_of_derivedForgetIdentity` reduces the
hypothesis `forgetIsoApp` of `Stacks.Perfect.AbelianSupportedEndoModelBridge` to the degree-`c`
cohomology of that identity, which is `DerivedForgetIdentity`.  This file takes that degree-`c`
cohomology and so discharges `forgetIsoApp`.

It then discharges the other `ψ`-free hypothesis of that file, `hforgetIso`, which is the same
degree-`c` identity in the `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` spelling of
[Stacks, Tag 0G7S] rather than the Gysin map's.  The only difference between the two spellings is
where the degree-`c` cohomology sheaf is taken relative to `i_*`; the comparison between the two
places is `Stacks.Perfect.AbelianSupportedEndoModelFactors.pushHomologySingle`, and
`supportCohomologySheafFunctorIso_hom_app_eq` identifies it with the component of
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso` that the `0G7S` spelling is
built from.  So no new mathematics is needed for `hforgetIso` beyond `derivedForgetIdentity`: it is
the untwisted form of `forgetIsoApp`, for an arbitrary closed subset instead of the zero locus of a
global family of equations.

## Main results

* `derivedForgetIdentity`: **`DerivedForgetIdentity` holds**, for every closed subset and every
  degree.
* `forgetIsoApp`: **the hypothesis of
  `Stacks.Perfect.AbelianSupportedEndoModelBridge.forgetIsoSquare_of_forgetIsoApp` holds.**
* `supportCohomologySheafForgetIso_hom_app`: **the hypothesis `hforgetIso` of
  `Stacks.Perfect.AbelianSupportedEndoModelBridge` holds**, for every closed subset and every
  degree — the two constructions of [Stacks, Tag 0G74] part (2), read on degree-`c` cohomology
  sheaves, are the same isomorphism.
* `supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap`: **the two constructions of
  the action of `i_*ℋ ᶜ_T` on a morphism of the underlying abelian sheaves agree**,
  unconditionally.  This is the right-hand vertical arrow of the comparison square of step (ii) of
  [Stacks, Tag 0G85], and the statement carries no hypothesis beyond `hT`.

## Implementation notes

Feeding the identity of the two transformations through `Hᶜ` needs four "an exact functor commutes
with `Hⁿ`" comparisons and the two readings of `Φ(ℱ[0]) ≅ (Φℱ)[0]`.  Three of the identifications
were already in the library
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`,
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso_eq` and
`Stacks.Perfect.AbelianSupportedEndoModelFactors.singleForgetIso_eq`); the fourth is the
degreewise reading of the derived pushforward/forget comparison,
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_homology`.

Every rearrangement below is a `private` lemma stated at a variable category and applied with
`exact`: the chain crosses the two spellings `i_* ⋙ Φ_X` and `Φ_T ⋙ i_*^{ab}` of one functor, and
also the two spellings `Stacks.Cohomology.SupportedComplexes.abelianClosedPushforward` and
`Stacks.Cohomology.ModulePushforwardComparison.abelianPushforward` of the abelian direct image,
which are definitionally equal and which `rw` and `simp` refuse to identify.  This is the device of
`Stacks.Perfect.AbelianSupportedEndoModelFactors.assoc_of_head` and of `chain_cancel` in
`StacksFrontier/Topology/Sheaves/Cohomology/ModulePushforwardComparison/DerivedCategory.lean`.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G74] or [Stacks, Tag 0G85].

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianModelComparison (abelianPushHomologySingleIso)
open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward)
open Stacks.Cohomology.ModulePushforwardComparison
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.AbelianCechCokernelPassage (forgetDerivedHomology)
open Stacks.Perfect.AbelianCechDerivedSquare (forgetComparisonIso)
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.AbelianSupportedEndoModelBridge (singleForgetIso pushIsoApp endoForgetIsoApp
  supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso)
open Stacks.Perfect.AbelianSupportedEndoModelFactors
open Stacks.Perfect.CechDerivedSupport (isClosed_equationsClosedSet)
open Stacks.Perfect.CechSupportTransport (supportCohomologyToPushforward)
open Stacks.Perfect.GysinAbelianSquare (abelianClosedPushforward)
open Stacks.Perfect.SupportedFraction (supportPushSingle)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedEndoForgetDegreewise

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Formal rearrangements -/

/-- Stripping the common last factor off the two sides of the degreewise identity, at abstract
categories: the general degreewise comparison is read in the direction with the comparison of the
forgetful functor on `T` inverted, and then followed by the remaining factor. -/
private lemma assemble_formal {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : C₀ ⥤ D₀)
    {n₀ n₁ n₂ : C₀} {a₀ a₁ a₂ a₃ : D₀} (α : a₀ ≅ a₁) (π : a₁ ⟶ a₂) (ρ : a₂ ⟶ W.obj n₀)
    (μ : n₀ ⟶ n₁) (ν : n₁ ⟶ n₀) (ξ : n₁ ⟶ n₂) (β : a₀ ⟶ a₃) (γ : a₃ ⟶ W.obj n₁)
    (hνμ : ν ≫ μ = 𝟙 n₁) (key : β ≫ γ ≫ W.map ν = α.hom ≫ π ≫ ρ) :
    π ≫ ρ ≫ W.map (μ ≫ ξ) = α.inv ≫ β ≫ γ ≫ W.map ξ := by
  have h : β ≫ γ = α.hom ≫ π ≫ ρ ≫ W.map μ := by
    have h0 : (β ≫ γ ≫ W.map ν) ≫ W.map μ = (α.hom ≫ π ≫ ρ) ≫ W.map μ := by rw [key]
    simp only [Category.assoc] at h0
    rwa [← W.map_comp, hνμ, W.map_id, Category.comp_id] at h0
  rw [W.map_comp, ← Category.assoc β γ (W.map ξ), h]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

/-- Rewriting the unbounded-model side of the degreewise identity, at an abstract category: the
first factor splits by the identity of the two readings of [Stacks, Tag 0G74] part (2), the second
is rewritten by the identity of the two readings of `Φ(ℱ[0]) ≅ (Φℱ)[0]`, the two are collapsed into
one, and the naturality of the comparison for the abelian direct image finishes. -/
private lemma rhs_formal {C₀ : Type*} [Category* C₀] {a₀ a₁ a₂ a₃ b₀ b₁ : C₀}
    (P : a₀ ⟶ a₂) (β : a₀ ⟶ a₁) (p : a₁ ⟶ a₂) (q q' : a₂ ⟶ a₃) (g : a₃ ⟶ b₁) (γ : a₁ ⟶ b₀)
    (w : b₀ ⟶ b₁) (pq : a₁ ⟶ a₃)
    (hP : P = β ≫ p) (hq : q = q') (hpq : p ≫ q' = pq) (hn : pq ≫ g = γ ≫ w) :
    P ≫ q ≫ g = β ≫ γ ≫ w := by
  rw [hP, hq, Category.assoc β p (q' ≫ g), ← Category.assoc p q' g, hpq, hn]

/-- Splitting the image of a morphism known to be a composite, at abstract categories. -/
private lemma map_split {A₀ B₀ : Type*} [Category* A₀] [Category* B₀] (W : A₀ ⥤ B₀)
    {a b d : A₀} (x : a ⟶ b) (y : b ⟶ d) (z : a ⟶ d) (h : x ≫ y = z) :
    W.map z = W.map x ≫ W.map y := by
  rw [← h, W.map_comp]

/-- Collapsing two successive images of a composable pair under a composite of two functors, at
abstract categories. -/
private lemma map_map_comp {A₀ B₀ E₀ : Type*} [Category* A₀] [Category* B₀] [Category* E₀]
    (V : A₀ ⥤ B₀) (W : B₀ ⥤ E₀) {x y z : A₀} (a : x ⟶ y) (b : y ⟶ z) :
    W.map (V.map a) ≫ W.map (V.map b) = W.map (V.map (a ≫ b)) := by
  rw [← W.map_comp, ← V.map_comp]

/-- Naturality of a transformation `V ⋙ W ⟶ W' ⋙ V'` at a composite, with the image of the
composite under `W'` split, at abstract categories. -/
private lemma naturality_map_comp {A₀ B₀ C₀ E₀ : Type*} [Category* A₀] [Category* B₀]
    [Category* C₀] [Category* E₀] (V : A₀ ⥤ B₀) (W : B₀ ⥤ E₀) (W' : A₀ ⥤ C₀) (V' : C₀ ⥤ E₀)
    (e : V ⋙ W ⟶ W' ⋙ V') {x y z : A₀} (a : x ⟶ y) (b : y ⟶ z) :
    W.map (V.map (a ≫ b)) ≫ e.app z = e.app x ≫ V'.map (W'.map a ≫ W'.map b) :=
  (e.naturality (a ≫ b)).trans (whisker_eq _ (congrArg V'.map (W'.map_comp a b)))

/-- The two descents of "an exact functor commutes with `Hⁿ`" agree componentwise, at abstract
categories. -/
private lemma mapDerivedCategoryHomologyFunctorIso_hom_app_eq.{w₁, w₂, v₁, v₂, u₁, u₂}
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ)
    (K : DerivedCategory C₁) :
    (F.mapDerivedCategoryHomologyIso n).hom.app K =
      (F.mapDerivedCategoryHomologyFunctorIso n).hom.app K :=
  by rw [F.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso]

/-! ### The degreewise identity -/

section Identity

variable {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) (c : ℕ) (H : X.Modules)

/-- **The two readings of [Stacks, Tag 0G74] part (2) agree in degree `c`.**  This is
`Stacks.Perfect.AbelianSupportedEndoModelFactors.DerivedForgetIdentity`, the one input that
`forgetIsoApp` was reduced to. -/
theorem derivedForgetIdentity : DerivedForgetIdentity hT c := by
  intro H
  let := pushforward_preservesFiniteLimits X.toRingedSpace T
  let := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  let : PreservesFiniteColimits
      (abelianPushforward (closedSubsetInclusion X.toRingedSpace T)) :=
    Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
      X.toRingedSpace T hT
  let := Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits
    X.toRingedSpace T hT
  let := Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteColimits
    X.toRingedSpace T hT
  have hα : ((abelianSheaf X).mapDerivedCategoryHomologyFunctorIso (c : ℤ)).hom.app
        (supportPushSingle hT H) =
      (forgetDerivedHomology (supportPushSingle hT H) (c : ℤ)).hom :=
    (mapDerivedCategoryHomologyFunctorIso_hom_app_eq _ _ _).symm
  have hν : ((_root_.SheafOfModules.toSheaf
            (structureSheafRing
              (closedSubsetRingedSpace X.toRingedSpace
                T))).mapDerivedCategoryHomologyFunctorIso (c : ℤ)).hom.app
        ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj H)) =
      (modelForgetHomology X.toRingedSpace T hT c H).inv :=
    (mapDerivedCategoryHomologyFunctorIso_hom_app_eq _ _ _).symm
  -- the general degreewise comparison, transported to the spellings of the identity
  have key : (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
          ((derivedModulePushforwardCompToSheafIso
            (closedSubsetInclusion X.toRingedSpace T)).hom.app
            ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj H))) ≫
        ((abelianPushforward
              (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategoryHomologyFunctorIso
            (c : ℤ)).hom.app
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing
              (closedSubsetRingedSpace X.toRingedSpace T))).mapDerivedCategory.obj
            ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
              ((DerivedCategory.singleFunctor X.Modules 0).obj H))) ≫
        (abelianClosedPushforward X.toRingedSpace T).map
          (modelForgetHomology X.toRingedSpace T hT c H).inv =
      (forgetDerivedHomology (supportPushSingle hT H) (c : ℤ)).hom ≫
        (abelianSheaf X).map (pushHomologySingle hT c H).hom ≫
        (modulePushforwardCompToSheafIso
            (closedSubsetInclusion X.toRingedSpace T)).hom.app
          ((localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).obj H) := by
    rw [← hα, ← hν]
    exact derivedModulePushforwardCompToSheafIso_homology
      (closedSubsetInclusion X.toRingedSpace T) (c : ℤ)
      ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj H))
  -- the unbounded-model side, rewritten by Step A and by the two readings of `Φ(ℱ[0])`
  have hStepA := NatTrans.congr_app
    (Stacks.Perfect.SupportedEndoForgetIdentity.forgetComparison_eq hT)
    ((DerivedCategory.singleFunctor X.Modules 0).obj H)
  have hP : (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
        (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj H)).hom =
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
          ((derivedModulePushforwardCompToSheafIso
            (closedSubsetInclusion X.toRingedSpace T)).hom.app
            ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj H))) ≫
        (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
          ((abelianClosedPushforward T).mapDerivedCategory.map
            ((localCohomologySheafForgetComparison X.toRingedSpace T hT
            (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT)
            (derivedAbelianSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
            (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
            (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj H))) :=
    map_split _ _ _ _ hStepA
  have hq : (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          (singleForgetIso H).hom) =
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
        ((abelianClosedPushforward T).mapDerivedCategory.map
          ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT).map
          (singleForgetMathlib X.toRingedSpace H).hom)) :=
    congrArg (fun z => (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
      ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map (Iso.hom z)))
      (singleForgetIso_eq H)
  exact (assemble_formal _ _ _ _ _ _
        ((DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).map
            ((localCohomologySheafForgetComparison X.toRingedSpace T hT
            (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT)
            (derivedAbelianSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
            (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
            (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj H)) ≫
          (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).map
            ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT).map
          (singleForgetMathlib X.toRingedSpace H).hom)) _ _
        (Iso.inv_hom_id (modelForgetHomology X.toRingedSpace T hT c H)) key).trans
    (whisker_eq _ (rhs_formal _ _ _ _ _ _ _ _ _ hP hq (map_map_comp _ _ _ _)
      (naturality_map_comp _ _ _ _
        ((abelianClosedPushforward T).mapDerivedCategoryHomologyFunctorIso (c : ℤ)).hom _ _))).symm

/-! ### Stacks 0G74 part (2) in the `supportCohomologySheaf` spelling -/

/-- **[Stacks, Tag 0G74] part (2) at a module, for an arbitrary closed subset and degree**: the
classical-model reading and the unbounded-model reading of the identification agree, once the two
places at which the degree-`c` cohomology sheaf is taken are compared by `pushHomologySingle`.

This is the proof of
`Stacks.Perfect.AbelianSupportedEndoModelFactors.forgetIsoApp_of_derivedForgetIdentity` with the
family of equations removed — that statement spells the comparison of the two places as
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward`, which needs the equations,
and `supportCohomologyToPushforward_eq` says the two spellings are the same morphism.  The
hypothesis is discharged by `derivedForgetIdentity`. -/
theorem pushHomologySingle_pushIsoApp_eq_endoForgetIsoApp :
    (abelianSheaf X).map (pushHomologySingle hT c H).hom ≫ (pushIsoApp hT c H).hom =
      (endoForgetIsoApp hT c H).hom :=
  ((whisker_eq _ (pushIsoApp_hom hT c H)).trans
      (AbelianSupportedEndoModelFactors.assoc_of_head _ _ _ _ _
        (derivedForgetIdentity hT c H))).trans
    (endoForgetIsoApp_hom hT c H).symm

/-- **The comparison of the two places at which the degree-`c` cohomology sheaf is taken is
`pushHomologySingle`.**  The left-hand side is the component of
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`, which is built from
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso`; the right-hand side is
built from `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`.  Those are two of the
three copies of "an exact functor commutes with `Hᶜ`", and the triangle identifying them is
`exactFunctorDerivedHomologyIso_eq` followed by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`. -/
theorem supportCohomologySheafFunctorIso_hom_app_eq :
    (Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso hT (c : ℤ)).hom.app H =
      (pushHomologySingle hT c H).hom := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace T
  let := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  have h : exactFunctorDerivedHomologyIso
        (modulePushforward (closedSubsetInclusion X.toRingedSpace T)) (c : ℤ) =
      (modulePushforward
        (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategoryHomologyFunctorIso (c : ℤ) :=
    (exactFunctorDerivedHomologyIso_eq _ _).trans
      (CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso
        _ _)
  exact congrArg (fun z => z.hom.app
    ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj H))) h

/-- **The component of `supportCohomologySheafForgetIso` splits as the comparison of the two
places at which the degree-`c` cohomology sheaf is taken, followed by `pushIsoApp`.**  Both sides
are the same term: `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso` is a
`CategoryTheory.Iso.trans` of a `CategoryTheory.Functor.isoWhiskerRight` with
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso`, and `pushIsoApp` is the
component of the latter. -/
theorem supportCohomologySheafForgetIso_hom_app_split :
    (Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso hT c).hom.app H =
      (abelianSheaf X).map
          ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso
            hT (c : ℤ)).hom.app H) ≫
        (pushIsoApp hT c H).hom := rfl

/-- **The hypothesis `hforgetIso` of
`supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso` of
`Stacks.Perfect.AbelianSupportedEndoModelBridge` holds**, for every closed subset and every
degree: the two constructions of [Stacks, Tag 0G74]
part (2), read on degree-`c` cohomology sheaves, are the same isomorphism.  The left-hand side is
the one assembled in `Stacks.Perfect.GysinAbelianSquare` out of the comparison on `T`, the
right-hand side the one assembled in `Stacks.Perfect.AbelianSupportedEndoModelBridge` out of the
unbounded model with `i_*` folded in.

No morphism of coefficient modules occurs, and there is no hypothesis beyond `hT`; in particular
no quasi-coherence. -/
theorem supportCohomologySheafForgetIso_hom_app :
    (Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso hT c).hom.app H =
      (endoForgetIsoApp hT c H).hom :=
  (supportCohomologySheafForgetIso_hom_app_split hT c H).trans
    ((congrArg (fun z => (abelianSheaf X).map z ≫ (pushIsoApp hT c H).hom)
        (supportCohomologySheafFunctorIso_hom_app_eq hT c H)).trans
      (pushHomologySingle_pushIsoApp_eq_endoForgetIsoApp hT c H))

end Identity

/-! ### The two actions of `i_*ℋ ᶜ_T` on a morphism of the underlying abelian sheaves agree -/

section AbelianMap

variable {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) (c : ℕ)

/-- **The two constructions of the action of `i_*ℋ ᶜ_T` on a morphism of the underlying abelian
sheaves agree, unconditionally.**  This is
`supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso` of
`Stacks.Perfect.AbelianSupportedEndoModelBridge`, with its hypothesis `hforgetIso` discharged by
`supportCohomologySheafForgetIso_hom_app`.

The left-hand side is the right-hand vertical arrow of the comparison square of step (ii) of
[Stacks, Tag 0G85] in the Gysin map's spelling; the right-hand side is the one obtained from the
unbounded model.  There is no hypothesis beyond `hT`: nothing on `ψ`, which is an arbitrary
morphism of the underlying abelian presheaves and in particular need not be `𝒪_X`-linear, and no
quasi-coherence. -/
theorem supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap {F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap hT c
        (Stacks.Perfect.AbelianFraction.abHom ψ) =
      Stacks.Perfect.AbelianCechCokernelPassage.supportCohomologyForgetAbMap hT (c : ℤ) ψ :=
  supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap_of_forgetIso hT c ψ
    (supportCohomologySheafForgetIso_hom_app hT c)

end AbelianMap

/-! ### The hypothesis `forgetIsoApp`, and the square of Stacks 0G85 for the Gysin formula -/

section Consequences

attribute [local instance]
  AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms

variable {X : Scheme.{u}} {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))

/-- **The hypothesis `forgetIsoApp` of
`Stacks.Perfect.AbelianSupportedEndoModelBridge.forgetIsoSquare_of_forgetIsoApp` holds.**  The
comparison between the two places at which the degree-`c` cohomology sheaf is taken carries the
classical-model reading of [Stacks, Tag 0G74] part (2) to the unbounded-model reading.  This is
`Stacks.Perfect.AbelianSupportedEndoModelFactors.forgetIsoApp_of_derivedForgetIdentity` with its
hypothesis discharged by `derivedForgetIdentity`. -/
theorem forgetIsoApp (H : X.Modules) :
    (abelianSheaf X).map (supportCohomologyToPushforward f H).hom ≫
        (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom =
      (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom :=
  forgetIsoApp_of_derivedForgetIdentity f
    (derivedForgetIdentity (isClosed_equationsClosedSet f) (n + 1)) H

/-- **The class in `i_*ℋ ᶜ_Z(ℱ)` of a top-degree Čech cochain is natural in an arbitrary morphism
of the underlying abelian sheaves of the coefficient modules.**  This is
`Stacks.Perfect.AbelianSupportedEndoModelBridge.topCechClassAbelianNatural_of_forgetIsoApp` with
its hypothesis discharged by `forgetIsoApp`. -/
theorem topCechClassAbelianNatural {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural f ψ :=
  Stacks.Perfect.AbelianSupportedEndoModelBridge.topCechClassAbelianNatural_of_forgetIsoApp f ψ
    (forgetIsoApp f)

/-- **The comparison square of [Stacks, Tag 0G85] for the Gysin formula holds.**  This is
`Stacks.Perfect.GysinFractionDeRham.gysinFormulaCommutesWithDeRham_of_topCechClassNatural` with its
hypothesis discharged by `topCechClassAbelianNatural`.

This is the square for `AlgebraicGeometry.Scheme.Hom.gysinFormulaHom`.  The square for
`AlgebraicGeometry.Scheme.Hom.gysinMap` itself needs in addition restriction of `p`-forms to `Z`
as a morphism of abelian sheaves together with its commutation with the de Rham differentials;
those are supplied in
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinMapDeRham.lean`, which reduces the square for the
Gysin map to this one and carries the `@[stacks 0G85]` attribute.  That is why no
`@[stacks 0G85]` attribute is attached here. -/
theorem gysinFormulaCommutesWithDeRham {S : Scheme.{u}} (π : X ⟶ S) (p : ℕ) :
    AlgebraicGeometry.Scheme.Hom.GysinFormulaCommutesWithDeRham π f p :=
  Stacks.Perfect.GysinFractionDeRham.gysinFormulaCommutesWithDeRham_of_topCechClassNatural f π p
    (topCechClassAbelianNatural f _)

end Consequences

end Stacks.Perfect.SupportedEndoForgetDegreewise

end
