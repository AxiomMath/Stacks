module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NoetherianComponentEnvelope
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoof
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedHomotopy
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChowHomologyCoherentKZeroBijective
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterVectorBundle
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularVectorBundleKGroup
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRegular
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TriangleAdditivityResolution

/-!
# The map `α ↦ ch(α) ∩ [X]` and the dimension of supports

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a Noetherian
scheme locally of finite type over `S`. Lemma 0FEY of the Stacks Project concerns the composition

  `K_0(Vect(X)) ⟶ A^*(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,   `α ↦ ch(α) ∩ [X]`,

of the Chern character of Remark 0FEM with capping the fundamental class. When `X` is moreover
regular with affine diagonal, `K_0(Vect(X)) = K'_0(X)` (Stacks 0FDI, 0F8A, 0FDJ) and the
composition becomes a homomorphism `K'_0(X) ⟶ CH_*(X) ⊗ 𝐐`. By Remark 0FEU it is the map of
Proposition 0FEW for `X = Y`, and the proof of that proposition reduces bijectivity to two
conditions on it. This file constructs the composition and proves the first condition: **the
class of a coherent module whose support has delta-dimension at most `j` goes into
`⨁_{j' ≤ j} CH_{j'}(X) ⊗ 𝐐`**.

The argument is the source's, with the localized Chern character of `X ⟶ X` unwound. Let `ℱ` be
a coherent `𝒪_X`-module with support `Z` of delta-dimension at most `j`, and let `α` be the class
in `K_0(Vect(X))` corresponding to `[ℱ]`. The object `ℱ[0]` is perfect and is represented by a
bounded complex `ℰ^•` of finite locally free modules (Stacks 0F8F), and `α` is the Euler
characteristic `∑_n (-1)^n [ℰ^n]`. So `P_p(α) = ∑_n (-1)^n P_p(ℰ^n)` is the power sum
`P_p(ℱ[0])` of the perfect object (Remark 0FEU). The object `ℱ[0]` restricts to zero on `X ∖ Z`,
so by Stacks 0FB2 `P_p(ℱ[0]) = i_* ∘ P_p(Z ⟶ X, ℱ[0])`, with `i : Z ⟶ X` the reduced closed
subscheme on the support. Hence `P_p(α) ∩ β` lies in the image of `CH_{k-p}(Z)` for
`β ∈ CH_k(X)`, which is zero when `k - p > j`.

## Main definitions

* `Stacks.Chow.chernCharacterCapFundamentalClass` — `α ↦ ch(α) ∩ [X]` on `K_0(Vect(X))`.
* `Stacks.Chow.rationalChernCharacterCapFundamentalClass` — its `𝐐`-linear extension to
  `K_0(Vect(X)) ⊗ 𝐐`, the map of Stacks 0FEY.
* `Stacks.Chow.coherentChernCharacterCapFundamentalClass` — for `X` regular with affine diagonal,
  the same map read on `K'_0(X)` through `AlgebraicGeometry.regularVectorBundleKZeroAddEquiv`.

## Main results

* `Stacks.Chow.chernCharacterCapFundamentalClass_eq_sum` — for `δ_{X/S}` bounded,
  `ch(α) ∩ [X] = ∑_p ch_p(α) ∩ [X]`, each summand being the map `c ↦ c ∩ [X]` of Stacks 0FEW.
* `Stacks.Chow.bijective_liftBaseChange_coherentChernCharacterCapFundamentalClass_iff` — the
  `𝐐`-linear extension on `K'_0(X) ⊗ 𝐐` is bijective exactly when the one on `K_0(Vect(X)) ⊗ 𝐐`
  is.
* `Stacks.Chow.perfectPowerSum_eq_powerSumKHom_eulerCharComplex` — the compatibility of
  Remark 0FEU for the power sums: `P_p(E) = ∑_n (-1)^n P_p(ℰ^n)` for a perfect object `E`
  represented by a bounded complex `ℰ^•` of finite locally free modules.
* `Stacks.Chow.chowCohomologyCap_properPushforwardChowCohomology_eq_zero` — for a proper
  `i : Z ⟶ X`, the cap product of `i_* ∘ c` with a class of `CH_k(X)` vanishes when no point of
  `Z` has delta-dimension `k - p`.
* `Stacks.Chow.isDimensionTriangular_coherentChernCharacterCapFundamentalClass` — **condition (1)
  of the proof of Stacks 0FEW** for `α ↦ ch(α) ∩ [X]` on a regular Noetherian `X` with affine
  diagonal.

## Implementation notes

The source states Lemma 0FEY for `X` quasi-compact; being locally of finite type over the locally
Noetherian `S`, such an `X` is Noetherian, which is the hypothesis used here. No bound on
`δ_{X/S}` is needed for condition (1): every summand `ch_p(α) ∩ β` with `β ∈ CH_k(X)` either lies
in degree `k - p ≤ j` or vanishes, whatever the range of `p` summed over.

The localized classes are taken in Situation 0GUJ for the perfect object `ℱ[0]` (or rather an
object of `D_perf(𝒪_X)` isomorphic to it) and the reduced closed subscheme on the support of `ℱ`,
with the finiteness alternative "`X` is quasi-compact".

## References

* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FEU](https://stacks.math.columbia.edu/tag/0FEU)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Capping with a class pushed forward from a closed subscheme -/

section Vanishing

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The cap product of a pushed-forward class lands in the Chow groups of its source.** For a
proper `i : Z ⟶ X` and `c ∈ A^p(Z ⟶ X)`, the operation of `i_* ∘ c ∈ A^p(X)` on `CH_k(X)` is
`β ↦ i_*(c ∩ β)` with `c ∩ β ∈ CH_{k-p}(Z)`, so it vanishes when no point of `Z` has
delta-dimension `k - p`. -/
theorem chowCohomologyCap_properPushforwardChowCohomology_eq_zero {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (i : Z ⟶ X) [IsProper i] (hi : i ≫ sX = sZ) {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) (k : ℤ)
    (hk : ∀ z : Z, relativeDimension C.dimensionFunction sZ z ≠ k - p)
    (α : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX p
      (properPushforwardChowCohomology C sX sZ i hi c) k α = 0 := by
  have h0 : ∀ y : chowGroup C (pullback.fst (i ≫ 𝟙 X) (𝟙 X) ≫ sZ) (k - p), y = 0 :=
    chowGroup_eq_zero C _ fun y => by
      rw [relativeDimension_comp_isOpenImmersion]
      exact hk _
  simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, properPushforwardChowCohomology,
    bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply]
  rw [h0 (BivariantClass.cap _ _ _ _), map_zero, map_zero]

end Vanishing

/-! ### A coherent module in degree zero vanishes off its support -/

section Support

variable {X : Scheme.{u}}

/-- An object of `D(𝒪_X)` isomorphic to `ℱ[0]` has its cohomology sheaves supported on any set
containing the support of `ℱ`: in degree zero the cohomology sheaf is `ℱ`, in every other degree
it vanishes. -/
theorem cohomologySupportedOn_of_iso_single (F : X.Modules) (T : Set X)
    (hF : SheafOfModules.supp F ⊆ T) (K : DerivedCategory X.Modules)
    (e : K ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F) :
    AlgebraicGeometry.CohomologySupportedOn X.ringCatSheaf T K := by
  intro n y hy
  have hK : IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
      (((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)).val.presheaf) y) := by
    rcases eq_or_ne n 0 with rfl | hn
    · refine IsZero.of_iso ?_ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
        ((ExtensionByZeroModules.toAb X.ringCatSheaf).mapIso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F)))
      rw [AddCommGrpCat.isZero_iff_subsingleton]
      exact subsingleton_of_forall_eq 0 fun a => by_contra fun ha => hy (hF ⟨a, ha⟩)
    · let _ : HasZeroMorphisms (TopCat.Presheaf AddCommGrpCat.{u} X) :=
        inferInstanceAs (HasZeroMorphisms ((TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))
      have : (ExtensionByZeroModules.toAb X.ringCatSheaf).PreservesZeroMorphisms := by
        show (_root_.SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf X.ringCatSheaf.obj).PreservesZeroMorphisms
        infer_instance
      refine Functor.map_isZero _ (Functor.map_isZero (ExtensionByZeroModules.toAb _) ?_)
      refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ n).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _))
      refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _)
      exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn
  exact hK.of_iso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
    ((ExtensionByZeroModules.toAb X.ringCatSheaf).mapIso
      ((DerivedCategory.homologyFunctor _ n).mapIso e)))

/-- **`ℱ[0]` restricts to zero off a closed set containing the support of `ℱ`**: the derived
pullback to the open complement of an object isomorphic to `ℱ[0]` is zero. This is the first
alternative of condition (2) of Situation 0GUJ for such an object. -/
theorem isZero_derivedPullback_ofRestrict_compl (F : X.Modules) (T : Set X) (hT : IsClosed T)
    (hF : SheafOfModules.supp F ⊆ T) (K : DerivedCategory X.Modules)
    (e : K ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (X.toRingedSpace.ofRestrict
        (⟨Tᶜ, hT.isOpen_compl⟩ : TopologicalSpace.Opens X).isOpenEmbedding)).obj K) :=
  IsZero.of_iso
    (Stacks.Cohomology.PushforwardRestriction.isZero_derived_restrict_compl_of_supported _ T hT K
      (cohomologySupportedOn_of_iso_single F T hF K e))
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso X.toRingedSpace
      ⟨Tᶜ, hT.isOpen_compl⟩).app K)

end Support

/-! ### The class in `K_0(Vect(X))` of a coherent module on a regular scheme -/

section KTheory

open Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

/-- **The class in `K_0(Vect(X))` of a coherent module is an Euler characteristic.** On a
quasi-compact regular `X` with affine diagonal, a coherent `ℱ` is, placed in degree zero,
isomorphic to a perfect object `K`, which is represented by a bounded complex `ℰ^•` of finite
locally free modules (Stacks 0F8F); the class of `ℱ` in `K'_0(X)` corresponds to
`∑_n (-1)^n [ℰ^n]` in `K_0(Vect(X))`. -/
theorem exists_regularVectorBundleKZeroAddEquiv_symm_mk (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ∃ (K : PerfectDerivedCategory X) (E : CochainComplex X.Modules ℤ),
      Nonempty (K.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F.obj) ∧
      boundedFiniteLocallyFreeComplex X E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K.obj) ∧
      (regularVectorBundleKZeroAddEquiv X hX).symm
          (@KZero.mk _ _ (coherentModulesAbelian X) F) =
        eulerCharComplex X E := by
  have := isLocallyNoetherian_of_isRegular hX
  have : IsNoetherian X := ⟨⟩
  have := AlgebraicGeometry.IsRegular.hasResolutionProperty X hX
  obtain ⟨K, ⟨eK⟩⟩ := (exists_addEquiv_K0_coherentKZero_of_isRegular X hX).choose_spec.1 F
  obtain ⟨E, hE, ⟨eE⟩⟩ :=
    exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty X K.obj K.property
  refine ⟨K, E, ⟨eK⟩, hE, ⟨eE⟩, ?_⟩
  have h2 : (regularVectorBundleKZeroAddEquiv X hX).symm (KZero.mk _ F) =
      (vectorBundleKZeroAddEquiv X).symm (Pretriangulated.K0.cls K) := by
    rw [AddEquiv.symm_apply_eq]
    show _ = (exists_addEquiv_K0_coherentKZero_of_isRegular X hX).choose
      (vectorBundleKZeroAddEquiv X ((vectorBundleKZeroAddEquiv X).symm
        (Pretriangulated.K0.cls K)))
    rw [AddEquiv.apply_symm_apply,
      (exists_addEquiv_K0_coherentKZero_of_isRegular X hX).choose_spec.2.1 F K eK]
  rw [h2]
  have h3 := inverseAddHom_comparisonAddHom X
    (exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty X)
    (exists_boundedFiniteLocallyFree_roof_of_hasResolutionProperty X)
    (forall_isFiniteLocallyFree_cycles X)
    ((vectorBundleKZeroAddEquiv X).symm (Pretriangulated.K0.cls K))
  rw [← vectorBundleKZeroAddEquiv_apply, AddEquiv.apply_symm_apply, inverseAddHom_cls] at h3
  rw [← h3]
  exact eulerCharPerfect_eq X _ (exists_boundedFiniteLocallyFree_roof_of_hasResolutionProperty X)
    (forall_isFiniteLocallyFree_cycles X) K E hE eE

end KTheory

/-! ### The power sums of a bounded complex of finite locally free modules -/

section PowerSum

open Stacks.Perfect.BoundedLocallyFreeComplexes

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`P_p(ℰ^•)` is `P_p` of the Euler characteristic** `∑_n (-1)^n [ℰ^n] ∈ K_0(Vect(X))`, for a
bounded complex `ℰ^•` of finite locally free modules. -/
theorem powerSumKHom_eulerCharComplex {E : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) (hP : IsLocallyBoundedFiniteLocallyFree E)
    (p : ℕ) :
    powerSumKHom C sX p (eulerCharComplex X E) = powerSumComplex C sX hP p := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff X.Modules E).mp hE.1.1
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff E).mp hE.1.2
  rw [eulerCharComplex_eq_sum X E a b ha hb, map_sum,
    powerSumComplex_eq_sum_Icc C sX hP a b
      (fun n hn => hn.elim (E.isZero_of_isStrictlyGE a n ·) (E.isZero_of_isStrictlyLE b n ·)) p]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_zsmul, @powerSumKHom_classOf C _ sX _ p (E.X n) (hP.1 n)]

/-- **The compatibility of Remark 0FEU for the power sums.** If a perfect object `K` whose Chern
classes are defined is represented by a bounded complex `ℰ^•` of finite locally free modules,
then `P_p(K)` is the image under `P_p` of the class `∑_n (-1)^n [ℰ^n]` of `K` in
`K_0(Vect(X))`. -/
theorem perfectPowerSum_eq_powerSumKHom_eulerCharComplex {K : DerivedCategory X.Modules}
    (hK : HasDefinedChernClasses K) {E : CochainComplex X.Modules ℤ}
    (hE : boundedFiniteLocallyFreeComplex X E) (e : DerivedCategory.Q.obj E ≅ K) (p : ℕ) :
    perfectPowerSum C sX hK p = powerSumKHom C sX p (eulerCharComplex X E) :=
  (perfectPowerSum_eq_powerSumComplex C sX hK
    (isLocallyBoundedFiniteLocallyFree_of_boundedFiniteLocallyFreeComplex hE) e.symm p).trans
    (powerSumKHom_eulerCharComplex C sX hE _ p).symm

end PowerSum

/-! ### The map `α ↦ ch(α) ∩ [X]` -/

section Composite

open Stacks.Perfect.BoundedLocallyFreeComplexes

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

local notation "CHQ" => DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j

/-- **`ch(α) ∩ -` does not raise degrees beyond `j`** as soon as no `P_p(α) ∩ -` reaches a degree
above `j`: if `P_p(α) ∩ β = 0` for all `β ∈ CH_k(X)` with `k - p > j`, then `ch(α) ∩ v` has no
component in degree `j' > j`, for every `v ∈ CH_*(X) ⊗ 𝐐`. -/
theorem chernCharacterCap_apply_eq_zero (a : VectorBundleKZero X) (j : ℤ)
    (h : ∀ (p : ℕ) (k : ℤ) (α : chowGroup C sX k), j < k - p →
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p (powerSumKHom C sX p a p) k α = 0)
    (v : CHQ) {j' : ℤ} (hj : j < j') : chernCharacterCap C sX a v j' = 0 := by
  induction v using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply]
  | add v w hv hw => rw [map_add, DirectSum.add_apply, hv, hw, add_zero]
  | of k t =>
    rw [← DirectSum.lof_eq_of ℚ, chernCharacterCap_lof, DFinsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [rationalChowCap_lof, DirectSum.lof_eq_of]
    by_cases hk : k - p = j'
    · have hzero : rationalChowCapComponent C (gysinSystemOfInvertible C) sX p k
          (chernCharacterVectorBundle C sX a p) t = 0 := by
        induction t using TensorProduct.induction_on with
        | zero => rw [map_zero]
        | add t t' ht ht' => rw [map_add, ht, ht', add_zero]
        | tmul q α =>
          show rationalChowCapComponent C (gysinSystemOfInvertible C) sX p k
            (((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] powerSumKHom C sX p a p) (q ⊗ₜ[ℤ] α) = 0
          rw [rationalChowCapComponent_tmul_tmul, h p k α (by omega), TensorProduct.tmul_zero]
      rw [hzero, map_zero, DirectSum.zero_apply]
    · exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk)

variable [IsNoetherian X]

/-- **The map `α ↦ ch(α) ∩ [X]` of Stacks 0FEY**, `K_0(Vect(X)) ⟶ CH_*(X) ⊗ 𝐐`, for a Noetherian
`X`: the Chern character of Remark 0FEM followed by capping the fundamental class. -/
def chernCharacterCapFundamentalClass : VectorBundleKZero X →+ CHQ where
  toFun a := chernCharacterCap C sX a (rationalFundamentalClass C sX)
  map_zero' := by
    rw [← chernCharacterCapHom_apply, map_zero, LinearMap.zero_apply]
  map_add' a b := by
    simp only [← chernCharacterCapHom_apply, map_add, LinearMap.add_apply]

/-- The map `α ↦ ch(α) ∩ [X]` evaluates to `ch(α) ∩ [X]`. -/
theorem chernCharacterCapFundamentalClass_apply (a : VectorBundleKZero X) :
    chernCharacterCapFundamentalClass C sX a =
      chernCharacterCap C sX a (rationalFundamentalClass C sX) :=
  rfl

/-- **The value on the class of a finite locally free module**: `[ℰ] ↦ ch(ℰ) ∩ [X]`, the total cap
product of `ch(ℰ) = (ch_0(ℰ), ch_1(ℰ), …)`. -/
theorem chernCharacterCapFundamentalClass_classOf (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    chernCharacterCapFundamentalClass C sX (VectorBundleKZero.classOf X E) =
      totalRationalChowCap C (gysinSystemOfInvertible C) sX
        (fun p => chernCharacterOfFiniteLocallyFree C sX E p) (rationalFundamentalClass C sX) := by
  rw [chernCharacterCapFundamentalClass_apply, chernCharacterCap]
  congr 2
  exact funext (chernCharacterVectorBundle_classOf C sX E)

/-- **`ch(α) ∩ [X] = ∑_p ch_p(α) ∩ [X]`** for `δ_{X/S}` bounded, between `lo` and `lo + N`: each
summand is the map `c ↦ c ∩ [X]` of Stacks 0FEW (`Stacks.Chow.rationalCapFundamentalClass`). -/
theorem chernCharacterCapFundamentalClass_eq_sum (lo : ℤ)
    (hlo : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x) (N : ℕ)
    (hN : ∀ x : X, relativeDimension C.dimensionFunction sX x - lo ≤ N)
    (a : VectorBundleKZero X) :
    chernCharacterCapFundamentalClass C sX a =
      ∑ p ∈ Finset.range (N + 1), rationalCapFundamentalClass C (gysinSystemOfInvertible C) sX
        sX (𝟙 X) (Category.id_comp sX) p (chernCharacterVectorBundle C sX a p) := by
  simp only [← rationalChowCap_rationalFundamentalClass, chernCharacterCapFundamentalClass_apply,
    rationalFundamentalClass_eq, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : ∃ x : X, relativeDimension C.dimensionFunction sX x = n
  · obtain ⟨x, hx⟩ := hn
    rw [← DirectSum.lof_eq_of ℚ, chernCharacterCap_lof_eq_sum C sX lo hlo a n _ _ fun p hp => ?_]
    rw [Finset.mem_range]
    have := hN x
    omega
  · have h0 : fundamentalChowClass C sX n = 0 :=
      chowGroup_eq_zero C sX (fun x hx => hn ⟨x, hx⟩) _
    simp only [h0, TensorProduct.tmul_zero, map_zero, Finset.sum_const_zero]

/-- **The map of Stacks 0FEY**, `K_0(Vect(X)) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`, `α ↦ ch(α) ∩ [X]`: the
`𝐐`-linear extension of `Stacks.Chow.chernCharacterCapFundamentalClass`. -/
def rationalChernCharacterCapFundamentalClass : ℚ ⊗[ℤ] VectorBundleKZero X →ₗ[ℚ] CHQ :=
  (chernCharacterCapFundamentalClass C sX).toIntLinearMap.liftBaseChange ℚ

/-- `r ⊗ α ↦ r (ch(α) ∩ [X])`. -/
theorem rationalChernCharacterCapFundamentalClass_tmul (r : ℚ) (a : VectorBundleKZero X) :
    rationalChernCharacterCapFundamentalClass C sX (r ⊗ₜ[ℤ] a) =
      r • chernCharacterCapFundamentalClass C sX a :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The map of Stacks 0FEY is `α ↦ ch(α) ∩ [X]` with `ch(α) ∩ -` the operator
`Stacks.Chow.rationalChernCharacterCap` of `α ∈ K_0(Vect(X)) ⊗ 𝐐`. -/
theorem rationalChernCharacterCapFundamentalClass_apply (x : ℚ ⊗[ℤ] VectorBundleKZero X) :
    rationalChernCharacterCapFundamentalClass C sX x =
      rationalChernCharacterCap C sX x (rationalFundamentalClass C sX) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, LinearMap.zero_apply]
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy]
  | tmul r a =>
    rw [rationalChernCharacterCapFundamentalClass_tmul, rationalChernCharacterCap_tmul,
      LinearMap.smul_apply, chernCharacterCapFundamentalClass_apply]

variable [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)

/-- **The map `α ↦ ch(α) ∩ [X]` on `K'_0(X)`**, for `X` regular Noetherian with affine diagonal:
`Stacks.Chow.chernCharacterCapFundamentalClass` read through the identification
`K'_0(X) = K_0(Vect(X))` of `AlgebraicGeometry.regularVectorBundleKZeroAddEquiv`. -/
def coherentChernCharacterCapFundamentalClass : CoherentKZero X →+ CHQ :=
  (chernCharacterCapFundamentalClass C sX).comp
    (regularVectorBundleKZeroAddEquiv X hX).symm.toAddMonoidHom

/-- On the class of a finite locally free module the map on `K'_0(X)` is `[ℰ] ↦ ch(ℰ) ∩ [X]`. -/
theorem coherentChernCharacterCapFundamentalClass_classOf (E : X.Modules)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    coherentChernCharacterCapFundamentalClass C sX hX
        (@KZero.mk _ _ (coherentModulesAbelian X)
          ⟨E, @isCoherent_of_isFiniteLocallyFree_of_isLocallyNoetherian X
            (isLocallyNoetherian_of_isRegular hX) E hE⟩) =
      chernCharacterCapFundamentalClass C sX (VectorBundleKZero.classOf X E) := by
  show chernCharacterCapFundamentalClass C sX ((regularVectorBundleKZeroAddEquiv X hX).symm _) = _
  rw [← regularVectorBundleKZeroAddEquiv_classOf' X hX E hE, AddEquiv.symm_apply_apply]

/-- **Bijectivity on `K'_0(X) ⊗ 𝐐` is bijectivity on `K_0(Vect(X)) ⊗ 𝐐`**: the `𝐐`-linear
extension of the map on `K'_0(X)` is that of `α ↦ ch(α) ∩ [X]` precomposed with the base change of
the isomorphism `K'_0(X) ≅ K_0(Vect(X))`. So Stacks 0FEY may be stated in the source's form, on
`K_0(Vect(X)) ⊗ 𝐐`. -/
theorem bijective_liftBaseChange_coherentChernCharacterCapFundamentalClass_iff :
    Function.Bijective
        ((coherentChernCharacterCapFundamentalClass C sX hX).toIntLinearMap.liftBaseChange ℚ) ↔
      Function.Bijective (rationalChernCharacterCapFundamentalClass C sX) := by
  let e := ((regularVectorBundleKZeroAddEquiv X hX).symm.toIntLinearEquiv).baseChange ℤ ℚ
    (CoherentKZero X) (VectorBundleKZero X)
  have h : (coherentChernCharacterCapFundamentalClass C sX hX).toIntLinearMap.liftBaseChange ℚ =
      rationalChernCharacterCapFundamentalClass C sX ∘ₗ e.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul r a =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.baseChange_tmul, rationalChernCharacterCapFundamentalClass_tmul]
      rfl
  rw [h, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact Function.Bijective.of_comp_iff _ e.bijective

/-- **Condition (1) of the proof of Stacks 0FEW for `α ↦ ch(α) ∩ [X]`.** Let `X` be a regular
Noetherian scheme locally of finite type over the base, with affine diagonal. If the support of a
coherent `𝒪_X`-module `ℱ` has delta-dimension at most `j`, then `ch([ℱ]) ∩ [X]` lies in
`⨁_{j' ≤ j} CH_{j'}(X) ⊗ 𝐐`.

The class of `ℱ` in `K_0(Vect(X))` is `∑_n (-1)^n [ℰ^n]` for a bounded complex `ℰ^•` of finite
locally free modules representing `ℱ[0]`, so `P_p` of it is `P_p(ℱ[0])` (Remark 0FEU), which is
`i_* ∘ P_p(Z ⟶ X, ℱ[0])` for the reduced closed subscheme `i : Z ⟶ X` on the support (Stacks 0FB2),
`ℱ[0]` vanishing off `Z`. Capping with it therefore factors through `CH_*(Z)`, which vanishes in
degrees above `j`. -/
theorem isDimensionTriangular_coherentChernCharacterCapFundamentalClass :
    IsDimensionTriangular C sX (coherentChernCharacterCapFundamentalClass C sX hX) := by
  intro j j' F hjj'
  obtain ⟨K, E, ⟨eK⟩, hE, ⟨eE⟩, heq⟩ := exists_regularVectorBundleKZeroAddEquiv_symm_mk X hX F.obj
  have heq' : (regularVectorBundleKZeroAddEquiv X hX).symm (KZero.mk _ F.obj) =
      eulerCharComplex X E := heq
  show chernCharacterCap C sX ((regularVectorBundleKZeroAddEquiv X hX).symm
    (KZero.mk _ F.obj)) (rationalFundamentalClass C sX) j' = 0
  rw [heq']
  refine chernCharacterCap_apply_eq_zero C sX _ j (fun p k α hk => ?_) _ hjj'
  have : _root_.SheafOfModules.IsCoherent F.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent F.obj.property
  set I := reducedSupport F.obj.obj
  have hrange : Set.range I.subschemeι.base = SheafOfModules.supp F.obj.obj := by
    rw [← coe_support_reducedSupport F.obj.obj]
    exact I.range_subschemeι
  have hzero := isZero_derivedPullback_ofRestrict_compl F.obj.obj _
    I.subschemeι.isClosedEmbedding.isClosed_range hrange.symm.subset K.obj eK
  let S : LocalizedSituation.{u} :=
    { base := C
      X := X
      a := sX
      Z := I.subscheme
      i := I.subschemeι
      E := K.obj
      p := 0
      perfect := K.property
      restriction := Or.inl hzero
      finiteness := Or.inl inferInstance }
  have hS : S.IsZeroOnComplement := hzero
  have h1 : powerSumKHom C sX p (eulerCharComplex X E) p =
      properPushforwardChowCohomology C sX (I.subschemeι ≫ sX) I.subschemeι rfl
        (S.localizedPowerSum hS p) := by
    rw [← perfectPowerSum_eq_powerSumKHom_eulerCharComplex C sX S.hasDefinedChernClasses_E hE eE]
    exact (S.properPushforwardChowCohomology_localizedPowerSum hS p).symm
  rw [h1]
  refine chowCohomologyCap_properPushforwardChowCohomology_eq_zero C sX _ _ rfl _ k
    (fun z => ?_) α
  rw [relativeDimension_comp_closedImmersion]
  have hz : I.subschemeι z ∈ SheafOfModules.supp F.obj.obj := hrange ▸ ⟨z, rfl⟩
  have := relativeDimension_le_of_mem_supp_dimLE C sX j F _ hz
  omega

end Composite

end Stacks.Chow

end
