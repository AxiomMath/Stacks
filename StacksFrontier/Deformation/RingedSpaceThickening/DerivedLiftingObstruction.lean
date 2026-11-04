module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification
public import StacksFrontier.Deformation.RingedSpaceThickening.MapLift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import all StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The derived obstruction to lifting a map of modules across a first-order thickening (Stacks 08LK)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces with ideal
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules, put `ℱ = i^* ℱ'` and
`𝒢 = i^* 𝒢'`, and let `φ : ℱ ⟶ 𝒢` be `𝒪_X`-linear. There is a class

    o(φ) ∈ Ext¹_{𝒪_X}(Li^* ℱ', ℐ𝒢')

whose vanishing is necessary and sufficient for `φ` to lift to an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.derivedPushforwardIsoMapDerivedCategory`: for a
  morphism along which direct image is exact, the derived pushforward `Ri_*` is the degreewise
  pushforward read on derived categories.
* `AlgebraicGeometry.RingedSpaceThickening.ambientMapLiftObstruction`: the class
  `o(φ) ∈ Ext¹_{𝒪_{X'}}(ℱ', ℐ𝒢')` of the source's proof, before it is transported to `X`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.ambientMapLiftObstruction_eq_zero_iff`: the ambient
  class vanishes exactly when `φ` lifts.
* `AlgebraicGeometry.RingedSpaceThickening.exists_derivedMapLiftingObstruction`: **Stacks 08LK**,
  the existence of a class in `Ext¹_{𝒪_X}(Li^* ℱ', ℐ𝒢')` whose vanishing is equivalent to the
  existence of a lift.

## Implementation notes

The construction is the source's. A lift of `φ` is the same thing as a lift of its transpose
`ψ : ℱ' ⟶ i_* 𝒢'` along the surjection `𝒢' ⟶ i_* i^* 𝒢'`, whose kernel is `ℐ𝒢'`; by exactness
of the covariant `Ext` sequence of

    0 ⟶ ℐ𝒢' ⟶ 𝒢' ⟶ i_* i^* 𝒢' ⟶ 0

such a lift exists exactly when `ψ^* [𝒢'] ∈ Ext¹_{𝒪_{X'}}(ℱ', ℐ𝒢')` vanishes. That the
displayed sequence is short exact is surjectivity of the unit of `i^* ⊣ i_*` at `𝒢'`, which for
a thickening holds at every module (`epi_unit_app_of_isThickening`).

Transporting the class to `X` is the adjunction `Li^* ⊣ Ri_*` of **Stacks 079W**. Direct image
along a thickening is exact, so `Ri_*` is the degreewise pushforward on derived categories, and
the shift of the degree-zero complex on `ℐ𝒢'` is carried to the shift of the degree-zero
complex on `i^* ℐ𝒢'` — the unit at `ℐ𝒢'` being invertible, as `ℐ(ℐ𝒢') = 0`. Transposing
across the adjunction is injective, so vanishing is preserved in both directions, and the
resulting class lies in `Ext¹_{𝒪_X}(Li^* ℱ', ℐ𝒢')`.

The source asserts existence of the class, not uniqueness, and that is what is stated: the
conclusion is an `∃` over the `Ext` group, with the biconditional as the property.

The model of the derived category and of the `Ext` groups is the standard one,
`HasDerivedCategory.standard` and `HasExt.standard`, taken as local instances as in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional`.

## References

* [Stacks Project, Tag 08LK](https://stacks.math.columbia.edu/tag/08LK)
* [Stacks Project, Tag 08LH](https://stacks.math.columbia.edu/tag/08LH)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard HasExt.standard

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- For a morphism of ringed spaces along which direct image is exact, the derived pushforward
`Ri_*` is canonically the degreewise pushforward read on derived categories: an exact functor
inverts quasi-isomorphisms, so the induced functor is already a right derived functor of it. -/
noncomputable def derivedPushforwardIsoMapDerivedCategory
    [PreservesFiniteLimits (modulePushforward i)]
    [PreservesFiniteColimits (modulePushforward i)] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i ≅
      (modulePushforward i).mapDerivedCategory.{u + 1, u + 1} := by
  let F := modulePushforward i
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)
  let e := F.mapDerivedCategoryFactorsh.{u + 1, u + 1}
  let α := e.inv
  letI : F.mapDerivedCategory.{u + 1, u + 1}.IsRightDerivedFunctor α W :=
    Functor.isRightDerivedFunctor_of_inverts W F.mapDerivedCategory.{u + 1, u + 1} e
  exact Functor.rightDerivedUnique
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory.{u, u + 1}
        i).totalRightDerived DerivedCategory.Qh W)
    (F.mapDerivedCategory.{u + 1, u + 1})
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory.{u, u + 1}
        i).totalRightDerivedUnit DerivedCategory.Qh W)
    α W

/-- The class `o(φ) ∈ Ext¹_{𝒪_{X'}}(ℱ', ℐ𝒢')` obstructing a lift of `φ : i^* ℱ' ⟶ i^* 𝒢'`,
read on the thickening `X'`: the restriction along the transpose `ℱ' ⟶ i_* i^* 𝒢'` of `φ` of
the class of the short exact sequence `0 ⟶ ℐ𝒢' ⟶ 𝒢' ⟶ i_* i^* 𝒢' ⟶ 0`. -/
noncomputable def ambientMapLiftObstruction (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G') :
    Abelian.Ext.{u + 1} F' (infinitesimalPart i G') 1 :=
  letI S := ShortComplex.kernelSequence
    ((modulePullbackPushforwardAdjunction i).unit.app G')
  haveI : Epi S.g := epi_unit_app_of_isThickening i hi.1 G'
  (Abelian.Ext.mk₀ ((modulePullbackPushforwardAdjunction i).homEquiv F'
      ((modulePullback i).obj G') φ)).comp
    (⟨ShortComplex.kernelSequence_exact _⟩ : S.ShortExact).extClass (zero_add 1)

/-- The ambient obstruction class vanishes exactly when `φ : i^* ℱ' ⟶ i^* 𝒢'` lifts to an
`𝒪_{X'}`-linear map `ℱ' ⟶ 𝒢'`: lifts of `φ` are lifts of its transpose along
`𝒢' ⟶ i_* i^* 𝒢'`, and the covariant `Ext` sequence detects those. -/
theorem ambientMapLiftObstruction_eq_zero_iff (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G') :
    ambientMapLiftObstruction i hi F' G' φ = 0 ↔ Nonempty (MapLift i F' G' φ) := by
  let η := (modulePullbackPushforwardAdjunction i).unit
  let S := ShortComplex.kernelSequence (η.app G')
  have : Epi S.g := epi_unit_app_of_isThickening i hi.1 G'
  have hS : S.ShortExact := ⟨ShortComplex.kernelSequence_exact _⟩
  let adjE := (modulePullbackPushforwardAdjunction i).homEquiv F' ((modulePullback i).obj G')
  let ψ := adjE φ
  change (Abelian.Ext.mk₀ ψ).comp hS.extClass (zero_add 1) = 0 ↔ _
  refine (hS.mk₀_comp_extClass_eq_zero_iff ψ).trans ?_
  change (∃ t : F' ⟶ G', t ≫ η.app G' = ψ) ↔ _
  have htranspose (t : F' ⟶ G') : adjE ((modulePullback i).map t) = t ≫ η.app G' := by
    rw [Adjunction.homEquiv_unit]
    exact (η.naturality t).symm
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨⟨t, adjE.injective ((htranspose t).trans ht)⟩⟩,
    fun ⟨⟨t, ht⟩⟩ ↦ ⟨t, (htranspose t).symm.trans (congrArg adjE ht)⟩⟩

/-- **Stacks Project, Tag 08LK.** Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening
of ringed spaces with ideal `ℐ`, let `ℱ'` and `𝒢'` be `𝒪_{X'}`-modules and let
`φ : i^* ℱ' ⟶ i^* 𝒢'` be `𝒪_X`-linear. There is a class `o(φ) ∈ Ext¹_{𝒪_X}(Li^* ℱ', ℐ𝒢')`
whose vanishing is necessary and sufficient for `φ` to lift to an `𝒪_{X'}`-linear map
`ℱ' ⟶ 𝒢'`. -/
@[stacks 08LK]
theorem exists_derivedMapLiftingObstruction (hi : IsFirstOrderThickening i)
    (F' G' : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback i).obj F' ⟶ (modulePullback i).obj G') :
    ∃ o : DerivedCategory.Ext
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i).obj
          ((DerivedCategory.singleFunctor _ 0).obj F'))
        ((DerivedCategory.singleFunctor _ 0).obj (infinitesimalPartOnSource i G')) 1,
      (o = 0 ↔ Nonempty (MapLift i F' G' φ)) := by
  have : PreservesFiniteLimits (modulePushforward i) :=
    preservesFiniteLimits_modulePushforward i
  have : PreservesFiniteColimits (modulePushforward i) :=
    preservesFiniteColimits_modulePushforward i hi.1
  let I := infinitesimalPart i G'
  let J := infinitesimalPartOnSource i G'
  have := infinitesimalPart_unit_isIso i hi G'
  let F := (modulePushforward i).mapDerivedCategory
  let adj :=
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction i).ofNatIsoRight
      (derivedPushforwardIsoMapDerivedCategory i)
  let e₀ : F.obj ((DerivedCategory.singleFunctor _ 0).obj J) ≅
      (DerivedCategory.singleFunctor _ 0).obj I :=
    (Functor.mapDerivedCategorySingleFunctor (modulePushforward i) 0).app J ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (asIso ((modulePullbackPushforwardAdjunction i).unit.app I)).symm
  let e₁ : F.obj (((DerivedCategory.singleFunctor _ 0).obj J)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj I)⟦(1 : ℤ)⟧ :=
    (F.commShiftIso (1 : ℤ)).app _ ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso e₀
  let c := ambientMapLiftObstruction i hi F' G' φ
  have : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i).Additive :=
    adj.left_adjoint_additive
  refine ⟨(adj.homEquiv _ _).symm (c.hom ≫ e₁.inv), ?_⟩
  rw [← adj.homAddEquiv_symm_zero, (adj.homEquiv _ _).symm.injective.eq_iff]
  change c.hom ≫ e₁.inv = 0 ↔ _
  rw [Preadditive.IsIso.comp_right_eq_zero, ← Abelian.Ext.zero_hom F' I 1,
    Abelian.Ext.homEquiv.injective.eq_iff]
  exact ambientMapLiftObstruction_eq_zero_iff i hi F' G' φ

end AlgebraicGeometry.RingedSpaceThickening

end
