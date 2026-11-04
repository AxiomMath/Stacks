module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedHomogeneousComposite
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.BaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat

/-!
# The rational Chow ring of a projective bundle presented as a base change

Let `k` be a field, let `ℰ` be a finite locally free module of rank `n + 1` on a scheme `X₀`, and
let `q : Q ⟶ U` be a morphism of smooth projective schemes over `k` which is the base change of
the projective bundle `π : 𝐏(ℰ) ⟶ X₀` along some `g : U ⟶ X₀`, with second projection
`h : Q ⟶ 𝐏(ℰ)`, and let `ℒ ≅ h^*𝒪(1)`. This file reads the projective bundle formula on the
rational Chow rings `CH^*(-) ⊗ 𝐐` of Section 0FEX: writing `c₁(ℒ)` for the class
`ch_1(ℒ) ∩ [Q]`,

* every class of `CH^*(Q) ⊗ 𝐐` is `∑_{i ≤ n} c₁(ℒ)^i · q^!y_i` (Stacks 02TX);
* `q_*(c₁(ℒ)^i)` is `0` for `i < n` and `1` for `i = n` (Stacks 02TW);

and records the projection formula `f_*(x · f^!y) = f_*x · y` (Stacks 0FFA) for a morphism of
smooth projective schemes.

The integral statements are `Stacks.Chow.bijective_bundleMap_of_isPullback` and
`Stacks.Chow.bundleProjection_of_isPullback`. Three bridges carry them to the rational Chow
rings. First, the Gysin map of the flat morphism `q`, of relative dimension `n`, is flat
pullback (Stacks 0FF4): its homogeneous part in degree `-n` is the class of Stacks 0B78, and the
others vanish. Second, in rank one `ch_1(ℒ) = c_1(ℒ)`, whose cap operation is the first Chern
class operation `c₁(ℒ) ∩ -` of Stacks 02SO. Third, the product with `ch_p(α') ∩ [Q]` is the
operator `ch_p(α') ∩ -`, which commutes with every `ch(β') ∩ -`. Hence `c₁(ℒ)^i · q^!(r ⊗ α)` is
`r ⊗ (c₁(ℒ)^i ∩ q^*α)`, the summand of the map of Stacks 02TX, and its pushforward is
`r ⊗ q_*(c₁(ℒ)^i ∩ q^*α)`, the operation of Stacks 02TW; the unit is `q^!1`.

## Main definitions

* `Stacks.WeilCohomology.rationalFirstChernClass` — `c₁(ℒ) = ch_1(ℒ) ∩ [Y]` in `CH^*(Y) ⊗ 𝐐`.
* `Stacks.WeilCohomology.rationalPush` — proper pushforward `f_*` on the rational Chow rings.

## Main results

* `Stacks.WeilCohomology.rationalPush_mul_smoothGysinRingHom` — the projection formula
  (Stacks 0FFA).
* `Stacks.WeilCohomology.exists_eq_sum_rationalFirstChernClass_pow_mul` — Stacks 02TX on the
  rational Chow ring.
* `Stacks.WeilCohomology.rationalPush_rationalFirstChernClass_pow` — Stacks 02TW on the rational
  Chow ring.
* `Stacks.Chow.lciGysinRational_of_tmul_of_flat` — Stacks 0FF4 on `CH_*(-) ⊗ 𝐐`, for a flat
  morphism of constant relative dimension.
* `Stacks.Chow.rationalChernCharacterComponentCap_one_of_tmul` — `ch_1(ℒ) ∩ - = c₁(ℒ) ∩ -` for an
  invertible module.
* `Stacks.Chow.rationalIntersectionProduct_rationalChernCharacterComponentCap` —
  `(ch_p(α') ∩ [X]) · β = ch_p(α') ∩ β`.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 0FFA](https://stacks.math.columbia.edu/tag/0FFA)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u

namespace Stacks.Chow

section FlatGysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)
  (m : ℕ) (hm : AlgebraicGeometry.RelativeDimension f m)

/-- **The homogeneous parts of the Gysin map of a flat morphism** (Stacks 0FF4): for `f` flat of
constant relative dimension `m`, the part of `f^!` in degree `q` is the flat pullback class
`f^* ∈ A^{-m}(X ⟶ Y)` of Stacks 0B78 if `q = -m`, and zero otherwise. -/
theorem lciGysinBivariantClass_eq_single_flatPullback (q : ℤ) :
    lciGysinMapComponent C sX sY hf hlci h q =
      Pi.single (M := fun q : ℤ => BivariantClass C (gysinSystemOfInvertible C) sX sY f hf q)
        (-(m : ℤ)) (flatPullbackBivariantClassOfInvertible C sX sY f hf m hm) q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  rw [lciGysinMapComponent, lciGysinMap_eq_completedFlatPullbackOfFlatLCI,
    completedFlatPullbackOfFlatLCI, completedFlatPullback_eq_toCompleted C sX sY f hf m hm,
    completedBivariantSequenceOfInvertible_toCompleted]

/-- **Stacks 0FF4 on `CH_*(-) ⊗ 𝐐`**: for `f` flat of constant relative dimension `m`, the Gysin
map sends `r ⊗ β`, `β ∈ CH_k(Y)`, to `r ⊗ f^*β` in degree `k + m`. -/
theorem lciGysinRational_of_tmul_of_flat (k : ℤ) (r : ℚ) (β : chowGroup C sY k) :
    lciGysinRational C sX sY hf hlci h
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) k (r ⊗ₜ β)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (k + m)
        (r ⊗ₜ flatPullbackChow C sX sY f hf m hm k
          (flatPullbackFactorsThroughRationalEquivalence_general C sX sY f hf m hm k) β) := by
  classical
  have hsupp : lciGysinSupport C sX sY hf hlci h ⊆ (({-(m : ℤ)} : Finset ℤ) : Set ℤ) := by
    intro q hq
    by_contra hne
    refine hq ?_
    rw [lciGysinBivariantClass_eq_single_flatPullback C sX sY hf hlci h m hm,
      Pi.single_eq_of_ne (by simpa using hne)]
  rw [lciGysinRational_eq_sum C sX sY hf hlci h _ hsupp, Finset.sum_singleton,
    lciGysinRationalComponent, rationalChowMap_of_tmul]
  refine of_tmul_eq_of_tmul_of_heq C sX (by ring) r ?_
  rw [lciGysinChow, BivariantClass.capTargetHom_apply,
    lciGysinBivariantClass_eq_single_flatPullback C sX sY hf hlci h m hm, Pi.single_eq_same]
  exact flatPullbackBivariantClass_capTarget_heq C _ sX sY f hf m hm (flatPullbackDescends C) _
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX sY f hf m hm) k β

end FlatGysin

section FirstChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **`ch_1(ℒ) = c_1(ℒ)` for an invertible module `ℒ`**: in rank one the first power sum is the
first Chern class. -/
theorem chernCharacterVectorBundle_classOf_one_of_isInvertible :
    letI := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
    chernCharacterVectorBundle C sX (VectorBundleKZero.classOf X L) 1 =
      (1 : ℚ) ⊗ₜ[ℤ] totalChern C sX L 1 1 := by
  let := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  rw [chernCharacterVectorBundle_apply, powerSumKHom_classOf,
    powerSumOfFiniteLocallyFree_eq_powerSumTotal _ _ _ 1, powerSumTotal_of_rank_one, pow_one,
    TotalChowClass.homComponent_apply, if_pos rfl,
    show ((Nat.factorial 1 : ℕ) : ℚ)⁻¹ = 1 by norm_num]

/-- **Capping with `c_1(ℒ) ∈ A^1(X)` is the first Chern class operation `c₁(ℒ) ∩ -`** of
Stacks 02SO, for an invertible module `ℒ`. -/
theorem chowCohomologyCap_totalChern_one_heq (k : ℤ) (x : chowGroup C sX k) :
    letI := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
    chowCohomologyCap C (gysinSystemOfInvertible C) sX ((1 : ℕ) : ℤ) (totalChern C sX L 1 1) k x ≍
      (invCap C sX L).capOnChow C sX (k - 1) (chowGroupCast C sX (by omega) x) := by
  let := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank L 1 (𝟙 X)
  have := GenuineChern.isInvertible_pullback (𝟙 X) L
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sX _ _ k x).trans ?_
  have h1 := GenuineChern.idRule_chernClass C sX L 1 1 (𝟙 X) k
    (chowGroupCongr C (Category.id_comp sX).symm k x)
  have h2 := GenuineChern.chernCap_one_eq_invCap C (𝟙 X ≫ sX)
    ((Scheme.Modules.pullback (𝟙 X)).obj L) k (chowGroupCongr C (Category.id_comp sX).symm k x)
  have h3 := invCap_capOnChow_congr C (𝟙 X ≫ sX) ((Scheme.Modules.pullback (𝟙 X)).obj L) L
    ((Scheme.Modules.pullbackId X).app L) (k - 1)
    (chowGroupCast C (𝟙 X ≫ sX) (by omega) (chowGroupCongr C (Category.id_comp sX).symm k x))
  have h4 := chowGroupCongr_invCap_capOnChow C L (Category.id_comp sX) (k - 1)
    (chowGroupCast C (𝟙 X ≫ sX) (by omega) (chowGroupCongr C (Category.id_comp sX).symm k x))
  refine (heq_of_eq (h1.trans (h2.trans h3))).trans ?_
  refine (chowGroupCongr_heq C _ _ _).symm.trans ((heq_of_eq h4).trans (heq_of_eq (congrArg _ ?_)))
  exact eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ((chowGroupCast_heq C _ _ _).trans
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCast_heq C _ _ _).symm)))

/-- **`ch_1(ℒ) ∩ -` on `CH_*(X) ⊗ 𝐐` is `c₁(ℒ) ∩ -`** for an invertible module `ℒ`:
`ch_1(ℒ) ∩ (r ⊗ z) = r ⊗ (c₁(ℒ) ∩ z)`, `z ∈ CH_m(X)`, in degree `m - 1`. -/
theorem rationalChernCharacterComponentCap_one_of_tmul (m : ℤ) (r : ℚ) (z : chowGroup C sX m) :
    letI := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
    rationalChernCharacterComponentCap C sX 1 (1 ⊗ₜ VectorBundleKZero.classOf X L)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) m (r ⊗ₜ z)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (m - 1)
        (r ⊗ₜ (invCap C sX L).capOnChow C sX (m - 1) (chowGroupCast C sX (by omega) z)) := by
  let := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L inferInstance
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  rw [rationalChernCharacterComponentCap_tmul, one_smul,
    chernCharacterVectorBundle_classOf_one_of_isInvertible,
    rationalChowCap_of_tmul, one_mul]
  exact of_tmul_eq_of_tmul_of_heq C sX (by simp) r (chowCohomologyCap_totalChern_one_heq C sX L m z)

end FirstChern

section Product

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X)
  (hb : ∃ lo hi : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x ∧
    relativeDimension C.dimensionFunction sX x ≤ hi)

/-- **The product with `ch_p(α') ∩ [X]` is `ch_p(α') ∩ -`**: for the product of Section 0FEX,
`(ch_p(α') ∩ [X]) · β = ch_p(α') ∩ β`, the operator `ch_p(α') ∩ -` commuting with every
`ch(β') ∩ -`. -/
theorem rationalIntersectionProduct_rationalChernCharacterComponentCap (p : ℕ)
    (a : ℚ ⊗[ℤ] VectorBundleKZero X)
    (β : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) :
    rationalIntersectionProduct hX hb
        (rationalChernCharacterComponentCap C sX p a (rationalFundamentalClass C sX)) β =
      rationalChernCharacterComponentCap C sX p a β := by
  obtain ⟨b, rfl⟩ := (bijective_flip_rationalChernCharacterCap hX hb).2 β
  rw [LinearMap.flip_apply, rationalIntersectionProduct_comm hX hb,
    rationalIntersectionProduct_rationalChernCharacterCap]
  obtain ⟨lo, hi, hb'⟩ := hb
  have hc : Commute (rationalChernCharacterComponentCap C sX p a)
      (rationalChernCharacterCap C sX b) := by
    rw [rationalChernCharacterCap_eq_sum C sX hb' (N := (hi - lo).toNat) (by omega),
      LinearMap.sum_apply]
    exact Commute.sum_right _ _ _ fun q _ => commute_rationalChernCharacterComponentCap C sX p q a b
  exact (LinearMap.congr_fun hc.eq (rationalFundamentalClass C sX)).symm

end Product

end Stacks.Chow

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The class `c₁(ℒ) ∩ [Y] = ch₁(ℒ) ∩ [Y]` of an invertible module in the rational Chow ring
`CH^*(Y) ⊗ 𝐐`. -/
def rationalFirstChernClass (Y : (SmoothProjectiveScheme k).FullSubcategory)
    (L : Y.obj.left.Modules) :
    smoothRationalChowRing (k := k) Y.obj.hom :=
  smoothChowEquiv Y.obj.hom (rationalChernCharacterComponentCap (fieldChowSituation k) Y.obj.hom 1
    (1 ⊗ₜ VectorBundleKZero.classOf _ L)
    (rationalFundamentalClass (fieldChowSituation k) Y.obj.hom))

/-- Proper pushforward `f_* : CH^*(X) ⊗ 𝐐 ⟶ CH^*(Y) ⊗ 𝐐` along a morphism of smooth projective
schemes, read on the rational Chow rings. -/
def rationalPush {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    smoothRationalChowRing (k := k) X.obj.hom →ₗ[ℚ] smoothRationalChowRing (k := k) Y.obj.hom :=
  haveI : IsProper f.hom.left := by
    have : IsProper (f.hom.left ≫ Y.obj.hom) := by rw [Over.w f.hom]; infer_instance
    exact IsProper.of_comp f.hom.left Y.obj.hom
  (smoothChowEquiv Y.obj.hom).toLinearMap ∘ₗ
    rationalProperChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom (Over.w f.hom) ∘ₗ
    (smoothChowEquiv X.obj.hom).symm.toLinearMap

/-- A morphism of smooth projective schemes over `k` is proper. -/
private theorem isProper_hom_left {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    IsProper f.hom.left := by
  have : IsProper (f.hom.left ≫ Y.obj.hom) := by rw [Over.w f.hom]; infer_instance
  exact IsProper.of_comp f.hom.left Y.obj.hom

/-- **The projection formula** `f_*(x · f^!y) = f_*x · y` on the rational Chow rings
(Stacks 0FFA). -/
theorem rationalPush_mul_smoothGysinRingHom {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y)
    (x : smoothRationalChowRing (k := k) X.obj.hom)
    (y : smoothRationalChowRing (k := k) Y.obj.hom) :
    rationalPush f (x * smoothGysinRingHom X.obj.hom Y.obj.hom (Over.w f.hom) y) =
      rationalPush f x * y := by
  have := isProper_hom_left f
  obtain ⟨α, rfl⟩ := (smoothChowEquiv X.obj.hom).surjective x
  obtain ⟨β, rfl⟩ := (smoothChowEquiv Y.obj.hom).surjective y
  rw [smoothGysinRingHom_equiv, RationalIntersectionRing.equiv_mul_equiv]
  have := rationalProperChowPushforward_rationalIntersectionProduct_lciGysinRational
    (C := fieldChowSituation k) (Over.w f.hom) (isRegular_of_smooth_over_field X.obj.hom)
    (isRegular_of_smooth_over_field Y.obj.hom)
    (topologicalKrullDim_ne_top_of_isProper k X.obj.hom)
    (topologicalKrullDim_ne_top_of_isProper k Y.obj.hom)
    (GysinMapExists.of_smooth_source f.hom.left Y.obj.hom X.obj.hom (Over.w f.hom)) α β
  exact congrArg (smoothChowEquiv Y.obj.hom) this

section Classes

local notation "CHQ(" s ")" =>
  DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) s j

/-- **The product with `c₁(ℒ) ∩ [Y]` is the first Chern class operation**: in `CH^*(Y) ⊗ 𝐐`,
`(c₁(ℒ) ∩ [Y]) · (r ⊗ z) = r ⊗ (c₁(ℒ) ∩ z)` for `z ∈ CH_m(Y)`. -/
theorem rationalFirstChernClass_mul_smoothChowEquiv_of
    (Y : (SmoothProjectiveScheme k).FullSubcategory)
    (L : Y.obj.left.Modules)
    [SheafOfModules.IsInvertible Y.obj.left.sheaf.obj Y.obj.left.ringCatSheaf.property L]
    (m : ℤ) (r : ℚ) (z : chowGroup (fieldChowSituation k) Y.obj.hom m) :
    rationalFirstChernClass Y L *
        smoothChowEquiv Y.obj.hom
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] _) m (r ⊗ₜ z) : CHQ(Y.obj.hom)) =
      smoothChowEquiv Y.obj.hom (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] _) (m - 1)
        (r ⊗ₜ (invCap (fieldChowSituation k) Y.obj.hom L).capOnChow (fieldChowSituation k)
          Y.obj.hom (m - 1) (chowGroupCast (fieldChowSituation k) Y.obj.hom (by omega) z)) :
            CHQ(Y.obj.hom)) := by
  rw [rationalFirstChernClass, RationalIntersectionRing.equiv_mul_equiv,
    rationalIntersectionProduct_rationalChernCharacterComponentCap,
    rationalChernCharacterComponentCap_one_of_tmul]

/-- **The product with `(c₁(ℒ) ∩ [Y])^i` is the `i`-th power of the first Chern class
operation**: `(c₁(ℒ) ∩ [Y])^i · (r ⊗ z) = r ⊗ (c₁(ℒ)^i ∩ z)` for `z ∈ CH_a(Y)`, `a = m + i`. -/
theorem rationalFirstChernClass_pow_mul_smoothChowEquiv_of
    (Y : (SmoothProjectiveScheme k).FullSubcategory)
    (L : Y.obj.left.Modules)
    [SheafOfModules.IsInvertible Y.obj.left.sheaf.obj Y.obj.left.ringCatSheaf.property L]
    (i : ℕ) (a m : ℤ) (h : a = m + i) (r : ℚ) (z : chowGroup (fieldChowSituation k) Y.obj.hom a) :
    rationalFirstChernClass Y L ^ i *
        smoothChowEquiv Y.obj.hom
          (DirectSum.of (fun _ : ℤ => ℚ ⊗[ℤ] _) a (r ⊗ₜ z) : CHQ(Y.obj.hom)) =
      smoothChowEquiv Y.obj.hom (DirectSum.of (fun _ : ℤ => ℚ ⊗[ℤ] _) m
        (r ⊗ₜ capPow (fieldChowSituation k) Y.obj.hom (invCap (fieldChowSituation k) Y.obj.hom L)
          i a m h z) : CHQ(Y.obj.hom)) := by
  induction i generalizing m with
  | zero =>
    rw [pow_zero, one_mul, capPow_zero_apply]
    exact congrArg _ (of_tmul_eq_of_tmul_of_heq _ _ (by simpa using h) r
      (chowGroupCast_heq _ _ _ _).symm)
  | succ i ih =>
    rw [pow_succ', mul_assoc, ih (m + 1) (by push_cast at h; omega),
      rationalFirstChernClass_mul_smoothChowEquiv_of, capPow_succ_apply']
    exact congrArg _ (of_tmul_eq_of_tmul_of_heq _ _ (by ring) r
      (ChernCapOperator.capOnChow_heq _ _ _ (by ring) (chowGroupCast_heq _ _ _ _)))

/-- **The Gysin map of a flat morphism is flat pullback** (Stacks 0FF4) on the rational Chow
rings: `f^!(r ⊗ β) = r ⊗ f^*β` for `f` flat of relative dimension `m` and `β ∈ CH_j(Y)`. -/
theorem smoothGysinRingHom_smoothChowEquiv_of_flat
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) [Flat f.hom.left] (m : ℕ) (hm : RelativeDimension f.hom.left m) (j : ℤ) (r : ℚ)
    (β : chowGroup (fieldChowSituation k) Y.obj.hom j) :
    smoothGysinRingHom X.obj.hom Y.obj.hom (Over.w f.hom)
        (smoothChowEquiv Y.obj.hom (DirectSum.of (fun _ : ℤ => ℚ ⊗[ℤ] _) j (r ⊗ₜ β) :
          CHQ(Y.obj.hom))) =
      smoothChowEquiv X.obj.hom (DirectSum.of (fun _ : ℤ => ℚ ⊗[ℤ] _) (j + m)
        (r ⊗ₜ flatPullbackChow (fieldChowSituation k) X.obj.hom Y.obj.hom f.hom.left
          (Over.w f.hom) m hm j
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ j) β) :
            CHQ(X.obj.hom)) := by
  rw [smoothGysinRingHom_equiv]
  exact congrArg _ (lciGysinRational_of_tmul_of_flat _ _ _ _ _ _ m hm j r β)

/-- Proper pushforward on the rational Chow rings sends `r ⊗ z` to `r ⊗ f_*z`. -/
theorem rationalPush_smoothChowEquiv_of {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y)
    [IsProper f.hom.left] (j : ℤ) (r : ℚ) (z : chowGroup (fieldChowSituation k) X.obj.hom j) :
    rationalPush f
        (smoothChowEquiv X.obj.hom (DirectSum.of (fun _ : ℤ => ℚ ⊗[ℤ] _) j (r ⊗ₜ z) :
          CHQ(X.obj.hom))) =
      smoothChowEquiv Y.obj.hom (DirectSum.of (fun _ : ℤ => ℚ ⊗[ℤ] _) j
        (r ⊗ₜ properChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom f.hom.left
          (Over.w f.hom) j (properPushforwardDescends _ _ _ _ _ _) z) : CHQ(Y.obj.hom)) := by
  simp only [rationalPush, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  exact congrArg _ (rationalProperChowPushforward_of_tmul _ _ _ _ j r z)

end Classes

section Bundle

variable {X₀ : Scheme.{u}} (E : X₀.Modules) (n : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  {Q U : (SmoothProjectiveScheme k).FullSubcategory} (q : Q ⟶ U) (g : U.obj.left ⟶ X₀)
  (h : Q.obj.left ⟶ Stacks.Chow.bundle E)
  (hsq : IsPullback q.hom.left h g (Stacks.Chow.bundleProj E))
  (L : Q.obj.left.Modules) [SheafOfModules.IsInvertible Q.obj.left.sheaf.obj
    Q.obj.left.ringCatSheaf.property L]
  (eL : L ≅ (Scheme.Modules.pullback h).obj (Stacks.Chow.bundleTwist E))

include n hsq in
/-- A base change `q` of the projective bundle `𝐏(ℰ) ⟶ X₀` of a module of rank `n + 1` is flat. -/
theorem flat_of_isPullback_bundleProj : Flat q.hom.left := by
  let := flat_bundleProj E n
  exact MorphismProperty.of_isPullback (P := @Flat) hsq.flip inferInstance

include hsq in
/-- A base change `q` of the projective bundle `𝐏(ℰ) ⟶ X₀` of a module of rank `n + 1` has relative
dimension `n` (Stacks 02NK). -/
theorem relativeDimension_of_isPullback_bundleProj : RelativeDimension q.hom.left n := by
  let := locallyOfFiniteType_bundleProj E n
  exact RelativeDimension.of_isPullback hsq.flip (relativeDimension_bundleProj E n)

include hsq eL

/-- **Stacks 02TX on the rational Chow ring**: `CH^*(Q) ⊗ 𝐐` is spanned by the classes
`c₁(ℒ)^i · q^!y`, `i ≤ n`. -/
theorem exists_eq_sum_rationalFirstChernClass_pow_mul
    (x : smoothRationalChowRing (k := k) Q.obj.hom) :
    ∃ y : Fin (n + 1) → smoothRationalChowRing (k := k) U.obj.hom,
      x = ∑ i : Fin (n + 1), rationalFirstChernClass Q L ^ (i : ℕ) *
        smoothGysinRingHom Q.obj.hom U.obj.hom (Over.w q.hom) (y i) := by
  classical
  have := flat_of_isPullback_bundleProj E n q g h hsq
  have hqn := relativeDimension_of_isPullback_bundleProj E n q g h hsq
  obtain ⟨α, rfl⟩ := (smoothChowEquiv Q.obj.hom).surjective x
  induction α using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add α β hα hβ =>
    obtain ⟨y, hy⟩ := hα
    obtain ⟨y', hy'⟩ := hβ
    refine ⟨y + y', ?_⟩
    rw [map_add, hy, hy']
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  | of j t =>
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add t t' ht ht' =>
      obtain ⟨y, hy⟩ := ht
      obtain ⟨y', hy'⟩ := ht'
      refine ⟨y + y', ?_⟩
      rw [map_add, map_add, hy, hy']
      simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    | tmul r z =>
      have hj : j = (j - n) + n := by ring
      obtain ⟨β, hβ⟩ := (bijective_bundleMap_of_isPullback (fieldChowSituation k) E n U.obj.hom
        Q.obj.hom g q.hom.left (Over.w q.hom) hqn h hsq L eL (j - n)).2
          (chowGroupCast _ _ hj z)
      refine ⟨fun i => smoothChowEquiv U.obj.hom
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) U.obj.hom j)
          (j - n + (i : ℕ)) (r ⊗ₜ β i)), ?_⟩
      have hterm : ∀ i : Fin (n + 1), rationalFirstChernClass Q L ^ (i : ℕ) *
          smoothGysinRingHom Q.obj.hom U.obj.hom (Over.w q.hom) (smoothChowEquiv U.obj.hom
            (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) U.obj.hom j)
              (j - n + (i : ℕ)) (r ⊗ₜ β i))) =
          smoothChowEquiv Q.obj.hom
            (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) Q.obj.hom j)
              (j - n + n) (r ⊗ₜ bundleTerm (fieldChowSituation k) U.obj.hom Q.obj.hom q.hom.left
                (Over.w q.hom) n hqn (invCap (fieldChowSituation k) Q.obj.hom L) (j - n) i
                (β i))) := by
        intro i
        rw [smoothGysinRingHom_smoothChowEquiv_of_flat q n hqn,
          rationalFirstChernClass_pow_mul_smoothChowEquiv_of Q L i _ (j - n + n) (by ring)]
        rfl
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum, ← map_sum, ← TensorProduct.tmul_sum,
        ← bundleMap_apply, hβ]
      exact congrArg _ (of_tmul_eq_of_tmul_of_heq _ _ hj r (chowGroupCast_heq _ _ _ _).symm)

/-- **Stacks 02TW on the rational Chow ring**: `q_*(c₁(ℒ)^i) = 0` for `i < n` and `= 1` for
`i = n`. -/
theorem rationalPush_rationalFirstChernClass_pow (i : Fin (n + 1)) :
    rationalPush q (rationalFirstChernClass Q L ^ (i : ℕ)) = if i = Fin.last n then 1 else 0 := by
  classical
  have := isProper_hom_left q
  have := flat_of_isPullback_bundleProj E n q g h hsq
  have hqn := relativeDimension_of_isPullback_bundleProj E n q g h hsq
  have h1 : (1 : smoothRationalChowRing (k := k) U.obj.hom) =
      ∑ d ∈ (fundamentalClassDegrees_finite (fieldChowSituation k) U.obj.hom).toFinset,
        smoothChowEquiv U.obj.hom
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) U.obj.hom j) d
            ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k) U.obj.hom d)) := by
    rw [RationalIntersectionRing.one_eq, rationalFundamentalClass_eq, map_sum]
  have key : ∀ d : ℤ, rationalPush q (rationalFirstChernClass Q L ^ (i : ℕ) *
      smoothGysinRingHom Q.obj.hom U.obj.hom (Over.w q.hom) (smoothChowEquiv U.obj.hom
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) U.obj.hom j) d
          ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k) U.obj.hom d)))) =
      if i = Fin.last n then smoothChowEquiv U.obj.hom
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) U.obj.hom j) d
          ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k) U.obj.hom d)) else 0 := by
    intro d
    rw [smoothGysinRingHom_smoothChowEquiv_of_flat q n hqn,
      rationalFirstChernClass_pow_mul_smoothChowEquiv_of Q L i _ (d + n - (i : ℕ)) (by ring),
      rationalPush_smoothChowEquiv_of]
    have hb := bundleProjection_of_isPullback (fieldChowSituation k) E n U.obj.hom Q.obj.hom g
      q.hom.left (Over.w q.hom) hqn h hsq L eL i (Nat.lt_succ_iff.mp i.isLt) d (d + n - (i : ℕ))
      (by ring) (fundamentalChowClass (fieldChowSituation k) U.obj.hom d)
    refine (congrArg (fun t => smoothChowEquiv U.obj.hom
      (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) U.obj.hom j)
        (d + n - (i : ℕ)) ((1 : ℚ) ⊗ₜ t))) hb).trans ?_
    by_cases hi : i = Fin.last n
    · have hin : (i : ℕ) = n := by rw [hi, Fin.val_last]
      simp only [dif_pos hin, if_pos hi]
      exact congrArg _ (of_tmul_eq_of_tmul_of_heq _ _ (by omega) 1 (chowGroupCast_heq _ _ _ _))
    · have hin : (i : ℕ) ≠ n := fun h' => hi (Fin.ext (by rw [h', Fin.val_last]))
      simp only [dif_neg hin, if_neg hi, TensorProduct.tmul_zero, map_zero]
  have hone : rationalFirstChernClass Q L ^ (i : ℕ) = rationalFirstChernClass Q L ^ (i : ℕ) *
      smoothGysinRingHom Q.obj.hom U.obj.hom (Over.w q.hom) 1 := by
    rw [map_one, mul_one]
  rw [hone, h1, map_sum, Finset.mul_sum, map_sum, Finset.sum_congr rfl fun d _ => key d]
  by_cases hi : i = Fin.last n
  · simp only [if_pos hi]
  · simp only [if_neg hi, Finset.sum_const_zero]

end Bundle

end Stacks.WeilCohomology

end
