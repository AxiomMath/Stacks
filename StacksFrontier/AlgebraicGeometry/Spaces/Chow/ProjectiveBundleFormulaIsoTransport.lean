module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LineBundleFlatPullbackChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional

/-!
# The two halves of the projective bundle formula along an isomorphism of bundles

Let `π : P → X` and `π' : P' → X` be proper morphisms of good algebraic spaces over the base,
flat of relative dimension `n`, with invertible modules `ℒ` on `P` and `ℒ'` on `P'`, and let
`φ : P' ≅ P` be an isomorphism over `X` with `φ^*ℒ ≅ ℒ'`. This file shows that the top power of
Stacks 0ERU (`AlgebraicGeometry.Space.BundleTopPowerIdentity`) and the surjectivity half of
Stacks 0ERV (`AlgebraicGeometry.Space.BundleFormulaSurjective`) pass from `(π, ℒ)` to
`(π', ℒ')`.

The proofs only use that `φ` is flat of relative dimension `0` with `φ^*π^* = π'^*`
(Stacks 0EPA), that the square formed by `φ` and the identity of `X` is cartesian so that
`π'_*φ^* = π_*` (Stacks 0EPD), Stacks 0EQR for the cap products, and that
`φ^* (φ⁻¹)^* = id`.

## Main definitions

* `AlgebraicGeometry.Space.BundleTopPowerIdentity`: `π_*(c₁(ℒ)^n ∩ π^*α) = α` in `CH_k(X)`.
* `AlgebraicGeometry.Space.BundleFormulaSurjective`: the map of the projective bundle formula is
  surjective in every degree.

## Main results

* `AlgebraicGeometry.Space.BundleTopPowerIdentity.of_iso`
* `AlgebraicGeometry.Space.BundleFormulaSurjective.of_iso`

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Defs

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The top power of Stacks 0ERU in the Chow group**: `π_*(c₁(ℒ)^n ∩ π^*α) = α` in `CH_k(X)` for
every `k` and every `k`-cycle `α` on `X`. -/
def BundleTopPowerIdentity : Prop :=
  ∀ (k : ℤ) (α : CycleGroup D sX k),
    chowClassCanonical.{u + 1} D sX hX k
        (properCyclePushforward D sP hP sX hX hπB hp.2.1.2 k
          (firstChernCapPowCycleMap D sP hP L hL n k
            (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k (k + n) rfl α))) =
      chowClassCanonical.{u + 1} D sX hX k α

/-- **The surjectivity half of Stacks 0ERV**: the map `(α_i) ↦ ∑_i c₁(ℒ)^i ∩ π^*α_i` is surjective
in every degree. -/
def BundleFormulaSurjective : Prop :=
  ∀ (N : ℤ) (d : Fin (n + 1) → ℤ) (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)),
    Function.Surjective (bundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL N d hd)

end Defs

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X P P' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (sP' : P' ⟶ D.space) (hP' : D.IsGood sP')
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (π' : P' ⟶ X) (hπB' : π' ≫ sX = sP') (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (hflat' : IsFlat D.site D.base D.base_mem π')
    (hrel' : HasRelativeDimension n D.site D.base D.base_mem π')
    (hp' : IsProper D.site D.base D.base_mem π')
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (L' : Modules.{u, u} D.site D.base D.base_mem P' hP'.1)
    (hL' : IsInvertibleModule (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L')
    (φ : P' ⟶ P) [IsIso φ] (hφB : φ ≫ sP = sP') (hφπ : φ ≫ π = π')
    (e : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk φ : (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P, hP.1⟩)).obj L ≅ L')

include hP hP' in
/-- An isomorphism is flat of relative dimension `0`. -/
theorem isFlat_and_hasRelativeDimension_zero_of_isIso :
    IsFlat D.site D.base D.base_mem φ ∧ HasRelativeDimension 0 D.site D.base D.base_mem φ :=
  ⟨isFlat_of_isEtale D.site D.base D.base_mem
      (isEtale_of_isOpenImmersion D.site D.base D.base_mem
        (isOpenImmersion_of_isIso D.site D.base D.base_mem φ)),
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem φ hP.1
      (isEtale_of_isOpenImmersion D.site D.base D.base_mem
        (isOpenImmersion_of_isIso D.site D.base D.base_mem φ))⟩

include hφπ in
/-- `φ^*π^* = π'^*` on cycles. -/
theorem flatPullbackMap_comp_of_isIso (k m : ℤ) (h : k + (n : ℤ) = m) (α : CycleGroup D sX k) :
    flatPullbackMap D sP' hP' sP hP φ hφB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 m m (by simp)
        (flatPullbackMap D sP hP sX hX π hπB n hflat hrel k m h α) =
      flatPullbackMap D sP' hP' sX hX π' hπB' n hflat' hrel' k m h α := by
  have hφ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ
  refine Subtype.ext ?_
  have h1 := congrArg (fun ψ => (ψ α).1)
    (flatPullbackMap_comp D sP' hP' sP hP sX hX φ π hφB hπB 0 n hφ.1 hφ.2 hflat hrel k m
      (by push_cast; omega))
  refine (Eq.trans ?_ h1.symm).trans (flatPullbackMap_coe_congr D sP' hP' sX hX hφπ _ _
    (by omega) _ _ _ _ k m k m _ _ _ _ rfl)
  exact coe_flatPullbackMap_congr D sP hP sP' hP' φ hφB 0 hφ.1 hφ.2 h.symm rfl (by simp)
    (by push_cast; omega) _ _
    (coe_flatPullbackMap_congr D sX hX sP hP π hπB n hflat hrel rfl h.symm _ _ _ _ rfl)

include hφπ in
/-- `π'_*φ^* = π_*` on cycles: the square formed by `φ` and the identity of `X` is cartesian, and
flat pullback along the identity is the identity. -/
theorem properCyclePushforward_flatPullbackMap_of_isIso_over (k : ℤ) (β : CycleGroup D sP k) :
    properCyclePushforward D sP' hP' sX hX hπB' hp'.2.1.2 k
        (flatPullbackMap D sP' hP' sP hP φ hφB 0
          (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
          (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 k k (by simp) β) =
      properCyclePushforward D sP hP sX hX hπB hp.2.1.2 k β := by
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D sX hX sX hX (𝟙 X)
  have sq : IsPullback φ π' π (𝟙 X) := IsPullback.of_horiz_isIso ⟨by rw [hφπ, Category.comp_id]⟩
  have h := flatPullback_properPushforward_unconditional D sP' hP' sP hP sX hX sX hX hφB hπB' hπB
    (Category.id_comp sX) 0 hid.1 hid.2 sq hp k k (by simp) β
  refine Subtype.ext ?_
  rw [← h]
  exact flatPullbackMap_id_coe D sX hX (Category.id_comp sX) hid.1 hid.2 k k (by simp) _

/-- The first Chern cap power for `ℒ'` on a flat pullback along `φ` is the flat pullback along `φ`
of the one for `ℒ`, up to rational equivalence. -/
private theorem chowClass_firstChernCapPowCycleMap_flatPullbackMap_of_isIso (s : ℕ) (m : ℤ)
    (α : CycleGroup D sP (m + s))
    (e : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk φ : (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P, hP.1⟩)).obj L ≅ L') :
    chowClassCanonical.{u + 1} D sP' hP' m (firstChernCapPowCycleMap D sP' hP' L' hL' s m
        (flatPullbackMap D sP' hP' sP hP φ hφB 0
          (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
          (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 (m + s) (m + s)
          (by simp) α)) =
      chowClassCanonical.{u + 1} D sP' hP' m (flatPullbackMap D sP' hP' sP hP φ hφB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 m m (by simp)
        (firstChernCapPowCycleMap D sP hP L hL s m α)) := by
  rw [chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback
      D sP' hP' sP hP φ hφB 0 _ _ L hL s m m (by simp) (by simp),
    chowClassCanonical_firstChernCapPowCycleMap_congr_iso D sP' hP' _ L'
      (modulePullbackInvertible
        (ObjectProperty.homMk φ : (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨P, hP.1⟩) L hL) hL' e]

include hφB hφπ e hp' in
/-- **The top power passes along an isomorphism of bundles.** -/
theorem BundleTopPowerIdentity.of_iso
    (h : BundleTopPowerIdentity D sX hX sP hP π hπB n hflat hrel hp L hL) :
    BundleTopPowerIdentity D sX hX sP' hP' π' hπB' n hflat' hrel' hp' L' hL' := by
  intro k α
  have hφ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ
  rw [← flatPullbackMap_comp_of_isIso D sX hX sP hP sP' hP' π hπB π' hπB' n hflat hrel hflat'
      hrel' φ hφB hφπ k (k + n) rfl α,
    ← chowGroupCanonicalProperPushforward_chowClassCanonical.{u + 1} D sP' hP' sX hX hπB' hp',
    chowClass_firstChernCapPowCycleMap_flatPullbackMap_of_isIso D sP hP sP' hP' L hL L'
      hL' φ hφB n k _ e,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    properCyclePushforward_flatPullbackMap_of_isIso_over D sX hX sP hP sP' hP' π hπB π' hπB' hp hp'
      φ hφB hφπ]
  exact h k α

include hφπ e in
/-- The summands of the projective bundle formula for `(π', ℒ')` are the flat pullbacks along `φ`
of those for `(π, ℒ)`. -/
theorem bundleFormulaCap_bundleFormulaPull_of_isIso (s : ℕ) (m N : ℤ) (h : m + (n : ℤ) = N + s)
    (α : CycleGroup D sX m) :
    bundleFormulaCap D sP' hP' L' hL' s (N + s) N rfl
        (bundleFormulaPull D sX hX sP' hP' π' hπB' n hflat' hrel' m (N + s) h
          (chowClassCanonical.{u + 1} D sX hX m α)) =
      flatPullbackChowMapCanonical.{u + 1} D sP' hP' sP hP φ hφB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 N N (by simp)
        (bundleFormulaCap D sP hP L hL s (N + s) N rfl
          (bundleFormulaPull D sX hX sP hP π hπB n hflat hrel m (N + s) h
            (chowClassCanonical.{u + 1} D sX hX m α))) := by
  have hφ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ
  change chowClassCanonical.{u + 1} D sP' hP' N (firstChernCapPowCycleMap D sP' hP' L' hL' s N
      (cycleGroupCast D sP' rfl
        (flatPullbackMap D sP' hP' sX hX π' hπB' n hflat' hrel' m (N + s) h α))) =
    chowClassCanonical.{u + 1} D sP' hP' N (flatPullbackMap D sP' hP' sP hP φ hφB 0 hφ.1 hφ.2 N N
      (by simp) (firstChernCapPowCycleMap D sP hP L hL s N
        (cycleGroupCast D sP rfl
          (flatPullbackMap D sP hP sX hX π hπB n hflat hrel m (N + s) h α))))
  rw [← chowClass_firstChernCapPowCycleMap_flatPullbackMap_of_isIso D sP hP sP' hP' L hL L' hL'
    φ hφB s N _ e]
  congr 2
  rw [← flatPullbackMap_comp_of_isIso D sX hX sP hP sP' hP' π hπB π' hπB' n hflat hrel hflat'
    hrel' φ hφB hφπ m (N + s) h α]
  rfl

include hφπ e in
/-- **The map of the projective bundle formula for `(π', ℒ')` is the flat pullback along `φ` of
the one for `(π, ℒ)`.** -/
theorem bundleFormulaMap_of_isIso (N : ℤ) (d : Fin (n + 1) → ℤ)
    (hd : ∀ i, d i + (n : ℤ) = N + (i : ℕ)) (a : ∀ i, chowGroupCanonical.{u + 1} D sX hX (d i)) :
    bundleFormulaMap D sX hX sP' hP' π' hπB' n hflat' hrel' L' hL' N d hd a =
      flatPullbackChowMapCanonical.{u + 1} D sP' hP' sP hP φ hφB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 N N (by simp)
        (bundleFormulaMap D sX hX sP hP π hπB n hflat hrel L hL N d hd a) := by
  choose α hα using fun i => QuotientAddGroup.mk_surjective (a i)
  have ha : a = fun i => chowClassCanonical.{u + 1} D sX hX (d i) (α i) :=
    funext fun i => (hα i).symm
  subst ha
  simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    bundleFormulaCap_bundleFormulaPull_of_isIso D sX hX sP hP sP' hP' π hπB π' hπB' n hflat hrel
      hflat' hrel' L hL L' hL' φ hφB hφπ e i (d i) N (hd i) (α i)

include hφB hφπ e hp hp' in
/-- **The surjectivity half of Stacks 0ERV passes along an isomorphism of bundles.** -/
theorem BundleFormulaSurjective.of_iso
    (h : BundleFormulaSurjective D sX hX sP hP π hπB n hflat hrel L hL) :
    BundleFormulaSurjective D sX hX sP' hP' π' hπB' n hflat' hrel' L' hL' := by
  intro N d hd b'
  have hφ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ
  have hψB : inv φ ≫ sP' = sP := by rw [← hφB, IsIso.inv_hom_id_assoc]
  have hψ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' sP hP (inv φ)
  obtain ⟨β', rfl⟩ := QuotientAddGroup.mk_surjective b'
  obtain ⟨a, ha⟩ := h N d hd (chowClassCanonical.{u + 1} D sP hP N
    (flatPullbackMap D sP hP sP' hP' (inv φ) hψB 0 hψ.1 hψ.2 N N (by simp) β'))
  refine ⟨a, ?_⟩
  rw [bundleFormulaMap_of_isIso D sX hX sP hP sP' hP' π hπB π' hπB' n hflat hrel hflat' hrel' L hL
    L' hL' φ hφB hφπ e N d hd a, ha, flatPullbackChowMapCanonical_chowClassCanonical]
  change chowClassCanonical.{u + 1} D sP' hP' N _ = chowClassCanonical.{u + 1} D sP' hP' N β'
  congr 1
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D sP' hP' sP' hP' (𝟙 P')
  refine Subtype.ext ?_
  have h1 := congrArg (fun ψ => (ψ β').1)
    (flatPullbackMap_comp D sP' hP' sP hP sP' hP' φ (inv φ) hφB hψB 0 0 hφ.1 hφ.2 hψ.1 hψ.2 N N
      (by simp))
  refine (Eq.trans ?_ h1.symm).trans ((flatPullbackMap_coe_congr D sP' hP' sP' hP'
    (IsIso.hom_inv_id φ) _ (Category.id_comp sP') rfl _ hid.1 _ hid.2 N N N N _ (by simp) _ _
    rfl).trans (flatPullbackMap_id_coe D sP' hP' (Category.id_comp sP') hid.1 hid.2 N N (by simp)
    β'))
  exact coe_flatPullbackMap_congr D sP hP sP' hP' φ hφB 0 hφ.1 hφ.2 (by simp) rfl (by simp)
    (by simp) _ _
    (coe_flatPullbackMap_congr D sP' hP' sP hP (inv φ) hψB 0 hψ.1 hψ.2 rfl (by simp) (by simp)
      (by simp) _ _ rfl)

end Iso

end AlgebraicGeometry.Space

end
