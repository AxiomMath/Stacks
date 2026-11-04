module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# The minimal field of definition of an element of `Frac(K ⊗[k] K₀)`

Let `k` be a field and `K`, `K₀` field extensions of `k` such that `K ⊗[k] K₀` is a domain.  For
an intermediate field `k ⊆ K' ⊆ K` the ring map `K' ⊗[k] K₀ → K ⊗[k] K₀` is injective (every
module over a field is flat), so `K' ⊗[k] K₀` is a domain and there is an induced map of
fraction fields `Frac(K' ⊗[k] K₀) → Frac(K ⊗[k] K₀)`.  For every `f ∈ Frac(K ⊗[k] K₀)` there is
a least `K'` such that `f` lies in the image of this map, the *minimal field of definition*
of `f`; it is finitely generated over `k` and it is compatible with extending `K`.

## Main results

* `TensorProduct.fractionRingMap`: the map `Frac(K ⊗[k] K₀) → Frac(L ⊗[k] K₀)` induced by a
  `k`-algebra map of fields `a : K → L`.
* `TensorProduct.fieldOfDefinition`: the minimal field of definition of `f`.
* `TensorProduct.fieldOfDefinition_isLeast`, `TensorProduct.fieldOfDefinition_spec`,
  `TensorProduct.fieldOfDefinition_le`: it is the least intermediate field `K'` with
  `f ∈ Set.range (fractionRingMap K₀ K'.val)`.
* `TensorProduct.fieldOfDefinition_fg`: it is finitely generated over `k`.
* `TensorProduct.fieldOfDefinition_map`: for `a : K →ₐ[k] L` with `L ⊗[k] K₀` a domain, the
  minimal field of definition of the image of `f` is the image under `a` of that of `f`.

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, I 3.5.
* D. Perrin, *Approximation des schémas en groupes, quasi compacts sur un corps*,
  Bull. SMF 104 (1976), 1.3.1.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct.FieldOfDefinition

variable {k K L K₀ : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Field K₀] [Algebra k K₀]

variable (k K₀) in
/-- The `K`-basis `(1 ⊗ eᵢ)` of `K ⊗[k] K₀` induced by the chosen `k`-basis `(eᵢ)` of `K₀`. -/
noncomputable def basis (K : Type*) [Field K] [Algebra k K] :
    Module.Basis (Module.Basis.ofVectorSpaceIndex k K₀) K (K ⊗[k] K₀) :=
  Algebra.TensorProduct.basis K (Module.Basis.ofVectorSpace k K₀)

variable (k K₀) in
/-- The `K`-basis of `(K ⊗[k] K₀) × (K ⊗[k] K₀)` obtained from `basis k K₀ K` on each factor. -/
noncomputable def pairBasis (K : Type*) [Field K] [Algebra k K] :
    Module.Basis (Module.Basis.ofVectorSpaceIndex k K₀ ⊕ Module.Basis.ofVectorSpaceIndex k K₀) K
      ((K ⊗[k] K₀) × (K ⊗[k] K₀)) :=
  (basis k K₀ K).prod (basis k K₀ K)

/-- `c • (1 ⊗ eᵢ) = c ⊗ eᵢ`. -/
theorem basis_smul (c : K) (i : Module.Basis.ofVectorSpaceIndex k K₀) :
    c • basis k K₀ K i = c ⊗ₜ Module.Basis.ofVectorSpace k K₀ i :=
  Algebra.TensorProduct.basis_repr_symm_apply' _ _ _

/-- `φ ⊗ 1` acts on coordinates along the bases `(1 ⊗ eᵢ)` by `φ`. -/
theorem basis_repr_rTensor (φ : K →ₗ[k] L) (x : K ⊗[k] K₀) (i) :
    (basis k K₀ L).repr (φ.rTensor K₀ x) i = φ ((basis k K₀ K).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
    simp only [basis, LinearMap.rTensor_tmul, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    rw [mul_comm c, ← _root_.Algebra.smul_def, map_smul, _root_.Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- `(φ ⊗ 1) × (φ ⊗ 1)` acts on coordinates along `pairBasis` by `φ`. -/
theorem pairBasis_repr_prodMap (φ : K →ₗ[k] L) (v : (K ⊗[k] K₀) × (K ⊗[k] K₀)) (j) :
    (pairBasis k K₀ L).repr ((φ.rTensor K₀).prodMap (φ.rTensor K₀) v) j =
      φ ((pairBasis k K₀ K).repr v j) := by
  rcases j with i | i <;> simp [pairBasis, basis_repr_rTensor]

/-- The `inl` coordinates of a pair are those of its first component. -/
theorem pairBasis_repr_inl (v : (K ⊗[k] K₀) × (K ⊗[k] K₀)) (i) :
    (pairBasis k K₀ K).repr v (.inl i) = (basis k K₀ K).repr v.1 i := by
  simp [pairBasis]

/-- The `inr` coordinates of a pair are those of its second component. -/
theorem pairBasis_repr_inr (v : (K ⊗[k] K₀) × (K ⊗[k] K₀)) (i) :
    (pairBasis k K₀ K).repr v (.inr i) = (basis k K₀ K).repr v.2 i := by
  simp [pairBasis]

/-- If all coordinates of a pair lie in `S`, so do those of each component. -/
private theorem pair_repr_mem {S : Set K} {v : (K ⊗[k] K₀) × (K ⊗[k] K₀)}
    (h : ∀ j, (pairBasis k K₀ K).repr v j ∈ S) :
    (∀ i, (basis k K₀ K).repr v.1 i ∈ S) ∧ ∀ i, (basis k K₀ K).repr v.2 i ∈ S :=
  ⟨fun i ↦ pairBasis_repr_inl v i ▸ h (.inl i), fun i ↦ pairBasis_repr_inr v i ▸ h (.inr i)⟩

/-- A pair with a coordinate equal to `1` is nonzero. -/
private theorem ne_zero_of_repr_eq_one {v : (K ⊗[k] K₀) × (K ⊗[k] K₀)}
    (hv : ∃ s, (pairBasis k K₀ K).repr v s = 1) : v ≠ 0 := by
  obtain ⟨s, hs⟩ := hv
  rintro rfl
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hs
  exact zero_ne_one hs

/-- An element of `L ⊗[k] K₀` whose coordinates lie in the image of `a : K → L` lies in the
image of `a ⊗ 1`. -/
theorem mem_range_rTensor (a : K →ₐ[k] L) {x : L ⊗[k] K₀}
    (hx : ∀ i, (basis k K₀ L).repr x i ∈ Set.range a) :
    x ∈ Set.range (a.toLinearMap.rTensor K₀) := by
  choose d hd using hx
  refine ⟨∑ i ∈ ((basis k K₀ L).repr x).support, d i ⊗ₜ Module.Basis.ofVectorSpace k K₀ i, ?_⟩
  conv_rhs => rw [← (basis k K₀ L).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, hd, basis_smul]

end TensorProduct.FieldOfDefinition

namespace TensorProduct

open FieldOfDefinition

variable {k K L K₀ : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Field K₀] [Algebra k K₀]

/-- If `K ⊗[k] K₀` is a domain, so is `K' ⊗[k] K₀` for every intermediate field `K'`. -/
instance isDomain_intermediateField [IsDomain (K ⊗[k] K₀)] (K' : IntermediateField k K) :
    IsDomain (K' ⊗[k] K₀) :=
  Function.Injective.isDomain (Algebra.TensorProduct.map K'.val (AlgHom.id k K₀)).toRingHom
    (Module.Flat.rTensor_preserves_injective_linearMap _ K'.val.toRingHom.injective)

variable (K₀) in
/-- The map of fraction fields `Frac(K ⊗[k] K₀) → Frac(L ⊗[k] K₀)` induced by a `k`-algebra map
`a : K → L` of fields, i.e. by the injective ring map `a ⊗ 1 : K ⊗[k] K₀ → L ⊗[k] K₀`. -/
noncomputable def fractionRingMap [IsDomain (L ⊗[k] K₀)] (a : K →ₐ[k] L) :
    FractionRing (K ⊗[k] K₀) →+* FractionRing (L ⊗[k] K₀) :=
  IsLocalization.map _ (Algebra.TensorProduct.map a (AlgHom.id k K₀)).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Module.Flat.rTensor_preserves_injective_linearMap
        _ a.toRingHom.injective))

/-- `fractionRingMap K₀ a` extends `a ⊗ 1`. -/
theorem fractionRingMap_algebraMap [IsDomain (L ⊗[k] K₀)] (a : K →ₐ[k] L) (x : K ⊗[k] K₀) :
    fractionRingMap K₀ a (algebraMap _ _ x) = algebraMap _ _ (a.toLinearMap.rTensor K₀ x) :=
  IsLocalization.map_eq _ _

/-- `a ⊗ 1` is nonzero on nonzero elements. -/
private theorem rTensor_ne_zero (a : K →ₐ[k] L) {x : K ⊗[k] K₀} (hx : x ≠ 0) :
    a.toLinearMap.rTensor K₀ x ≠ 0 :=
  (map_ne_zero_iff _ (Module.Flat.rTensor_preserves_injective_linearMap _
    a.toRingHom.injective)).mpr hx

/-- `a ⊗ 1` carries a solution `p = f * q` to a solution `p' = fractionRingMap a f * q'`. -/
private theorem algebraMap_rTensor_eq_mul [IsDomain (L ⊗[k] K₀)] (a : K →ₐ[k] L)
    {f : FractionRing (K ⊗[k] K₀)} {p q : K ⊗[k] K₀}
    (h : algebraMap _ (FractionRing (K ⊗[k] K₀)) p = f * algebraMap _ _ q) :
    algebraMap _ (FractionRing (L ⊗[k] K₀)) (a.toLinearMap.rTensor K₀ p) =
      fractionRingMap K₀ a f * algebraMap _ _ (a.toLinearMap.rTensor K₀ q) := by
  rw [← fractionRingMap_algebraMap, ← fractionRingMap_algebraMap, h, map_mul]

end TensorProduct

namespace TensorProduct.FieldOfDefinition

variable {k K L K₀ : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Field K₀] [Algebra k K₀] [IsDomain (K ⊗[k] K₀)]

/-- The `K`-subspace of pairs `(p, q)` in `(K ⊗[k] K₀) × (K ⊗[k] K₀)` with `p = f * q` in the
fraction field. -/
def solutions (f : FractionRing (K ⊗[k] K₀)) : Submodule K ((K ⊗[k] K₀) × (K ⊗[k] K₀)) where
  carrier := {v | algebraMap _ (FractionRing (K ⊗[k] K₀)) v.1 = f * algebraMap _ _ v.2}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, map_add] at *
    rw [hv, hw, mul_add]
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd] at hv ⊢
    rw [_root_.Algebra.smul_def, _root_.Algebra.smul_def, map_mul, map_mul, hv]
    ring

/-- A normalised solution of minimal support: an element of `solutions f` with some coordinate
equal to `1` whose support is at most as large as that of any nonzero element of `solutions f`. -/
def IsMinimal (f : FractionRing (K ⊗[k] K₀)) (v : (K ⊗[k] K₀) × (K ⊗[k] K₀)) : Prop :=
  v ∈ solutions f ∧ (∃ s, (pairBasis k K₀ K).repr v s = 1) ∧
    ∀ w ∈ solutions f, w ≠ 0 →
      ((pairBasis k K₀ K).repr v).support.card ≤ ((pairBasis k K₀ K).repr w).support.card

/-- `f` is defined over `K'`: it is a quotient `p / q` of elements of `K ⊗[k] K₀` whose
coordinates along `basis k K₀ K` lie in `K'`. -/
def IsDefinedOver (f : FractionRing (K ⊗[k] K₀)) (K' : IntermediateField k K) : Prop :=
  ∃ p q : K ⊗[k] K₀, q ≠ 0 ∧ (∀ i, (basis k K₀ K).repr p i ∈ K') ∧
    (∀ i, (basis k K₀ K).repr q i ∈ K') ∧
    algebraMap _ (FractionRing (K ⊗[k] K₀)) p = f * algebraMap _ _ q

/-- A normalised solution of minimal support exists. -/
theorem exists_isMinimal (f : FractionRing (K ⊗[k] K₀)) : ∃ v, IsMinimal f v := by
  classical
  set B := pairBasis k K₀ K
  have hex : ∃ n, ∃ w ∈ solutions f, w ≠ 0 ∧ (B.repr w).support.card = n := by
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (K ⊗[k] K₀)) f
    refine ⟨_, (p, q), ?_, fun h ↦ nonZeroDivisors.coe_ne_zero q (congrArg Prod.snd h), rfl⟩
    show algebraMap _ _ p = f * algebraMap _ _ (q : K ⊗[k] K₀)
    rw [← hpq]
    exact (IsLocalization.mk'_spec _ p q).symm
  obtain ⟨w, hw, hw0, hwn⟩ := Nat.find_spec hex
  have hmin : ∀ u ∈ solutions f, u ≠ 0 →
      (B.repr w).support.card ≤ (B.repr u).support.card :=
    fun u hu hu0 ↦ hwn ▸ Nat.find_min' hex ⟨u, hu, hu0, rfl⟩
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp (B.repr.map_ne_zero_iff.mpr hw0)
  rw [Finsupp.coe_zero, Pi.zero_apply] at hs
  refine ⟨(B.repr w s)⁻¹ • w, (solutions f).smul_mem _ hw, ⟨s, ?_⟩, fun u hu hu0 ↦ ?_⟩
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hs
  rw [map_smul, Finsupp.support_smul_eq (inv_ne_zero hs)]
  exact hmin u hu hu0

omit [IsDomain (K ⊗[k] K₀)] in
/-- If `v` has minimal support in a subspace `V` and is normalised at `s`, then any additive map
`P` preserving `V` and acting coordinatewise by some `π` with `π 1 = 1` fixes the coordinates
of `v`. -/
theorem apply_repr_eq_of_minimal {ι M : Type*} [AddCommGroup M] [Module K M]
    (B : Module.Basis ι K M) (V : Submodule K M) {v : M} (hv : v ∈ V)
    (hmin : ∀ w ∈ V, w ≠ 0 → (B.repr v).support.card ≤ (B.repr w).support.card)
    {s : ι} (hs : B.repr v s = 1) (π : K →+ K) (hπ : π 1 = 1) (P : M →+ M)
    (hPV : ∀ x ∈ V, P x ∈ V) (hP : ∀ x j, B.repr (P x) j = π (B.repr x j)) (j : ι) :
    π (B.repr v j) = B.repr v j := by
  classical
  have hw : v - P v = 0 := by
    by_contra hw
    have hsub : (B.repr (v - P v)).support ⊆ (B.repr v).support.erase s := by
      intro j hj
      rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply, hP] at hj
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      refine ⟨?_, fun h0 ↦ ?_⟩
      · rintro rfl
        rw [hs, hπ, sub_self] at hj
        exact hj rfl
      · rw [h0, map_zero, sub_zero] at hj
        exact hj rfl
    have hlt := (Finset.card_le_card hsub).trans_lt
      (Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr (hs ▸ one_ne_zero)))
    exact hlt.not_ge (hmin _ (V.sub_mem hv (hPV v hv)) hw)
  have := congrArg (fun x ↦ B.repr x j) hw
  simp only [map_sub, Finsupp.sub_apply, hP, map_zero, Finsupp.coe_zero, Pi.zero_apply,
    sub_eq_zero] at this
  exact this.symm

/-- The coordinates of a normalised solution of minimal support lie in every
intermediate field over which `f` is defined. -/
theorem repr_mem_of_isMinimal {f : FractionRing (K ⊗[k] K₀)} {v} (hv : IsMinimal f v)
    {K' : IntermediateField k K} (hK' : IsDefinedOver f K') (j) :
    (pairBasis k K₀ K).repr v j ∈ K' := by
  obtain ⟨p₀, q₀, hq₀, hp₀', hq₀', hpq₀⟩ := hK'
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K' K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K' K).injective)
  have hπx : ∀ c : K', π (c : K) = c := fun c ↦ LinearMap.congr_fun hπ c
  let π' : K →ₗ[k] K := K'.val.toLinearMap ∘ₗ π.restrictScalars k
  have hπ'1 : π' 1 = 1 := by
    show (π ((1 : K') : K) : K) = 1
    rw [hπx]
    rfl
  have hπ'mul : ∀ c ∈ K', ∀ x, π' (c * x) = c * π' x := by
    intro c hc x
    show (π (c * x) : K) = c * π x
    have : c * x = (⟨c, hc⟩ : K') • x := rfl
    rw [this, map_smul]
    rfl
  let P := π'.rTensor K₀
  have hPtmul : ∀ c ∈ K', ∀ (e : K₀) x, P ((c ⊗ₜ e) * x) = (c ⊗ₜ e) * P x := by
    intro c hc e x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d m =>
      simp only [P, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, hπ'mul c hc]
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
  have hPmul : ∀ z, (∀ i, (basis k K₀ K).repr z i ∈ K') → ∀ x, P (z * x) = z * P x := by
    intro z hz x
    rw [← (basis k K₀ K).linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [basis_smul]
    exact hPtmul _ (hz i) _ _
  obtain ⟨hvV, ⟨s, hs⟩, hmin⟩ := hv
  have key := apply_repr_eq_of_minimal (pairBasis k K₀ K) (solutions f) hvV hmin hs
    π'.toAddMonoidHom hπ'1 (P.prodMap P).toAddMonoidHom ?_
    (fun x j ↦ pairBasis_repr_prodMap π' x j) j
  · rw [← key]
    exact (π _).2
  · rintro ⟨p, q⟩ (hpq : algebraMap _ _ p = f * algebraMap _ _ q)
    show algebraMap _ _ (P p) = f * algebraMap _ _ (P q)
    have hinj := IsFractionRing.injective (K ⊗[k] K₀) (FractionRing (K ⊗[k] K₀))
    have h1 : q₀ * p = p₀ * q := hinj (by rw [map_mul, map_mul, hpq, hpq₀]; ring)
    have hq₀F : algebraMap _ (FractionRing (K ⊗[k] K₀)) q₀ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq₀
    apply mul_right_cancel₀ hq₀F
    calc algebraMap _ _ (P p) * algebraMap _ _ q₀ = algebraMap _ _ (P (q₀ * p)) := by
          rw [hPmul q₀ hq₀', ← map_mul, mul_comm]
      _ = algebraMap _ _ (P (p₀ * q)) := by rw [h1]
      _ = f * algebraMap _ _ q₀ * algebraMap _ _ (P q) := by rw [hPmul p₀ hp₀', map_mul, hpq₀]
      _ = f * algebraMap _ _ (P q) * algebraMap _ _ q₀ := by ring

/-- `f` comes from `Frac(K' ⊗[k] K₀)` if and only if it is a quotient `p / q` with `p`, `q`
having coordinates in `K'`. -/
theorem mem_range_fractionRingMap_iff {f : FractionRing (K ⊗[k] K₀)}
    {K' : IntermediateField k K} :
    f ∈ Set.range (fractionRingMap K₀ K'.val) ↔ IsDefinedOver f K' := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (K' ⊗[k] K₀)) z
    refine ⟨K'.val.toLinearMap.rTensor K₀ p, K'.val.toLinearMap.rTensor K₀ q,
      rTensor_ne_zero _ (nonZeroDivisors.coe_ne_zero q),
      fun i ↦ ?_, fun i ↦ ?_, ?_⟩
    · rw [basis_repr_rTensor]
      exact SetLike.coe_mem _
    · rw [basis_repr_rTensor]
      exact SetLike.coe_mem _
    · simp only [fractionRingMap, IsLocalization.map_mk']
      exact (IsLocalization.mk'_spec _ _ _).symm
  · rintro ⟨p, q, hq, hp', hq', hpq⟩
    obtain ⟨p', rfl⟩ := mem_range_rTensor K'.val (fun i ↦ ⟨⟨_, hp' i⟩, rfl⟩)
    obtain ⟨q', rfl⟩ := mem_range_rTensor K'.val (fun i ↦ ⟨⟨_, hq' i⟩, rfl⟩)
    have hq'0 : q' ≠ 0 := by
      rintro rfl
      exact hq (map_zero _)
    refine ⟨IsLocalization.mk' _ p'
      (⟨q', mem_nonZeroDivisors_of_ne_zero hq'0⟩ : nonZeroDivisors _), ?_⟩
    rwa [fractionRingMap, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]

omit [IsDomain (K ⊗[k] K₀)] in
/-- If `f` is defined over `K'`, its image under `a` is defined over `a(K')`. -/
theorem isDefinedOver_map [IsDomain (L ⊗[k] K₀)] (a : K →ₐ[k] L)
    {f : FractionRing (K ⊗[k] K₀)} {K' : IntermediateField k K} (h : IsDefinedOver f K') :
    IsDefinedOver (fractionRingMap K₀ a f) (K'.map a) := by
  obtain ⟨p, q, hq, hp', hq', hpq⟩ := h
  refine ⟨a.toLinearMap.rTensor K₀ p, a.toLinearMap.rTensor K₀ q,
    rTensor_ne_zero a hq, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · rw [basis_repr_rTensor]
    exact (IntermediateField.mem_map _).mpr ⟨_, hp' i, rfl⟩
  · rw [basis_repr_rTensor]
    exact (IntermediateField.mem_map _).mpr ⟨_, hq' i, rfl⟩
  · exact algebraMap_rTensor_eq_mul a hpq

/-- A chosen normalised solution of minimal support for `f`. -/
noncomputable def minimalSolution (f : FractionRing (K ⊗[k] K₀)) :
    (K ⊗[k] K₀) × (K ⊗[k] K₀) :=
  (exists_isMinimal f).choose

/-- `minimalSolution f` is a normalised solution of minimal support. -/
theorem isMinimal_minimalSolution (f : FractionRing (K ⊗[k] K₀)) :
    IsMinimal f (minimalSolution f) :=
  (exists_isMinimal f).choose_spec

end TensorProduct.FieldOfDefinition

namespace TensorProduct

open FieldOfDefinition

variable {k K L K₀ : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Field K₀] [Algebra k K₀] [IsDomain (K ⊗[k] K₀)]

/-- The minimal field of definition of `f ∈ Frac(K ⊗[k] K₀)`: the least intermediate field
`k ⊆ K' ⊆ K` such that `f` comes from `Frac(K' ⊗[k] K₀)`.  It is generated over `k` by the
coordinates of the normalised solution `minimalSolution f` of `p = f q` of minimal support. -/
noncomputable def fieldOfDefinition (f : FractionRing (K ⊗[k] K₀)) : IntermediateField k K :=
  IntermediateField.adjoin k (Set.range ((pairBasis k K₀ K).repr (minimalSolution f)))

/-- `f` is defined over `fieldOfDefinition f`. -/
theorem isDefinedOver_fieldOfDefinition (f : FractionRing (K ⊗[k] K₀)) :
    IsDefinedOver f (fieldOfDefinition f) := by
  have hv := isMinimal_minimalSolution f
  have hmem := pair_repr_mem (S := (fieldOfDefinition f : Set K))
    fun j ↦ IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
  have hvV : algebraMap _ (FractionRing (K ⊗[k] K₀)) (minimalSolution f).1 =
      f * algebraMap _ _ (minimalSolution f).2 := hv.1
  refine ⟨(minimalSolution f).1, (minimalSolution f).2, fun hq ↦ ?_, hmem.1, hmem.2, hvV⟩
  have hp : (minimalSolution f).1 = 0 :=
    IsFractionRing.injective _ (FractionRing (K ⊗[k] K₀)) (by rw [hvV, hq, map_zero, mul_zero])
  exact ne_zero_of_repr_eq_one hv.2.1 (Prod.ext hp hq)

/-- `fieldOfDefinition f` is the least intermediate field `K'` such that `f` lies in the image
of `Frac(K' ⊗[k] K₀) → Frac(K ⊗[k] K₀)`. -/
theorem fieldOfDefinition_isLeast (f : FractionRing (K ⊗[k] K₀)) :
    IsLeast {K' : IntermediateField k K | f ∈ Set.range (fractionRingMap K₀ K'.val)}
      (fieldOfDefinition f) := by
  refine ⟨mem_range_fractionRingMap_iff.mpr (isDefinedOver_fieldOfDefinition f),
    fun K' hK' ↦ ?_⟩
  rw [fieldOfDefinition, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  exact repr_mem_of_isMinimal (isMinimal_minimalSolution f)
    (mem_range_fractionRingMap_iff.mp hK') j

/-- `f` comes from `Frac(fieldOfDefinition f ⊗[k] K₀)`. -/
theorem fieldOfDefinition_spec (f : FractionRing (K ⊗[k] K₀)) :
    f ∈ Set.range (fractionRingMap K₀ (fieldOfDefinition f).val) :=
  (fieldOfDefinition_isLeast f).1

/-- `fieldOfDefinition f` is contained in every intermediate field `K'` such that `f` comes
from `Frac(K' ⊗[k] K₀)`. -/
theorem fieldOfDefinition_le {f : FractionRing (K ⊗[k] K₀)} {K' : IntermediateField k K}
    (hK' : f ∈ Set.range (fractionRingMap K₀ K'.val)) : fieldOfDefinition f ≤ K' :=
  (fieldOfDefinition_isLeast f).2 hK'

/-- The minimal field of definition is finitely generated over `k`. -/
theorem fieldOfDefinition_fg (f : FractionRing (K ⊗[k] K₀)) : (fieldOfDefinition f).FG :=
  IntermediateField.fg_def.mpr ⟨_, Finsupp.finite_range _, rfl⟩

/-- The minimal field of definition is compatible with extending `K`: for a `k`-algebra map
`a : K → L` of fields with `L ⊗[k] K₀` a domain, the minimal field of definition of the image of
`f` in `Frac(L ⊗[k] K₀)` is the image under `a` of the minimal field of definition of `f`. -/
theorem fieldOfDefinition_map [IsDomain (L ⊗[k] K₀)] (a : K →ₐ[k] L)
    (f : FractionRing (K ⊗[k] K₀)) :
    fieldOfDefinition (fractionRingMap K₀ a f) = (fieldOfDefinition f).map a := by
  set g := fractionRingMap K₀ a f
  set Φ := (a.toLinearMap.rTensor K₀).prodMap (a.toLinearMap.rTensor K₀)
  have hrepr : ∀ v j, (pairBasis k K₀ L).repr (Φ v) j = a ((pairBasis k K₀ K).repr v j) :=
    fun v j ↦ pairBasis_repr_prodMap a.toLinearMap v j
  have hsol : ∀ v ∈ solutions f, Φ v ∈ solutions g := by
    rintro ⟨p, q⟩ (h : algebraMap _ _ p = f * algebraMap _ _ q)
    exact algebraMap_rTensor_eq_mul a h
  have hcard : ∀ v, ((pairBasis k K₀ L).repr (Φ v)).support.card =
      ((pairBasis k K₀ K).repr v).support.card := by
    intro v
    congr 1
    ext j
    simp [Finsupp.mem_support_iff, hrepr]
  obtain ⟨hvV, ⟨s, hs⟩, hvmin⟩ := isMinimal_minimalSolution f
  have hvLmin : IsMinimal g (Φ (minimalSolution f)) := by
    refine ⟨hsol _ hvV, ⟨s, by rw [hrepr, hs, map_one]⟩, fun w hw hw0 ↦ ?_⟩
    obtain ⟨huV, -, humin⟩ := isMinimal_minimalSolution g
    have hmem : ∀ j, (pairBasis k K₀ L).repr (minimalSolution g) j ∈ Set.range a := fun j ↦ by
      obtain ⟨x, -, hx⟩ := (IntermediateField.mem_map _).mp (repr_mem_of_isMinimal
        (isMinimal_minimalSolution g) (isDefinedOver_map a (isDefinedOver_fieldOfDefinition f)) j)
      exact ⟨x, hx⟩
    obtain ⟨u₁, hu₁⟩ := mem_range_rTensor a (pair_repr_mem hmem).1
    obtain ⟨u₂, hu₂⟩ := mem_range_rTensor a (pair_repr_mem hmem).2
    have hΦu : Φ (u₁, u₂) = minimalSolution g := Prod.ext hu₁ hu₂
    have hu' : (u₁, u₂) ∈ solutions f := by
      show algebraMap _ _ u₁ = f * algebraMap _ _ u₂
      apply (fractionRingMap K₀ a).injective
      rw [map_mul, fractionRingMap_algebraMap, fractionRingMap_algebraMap, hu₁, hu₂]
      exact huV
    have hu'0 : (u₁, u₂) ≠ 0 := fun h ↦
      ne_zero_of_repr_eq_one (isMinimal_minimalSolution g).2.1 (by rw [← hΦu, h, map_zero])
    rw [hcard]
    calc ((pairBasis k K₀ K).repr (minimalSolution f)).support.card
        ≤ ((pairBasis k K₀ K).repr (u₁, u₂)).support.card := hvmin _ hu' hu'0
      _ = ((pairBasis k K₀ L).repr (minimalSolution g)).support.card := by rw [← hcard, hΦu]
      _ ≤ _ := humin w hw hw0
  refine (fieldOfDefinition_isLeast g).unique
    ⟨mem_range_fractionRingMap_iff.mpr
      (isDefinedOver_map a (isDefinedOver_fieldOfDefinition f)), fun K' hK' ↦ ?_⟩
  rw [fieldOfDefinition, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  rw [← hrepr]
  exact repr_mem_of_isMinimal hvLmin (mem_range_fractionRingMap_iff.mp hK') j

end TensorProduct

end
