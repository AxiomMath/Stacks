module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Prod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The filtration of an exterior power by the wedges with a submodule

Let `ι : E →ₗ[B] H` be a linear map of modules over a commutative ring `B`. The exterior powers of
`H` are filtered by the wedges with the image of `E`:

`F^k ⋀ⁿ H = ∑_{j ≥ k} (⋀ʲ ι)(⋀ʲ E) ∧ ⋀ⁿ⁻ʲ H`.

When `H = E × G` and `ι` is the first inclusion, the decomposition
`⋀ⁿ (E × G) ≅ ⨁_{p + q = n} ⋀ᵖ E ⊗ ⋀^q G` (`exteriorPower.prodEquivDirectSum`) identifies
`F^k ⋀ⁿ H` with the summands with `p ≥ k`, so **the graded piece `F^k / F^{k+1}` is
`⋀ᵏ E ⊗ ⋀ⁿ⁻ᵏ G`**, through `a ⊗ b ↦ (⋀ inl) a ∧ (⋀ inr) b`. An isomorphism `H ≅ E × G` carrying
`ι` to the first inclusion transports this to any split injection `ι`.

This is the linear algebra of the graded pieces of the filtration of [Stacks, Section 0FMK] on an
affine chart, used in the proof of [Stacks, Tag 0FUM]: for a smooth `A`-algebra `B` over `R` the
sequence `0 ⟶ B ⊗_A Ω_{A/R} ⟶ Ω_{B/R} ⟶ Ω_{B/A} ⟶ 0` is split exact.

## Main definitions

* `exteriorPower.wedgeLeftMul`: the map `y ↦ (⋀ ι) x ∧ y`, `⋀ⁿ⁻ʲ H ⟶ ⋀ⁿ H`, for `x ∈ ⋀ʲ E`.
* `exteriorPower.wedgeStep`: the step `F^k ⋀ⁿ H`.
* `exteriorPower.prodBlock`: the map `⋀ᵏ E ⊗ ⋀ⁿ⁻ᵏ G ⟶ ⋀ⁿ (E × G)`, `a ⊗ b ↦ (⋀ inl) a ∧ (⋀ inr) b`.
* `exteriorPower.prodGradedMap`: the induced map `⋀ᵏ E ⊗ ⋀ⁿ⁻ᵏ G ⟶ F^k / F^{k+1}`.

## Main results

* `exteriorPower.wedgeStep_mono`: the steps decrease.
* `exteriorPower.prodGradedMap_bijective`: **`⋀ᵏ E ⊗ ⋀ⁿ⁻ᵏ G ≅ F^k ⋀ⁿ (E × G) / F^{k+1}`.**
* `exteriorPower.wedgeStep_comap_map_of_comp_eq`: the filtration is carried along a linear
  isomorphism compatible with the two maps.

## References

* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public section

open scoped DirectSum TensorProduct

namespace exteriorPower

variable {B : Type*} [CommRing B] {E : Type*} [AddCommGroup E] [Module B E]
  {H : Type*} [AddCommGroup H] [Module B H] {G : Type*} [AddCommGroup G] [Module B G]

/-- The image of `⋀ʲ E` under a linear map lies in `⋀ʲ H`. -/
theorem map_coe_mem (ι : E →ₗ[B] H) {j : ℕ} (x : ⋀[B]^j E) :
    ExteriorAlgebra.map ι (x : ExteriorAlgebra B E) ∈ ⋀[B]^j H := by
  rw [← coe_map]
  exact (map j ι x).2

/-- A wedge of an element of `⋀ʲ` with one of `⋀ᵐ` lies in `⋀ʲ⁺ᵐ`. -/
theorem mul_mem_of_mem {j m n : ℕ} (h : j + m = n) {a b : ExteriorAlgebra B H}
    (ha : a ∈ ⋀[B]^j H) (hb : b ∈ ⋀[B]^m H) : a * b ∈ ⋀[B]^n H := by
  have := Submodule.mul_mem_mul ha hb
  rw [← pow_add, h] at this
  exact this

/-- **Left multiplication by the image of `x ∈ ⋀ʲ E`**, as a linear map `⋀ᵐ H ⟶ ⋀ⁿ H` for
`j + m = n`. -/
@[ega "III 1.1.7" "more general"]
def wedgeLeftMul (ι : E →ₗ[B] H) {j m n : ℕ} (h : j + m = n) (x : ⋀[B]^j E) :
    ⋀[B]^m H →ₗ[B] ⋀[B]^n H :=
  ((LinearMap.mulLeft B (ExteriorAlgebra.map ι (x : ExteriorAlgebra B E))).comp
    (⋀[B]^m H).subtype).codRestrict (⋀[B]^n H) fun y => mul_mem_of_mem h (map_coe_mem ι x) y.2

/-- In the exterior algebra, `wedgeLeftMul ι h x y` is the product `(⋀ ι) x * y`. -/
@[simp]
theorem coe_wedgeLeftMul (ι : E →ₗ[B] H) {j m n : ℕ} (h : j + m = n) (x : ⋀[B]^j E)
    (y : ⋀[B]^m H) :
    (wedgeLeftMul ι h x y : ExteriorAlgebra B H) =
      ExteriorAlgebra.map ι (x : ExteriorAlgebra B E) * y :=
  rfl

/-- **The `k`-th step `F^k ⋀ⁿ H = ∑_{j ≥ k} (⋀ʲ ι)(⋀ʲ E) ∧ ⋀ⁿ⁻ʲ H` of the wedge filtration.** -/
def wedgeStep (ι : E →ₗ[B] H) (k n : ℕ) : Submodule B (⋀[B]^n H) :=
  ⨆ (j : ℕ) (m : ℕ) (h : j + m = n) (_ : k ≤ j) (x : ⋀[B]^j E),
    LinearMap.range (wedgeLeftMul ι h x)

/-- For `x ∈ ⋀ʲ E` with `k ≤ j`, the wedge `(⋀ ι) x ∧ y` lies in the `k`-th step. -/
theorem wedgeLeftMul_mem_wedgeStep (ι : E →ₗ[B] H) {k j m n : ℕ} (h : j + m = n) (hk : k ≤ j)
    (x : ⋀[B]^j E) (y : ⋀[B]^m H) : wedgeLeftMul ι h x y ∈ wedgeStep ι k n :=
  Submodule.mem_iSup_of_mem j <| Submodule.mem_iSup_of_mem m <| Submodule.mem_iSup_of_mem h <|
    Submodule.mem_iSup_of_mem hk <| Submodule.mem_iSup_of_mem x ⟨y, rfl⟩

/-- The `k`-th step lies in a submodule `P` if and only if every wedge `(⋀ ι) x ∧ y` with
`x ∈ ⋀ʲ E` and `j ≥ k` lies in `P`. -/
theorem wedgeStep_le_iff (ι : E →ₗ[B] H) (k n : ℕ) (P : Submodule B (⋀[B]^n H)) :
    wedgeStep ι k n ≤ P ↔ ∀ (j m : ℕ) (h : j + m = n), k ≤ j → ∀ (x : ⋀[B]^j E)
      (y : ⋀[B]^m H), wedgeLeftMul ι h x y ∈ P := by
  simp only [wedgeStep, iSup_le_iff, LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
  rfl

/-- **The steps of the wedge filtration decrease.** -/
theorem wedgeStep_mono (ι : E →ₗ[B] H) {k k' : ℕ} (hk : k ≤ k') (n : ℕ) :
    wedgeStep ι k' n ≤ wedgeStep ι k n := by
  rw [wedgeStep_le_iff]
  intro j m h hj x y
  exact wedgeLeftMul_mem_wedgeStep ι h (hk.trans hj) x y

/-! ### Transport along an isomorphism -/

/-- `⋀ⁿ e` carries left multiplication by the image of `x` under `ι` to left multiplication by its
image under `e ∘ ι`. -/
theorem map_wedgeLeftMul {H' : Type*} [AddCommGroup H'] [Module B H'] (ι : E →ₗ[B] H)
    (e : H →ₗ[B] H') {j m n : ℕ} (h : j + m = n) (x : ⋀[B]^j E) (y : ⋀[B]^m H) :
    map n e (wedgeLeftMul ι h x y) = wedgeLeftMul (e ∘ₗ ι) h x (map m e y) := by
  refine Subtype.ext ?_
  rw [coe_map, coe_wedgeLeftMul, coe_wedgeLeftMul, coe_map, map_mul,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

/-- A linear map `e` with `e ∘ ι = ι'` carries the `k`-th step for `ι` into the one for `ι'`. -/
private theorem wedgeStep_le_comap_map {H' : Type*} [AddCommGroup H'] [Module B H']
    (ι : E →ₗ[B] H) (ι' : E →ₗ[B] H') (e : H →ₗ[B] H') (he : e ∘ₗ ι = ι') (k n : ℕ) :
    wedgeStep ι k n ≤ (wedgeStep ι' k n).comap (map n e) := by
  rw [wedgeStep_le_iff]
  intro j m h hj x y
  rw [Submodule.mem_comap, map_wedgeLeftMul, he]
  exact wedgeLeftMul_mem_wedgeStep ι' h hj x _

/-- **The wedge filtration is carried along a linear isomorphism compatible with the two maps.**
For `e : H ≃ H'` with `e ∘ ι = ι'`, the steps for `ι` are the preimages of the steps for `ι'`
under `⋀ⁿ e`. -/
theorem wedgeStep_comap_map_of_comp_eq {H' : Type*} [AddCommGroup H'] [Module B H']
    (ι : E →ₗ[B] H) (ι' : E →ₗ[B] H') (e : H ≃ₗ[B] H') (he : e.toLinearMap ∘ₗ ι = ι')
    (k n : ℕ) :
    wedgeStep ι k n = (wedgeStep ι' k n).comap (map n e.toLinearMap) := by
  refine le_antisymm (wedgeStep_le_comap_map ι ι' _ he k n) fun z hz => ?_
  have he' : e.symm.toLinearMap ∘ₗ ι' = ι := by
    rw [← he, ← LinearMap.comp_assoc]
    simp
  have hz' := wedgeStep_le_comap_map ι' ι _ he' k n hz
  rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← map_comp] at hz'
  simpa [map_id] using hz'

/-! ### The split case -/

variable (B E G)

/-- The index `(k, n - k)` of the block decomposition of `⋀ⁿ (E × G)`. -/
abbrev blockIndex (k m n : ℕ) (h : k + m = n) : {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
  ⟨(k, m), h⟩

/-- The family of blocks of the decomposition of `⋀ⁿ (E × G)`. -/
abbrev Block (n : ℕ) : {pq : ℕ × ℕ // pq.1 + pq.2 = n} → Type _ :=
  fun pq => TensorProduct B (⋀[B]^pq.1.1 E) (⋀[B]^pq.1.2 G)

variable {B E G}

/-- **The block map `⋀ᵏ E ⊗ ⋀ᵐ G ⟶ ⋀ⁿ (E × G)`**, `a ⊗ b ↦ (⋀ inl) a ∧ (⋀ inr) b`, for
`k + m = n`. -/
noncomputable def prodBlock {k m n : ℕ} (h : k + m = n) :
    TensorProduct B (⋀[B]^k E) (⋀[B]^m G) →ₗ[B] ⋀[B]^n (E × G) :=
  (prodEquivDirectSum n).symm.toLinearMap ∘ₗ
    DirectSum.lof B _ (Block B E G n) (blockIndex k m n h)

/-- In the exterior algebra, the block map sends `a ⊗ b` to the product `(⋀ inl) a * (⋀ inr) b`. -/
theorem coe_prodBlock_tmul {k m n : ℕ} (h : k + m = n) (a : ⋀[B]^k E) (b : ⋀[B]^m G) :
    (prodBlock h (a ⊗ₜ b) : ExteriorAlgebra B (E × G)) =
      ExteriorAlgebra.map (LinearMap.inl B E G) (a : ExteriorAlgebra B E) *
        ExteriorAlgebra.map (LinearMap.inr B E G) (b : ExteriorAlgebra B G) :=
  prodEquivDirectSum_symm_lof_tmul_coe n k m h a b

/-- The component of an element of `⋀ⁿ (E × G)` in the block of bidegree `pq`. -/
noncomputable def blockComponent {n : ℕ} (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    ⋀[B]^n (E × G) →ₗ[B] Block B E G n pq :=
  DirectSum.component B _ (Block B E G n) pq ∘ₗ (prodEquivDirectSum n).toLinearMap

/-- The component of bidegree `(k, m)` of the block map of bidegree `(k, m)` is the identity. -/
theorem blockComponent_prodBlock_self {k m n : ℕ} (h : k + m = n)
    (t : TensorProduct B (⋀[B]^k E) (⋀[B]^m G)) :
    blockComponent (blockIndex k m n h) (prodBlock h t) = t := by
  simp only [blockComponent, prodBlock, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact DirectSum.component.lof_self B _ _

/-- The block map of bidegree `(k, m)` has zero component in every other bidegree. -/
theorem blockComponent_prodBlock_of_ne {k m n : ℕ} (h : k + m = n)
    {pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}} (hpq : blockIndex k m n h ≠ pq)
    (t : TensorProduct B (⋀[B]^k E) (⋀[B]^m G)) :
    blockComponent pq (prodBlock h t) = 0 := by
  simp only [blockComponent, prodBlock, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [DirectSum.component.of, dif_neg hpq]

/-- The block map on a pure tensor is the wedge of the image of the first factor with the image
of the second. -/
theorem prodBlock_tmul {k m n : ℕ} (h : k + m = n) (a : ⋀[B]^k E) (b : ⋀[B]^m G) :
    prodBlock h (a ⊗ₜ b) =
      wedgeLeftMul (LinearMap.inl B E G) h a (map m (LinearMap.inr B E G) b) := by
  refine Subtype.ext ?_
  rw [coe_prodBlock_tmul, coe_wedgeLeftMul, coe_map]

/-- **The `k`-th block lies in the `k`-th step.** -/
theorem prodBlock_mem_wedgeStep {k m n : ℕ} (h : k + m = n)
    (t : TensorProduct B (⋀[B]^k E) (⋀[B]^m G)) :
    prodBlock h t ∈ wedgeStep (LinearMap.inl B E G) k n := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a b =>
    rw [prodBlock_tmul]
    exact wedgeLeftMul_mem_wedgeStep _ h le_rfl a _
  | add t t' ht ht' => rw [map_add]; exact Submodule.add_mem _ ht ht'

/-- Left multiplication by the image of `x ∈ ⋀ʲ E` carries the block of bidegree `(p, q)` to the
block of bidegree `(j + p, q)`. -/
theorem wedgeLeftMul_prodBlock {j m n p q : ℕ} (h : j + m = n) (h' : p + q = m)
    (x : ⋀[B]^j E) (a : ⋀[B]^p E) (b : ⋀[B]^q G) :
    wedgeLeftMul (LinearMap.inl B E G) h x (prodBlock h' (a ⊗ₜ b)) =
      prodBlock (k := j + p) (m := q) (by omega)
        (⟨(x : ExteriorAlgebra B E) * (a : ExteriorAlgebra B E), mul_mem_of_mem rfl x.2 a.2⟩ ⊗ₜ
          b) := by
  refine Subtype.ext ?_
  rw [coe_wedgeLeftMul, coe_prodBlock_tmul, coe_prodBlock_tmul, ← mul_assoc, ← map_mul]

/-- **The `k`-th step has no component of bidegree `(p, q)` with `p < k`.** -/
theorem blockComponent_eq_zero_of_mem_wedgeStep {k n : ℕ} {z : ⋀[B]^n (E × G)}
    (hz : z ∈ wedgeStep (LinearMap.inl B E G) k n) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (hpq : pq.1.1 < k) : blockComponent pq z = 0 := by
  suffices key : wedgeStep (LinearMap.inl B E G) k n ≤ LinearMap.ker (blockComponent pq) from
    key hz
  rw [wedgeStep_le_iff]
  intro j m h hj x y
  rw [LinearMap.mem_ker]
  have hT : (blockComponent pq ∘ₗ wedgeLeftMul (LinearMap.inl B E G) h x) ∘ₗ
      (prodEquivDirectSum (M := E) (N := G) m).symm.toLinearMap = 0 := by
    refine DirectSum.linearMap_ext B fun pq' => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨p, q⟩, h'⟩ := pq'
    show blockComponent pq (wedgeLeftMul (LinearMap.inl B E G) h x
      (prodBlock (k := p) (m := q) h' (a ⊗ₜ b))) = 0
    rw [wedgeLeftMul_prodBlock]
    refine blockComponent_prodBlock_of_ne _ (fun he => ?_) _
    have := congrArg (fun r : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => r.1.1) he
    simp only at this
    omega
  have := LinearMap.congr_fun hT (prodEquivDirectSum m y)
  simpa using this

/-- **An element of the `k`-th step whose component of bidegree `(k, m)` vanishes lies in the
`(k+1)`-st step.** -/
theorem mem_wedgeStep_succ_of_blockComponent_eq_zero {k m n : ℕ} (h : k + m = n)
    (z : ⋀[B]^n (E × G)) (hlt : ∀ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, pq.1.1 < k →
      blockComponent pq z = 0) (hk : blockComponent (blockIndex k m n h) z = 0) :
    z ∈ wedgeStep (LinearMap.inl B E G) (k + 1) n := by
  classical
  have hz : z = ∑ pq ∈ (prodEquivDirectSum (M := E) (N := G) n z).support,
      prodBlock pq.2 (blockComponent pq z) := by
    conv_lhs => rw [← (prodEquivDirectSum (M := E) (N := G) n).symm_apply_apply z,
      ← DirectSum.sum_support_of (prodEquivDirectSum (M := E) (N := G) n z), map_sum]
    rfl
  rw [hz]
  refine Submodule.sum_mem _ fun pq _ => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  rcases lt_trichotomy p k with hp | rfl | hp
  · rw [hlt _ hp, map_zero]
    exact Submodule.zero_mem _
  · have hq : q = m := by omega
    subst hq
    rw [show blockComponent ⟨(p, q), hpq⟩ z = 0 from hk, map_zero]
    exact Submodule.zero_mem _
  · exact wedgeStep_mono _ hp n (prodBlock_mem_wedgeStep hpq _)

variable (B E G) in
/-- **The map `⋀ᵏ E ⊗ ⋀ᵐ G ⟶ F^k ⋀ⁿ (E × G) / F^{k+1}`**, `a ⊗ b ↦ [(⋀ inl) a ∧ (⋀ inr) b]`. -/
noncomputable def prodGradedMap {k m n : ℕ} (h : k + m = n) :
    TensorProduct B (⋀[B]^k E) (⋀[B]^m G) →ₗ[B]
      (wedgeStep (LinearMap.inl B E G) k n ⧸
        (wedgeStep (LinearMap.inl B E G) (k + 1) n).comap
          (wedgeStep (LinearMap.inl B E G) k n).subtype) :=
  Submodule.mkQ _ ∘ₗ (prodBlock h).codRestrict _ (prodBlock_mem_wedgeStep h)

/-- **`⋀ᵏ E ⊗ ⋀ᵐ G ≅ F^k ⋀ⁿ (E × G) / F^{k+1}`**: the graded pieces of the wedge filtration of the
exterior powers of a direct sum. -/
@[sga "6 V 2.2.1" "special case"]
theorem prodGradedMap_bijective {k m n : ℕ} (h : k + m = n) :
    Function.Bijective (prodGradedMap B E G h) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have hmem' := (Submodule.Quotient.mk_eq_zero _).1 (show Submodule.Quotient.mk
        (⟨prodBlock h t, prodBlock_mem_wedgeStep h t⟩ :
          wedgeStep (LinearMap.inl B E G) k n) = 0 from ht)
    have hmem : prodBlock h t ∈ wedgeStep (LinearMap.inl B E G) (k + 1) n :=
      Submodule.mem_comap.1 hmem'
    have := blockComponent_eq_zero_of_mem_wedgeStep hmem (blockIndex k m n h) (by simp)
    rwa [blockComponent_prodBlock_self] at this
  · intro y
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨blockComponent (blockIndex k m n h) z, (Submodule.Quotient.eq _).2 ?_⟩
    rw [Submodule.mem_comap, map_sub]
    show prodBlock h (blockComponent (blockIndex k m n h) z) - z ∈ _
    rw [← neg_sub]
    refine neg_mem (mem_wedgeStep_succ_of_blockComponent_eq_zero h _ (fun pq hpq => ?_) ?_)
    · rw [map_sub, blockComponent_eq_zero_of_mem_wedgeStep hz pq hpq,
        blockComponent_prodBlock_of_ne h (fun he => by subst he; simp at hpq), sub_zero]
    · rw [map_sub, blockComponent_prodBlock_self, sub_self]

/-! ### The zeroth graded piece -/

/-- The zero map on generators kills every exterior power of positive degree. -/
theorem map_zero_coe_eq_zero {j : ℕ} (hj : 1 ≤ j) (x : ⋀[B]^j E) :
    ExteriorAlgebra.map (0 : E →ₗ[B] G) (x : ExteriorAlgebra B E) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hx : (x : ExteriorAlgebra B E) ∈ LinearMap.range (ExteriorAlgebra.ι B) *
      (LinearMap.range (ExteriorAlgebra.ι B (M := E)) ^ i) := by
    rw [← pow_succ']
    exact x.2
  generalize (x : ExteriorAlgebra B E) = y at hx
  induction hx using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b _ =>
    obtain ⟨e, rfl⟩ := ha
    rw [map_mul, ExteriorAlgebra.map_apply_ι, LinearMap.zero_apply, map_zero, zero_mul]
  | add a _ b _ ha hb => rw [map_add, ha, hb, add_zero]

variable (B E G) in
/-- The second projection `⋀ⁿ (E × G) ⟶ ⋀ⁿ G`. -/
noncomputable abbrev sndPower (n : ℕ) : ⋀[B]^n (E × G) →ₗ[B] ⋀[B]^n G :=
  map n (LinearMap.snd B E G)

/-- The first step lies in the kernel of the second projection. -/
theorem wedgeStep_one_le_ker_sndPower (n : ℕ) :
    wedgeStep (LinearMap.inl B E G) 1 n ≤ LinearMap.ker (sndPower B E G n) := by
  rw [wedgeStep_le_iff]
  intro j m h hj x y
  rw [LinearMap.mem_ker]
  refine Subtype.ext ?_
  rw [coe_map, coe_wedgeLeftMul, map_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    LinearMap.snd_comp_inl, map_zero_coe_eq_zero hj, zero_mul]
  rfl

/-- On the block of bidegree `(0, n)` the second projection is `c ⊗ b ↦ c • b`. -/
theorem sndPower_prodBlock_zero {n : ℕ} (a : ⋀[B]^0 E) (b : ⋀[B]^n G) :
    sndPower B E G n (prodBlock (zero_add n) (a ⊗ₜ b)) = zeroEquiv B E a • b := by
  obtain ⟨c, rfl⟩ := (zeroEquiv B E).symm.surjective a
  refine Subtype.ext ?_
  rw [coe_map, coe_prodBlock_tmul, map_mul, LinearEquiv.apply_symm_apply,
    ← AlgHom.comp_apply, ← AlgHom.comp_apply (ExteriorAlgebra.map (LinearMap.snd B E G)),
    ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, LinearMap.snd_comp_inl,
    LinearMap.snd_comp_inr, ExteriorAlgebra.map_id, AlgHom.id_apply]
  have hc : ((zeroEquiv B E).symm c : ExteriorAlgebra B E) =
      algebraMap B (ExteriorAlgebra B E) c := by
    rw [zeroEquiv_symm_apply]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hc, AlgHom.commutes, Submodule.coe_smul, Algebra.smul_def]

/-- **The kernel of the second projection `⋀ⁿ (E × G) ⟶ ⋀ⁿ G` is the first step of the wedge
filtration.** -/
theorem ker_sndPower (n : ℕ) :
    LinearMap.ker (sndPower B E G n) = wedgeStep (LinearMap.inl B E G) 1 n := by
  refine le_antisymm (fun z hz => ?_) (wedgeStep_one_le_ker_sndPower n)
  classical
  refine mem_wedgeStep_succ_of_blockComponent_eq_zero (zero_add n) z
    (fun pq hpq => absurd hpq (Nat.not_lt_zero _)) ?_
  have hz' : z = prodBlock (zero_add n) (blockComponent (blockIndex 0 n n (zero_add n)) z) +
      (z - prodBlock (zero_add n) (blockComponent (blockIndex 0 n n (zero_add n)) z)) := by
    abel
  have hrest : z - prodBlock (zero_add n) (blockComponent (blockIndex 0 n n (zero_add n)) z) ∈
      wedgeStep (LinearMap.inl B E G) 1 n := by
    refine mem_wedgeStep_succ_of_blockComponent_eq_zero (zero_add n) _
      (fun pq hpq => absurd hpq (Nat.not_lt_zero _)) ?_
    rw [map_sub, blockComponent_prodBlock_self, sub_self]
  have h0 : sndPower B E G n (prodBlock (zero_add n)
      (blockComponent (blockIndex 0 n n (zero_add n)) z)) = 0 := by
    have := LinearMap.mem_ker.1 hz
    rw [hz', map_add, wedgeStep_one_le_ker_sndPower n hrest, add_zero] at this
    exact this
  have hinj : Function.Injective (sndPower B E G n ∘ₗ prodBlock (zero_add n)) := by
    have heq : sndPower B E G n ∘ₗ prodBlock (zero_add n) =
        (TensorProduct.lid B _).toLinearMap ∘ₗ
          TensorProduct.map (zeroEquiv B E).toLinearMap LinearMap.id := by
      refine TensorProduct.ext' fun a b => ?_
      rw [LinearMap.comp_apply, sndPower_prodBlock_zero]
      simp
    rw [heq]
    exact (TensorProduct.lid B _).injective.comp
      (TensorProduct.congr (zeroEquiv B E) (LinearEquiv.refl B _)).injective
  exact hinj (by rw [LinearMap.comp_apply, h0, map_zero])

end exteriorPower

end
