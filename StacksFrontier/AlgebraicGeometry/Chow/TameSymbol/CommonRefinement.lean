module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# A common refinement of two finite modifications of a local ring

Let `(A, 𝔪)` be a local ring and let `A ⊆ B` and `A ⊆ B'` be two finite ring extensions whose
quotients `B/A` and `B'/A` are annihilated by a power of `𝔪`. Two such extensions are compared
through the third extension `C = (B ⊗_A B') / N`, where `N` is the `𝔪`-power torsion. This file
constructs it as a `Stacks.Chow.CommonRefinement`: a ring finite over `A`, receiving `A`, `B` and
`B'` injectively and compatibly, whose quotient by `A` is again annihilated by a power of `𝔪`.

The `𝔪`-power torsion is taken in the form of the `s`-power torsion for a single element
`s ∈ 𝔪` which is a nonzerodivisor of `A` and remains one in `B` and in `B'` — that is, the
kernel of `B ⊗_A B' → (B ⊗_A B')[1/s]`. The two notions agree as soon as a power of `𝔪` lies in
`(s)`, as it does in a one-dimensional Noetherian local ring, and the torsion at one element makes
the quotient `s`-torsion-free.

The three injectivity statements and the annihilation of `C/A` all rest on one observation. If
`𝔪^n` annihilates `B'/A` and `s ∈ 𝔪^n`, then multiplication by `s` carries `B'` into the image
of `A`, so — `A → B'` being injective — there is an `A`-linear retraction `φ : B' → A` with
`algebraMap A B' (φ y) = s • y`. Tensoring `φ` with `B` gives an `A`-linear map
`B ⊗_A B' → B` sending `b ⊗ 1` to `s • b`, which detects the elements of `B` that die in the
tensor product; and symmetrically on the other side.

## Main definitions

* `Stacks.Chow.CommonRefinement` — the datum of a common finite refinement.

## Main results

* `Stacks.Chow.nonempty_commonRefinement` — the quotient of `B ⊗_A B'` by its `s`-power torsion
  is a common refinement.
* `Stacks.Chow.exists_retraction_of_smul_mem_range` — the retraction `φ`.
* `Stacks.Chow.CommonRefinement.moduleFinite_left`,
  `Stacks.Chow.CommonRefinement.moduleFinite_right` — a common refinement is finite over each of
  the two extensions it refines.

## References

* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w

namespace Stacks.Chow

/-! ### The retraction supplied by an annihilated quotient -/

section Retraction

variable {A : Type u} [CommRing A] {B' : Type w} [CommRing B'] [Algebra A B']

/-- **An `A`-linear retraction scaling by `s`.** If multiplication by `s` carries `B'` into the
image of `A` and `A → B'` is injective, the resulting function `B' → A` is `A`-linear. -/
theorem exists_retraction_of_smul_mem_range (s : A)
    (hinj : Function.Injective (algebraMap A B'))
    (hs : ∀ y : B', ∃ α : A, s • y = algebraMap A B' α) :
    ∃ φ : B' →ₗ[A] A, ∀ y : B', algebraMap A B' (φ y) = s • y := by
  classical
  choose g hg using hs
  have hadd : ∀ x y : B', g (x + y) = g x + g y := fun x y =>
    hinj (by rw [map_add, ← hg, ← hg, ← hg, smul_add])
  have hsmul : ∀ (c : A) (x : B'), g (c • x) = c • g x := by
    intro c x
    apply hinj
    have h₁ : algebraMap A B' (g (c • x)) = s • (c • x) := (hg _).symm
    have h₂ : algebraMap A B' (c • g x) = c • (s • x) := by
      rw [smul_eq_mul, map_mul, ← hg, Algebra.smul_def c (s • x)]
    rw [h₁, h₂, smul_comm]
  exact ⟨{ toFun := g, map_add' := hadd, map_smul' := hsmul }, fun y => (hg y).symm⟩

/-- An element of a quotient annihilated by `𝔪 ^ n` is carried into the image of the base by any
member of `𝔪 ^ n`. -/
theorem smul_mem_range_of_mem_maximalIdeal_pow [IsLocalRing A] {n : ℕ}
    (hquot : maximalIdeal A ^ n • (⊤ : Submodule A B') ≤
      LinearMap.range (Algebra.linearMap A B'))
    {s : A} (hsm : s ∈ maximalIdeal A ^ n) (y : B') :
    ∃ α : A, s • y = algebraMap A B' α :=
  let ⟨α, hα⟩ := hquot (Submodule.smul_mem_smul hsm Submodule.mem_top)
  ⟨α, hα.symm⟩

end Retraction

/-! ### The datum of a common refinement -/

/-- **A common finite refinement of two finite modifications `A ⊆ B` and `A ⊆ B'`.** The carrier
is a ring finite over `A`, receiving all three rings injectively and compatibly, with `C/A`
annihilated by a power of the maximal ideal and with the chosen element `s` of the base remaining
a nonzerodivisor in it. -/
structure CommonRefinement (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type v) [CommRing B] [Algebra A B] (B' : Type w) [CommRing B'] [Algebra A B']
    (s : A) where
  /-- The refining ring. -/
  carrier : Type (max v w)
  [commRing : CommRing carrier]
  [algebraBase : Algebra A carrier]
  [algebraLeft : Algebra B carrier]
  [algebraRight : Algebra B' carrier]
  [towerLeft : IsScalarTower A B carrier]
  [towerRight : IsScalarTower A B' carrier]
  [finite : Module.Finite A carrier]
  /-- The base is a subring of the refinement. -/
  injBase : Function.Injective (algebraMap A carrier)
  /-- The first extension is a subring of the refinement. -/
  injLeft : Function.Injective (algebraMap B carrier)
  /-- The second extension is a subring of the refinement. -/
  injRight : Function.Injective (algebraMap B' carrier)
  /-- A power of the maximal ideal annihilates the quotient of the refinement by the base. -/
  quot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A carrier) ≤
    LinearMap.range (Algebra.linearMap A carrier)
  /-- The chosen element of the base is a nonzerodivisor of the refinement. -/
  param_mem_nonZeroDivisors : algebraMap A carrier s ∈ nonZeroDivisors carrier

attribute [instance] CommonRefinement.commRing CommonRefinement.algebraBase
  CommonRefinement.algebraLeft CommonRefinement.algebraRight CommonRefinement.towerLeft
  CommonRefinement.towerRight CommonRefinement.finite

namespace CommonRefinement

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {B : Type v} [CommRing B] [Algebra A B] {B' : Type w} [CommRing B'] [Algebra A B']
  {s : A} (R : CommonRefinement A B B' s)

/-- A common refinement is finite over the first extension it refines. -/
theorem moduleFinite_left : Module.Finite B R.carrier :=
  Module.Finite.of_restrictScalars_finite A B _

/-- A common refinement is finite over the second extension it refines. -/
theorem moduleFinite_right : Module.Finite B' R.carrier :=
  Module.Finite.of_restrictScalars_finite A B' _

end CommonRefinement

/-! ### The tensor product and its retractions -/

section TensorQuotient

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {B' : Type w} [CommRing B'] [Algebra A B']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem algebraMap_tensor_left (b : B) :
    algebraMap B (TensorProduct A B B') b = b ⊗ₜ[A] (1 : B') := by
  simp [Algebra.TensorProduct.algebraMap_apply]

private theorem algebraMap_tensor_right (b' : B') :
    algebraMap B' (TensorProduct A B B') b' = (1 : B) ⊗ₜ[A] b' := rfl

/-- **The retraction of `B ⊗_A B'` onto its left factor scaling by `s`.** -/
private theorem exists_tensorRetract_left (s : A)
    (hinj : Function.Injective (algebraMap A B'))
    (hs : ∀ y : B', ∃ α : A, s • y = algebraMap A B' α) :
    ∃ ψ : TensorProduct A B B' →ₗ[A] B,
      ∀ b : B, ψ (algebraMap B (TensorProduct A B B') b) = s • b := by
  obtain ⟨φ, hφ⟩ := exists_retraction_of_smul_mem_range s hinj hs
  have hφ1 : φ 1 = s := hinj (by rw [hφ, Algebra.smul_def, mul_one])
  refine ⟨(TensorProduct.rid A B).toLinearMap ∘ₗ LinearMap.lTensor B φ, fun b => ?_⟩
  rw [algebraMap_tensor_left]
  simp [hφ1]

/-- **The retraction of `B ⊗_A B'` onto its right factor scaling by `s`.** -/
private theorem exists_tensorRetract_right (s : A)
    (hinj : Function.Injective (algebraMap A B))
    (hs : ∀ y : B, ∃ α : A, s • y = algebraMap A B α) :
    ∃ ψ : TensorProduct A B B' →ₗ[A] B',
      ∀ b' : B', ψ (algebraMap B' (TensorProduct A B B') b') = s • b' := by
  obtain ⟨φ, hφ⟩ := exists_retraction_of_smul_mem_range s hinj hs
  have hφ1 : φ 1 = s := hinj (by rw [hφ, Algebra.smul_def, mul_one])
  refine ⟨(TensorProduct.lid A B').toLinearMap ∘ₗ LinearMap.rTensor B' φ, fun b' => ?_⟩
  rw [algebraMap_tensor_right]
  simp [hφ1]

/-- **A power of the maximal ideal annihilates `(B ⊗_A B')/A`.** -/
private theorem maximalIdeal_pow_smul_top_le_range_tensor [IsLocalRing A] {n n' : ℕ}
    (hB : maximalIdeal A ^ n • (⊤ : Submodule A B) ≤ LinearMap.range (Algebra.linearMap A B))
    (hB' : maximalIdeal A ^ n' • (⊤ : Submodule A B') ≤
      LinearMap.range (Algebra.linearMap A B')) :
    maximalIdeal A ^ (n + n') • (⊤ : Submodule A (TensorProduct A B B')) ≤
      LinearMap.range (Algebra.linearMap A (TensorProduct A B B')) := by
  rw [Submodule.smul_le]
  rintro r hr t -
  rw [pow_add] at hr
  refine Submodule.mul_induction_on hr ?_ ?_
  · intro a ha b hb
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      obtain ⟨α, hα⟩ := smul_mem_range_of_mem_maximalIdeal_pow hB ha x
      obtain ⟨β, hβ⟩ := smul_mem_range_of_mem_maximalIdeal_pow hB' hb y
      refine ⟨β * α, ?_⟩
      have key : (a * b) • (x ⊗ₜ[A] y) = (a • x) ⊗ₜ[A] (b • y) := by
        rw [mul_smul, TensorProduct.smul_tmul' b x y, TensorProduct.smul_tmul b x y,
          TensorProduct.smul_tmul' a x (b • y)]
      rw [key, hα, hβ, Algebra.algebraMap_eq_smul_one β, ← TensorProduct.smul_tmul,
        Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply, map_mul,
        ← Algebra.smul_def]
    | add x y hx hy => rw [smul_add]; exact add_mem hx hy
  · intro x y hx hy
    rw [add_smul]; exact add_mem hx hy

end TensorQuotient

/-! ### The construction -/

section Construction

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  {B' : Type w} [CommRing B'] [Algebra A B']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The `s`-power torsion of a commutative ring, as the kernel of the localization at `s`. -/
private def torsionAt {T : Type*} [CommRing T] (σ : T) : Ideal T :=
  RingHom.ker (algebraMap T (Localization.Away σ))

private theorem mem_torsionAt_iff {T : Type*} [CommRing T] (σ t : T) :
    t ∈ torsionAt σ ↔ ∃ k : ℕ, σ ^ k * t = 0 := by
  rw [torsionAt, RingHom.mem_ker, IsLocalization.map_eq_zero_iff (Submonoid.powers σ)]
  exact ⟨fun ⟨⟨y, k, hk⟩, hm⟩ => ⟨k, by subst hk; exact hm⟩, fun ⟨k, hk⟩ => ⟨⟨σ ^ k, k, rfl⟩, hk⟩⟩

private theorem mk_eq_zero_iff {T : Type*} [CommRing T] (σ t : T) :
    (Ideal.Quotient.mk (torsionAt σ)) t = 0 ↔ ∃ k : ℕ, σ ^ k * t = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.trans (mem_torsionAt_iff σ t)

private theorem algebraMap_quotient_torsionAt {T : Type*} [CommRing T] (σ t : T) :
    algebraMap T (T ⧸ torsionAt σ) t = (Ideal.Quotient.mk (torsionAt σ)) t := rfl

/-- If an `A`-linear retraction `ψ` of `T` onto `X` scales by `s ^ m` and `s` is a nonzerodivisor
of `X`, then `X` embeds in the quotient of `T` by its `s`-power torsion. -/
private theorem injective_algebraMap_quotient_torsionAt {A T X : Type*} [CommRing A] [CommRing T]
    [Algebra A T] [CommRing X] [Algebra A X] [Algebra X T] {s : A} {m : ℕ}
    (hs : algebraMap A X s ∈ nonZeroDivisors X) (ψ : T →ₗ[A] X)
    (hψ : ∀ b : X, ψ (algebraMap X T b) = (s ^ m) • b) :
    Function.Injective (algebraMap X (T ⧸ torsionAt (algebraMap A T s))) := by
  refine (injective_iff_map_eq_zero _).mpr fun b hb => ?_
  rw [IsScalarTower.algebraMap_apply X T (T ⧸ _), algebraMap_quotient_torsionAt,
    mk_eq_zero_iff] at hb
  obtain ⟨k, hk⟩ := hb
  rw [← map_pow, ← Algebra.smul_def] at hk
  have h := congrArg ψ hk
  rw [map_smul, hψ, map_zero, smul_smul, ← pow_add, Algebra.smul_def, map_pow] at h
  exact (mem_nonZeroDivisors_iff.mp (pow_mem hs (k + m))).1 b h

/-- **The common refinement `(B ⊗_A B')/(s`-power torsion`)` exists.** For two
finite modifications `A ⊆ B` and `A ⊆ B'` of a local ring and an element `s` of the maximal ideal
that is a nonzerodivisor in both, the quotient of `B ⊗_A B'` by its `s`-power torsion is a common
refinement: it is finite over `A`, receives all three rings injectively and compatibly, its
quotient by `A` is annihilated by a power of the maximal ideal, and `s` remains a nonzerodivisor
in it. -/
theorem nonempty_commonRefinement
    [Module.Finite A B] [Module.Finite A B'] {s : A}
    (hinjB : Function.Injective (algebraMap A B))
    (hinjB' : Function.Injective (algebraMap A B'))
    (hsB : algebraMap A B s ∈ nonZeroDivisors B)
    (hsB' : algebraMap A B' s ∈ nonZeroDivisors B')
    (hsm : s ∈ maximalIdeal A)
    (hquotB : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hquotB' : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B') ≤
      LinearMap.range (Algebra.linearMap A B')) :
    Nonempty (CommonRefinement A B B' s) := by
  classical
  obtain ⟨n, hn⟩ := hquotB
  obtain ⟨n', hn'⟩ := hquotB'
  obtain ⟨ψl, hψl⟩ := exists_tensorRetract_left (B := B) (s ^ n') hinjB'
    (smul_mem_range_of_mem_maximalIdeal_pow hn' ((maximalIdeal A).pow_mem_pow hsm n'))
  obtain ⟨ψr, hψr⟩ := exists_tensorRetract_right (B' := B') (s ^ n) hinjB
    (smul_mem_range_of_mem_maximalIdeal_pow hn ((maximalIdeal A).pow_mem_pow hsm n))
  let : Module.Finite B (TensorProduct A B B') := Module.Finite.base_change A B B'
  let : Module.Finite A (TensorProduct A B B') := Module.Finite.trans B _
  set T := TensorProduct A B B'
  set σ : T := algebraMap A T s with hσ
  have hinjL := injective_algebraMap_quotient_torsionAt (X := B) hsB ψl hψl
  have hinjR := injective_algebraMap_quotient_torsionAt (X := B') hsB' ψr hψr
  have hmkSmul : ∀ (c : A) (y : T), c • (Ideal.Quotient.mk (torsionAt σ)) y =
      (Ideal.Quotient.mk (torsionAt σ)) (c • y) :=
    fun c y => (map_smul (Ideal.Quotient.mkₐ A (torsionAt σ)).toLinearMap c y).symm
  refine ⟨{ carrier := T ⧸ torsionAt σ
            injBase := ?_
            injLeft := hinjL
            injRight := hinjR
            quot := ⟨n + n', ?_⟩
            param_mem_nonZeroDivisors := ?_ }⟩
  · rw [IsScalarTower.algebraMap_eq A B (T ⧸ torsionAt σ), RingHom.coe_comp]
    exact hinjL.comp hinjB
  · rw [Submodule.smul_le]
    rintro r hr z -
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨α, hα⟩ := maximalIdeal_pow_smul_top_le_range_tensor hn hn'
      (Submodule.smul_mem_smul hr (Submodule.mem_top (R := A) (M := T)))
    refine ⟨α, ?_⟩
    rw [Algebra.linearMap_apply, IsScalarTower.algebraMap_apply A T (T ⧸ torsionAt σ),
      algebraMap_quotient_torsionAt, hmkSmul]
    exact congrArg _ hα
  · rw [mem_nonZeroDivisors_iff]
    have key : ∀ z : T ⧸ torsionAt σ, algebraMap A (T ⧸ torsionAt σ) s * z = 0 → z = 0 := by
      intro z hz
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [IsScalarTower.algebraMap_apply A T (T ⧸ torsionAt σ), algebraMap_quotient_torsionAt,
        ← map_mul, mk_eq_zero_iff] at hz
      obtain ⟨k, hk⟩ := hz
      rw [mk_eq_zero_iff]
      exact ⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩
    exact ⟨key, fun z hz => key z (by rw [mul_comm]; exact hz)⟩

end Construction

end Stacks.Chow

end
