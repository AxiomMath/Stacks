module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChange

/-!
# `Away 𝒜 f` as the direct limit of the homogeneous pieces `𝒜 (n • d)`

The degree-zero homogeneous localization `HomogeneousLocalization.Away 𝒜 f` of a graded ring at a
homogeneous element `f` of degree `d` is presented as the direct limit of the pieces `𝒜 (n • d)`
along multiplication by `f`. The pieces are taken as modules over the degree-zero part `𝒜 0`, and
every element of `M ⊗[𝒜 0] Away 𝒜 f` comes from `M ⊗[𝒜 0] 𝒜 (n • d)` for a single `n`. The file
also forms the tensor product `(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} Away 𝒜 a` of the chart-level base change of
`Proj`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.piece₀`: the homogeneous piece `ℬ i` as a
  submodule over the degree-zero part `ℬ 0`.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.mkLin`: the map `ℬ (n • d) ⟶ Away ℬ f` sending a
  homogeneous element to the fraction with denominator `f ^ n`, as a `ℬ 0`-linear map.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.mulPowTo`: multiplication by `f ^ k`, the
  transition map of the direct system.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.gradedZeroMap`: the ring homomorphism
  `𝒜 0 ⟶ (S ⊗[R] 𝒜) 0`.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.chartTensor`: the tensor product
  `(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} Away 𝒜 a`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.awayMk_eq_zero_iff`: a fraction with denominator
  `f ^ n` vanishes exactly when a power of `f` annihilates its numerator.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.awayMk_eq_iff`: two fractions with denominators
  `f ^ n` and `f ^ m` agree exactly when the cross products agree after multiplication by some
  power of `f`.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.mkLin_mulPowTo`: raising the denominator by `f ^ k`
  while multiplying the numerator by `f ^ k` does not change the fraction, so the fraction maps
  are compatible with the transition maps.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.mkLin_jointly_surjective`: every element of
  `Away ℬ f` is in the range of some `mkLin`.
* `Stacks.AlgebraicGeometry.ProjAwayBaseChange.exists_lTensor_mkLin_eq`: every element of
  `M ⊗[ℬ 0] Away ℬ f` is the image of an element of `M ⊗[ℬ 0] ℬ (n • d)` for a single `n`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open HomogeneousLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjAwayBaseChange

/-! ### Fractions with a prescribed denominator -/

section Fractions

variable {ι B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [AddCommMonoid ι]
  [DecidableEq ι] (ℬ : ι → τ) [GradedRing ℬ] {f : B} {d : ι} (hf : f ∈ ℬ d)

/-- A fraction with denominator a power of `f` vanishes if and only if some power of `f`
annihilates its numerator. -/
public theorem awayMk_eq_zero_iff (n : ℕ) (x : B) (hx : x ∈ ℬ (n • d)) :
    Away.mk ℬ hf n x hx = 0 ↔ ∃ k : ℕ, f ^ k * x = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff]
  exact ⟨fun ⟨⟨_, k, rfl⟩, hc⟩ ↦ ⟨k, hc⟩, fun ⟨k, hk⟩ ↦ ⟨⟨f ^ k, k, rfl⟩, hk⟩⟩

/-- Two fractions with denominators powers of `f` agree if and only if the cross products agree
after multiplication by a power of `f`. -/
public theorem awayMk_eq_iff (n m : ℕ) (x y : B) (hx : x ∈ ℬ (n • d)) (hy : y ∈ ℬ (m • d)) :
    Away.mk ℬ hf n x hx = Away.mk ℬ hf m y hy ↔
      ∃ k : ℕ, f ^ k * (f ^ m * x) = f ^ k * (f ^ n * y) := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨fun ⟨⟨_, k, rfl⟩, hc⟩ ↦ ⟨k, hc⟩, fun ⟨k, hk⟩ ↦ ⟨⟨f ^ k, k, rfl⟩, hk⟩⟩

/-- Multiplying the numerator and the denominator of a fraction by `f ^ k` leaves it
unchanged. -/
public theorem awayMk_mulPow (n k : ℕ) (x : B) (hx : x ∈ ℬ (n • d))
    (hx' : f ^ k * x ∈ ℬ ((n + k) • d)) :
    Away.mk ℬ hf (n + k) (f ^ k * x) hx' = Away.mk ℬ hf n x hx := by
  rw [awayMk_eq_iff]
  exact ⟨0, by ring⟩

/-- A degree-zero scalar `c` multiplies a fraction through its numerator:
`(c * x) / f ^ n = c • (x / f ^ n)`. -/
public theorem awayMk_smul_zero (n : ℕ) (c : ℬ 0) (x z : B) (hx : x ∈ ℬ (n • d))
    (hz : z ∈ ℬ (n • d)) (hzx : z = (c : B) * x) :
    Away.mk ℬ hf n z hz = c • Away.mk ℬ hf n x hx := by
  subst hzx
  rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, Away.val_mk,
    Away.val_mk,
    show (fromZeroRingHom ℬ (Submonoid.powers f) c).val = Localization.mk (c : B) 1 from rfl,
    Localization.mk_mul, one_mul]

/-- Fractions with a common denominator add numeratorwise. -/
public theorem awayMk_add (n : ℕ) (x y : B) (hx : x ∈ ℬ (n • d)) (hy : y ∈ ℬ (n • d)) :
    Away.mk ℬ hf n (x + y) (add_mem hx hy) =
      Away.mk ℬ hf n x hx + Away.mk ℬ hf n y hy := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
    Localization.add_mk_self]

/-! ### The homogeneous pieces as modules over the degree-zero part -/

/-- The homogeneous piece `ℬ i`, as a submodule of `B` over the degree-zero part `ℬ 0`. -/
public def piece₀ (i : ι) : Submodule (ℬ 0) B where
  carrier := {x | x ∈ ℬ i}
  add_mem' := add_mem
  zero_mem' := zero_mem (ℬ i)
  smul_mem' c x hx := by
    have h : (c : B) * x ∈ ℬ (0 + i) := SetLike.mul_mem_graded c.2 hx
    rw [zero_add] at h
    rwa [Algebra.smul_def, SetLike.GradeZero.algebraMap_apply]

/-- Membership in `piece₀ ℬ i` is membership in `ℬ i`. -/
@[simp]
public theorem mem_piece₀ (i : ι) (x : B) : x ∈ piece₀ ℬ i ↔ x ∈ ℬ i := Iff.rfl

/-! ### The direct system -/

/-- The fraction map `ℬ (n • d) ⟶ Away ℬ f` with denominator `f ^ n`, as a `ℬ 0`-linear
map. -/
public def mkLin (n : ℕ) : piece₀ ℬ (n • d) →ₗ[ℬ 0] Away ℬ f where
  toFun x := Away.mk ℬ hf n (x : B) ((mem_piece₀ ℬ _ _).mp x.2)
  map_add' _ _ := awayMk_add ℬ hf n _ _ _ _
  map_smul' c x :=
    awayMk_smul_zero ℬ hf n c (x : B) ((c • x : piece₀ ℬ (n • d)) : B)
      ((mem_piece₀ ℬ _ _).mp x.2) ((mem_piece₀ ℬ _ _).mp (c • x).2) rfl

/-- `mkLin ℬ hf n x` is the fraction `x / f ^ n`. -/
@[simp]
public theorem mkLin_apply (n : ℕ) (x : piece₀ ℬ (n • d)) :
    mkLin ℬ hf n x = Away.mk ℬ hf n (x : B) ((mem_piece₀ ℬ _ _).mp x.2) := rfl

/-- The transition map of the direct system: multiplication by `f ^ k`, from the piece of degree
`n • d` to the piece of degree `m • d`, where `n + k = m`. -/
public def mulPowTo (n m k : ℕ) (hk : n + k = m) :
    piece₀ ℬ (n • d) →ₗ[ℬ 0] piece₀ ℬ (m • d) where
  toFun x := ⟨f ^ k * (x : B), by
    have h : f ^ k * (x : B) ∈ ℬ (k • d + n • d) :=
      SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) ((mem_piece₀ ℬ _ _).mp x.2)
    rwa [show k • d + n • d = m • d by rw [← hk, add_smul, add_comm]] at h⟩
  map_add' x y := Subtype.ext (by simpa using mul_add (f ^ k) (x : B) (y : B))
  map_smul' c x := Subtype.ext (by
    simp only [RingHom.id_apply, Submodule.coe_smul, Algebra.smul_def,
      SetLike.GradeZero.algebraMap_apply]
    ring)

/-- The underlying element of `mulPowTo ℬ hf n m k hk x` is `f ^ k * x`. -/
@[simp]
public theorem mulPowTo_coe (n m k : ℕ) (hk : n + k = m) (x : piece₀ ℬ (n • d)) :
    ((mulPowTo ℬ hf n m k hk x : piece₀ ℬ (m • d)) : B) = f ^ k * (x : B) := rfl

/-- The fraction maps are compatible with the transition maps: raising the denominator from
`f ^ n` to `f ^ m` and the numerator by `f ^ k` gives the same element of `Away ℬ f`. -/
public theorem mkLin_mulPowTo (n m k : ℕ) (hk : n + k = m) (x : piece₀ ℬ (n • d)) :
    mkLin ℬ hf m (mulPowTo ℬ hf n m k hk x) = mkLin ℬ hf n x := by
  subst hk
  exact awayMk_mulPow ℬ hf n k (x : B) _ _

/-- Every element of `Away ℬ f` is a fraction with denominator a power of `f`: the fraction maps
of the direct system are jointly surjective. -/
public theorem mkLin_jointly_surjective (z : Away ℬ f) :
    ∃ (n : ℕ) (x : piece₀ ℬ (n • d)), mkLin ℬ hf n x = z := by
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ hf z
  exact ⟨n, ⟨y, hy⟩, rfl⟩

/-! ### The common denominator -/

section Tensor

open scoped TensorProduct

variable {M : Type*} [AddCommGroup M] [Module (ℬ 0) M]

/-- Tensoring with `M`, the transition map `mulPowTo` is compatible with the fraction maps. -/
private theorem lTensor_mkLin_lTensor_mulPowTo (n m k : ℕ) (hk : n + k = m)
    (v : M ⊗[ℬ 0] piece₀ ℬ (n • d)) :
    LinearMap.lTensor M (mkLin ℬ hf m) (LinearMap.lTensor M (mulPowTo ℬ hf n m k hk) v) =
      LinearMap.lTensor M (mkLin ℬ hf n) v := by
  rw [← LinearMap.lTensor_comp_apply]
  exact congrArg (fun g ↦ LinearMap.lTensor M g v)
    (LinearMap.ext fun x ↦ mkLin_mulPowTo ℬ hf n m k hk x)

/-- Every element of `M ⊗[ℬ 0] Away ℬ f` is the image of an element of `M ⊗[ℬ 0] ℬ (n • d)` for
a single `n`. -/
public theorem exists_lTensor_mkLin_eq (u : M ⊗[ℬ 0] Away ℬ f) :
    ∃ (n : ℕ) (v : M ⊗[ℬ 0] piece₀ ℬ (n • d)),
      LinearMap.lTensor M (mkLin ℬ hf n) v = u := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul m z =>
      obtain ⟨n, x, hx⟩ := mkLin_jointly_surjective ℬ hf z
      exact ⟨n, m ⊗ₜ x, by rw [LinearMap.lTensor_tmul, hx]⟩
  | add u₁ u₂ h₁ h₂ =>
      obtain ⟨n₁, v₁, hv₁⟩ := h₁
      obtain ⟨n₂, v₂, hv₂⟩ := h₂
      refine ⟨max n₁ n₂,
        LinearMap.lTensor M (mulPowTo ℬ hf n₁ _ (max n₁ n₂ - n₁)
            (Nat.add_sub_cancel' (le_max_left n₁ n₂))) v₁ +
          LinearMap.lTensor M (mulPowTo ℬ hf n₂ _ (max n₁ n₂ - n₂)
            (Nat.add_sub_cancel' (le_max_right n₁ n₂))) v₂, ?_⟩
      rw [map_add, lTensor_mkLin_lTensor_mulPowTo, lTensor_mkLin_lTensor_mulPowTo, hv₁, hv₂]

end Tensor

end Fractions

/-! ### The degree-zero algebra structures of the chart-level base change -/

section BaseChange

open Stacks.ProjBaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]
  {d : ℕ} {a : A}

/-- The `𝒜 0`-algebra structure on `Away 𝒜 a`. -/
public abbrev awayAlgebra : Algebra (𝒜 0) (Away 𝒜 a) := inferInstance

/-- The `(S ⊗[R] 𝒜) 0`-algebra structure on `Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)`. -/
public abbrev awayAlgebraBaseChange : Algebra (grading 𝒜 S 0)
    (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) := inferInstance

/-- The ring homomorphism `𝒜 0 ⟶ (S ⊗[R] 𝒜) 0` induced on degree-zero parts by
`a ↦ 1 ⊗ₜ a`. -/
public def gradedZeroMap : (𝒜 0) →+* (grading 𝒜 S 0) :=
  (includeRight 𝒜 S).gradedZeroRingHom

/-- The tensor product `(S ⊗[R] 𝒜) 0 ⊗_{𝒜 0} Away 𝒜 a`, with `(S ⊗[R] 𝒜) 0` an `𝒜 0`-algebra
through `gradedZeroMap`. -/
public abbrev chartTensor (a : A) : Type u :=
  letI : Algebra (𝒜 0) (grading 𝒜 S 0) := (gradedZeroMap 𝒜 S).toAlgebra
  TensorProduct (𝒜 0) (grading 𝒜 S 0) (Away 𝒜 a)

end BaseChange

end Stacks.AlgebraicGeometry.ProjAwayBaseChange

end
