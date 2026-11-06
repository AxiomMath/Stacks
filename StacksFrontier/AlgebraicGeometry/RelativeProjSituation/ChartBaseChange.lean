module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MapBaseChange
public import StacksFrontier.RingTheory.GradedAlgebra.FinitelyGenerated
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDirectLimit

/-!
# The chart hypothesis of Tag 01NO from a degreewise base change

For a homomorphism of graded rings `f : 𝒜 →+*ᵍ ℬ`, `Stacks.Proj.IsBaseChangeOnCharts f` says that
for every homogeneous `a` of positive degree

`Away ℬ (f a) = Away 𝒜 a ⊗_{𝒜₀} ℬ₀`,

that is, extension of scalars along `𝒜₀ ⟶ ℬ₀` commutes with degree-zero localization at `a`.
This file proves it when `f` is a base change degreewise: for every `n`, the degree-`n` piece of
`ℬ` is `ℬ₀ ⊗_{𝒜₀} 𝒜ₙ`. Both sides are presented as direct limits of the homogeneous pieces of
degree `k • d` under multiplication by `a`, where `d` is the degree of `a`.

## Main definitions

* `Stacks.Proj.awayMk` is `y ↦ y / aⁿ` out of the degree-`n • d` piece, as a map of
  `𝒜 0`-modules, and `Stacks.Proj.mulPowPiece` is the transition map of the system.
* `Stacks.Proj.pieceMap` is the degree-`n` component of `f`, as a map of `𝒜 0`-modules.
* `Stacks.Proj.awayTensorLift` is the comparison
  `ℬ₀ ⊗_{𝒜₀} Away 𝒜 a ⟶ Away ℬ (f a)`.

## Main results

* `Stacks.Proj.exists_lTensor`: **every element of `ℬ₀ ⊗_{𝒜₀} Away 𝒜 a` comes from a single
  homogeneous stage of the system.**
* `Stacks.Proj.awayTensorLift_bijective` and `Stacks.Proj.isPushout_away`:
  **`Away ℬ (f a) = Away 𝒜 a ⊗_{𝒜₀} ℬ₀`.**
* `Stacks.Proj.isBaseChangeOnCharts_of_isBaseChange_pieces`: **the chart hypothesis of Tag 01NO,
  from the degreewise one.**

## Implementation notes

The gradings are families of `AddSubgroup`s, so they carry no module structure over their own
degree-zero part; `gradePieceSubmodule` supplies the degree-`n` piece as an `𝒜 0`-submodule of
`A`. The `𝒜 0`-module structure on a piece of `ℬ` is restriction of scalars along the degree-zero
part of `f`, and `Stacks.Proj.targetPieceModule` carries it at low priority so that the canonical
submodule structure on a piece of `𝒜` is still the one instance search finds. The `𝒜 0`-algebra
structure on `ℬ 0` depends on `f`, which does not appear in its type, so it is an
instance-implicit hypothesis together with the equation pinning it down; likewise the algebra
structures relating the two degree-zero localizations are hypotheses inside the chart section.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open HomogeneousLocalization TensorProduct

universe u

namespace Stacks.Proj

/-! ### The system of homogeneous pieces under multiplication by `a` -/

section OneRing

variable {A : Type u} [CommRing A] (𝒞 : ℕ → AddSubgroup A) [GradedRing 𝒞]

/-- An element of the degree-`n` piece read as a submodule over the degree-zero part is an element
of the degree-`n` piece. -/
public theorem mem_of_gradePiece {n : ℕ} (y : ↥(gradePieceSubmodule 𝒞 n)) : (y : A) ∈ 𝒞 n := y.2

variable {d : ℕ} {a : A} (ha : a ∈ 𝒞 d)

/-- The fraction `y / aⁿ`, as a map of `𝒞 0`-modules out of the degree-`n • d` piece. -/
public def awayMk (n : ℕ) : ↥(gradePieceSubmodule 𝒞 (n • d)) →ₗ[↥(𝒞 0)] Away 𝒞 a where
  toFun y := Away.mk 𝒞 ha n y (mem_of_gradePiece 𝒞 y)
  map_add' y z := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
      Localization.add_mk_self]
    rfl
  map_smul' r y := by
    apply HomogeneousLocalization.val_injective
    have hr : ((fromZeroRingHom 𝒞 (Submonoid.powers a)) r).val
        = Localization.mk (r : A) 1 := rfl
    change (Away.mk 𝒞 ha n _ (mem_of_gradePiece 𝒞 (r • y))).val
      = (fromZeroRingHom 𝒞 (Submonoid.powers a) r
          * Away.mk 𝒞 ha n (y : A) (mem_of_gradePiece 𝒞 y)).val
    rw [HomogeneousLocalization.val_mul, hr, Away.val_mk, Away.val_mk, Localization.mk_mul,
      one_mul]
    rfl

/-- `Stacks.Proj.awayMk` sends `y` to the fraction `y / aⁿ`. -/
@[simp] public theorem awayMk_apply (n : ℕ) (y : ↥(gradePieceSubmodule 𝒞 (n • d))) :
    awayMk 𝒞 ha n y = Away.mk 𝒞 ha n y (mem_of_gradePiece 𝒞 y) := rfl

/-- Multiplication by `a ^ (m - n)`, from the degree-`n • d` piece to the degree-`m • d` piece.
It is only meaningful for `n ≤ m`; the truncated subtraction keeps the map total. -/
public def mulPowPiece (n m : ℕ) (_ : n ≤ m) :
    ↥(gradePieceSubmodule 𝒞 (n • d)) →ₗ[↥(𝒞 0)] ↥(gradePieceSubmodule 𝒞 (m • d)) where
  toFun y := ⟨a ^ (m - n) * y, by
    rcases Nat.le_total n m with h | h
    · have := Away.pow_mul_mem 𝒞 ha (mem_of_gradePiece 𝒞 y) (m - n)
      rwa [Nat.add_sub_cancel' h] at this
    · rw [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
      exact (Nat.le_antisymm h (by omega) ▸ mem_of_gradePiece 𝒞 y : (y : A) ∈ 𝒞 (m • d))⟩
  map_add' y z := Subtype.ext (by simpa using mul_add (a ^ (m - n)) (y : A) z)
  map_smul' r y := Subtype.ext (by
    change a ^ (m - n) * ((r : A) * (y : A)) = (r : A) * (a ^ (m - n) * (y : A))
    ring)

/-- `Stacks.Proj.mulPowPiece` is multiplication by `a ^ (m - n)` on underlying elements. -/
@[simp] public theorem coe_mulPowPiece (n m : ℕ) (h : n ≤ m)
    (y : ↥(gradePieceSubmodule 𝒞 (n • d))) :
    (mulPowPiece 𝒞 ha n m h y : A) = a ^ (m - n) * y := rfl

/-- **Enlarging the denominator does not change the fraction.** -/
public theorem awayMk_mulPowPiece (n m : ℕ) (h : n ≤ m)
    (y : ↥(gradePieceSubmodule 𝒞 (n • d))) :
    awayMk 𝒞 ha m (mulPowPiece 𝒞 ha n m h y) = awayMk 𝒞 ha n y :=
  Away.mk_eq_mk_of_le 𝒞 ha h (y : A) (mem_of_gradePiece 𝒞 y) _

end OneRing

/-! ### The degreewise comparison -/

section TwoRings

variable {A B : Type u} [CommRing A] [CommRing B]
  {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) [Algebra ↥(𝒜 0) ↥(ℬ 0)]

/-- The `𝒜 0`-module structure on a homogeneous piece of `ℬ`, by restriction of scalars along the
degree-zero part of the base-ring map. Its priority is low so that on the source side, where
`𝒜 0` acts on a piece of `𝒜` directly, the canonical submodule structure is still found. -/
public instance (priority := 100) targetPieceModule (n : ℕ) :
    Module ↥(𝒜 0) ↥(gradePieceSubmodule ℬ n) :=
  Module.compHom _ (algebraMap ↥(𝒜 0) ↥(ℬ 0))

/-- The scalar tower `𝒜 0 → ℬ 0 → ℬ n` for the restricted `𝒜 0`-module structure on a homogeneous
piece of `ℬ`. -/
public instance (priority := 100) targetPieceTower (n : ℕ) :
    IsScalarTower ↥(𝒜 0) ↥(ℬ 0) ↥(gradePieceSubmodule ℬ n) :=
  ⟨fun x y z => by
    rw [Algebra.smul_def x y]
    exact mul_smul (algebraMap ↥(𝒜 0) ↥(ℬ 0) x) y z⟩

variable (halg : ∀ r : ↥(𝒜 0), (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) = f (r : A))

/-- The degree-`n` component of `f`, as a map of `𝒜 0`-modules. -/
public def pieceMap (n : ℕ) :
    ↥(gradePieceSubmodule 𝒜 n) →ₗ[↥(𝒜 0)] ↥(gradePieceSubmodule ℬ n) where
  toFun x := ⟨f x, f.map_mem (mem_of_gradePiece 𝒜 x)⟩
  map_add' x y := Subtype.ext (map_add f _ _)
  map_smul' r x := Subtype.ext (by
    change f ((r : A) * (x : A)) = (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) * f (x : A)
    rw [map_mul, halg])

/-- `Stacks.Proj.pieceMap` is `f` on underlying elements. -/
@[simp] public theorem coe_pieceMap (n : ℕ) (x : ↥(gradePieceSubmodule 𝒜 n)) :
    (pieceMap f halg n x : B) = f (x : A) := rfl

/-! ### One chart -/

section Chart

variable {d : ℕ} {a : A} (ha : a ∈ 𝒜 d)

/-- Rewriting a fraction over a bigger power of `a`, inside a tensor product. -/
public theorem lTensor_awayMk_mulPowPiece (n m : ℕ) (h : n ≤ m)
    (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(gradePieceSubmodule 𝒜 (n • d))) :
    LinearMap.lTensor ↥(ℬ 0) (awayMk 𝒜 ha m)
        (LinearMap.lTensor ↥(ℬ 0) (mulPowPiece 𝒜 ha n m h) u)
      = LinearMap.lTensor ↥(ℬ 0) (awayMk 𝒜 ha n) u := by
  induction u with
  | tmul b y => simp only [LinearMap.lTensor_tmul, awayMk_mulPowPiece]
  | add u v hu hv => simp only [map_add, hu, hv]

include ha in
/-- **Every element of `ℬ₀ ⊗ Away 𝒜 a` comes from a single homogeneous stage of the system.** -/
public theorem exists_lTensor (w : ↥(ℬ 0) ⊗[↥(𝒜 0)] Away 𝒜 a) :
    ∃ (n : ℕ) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(gradePieceSubmodule 𝒜 (n • d))),
      LinearMap.lTensor ↥(ℬ 0) (awayMk 𝒜 ha n) u = w := by
  induction w with
  | tmul b z =>
      obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ha z
      exact ⟨n, b ⊗ₜ ⟨x, hx⟩, by rw [LinearMap.lTensor_tmul, awayMk_apply]⟩
  | add w₁ w₂ h₁ h₂ =>
      obtain ⟨n₁, u₁, hu₁⟩ := h₁
      obtain ⟨n₂, u₂, hu₂⟩ := h₂
      refine ⟨max n₁ n₂,
        LinearMap.lTensor ↥(ℬ 0) (mulPowPiece 𝒜 ha n₁ _ (le_max_left n₁ n₂)) u₁
          + LinearMap.lTensor ↥(ℬ 0) (mulPowPiece 𝒜 ha n₂ _ (le_max_right n₁ n₂)) u₂, ?_⟩
      rw [map_add, lTensor_awayMk_mulPowPiece, lTensor_awayMk_mulPowPiece, hu₁, hu₂]

variable (hf : ∀ n, IsBaseChange ↥(ℬ 0) (pieceMap f halg n))

include halg in
/-- The degreewise identifications are compatible with multiplying a numerator by a power of
`a`. -/
public theorem equiv_lTensor_mulPowPiece (n m : ℕ) (h : n ≤ m)
    (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(gradePieceSubmodule 𝒜 (n • d))) :
    (hf (m • d)).equiv (LinearMap.lTensor ↥(ℬ 0) (mulPowPiece 𝒜 ha n m h) u)
      = mulPowPiece ℬ (f.map_mem ha) n m h ((hf (n • d)).equiv u) := by
  induction u with
  | tmul b y =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      refine Subtype.ext ?_
      show (b : B) * f (a ^ (m - n) * (y : A)) = f a ^ (m - n) * ((b : B) * f (y : A))
      rw [map_mul, map_pow]
      ring
  | add u v hu hv => simp only [map_add, hu, hv]

section AwayAlgebra

variable [Algebra (Away 𝒜 a) (Away ℬ (f a))] [Algebra ↥(𝒜 0) (Away ℬ (f a))]
  [IsScalarTower ↥(𝒜 0) ↥(ℬ 0) (Away ℬ (f a))]
  [IsScalarTower ↥(𝒜 0) (Away 𝒜 a) (Away ℬ (f a))]
  (hmap : ∀ z, algebraMap (Away 𝒜 a) (Away ℬ (f a)) z = Away.map f a z)

/-- **The comparison `ℬ₀ ⊗_{𝒜₀} Away 𝒜 a ⟶ Away ℬ (f a)`.** -/
public def awayTensorLift : ↥(ℬ 0) ⊗[↥(𝒜 0)] Away 𝒜 a →ₐ[↥(ℬ 0)] Away ℬ (f a) :=
  Algebra.TensorProduct.lift (Algebra.ofId ↥(ℬ 0) (Away ℬ (f a)))
    (IsScalarTower.toAlgHom ↥(𝒜 0) (Away 𝒜 a) (Away ℬ (f a)))
    (fun _ _ => mul_comm _ _)

include hmap in
/-- The comparison sends `b ⊗ z` to `algebraMap b * Away.map f a z`. -/
@[simp] public theorem awayTensorLift_tmul (b : ↥(ℬ 0)) (z : Away 𝒜 a) :
    awayTensorLift (𝒜 := 𝒜) f (a := a) (b ⊗ₜ z)
      = algebraMap ↥(ℬ 0) (Away ℬ (f a)) b * Away.map f a z := by
  show algebraMap ↥(ℬ 0) (Away ℬ (f a)) b * algebraMap (Away 𝒜 a) (Away ℬ (f a)) z = _
  rw [hmap]

include hmap halg in
/-- The comparison, on a pure tensor whose second factor is a fraction with numerator in a single
homogeneous piece. -/
public theorem awayTensorLift_tmul_awayMk (n : ℕ) (b : ↥(ℬ 0))
    (y : ↥(gradePieceSubmodule 𝒜 (n • d))) :
    awayTensorLift (𝒜 := 𝒜) f (a := a) (b ⊗ₜ awayMk 𝒜 ha n y)
      = awayMk ℬ (f.map_mem ha) n (b • pieceMap f halg (n • d) y) := by
  rw [awayTensorLift_tmul f hmap, awayMk_apply, Away.map_mk, map_smul, awayMk_apply]
  show _ = fromZeroRingHom ℬ (Submonoid.powers (f a)) b * _
  rfl

include hmap halg in
/-- The comparison, read on the degree-`n • d` stage of the system. -/
public theorem awayTensorLift_lTensor (n : ℕ)
    (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(gradePieceSubmodule 𝒜 (n • d))) :
    awayTensorLift (𝒜 := 𝒜) f (a := a) (LinearMap.lTensor ↥(ℬ 0) (awayMk 𝒜 ha n) u)
      = awayMk ℬ (f.map_mem ha) n ((hf (n • d)).equiv u) := by
  induction u with
  | tmul b y =>
      rw [LinearMap.lTensor_tmul, awayTensorLift_tmul_awayMk f halg ha hmap,
        IsBaseChange.equiv_tmul]
  | add u v hu hv => simp only [map_add, hu, hv]

include hmap halg ha hf in
/-- **The comparison `ℬ₀ ⊗_{𝒜₀} Away 𝒜 a ⟶ Away ℬ (f a)` is bijective.** -/
public theorem awayTensorLift_bijective :
    Function.Bijective (awayTensorLift (𝒜 := 𝒜) f (a := a)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
    obtain ⟨n, u, rfl⟩ := exists_lTensor ha w
    rw [awayTensorLift_lTensor f halg ha hf hmap] at hw
    obtain ⟨k, hk⟩ := (Away.mk_eq_zero_iff ℬ (f.map_mem ha) n
      ((hf (n • d)).equiv u : B) (mem_of_gradePiece ℬ _)).mp hw
    have hzero : mulPowPiece ℬ (f.map_mem ha) n (n + k) (Nat.le_add_right n k)
        ((hf (n • d)).equiv u) = 0 := by
      refine Subtype.ext ?_
      show f a ^ (n + k - n) * ((hf (n • d)).equiv u : B) = 0
      rwa [Nat.add_sub_cancel_left]
    have hu0 : LinearMap.lTensor ↥(ℬ 0)
        (mulPowPiece 𝒜 ha n (n + k) (Nat.le_add_right n k)) u = 0 := by
      refine (hf ((n + k) • d)).equiv.map_eq_zero_iff.mp ?_
      rw [equiv_lTensor_mulPowPiece f halg ha hf, hzero]
    rw [← lTensor_awayMk_mulPowPiece ha n (n + k) (Nat.le_add_right n k) u, hu0, map_zero]
  · intro z
    obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ (f.map_mem ha) z
    refine ⟨LinearMap.lTensor ↥(ℬ 0) (awayMk 𝒜 ha n) ((hf (n • d)).equiv.symm ⟨y, hy⟩), ?_⟩
    rw [awayTensorLift_lTensor f halg ha hf hmap, LinearEquiv.apply_symm_apply, awayMk_apply]

include hmap halg ha hf in
/-- **`Away ℬ (f a) = Away 𝒜 a ⊗_{𝒜₀} ℬ₀`**, as a pushout of algebras. -/
public theorem isPushout_away :
    Algebra.IsPushout ↥(𝒜 0) ↥(ℬ 0) (Away 𝒜 a) (Away ℬ (f a)) :=
  ⟨IsBaseChange.of_equiv
    (LinearEquiv.ofBijective (awayTensorLift (𝒜 := 𝒜) f (a := a)).toLinearMap
      (awayTensorLift_bijective f halg ha hf hmap))
    (fun z => by
      show awayTensorLift (𝒜 := 𝒜) f (a := a) ((1 : ↥(ℬ 0)) ⊗ₜ z) = _
      rw [awayTensorLift_tmul f hmap, map_one, one_mul]
      exact (hmap z).symm)⟩

end AwayAlgebra

end Chart

include halg in
/-- **The chart hypothesis of Tag 01NO, from the degreewise one.** If every homogeneous piece of
`ℬ` is the base change of the corresponding piece of `𝒜` along `𝒜 0 ⟶ ℬ 0`, then every standard
affine chart of `Proj ℬ` is the base change of the corresponding chart of `Proj 𝒜`. -/
public theorem isBaseChangeOnCharts_of_isBaseChange_pieces
    (hf : ∀ n, IsBaseChange ↥(ℬ 0) (pieceMap f halg n)) :
    Stacks.Proj.IsBaseChangeOnCharts f := by
  have hgz : (algebraMap ↥(𝒜 0) ↥(ℬ 0) : ↥(𝒜 0) →+* ↥(ℬ 0)) = f.gradedZeroRingHom :=
    RingHom.ext fun r => Subtype.ext (halg r)
  apply Stacks.Proj.IsBaseChangeOnCharts.of_isPushout f
  intro i _hi s hs
  let _ : Algebra (Away 𝒜 s) (Away ℬ (f s)) := (Away.map f s).toAlgebra
  let _ : Algebra ↥(𝒜 0) (Away ℬ (f s)) :=
    ((fromZeroRingHom ℬ (Submonoid.powers (f s))).comp f.gradedZeroRingHom).toAlgebra
  let _ : IsScalarTower ↥(𝒜 0) ↥(ℬ 0) (Away ℬ (f s)) :=
    IsScalarTower.of_algebraMap_eq' (by rw [hgz]; rfl)
  let _ : IsScalarTower ↥(𝒜 0) (Away 𝒜 s) (Away ℬ (f s)) :=
    IsScalarTower.of_algebraMap_eq'
      (AlgebraicGeometry.Proj.awayMap_comp_fromZeroRingHom f s).symm
  have _ := (isPushout_away f halg hs hf (fun _ => rfl)).symm
  rw [← hgz]
  exact CommRingCat.isPushout_of_isPushout ↥(𝒜 0) (Away 𝒜 s) ↥(ℬ 0) (Away ℬ (f s))

end TwoRings

end Stacks.Proj

end
