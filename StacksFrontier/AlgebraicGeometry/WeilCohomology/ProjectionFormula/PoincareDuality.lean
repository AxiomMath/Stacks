module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Pushforward from Poincaré duality

A pullback between two cohomology groups has a canonical contragredient map between their
complementary-degree groups whenever the target pairing is perfect.  This is the pushforward
furnished by Poincaré duality.

## Main definitions

* `Stacks.WeilCohomology.poincareDualPushforward` is the pushforward adjoint to a pullback with
  respect to the trace pairings.
* `Stacks.WeilCohomology.gradedPoincareDualPushforward` specializes the construction to
  complementary graded pieces with their Tate twists, cup products, and trace maps.
* `Stacks.WeilCohomology.tateTwist` constructs tensor-defined Tate twists from the chosen line,
  with `tateTwistMap` and `tateTwistZero` giving the induced linear maps and the zero-twist
  identification.
* `Stacks.WeilCohomology.tateTwistedPoincareDualPushforward` is the pushforward for constructed
  twisted cup products and trace pairings in every degree and twist.

## Main results

* `Stacks.WeilCohomology.poincareDualPushforward_pairing` is the defining adjointness equation;
  `Stacks.WeilCohomology.pair_poincareDualPushforward` is its simplification-oriented form.
* `Stacks.WeilCohomology.eq_poincareDualPushforward_iff` says that this equation uniquely
  characterizes the pushforward.
* `Stacks.WeilCohomology.gradedPoincareDualPushforward_trace_cup` and
  `Stacks.WeilCohomology.eq_gradedPoincareDualPushforward_iff` give the corresponding
  cup-product-and-trace formulas on the graded, twisted cohomology groups.
* `Stacks.WeilCohomology.tateTwistedPoincareDualPushforward_trace_cup` and
  `Stacks.WeilCohomology.eq_tateTwistedPoincareDualPushforward_iff` characterize the pushforward
  for the induced twisted pairings by the trace equation.

## Implementation notes

The four modules of `poincareDualPushforward` stand for `Hⁱ(X)`, `Hⁱ(Y)`, `H²ᵈ⁻ⁱ(X)(d)`, and
`H²ᵉ⁻ⁱ(Y)(e)`.  Thus the Tate twists, cup products, and trace maps are already incorporated in
the two displayed pairings.  The construction is stated for an arbitrary commutative semiring
and only requires perfectness of the target pairing; this is the part of Poincaré duality used
to construct the contragredient.  Concretely, the source functional is precomposed with
pullback and then transported back across the target perfect-pairing equivalence.
Consequently its value `f_* a` is characterized by
`pairX (pullback b) a = pairY b (f_* a)` for every `b`.

The named bridge from this abstract formulation to the cohomological statement is
`gradedPoincareDualPushforward_trace_cup`: its families are indexed first by cohomological
degree and then by Tate twist, and `cupX.compr₂ integrationX` (and similarly for `Y`) is
precisely the pairing `(α, β) ↦ ∫ α ∪ β`.

For the actual twists `V(n) = V ⊗ F(n)`, with the canonical tensor-unit equivalence
`tateTwistZero : V(0) ≃ₗ[F] V`, the shifted pushforward uses the pairing of degree `2d-q` and
twist `d-n` against degree `q` and twist `n`.  Its target has degree `q+2(e-d)` and twist
`n+e-d`; hence for `q=n=0` its source is canonically identified with `H⁰(X)` and its target is
`H²⁽ᵉ⁻ᵈ⁾(Y)(e-d)`, as required for the unit class.

The twisted interface takes the original untwisted cup products and pullback.  It constructs
their tensor extensions and derives shifted perfectness from the untwisted perfect pairing.
`tateTwistedPoincareDualPushforward_tensor` identifies its adjoint with the original pushforward
tensored with the identity on `F(n-d)`.  Line coordinates are internal to the construction;
independence of the chosen coordinate is proved in `tateCupWith_eq` and `tateLineMulWith_eq`.
The wrapper `poincareDualPushforwardFromUntwisted` accepts an element of `Hⁱ(X)` directly, in
particular `1 : H⁰(X)`.

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
-/

@[expose] public section

namespace Stacks.WeilCohomology

open scoped TensorProduct

universe uR uHX uHY uDX uDY uL

/-- The Poincaré-dual pushforward, i.e. the contragredient of `pullback` with respect to `pairX`
and `pairY`.

For `b : HY` and `a : DX`, it satisfies
`pairX (pullback b) a = pairY b (poincareDualPushforward pairX pairY pullback a)`.
In cohomological notation this is `integration_X (f⁺ b ∪ a) = integration_Y (b ∪ f_* a)`. -/
@[implicit_reducible]
noncomputable def poincareDualPushforward
    {R : Type uR} [CommSemiring R]
    {HX : Type uHX} [AddCommMonoid HX] [Module R HX]
    {HY : Type uHY} [AddCommMonoid HY] [Module R HY]
    {DX : Type uDX} [AddCommMonoid DX] [Module R DX]
    {DY : Type uDY} [AddCommMonoid DY] [Module R DY]
    (pairX : HX →ₗ[R] DX →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R) [pairY.IsPerfPair]
    (pullback : HY →ₗ[R] HX) : DX →ₗ[R] DY :=
  pairY.flip.toPerfPair.symm.toLinearMap.comp
    (pullback.dualMap.comp pairX.flip)

/-- The pushforward satisfies its defining adjointness equation. -/
theorem poincareDualPushforward_pairing
    {R : Type uR} [CommSemiring R]
    {HX : Type uHX} [AddCommMonoid HX] [Module R HX]
    {HY : Type uHY} [AddCommMonoid HY] [Module R HY]
    {DX : Type uDX} [AddCommMonoid DX] [Module R DX]
    {DY : Type uDY} [AddCommMonoid DY] [Module R DY]
    (pairX : HX →ₗ[R] DX →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R) [pairY.IsPerfPair]
    (pullback : HY →ₗ[R] HX) (b : HY) (a : DX) :
    pairX (pullback b) a =
      pairY b (poincareDualPushforward pairX pairY pullback a) := by
  simp [poincareDualPushforward]

/-- Simplification-oriented form of the defining adjointness equation. -/
@[simp]
theorem pair_poincareDualPushforward
    {R : Type uR} [CommSemiring R]
    {HX : Type uHX} [AddCommMonoid HX] [Module R HX]
    {HY : Type uHY} [AddCommMonoid HY] [Module R HY]
    {DX : Type uDX} [AddCommMonoid DX] [Module R DX]
    {DY : Type uDY} [AddCommMonoid DY] [Module R DY]
    (pairX : HX →ₗ[R] DX →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R) [pairY.IsPerfPair]
    (pullback : HY →ₗ[R] HX) (b : HY) (a : DX) :
    pairY b (poincareDualPushforward pairX pairY pullback a) =
      pairX (pullback b) a :=
  (poincareDualPushforward_pairing pairX pairY pullback b a).symm

/-- A linear map is the Poincaré-dual pushforward exactly when it satisfies the defining
adjointness equation.  In particular, that equation characterizes the pushforward uniquely. -/
theorem eq_poincareDualPushforward_iff
    {R : Type uR} [CommSemiring R]
    {HX : Type uHX} [AddCommMonoid HX] [Module R HX]
    {HY : Type uHY} [AddCommMonoid HY] [Module R HY]
    {DX : Type uDX} [AddCommMonoid DX] [Module R DX]
    {DY : Type uDY} [AddCommMonoid DY] [Module R DY]
    (pairX : HX →ₗ[R] DX →ₗ[R] R)
    (pairY : HY →ₗ[R] DY →ₗ[R] R) [pairY.IsPerfPair]
    (pullback : HY →ₗ[R] HX) (pushforward : DX →ₗ[R] DY) :
    pushforward = poincareDualPushforward pairX pairY pullback ↔
      ∀ b a, pairX (pullback b) a = pairY b (pushforward a) := by
  refine ⟨fun h b a => h ▸ poincareDualPushforward_pairing pairX pairY pullback b a,
    fun h => LinearMap.ext fun a => (LinearMap.IsPerfPair.bijective_right pairY).injective ?_⟩
  exact LinearMap.ext fun b =>
    (h b a).symm.trans (poincareDualPushforward_pairing pairX pairY pullback b a)

/-- The Tate line `F(n)`: tensor powers of the chosen line for nonnegative integers, and of its
dual for negative integers.  Scalars and the line may live in independent universes. -/
abbrev tateLine (F : Type uR) [Field F]
    (L : Type uL) [AddCommGroup L] [Module F L] (n : ℤ) :
    ModuleCat.{max uR uL} F :=
  match n with
  | .ofNat m => ModuleCat.of F (TensorPower F m L)
  | .negSucc m => ModuleCat.of F (TensorPower F (m + 1) (Module.Dual F L))

/-- The tensor-defined Tate twist, over the original coefficient field. -/
abbrev tateTwist (F : Type uR) [Field F]
    (L : Type uL) [AddCommGroup L] [Module F L]
    (V : Type uHX) [AddCommGroup V] [Module F V] (n : ℤ) :
    ModuleCat.{max uR uL uHX} F :=
  ModuleCat.of F (V ⊗[F] tateLine F L n)

section Twists

variable {F : Type uR} [Field F]
variable {L : Type uL} [AddCommGroup L] [Module F L]
variable {U : Type uHX} [AddCommGroup U] [Module F U]
variable {V : Type uHY} [AddCommGroup V] [Module F V]
variable {W : Type uDX} [AddCommGroup W] [Module F W]

/-- The canonical tensor-unit identification, including when the scalar, line, and vector space
have different universes.  Its inverse puts the unit class in `H⁰(X)(0)`. -/
noncomputable def tateTwistZero : tateTwist F L V 0 ≃ₗ[F] V :=
  (TensorProduct.congr (LinearEquiv.refl F V)
    (TensorPower.algebraMap₀ (R := F) (M := L)).symm).trans (TensorProduct.rid F V)

/-- A linear map induces a map on each twist by tensoring with the identity. -/
def tateTwistMap (f : U →ₗ[F] V) (n : ℤ) :
    tateTwist F L U n →ₗ[F] tateTwist F L V n :=
  TensorProduct.map f LinearMap.id

/-- Coordinates on a tensor power, used only to construct the intrinsic tensor operations. -/
noncomputable def tensorPowerCoordinates (c : L ≃ₗ[F] F) (n : ℕ) :
    TensorPower F n L ≃ₗ[F] F :=
  (PiTensorProduct.congr fun _ => c).trans
    (PiTensorProduct.constantBaseRingEquiv (Fin n) F).toLinearEquiv

/-- Coordinates on all integer powers of a line, with the dual coordinates in negative
degrees. -/
noncomputable def tateLineCoordinates (c : L ≃ₗ[F] F) (n : ℤ) :
    tateLine F L n ≃ₗ[F] F := by
  cases n with
  | ofNat m => exact tensorPowerCoordinates c m
  | negSucc m =>
    exact tensorPowerCoordinates
      (c.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)) (m + 1)

/-- Coordinates on a twist.  The induced operations below do not depend on the choice of
coordinates. -/
noncomputable def tateTwistCoordinates (c : L ≃ₗ[F] F) (n : ℤ) :
    tateTwist F L V n ≃ₗ[F] V :=
  (TensorProduct.congr (LinearEquiv.refl F V) (tateLineCoordinates c n)).trans
    (TensorProduct.rid F V)

/-- The coordinates of a pure tensor `v ⊗ l` are `v` scaled by the coordinate of `l`. -/
@[simp]
theorem tateTwistCoordinates_tmul (c : L ≃ₗ[F] F) (n : ℤ)
    (v : V) (l : tateLine F L n) :
    tateTwistCoordinates c n (v ⊗ₜ[F] l) = tateLineCoordinates c n l • v := by
  simp [tateTwistCoordinates]

/-- Coordinates on twists are natural in the untwisted space. -/
@[simp]
theorem tateTwistCoordinates_map (c : L ≃ₗ[F] F) (n : ℤ)
    (f : U →ₗ[F] V) (x : tateTwist F L U n) :
    tateTwistCoordinates c n (tateTwistMap f n x) =
      f (tateTwistCoordinates c n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul u l => simp [tateTwistMap, tateTwistCoordinates]
  | add x y hx hy => simp_all

/-- A coordinate on a one-dimensional line, chosen using one-dimensionality; no basis is
supplied as input. -/
noncomputable def tateLineCoordinate (hL : Module.finrank F L = 1) : L ≃ₗ[F] F :=
  (Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one hL)).symm

/-- Tensor cup product in coordinates.  The equality of total twists is part of its type. -/
noncomputable def tateCupWith (c : L ≃ₗ[F] F)
    (cup : U →ₗ[F] V →ₗ[F] W) (n m k : ℤ) (_h : n + m = k) :
    tateTwist F L U n →ₗ[F] tateTwist F L V m →ₗ[F] tateTwist F L W k :=
  (cup.compr₂ (tateTwistCoordinates c k).symm.toLinearMap).compl₁₂
    (tateTwistCoordinates c n).toLinearMap (tateTwistCoordinates c m).toLinearMap

/-- The induced cup product `U(n) × V(m) → W(k)`, for `n + m = k`. -/
noncomputable def tateCup (hL : Module.finrank F L = 1)
    (cup : U →ₗ[F] V →ₗ[F] W) (n m k : ℤ) (h : n + m = k) :
    tateTwist F L U n →ₗ[F] tateTwist F L V m →ₗ[F] tateTwist F L W k :=
  tateCupWith (tateLineCoordinate hL) cup n m k h

private theorem coordinate_change (c c' : L ≃ₗ[F] F) :
    ∃ r : Fˣ, ∀ l, c' l = (r : F) * c l := by
  let r := c' (c.symm 1)
  have hr : r ≠ 0 := by simp [r]
  refine ⟨Units.mk0 r hr, fun l => ?_⟩
  have h : l = c l • c.symm 1 := by
    apply c.injective
    simp
  conv_lhs => rw [h]
  simp [r, mul_comm]

private theorem tensorPowerCoordinates_change (c c' : L ≃ₗ[F] F)
    (r : Fˣ) (h : ∀ l, c' l = (r : F) * c l) (n : ℕ)
    (x : TensorPower F n L) :
    tensorPowerCoordinates c' n x = (r : F) ^ n * tensorPowerCoordinates c n x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simp [tensorPowerCoordinates, PiTensorProduct.constantBaseRingEquiv_tprod,
      h, Finset.prod_mul_distrib, mul_left_comm]
  | add x y hx hy => simp [hx, hy, mul_add]

private theorem tateLineCoordinates_change (c c' : L ≃ₗ[F] F)
    (r : Fˣ) (h : ∀ l, c' l = (r : F) * c l) (n : ℤ)
    (x : tateLine F L n) :
    tateLineCoordinates c' n x = ((r ^ n : Fˣ) : F) * tateLineCoordinates c n x := by
  have hd : c'.symm 1 = (↑r⁻¹ : F) • c.symm 1 := by
    apply c'.injective
    rw [c'.apply_symm_apply, map_smul, h, c.apply_symm_apply]
    simp
  cases n with
  | ofNat m =>
    simpa [tateLineCoordinates] using tensorPowerCoordinates_change c c' r h m x
  | negSucc m =>
    have hdual : ∀ l : Module.Dual F L,
        (c'.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)) l =
          (↑r⁻¹ : F) * (c.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)) l := by
      intro l
      change l (c'.symm 1) = _ * l (c.symm 1)
      rw [hd, map_smul, smul_eq_mul]
    simpa [tateLineCoordinates, zpow_negSucc, inv_pow] using
      tensorPowerCoordinates_change _ _ r⁻¹ hdual (m + 1) x

private theorem tateTwistCoordinates_change (c c' : L ≃ₗ[F] F)
    (r : Fˣ) (h : ∀ l, c' l = (r : F) * c l) (n : ℤ)
    (x : tateTwist F L V n) :
    tateTwistCoordinates c' n x = ((r ^ n : Fˣ) : F) • tateTwistCoordinates c n x := by
  induction x using TensorProduct.inductionOn with
  | tmul v l =>
    rw [tateTwistCoordinates_tmul, tateTwistCoordinates_tmul,
      tateLineCoordinates_change c c' r h]
    exact mul_smul _ _ _
  | add x y hx hy => simp [hx, hy, smul_add]

/-- Tensor cup products are independent of the coordinate used to construct them: the two input
scaling factors cancel the output scaling factor. -/
theorem tateCupWith_eq (c c' : L ≃ₗ[F] F)
    (cup : U →ₗ[F] V →ₗ[F] W) (n m k : ℤ) (h : n + m = k) :
    tateCupWith c cup n m k h = tateCupWith c' cup n m k h := by
  obtain ⟨r, hr⟩ := coordinate_change c c'
  refine LinearMap.ext₂ fun u v => (tateTwistCoordinates c' k).injective ?_
  rw [tateTwistCoordinates_change c c' r hr]
  simp only [tateCupWith, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [tateTwistCoordinates_change c c' r hr, tateTwistCoordinates_change c c' r hr]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  congr 1
  rw [← Units.val_mul, ← zpow_add, add_comm m n, h]

/-- The induced cup product can be computed in any coordinate on the line. -/
theorem tateCup_eq_with (hL : Module.finrank F L = 1) (c : L ≃ₗ[F] F)
    (cup : U →ₗ[F] V →ₗ[F] W) (n m k : ℤ) (h : n + m = k) :
    tateCup hL cup n m k h = tateCupWith c cup n m k h :=
  tateCupWith_eq _ _ _ _ _ _ _

/-- Multiplication of integer powers of a line in a coordinate. -/
noncomputable def tateLineMulWith (c : L ≃ₗ[F] F)
    (n m k : ℤ) (_h : n + m = k) :
    tateLine F L n ⊗[F] tateLine F L m ≃ₗ[F] tateLine F L k :=
  ((TensorProduct.congr (tateLineCoordinates c n) (tateLineCoordinates c m)).trans
    (TensorProduct.lid F F)).trans (tateLineCoordinates c k).symm

/-- The coordinate of a product of pure line tensors is the product of the coordinates. -/
private theorem tateLineCoordinates_tateLineMulWith (c : L ≃ₗ[F] F)
    (n m k : ℤ) (h : n + m = k) (l : tateLine F L n) (t : tateLine F L m) :
    tateLineCoordinates c k (tateLineMulWith c n m k h (l ⊗ₜ[F] t)) =
      tateLineCoordinates c n l * tateLineCoordinates c m t := by
  simp [tateLineMulWith]

/-- Multiplication of line powers is intrinsic. -/
theorem tateLineMulWith_eq (c c' : L ≃ₗ[F] F)
    (n m k : ℤ) (h : n + m = k) :
    tateLineMulWith c n m k h = tateLineMulWith c' n m k h := by
  obtain ⟨r, hr⟩ := coordinate_change c c'
  apply LinearEquiv.toLinearMap_injective
  ext l t
  change tateLineMulWith c n m k h (l ⊗ₜ[F] t) =
    tateLineMulWith c' n m k h (l ⊗ₜ[F] t)
  apply (tateLineCoordinates c' k).injective
  conv_lhs => rw [tateLineCoordinates_change c c' r hr]
  rw [tateLineCoordinates_tateLineMulWith, tateLineCoordinates_tateLineMulWith,
    tateLineCoordinates_change c c' r hr, tateLineCoordinates_change c c' r hr,
    mul_mul_mul_comm, ← Units.val_mul, ← zpow_add, h]

/-- The canonical multiplication `F(n) ⊗ F(m) ≃ F(k)` for `n + m = k`. -/
noncomputable def tateLineMul (hL : Module.finrank F L = 1)
    (n m k : ℤ) (h : n + m = k) :
    tateLine F L n ⊗[F] tateLine F L m ≃ₗ[F] tateLine F L k :=
  tateLineMulWith (tateLineCoordinate hL) n m k h

/-- The constructed cup product is the original product tensored with multiplication of the Tate
lines. -/
theorem tateCup_tmul (hL : Module.finrank F L = 1)
    (cup : U →ₗ[F] V →ₗ[F] W) (n m k : ℤ) (h : n + m = k)
    (u : U) (v : V) (l : tateLine F L n) (t : tateLine F L m) :
    tateCup hL cup n m k h (u ⊗ₜ[F] l) (v ⊗ₜ[F] t) =
      cup u v ⊗ₜ[F] tateLineMul hL n m k h (l ⊗ₜ[F] t) := by
  apply (tateTwistCoordinates (tateLineCoordinate hL) k).injective
  change tateTwistCoordinates _ k ((tateTwistCoordinates _ k).symm
    (cup (tateTwistCoordinates _ n (u ⊗ₜ[F] l))
      (tateTwistCoordinates _ m (v ⊗ₜ[F] t)))) = _
  rw [LinearEquiv.apply_symm_apply, tateTwistCoordinates_tmul,
    tateTwistCoordinates_tmul, tateTwistCoordinates_tmul]
  simp only [tateLineMul, tateLineCoordinates_tateLineMulWith, map_smul, LinearMap.smul_apply,
    smul_smul]
  rw [mul_comm]

/-- Canonical addition of twists, by the tensor associator and multiplication of line powers. -/
noncomputable def tateTwistAdd (hL : Module.finrank F L = 1)
    (n m k : ℤ) (h : n + m = k) :
    tateTwist F L (tateTwist F L V n) m ≃ₗ[F] tateTwist F L V k :=
  (TensorProduct.assoc F V (tateLine F L n) (tateLine F L m)).trans
    (TensorProduct.congr (LinearEquiv.refl F V) (tateLineMul hL n m k h))

/-- Addition of twists is compatible with the coordinates on the twists. -/
theorem tateTwistCoordinates_add (hL : Module.finrank F L = 1)
    (n m k : ℤ) (h : n + m = k) (x : tateTwist F L (tateTwist F L V n) m) :
    tateTwistCoordinates (tateLineCoordinate hL) k (tateTwistAdd hL n m k h x) =
      tateTwistCoordinates (tateLineCoordinate hL) n
        (tateTwistCoordinates (tateLineCoordinate hL) m x) := by
  have heq : (tateTwistCoordinates (V := V) (tateLineCoordinate hL) k).toLinearMap.comp
      (tateTwistAdd (V := V) hL n m k h).toLinearMap =
      (tateTwistCoordinates (V := V) (tateLineCoordinate hL) n).toLinearMap.comp
        (tateTwistCoordinates (V := tateTwist F L V n) (tateLineCoordinate hL) m).toLinearMap := by
    ext v l t
    change tateTwistCoordinates (tateLineCoordinate hL) k
      (v ⊗ₜ[F] tateLineMul hL n m k h (l ⊗ₜ[F] t)) =
      tateTwistCoordinates (tateLineCoordinate hL) n
        (tateTwistCoordinates (tateLineCoordinate hL) m ((v ⊗ₜ[F] l) ⊗ₜ[F] t))
    rw [tateTwistCoordinates_tmul, tateTwistCoordinates_tmul, map_smul,
      tateTwistCoordinates_tmul]
    simp only [tateLineMul, tateLineCoordinates_tateLineMulWith, smul_smul]
    rw [mul_comm]
  exact LinearMap.congr_fun heq x

/-- Cup product with an untwisted first argument. -/
noncomputable def tateCupLeft (cup : U →ₗ[F] V →ₗ[F] W) (n : ℤ) :
    U →ₗ[F] tateTwist F L V n →ₗ[F] tateTwist F L W n :=
  LinearMap.mk₂ F (fun u v => tateTwistMap (cup u) n v)
    (by intros; simp [tateTwistMap, TensorProduct.map_add_left])
    (by intros; simp [tateTwistMap, TensorProduct.map_smul_left])
    (by intros; simp) (by intros; simp)

/-- The canonical identification between a twist and the same space at a second twist, after
choosing line coordinates.  Used only in transport proofs. -/
noncomputable def tateTwistChange (c : L ≃ₗ[F] F) (n m : ℤ) :
    tateTwist F L V n ≃ₗ[F] tateTwist F L V m :=
  (tateTwistCoordinates c n).trans (tateTwistCoordinates c m).symm

/-- The twisted cup product is the untwisted-first-argument cup product read through the
coordinates on the twists. -/
theorem tateCup_transport (hL : Module.finrank F L = 1)
    (cup : U →ₗ[F] V →ₗ[F] W) (s n d : ℤ) (h : s + n = d)
    (u : tateTwist F L U s) (v : tateTwist F L V n) :
    tateCup hL cup s n d h u v =
      tateCupLeft cup d (tateTwistCoordinates (tateLineCoordinate hL) s u)
        (tateTwistChange (tateLineCoordinate hL) n d v) := by
  apply (tateTwistCoordinates (tateLineCoordinate hL) d).injective
  simp only [tateCup, tateCupWith, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, tateCupLeft, LinearMap.mk₂_apply]
  rw [tateTwistCoordinates_map]
  simp [tateTwistChange]

/-- Perfectness at arbitrary complementary twists is induced from perfectness of the untwisted
pairing, not an extra duality assumption. -/
theorem tateCup_isPerfPair (hL : Module.finrank F L = 1)
    (cup : U →ₗ[F] V →ₗ[F] W) (d : ℤ)
    (integration : tateTwist F L W d →ₗ[F] F)
    [(tateCupLeft cup d |>.compr₂ integration).IsPerfPair]
    (s n : ℤ) (h : s + n = d) :
    (tateCup hL cup s n d h |>.compr₂ integration).IsPerfPair := by
  let c := tateLineCoordinate hL
  have heq : (tateCup hL cup s n d h).compr₂ integration =
      ((tateCupLeft cup d).compr₂ integration).compl₁₂
        (tateTwistCoordinates c s).toLinearMap (tateTwistChange c n d).toLinearMap :=
    LinearMap.ext₂ fun u v => congrArg integration (tateCup_transport hL cup s n d h u v)
  exact heq ▸ LinearMap.IsPerfPair.compl₁₂ _ _ _

end Twists

section ShiftedPushforward

variable {F : Type uR} [Field F]
variable {L : Type uL} [AddCommGroup L] [Module F L]
variable {HX : ℤ → Type uHX} {HY : ℤ → Type uHY}
variable [∀ i, AddCommGroup (HX i)] [∀ i, Module F (HX i)]
variable [∀ i, AddCommGroup (HY i)] [∀ i, Module F (HY i)]
variable (hL : Module.finrank F L = 1) (d e : ℕ) (q n : ℤ)
variable (cupX : HX (2 * (d : ℤ) - q) →ₗ[F] HX q →ₗ[F] HX (2 * (d : ℤ)))
variable (cupY : HY (2 * (d : ℤ) - q) →ₗ[F]
  HY (q + 2 * ((e : ℤ) - d)) →ₗ[F] HY (2 * (e : ℤ)))
variable (integrationX : tateTwist F L (HX (2 * (d : ℤ))) d →ₗ[F] F)
variable (integrationY : tateTwist F L (HY (2 * (e : ℤ))) e →ₗ[F] F)
variable [(tateCupLeft cupY e |>.compr₂ integrationY).IsPerfPair]
variable (pullback : HY (2 * (d : ℤ) - q) →ₗ[F] HX (2 * (d : ℤ) - q))

/-- Pushforward at arbitrary degree and twist, using only the original cup products, pullback,
traces, one-dimensionality of the line, and the original perfect pairing.  Both shifted cup
products, the shifted pullback, and shifted perfectness are constructed from these data. -/
@[implicit_reducible]
noncomputable def tateTwistedPoincareDualPushforward :
    tateTwist F L (HX q) n →ₗ[F]
      tateTwist F L (HY (q + 2 * ((e : ℤ) - d))) (n + (e : ℤ) - d) := by
  letI := tateCup_isPerfPair hL cupY e integrationY ((d : ℤ) - n)
    (n + (e : ℤ) - d) (by omega)
  exact poincareDualPushforward
    ((tateCup hL cupX ((d : ℤ) - n) n d (by omega)).compr₂ integrationX)
    ((tateCup hL cupY ((d : ℤ) - n) (n + (e : ℤ) - d) e
      (show (d : ℤ) - n + (n + (e : ℤ) - d) = e by omega)).compr₂ integrationY)
    (tateTwistMap pullback ((d : ℤ) - n))

/-- The trace equation, for the induced twisted operations. -/
theorem tateTwistedPoincareDualPushforward_trace_cup
    (b : tateTwist F L (HY (2 * (d : ℤ) - q)) ((d : ℤ) - n))
    (a : tateTwist F L (HX q) n) :
    integrationX (tateCup hL cupX ((d : ℤ) - n) n d (by omega)
      (tateTwistMap pullback ((d : ℤ) - n) b) a) =
    integrationY (tateCup hL cupY ((d : ℤ) - n) (n + (e : ℤ) - d) e
      (show (d : ℤ) - n + (n + (e : ℤ) - d) = e by omega)
      b (tateTwistedPoincareDualPushforward hL d e q n
        cupX cupY integrationX integrationY pullback a)) := by
  let := tateCup_isPerfPair hL cupY e integrationY ((d : ℤ) - n)
    (n + (e : ℤ) - d) (by omega)
  exact poincareDualPushforward_pairing
    ((tateCup hL cupX ((d : ℤ) - n) n d (by omega)).compr₂ integrationX)
    ((tateCup hL cupY ((d : ℤ) - n) (n + (e : ℤ) - d) e
      (show (d : ℤ) - n + (n + (e : ℤ) - d) = e by omega)).compr₂ integrationY)
    (tateTwistMap pullback ((d : ℤ) - n)) b a

/-- The induced trace equation uniquely characterizes the shifted pushforward. -/
theorem eq_tateTwistedPoincareDualPushforward_iff
    (pushforward : tateTwist F L (HX q) n →ₗ[F]
      tateTwist F L (HY (q + 2 * ((e : ℤ) - d))) (n + (e : ℤ) - d)) :
    pushforward = tateTwistedPoincareDualPushforward hL d e q n
      cupX cupY integrationX integrationY pullback ↔
    ∀ b a, integrationX (tateCup hL cupX ((d : ℤ) - n) n d (by omega)
      (tateTwistMap pullback ((d : ℤ) - n) b) a) =
      integrationY (tateCup hL cupY ((d : ℤ) - n) (n + (e : ℤ) - d) e
      (show (d : ℤ) - n + (n + (e : ℤ) - d) = e by omega)
        b (pushforward a)) := by
  let := tateCup_isPerfPair hL cupY e integrationY ((d : ℤ) - n)
    (n + (e : ℤ) - d) (by omega)
  exact eq_poincareDualPushforward_iff _ _ _ pushforward

/-- Transport agreement with the original contragredient of the untwisted pullback.  This is the
extension used for the unit case `q = n = 0`. -/
theorem tateTwistedPoincareDualPushforward_transport :
    tateTwistedPoincareDualPushforward hL d e q n
      cupX cupY integrationX integrationY pullback =
    (tateTwistChange (tateLineCoordinate hL) (n + (e : ℤ) - d) e).symm.toLinearMap.comp
      ((poincareDualPushforward
        ((tateCupLeft cupX d).compr₂ integrationX)
        ((tateCupLeft cupY e).compr₂ integrationY) pullback).comp
          (tateTwistChange (tateLineCoordinate hL) n d).toLinearMap) := by
  symm
  apply (eq_tateTwistedPoincareDualPushforward_iff
    hL d e q n cupX cupY integrationX integrationY pullback _).2
  intro b a
  rw [tateCup_transport, tateCup_transport, tateTwistCoordinates_map]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact poincareDualPushforward_pairing
    ((tateCupLeft cupX d).compr₂ integrationX)
    ((tateCupLeft cupY e).compr₂ integrationY) pullback _ _

/-- The shifted pushforward is exactly the original Poincaré-dual pushforward tensored with the
identity on `F(n-d)`, under the canonical addition-of-twists identifications.  Thus the trace
construction and the transported extension agree. -/
theorem tateTwistedPoincareDualPushforward_tensor :
    tateTwistedPoincareDualPushforward hL d e q n
      cupX cupY integrationX integrationY pullback =
    (tateTwistAdd hL e (n - d) (n + (e : ℤ) - d) (by omega)).toLinearMap.comp
      ((tateTwistMap (poincareDualPushforward
        ((tateCupLeft cupX d).compr₂ integrationX)
        ((tateCupLeft cupY e).compr₂ integrationY) pullback) (n - d)).comp
          (tateTwistAdd hL d (n - d) n (by omega)).symm.toLinearMap) := by
  rw [tateTwistedPoincareDualPushforward_transport]
  refine LinearMap.ext fun a => ?_
  apply (tateTwistCoordinates (tateLineCoordinate hL) (n + (e : ℤ) - d)).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tateTwistCoordinates_add, tateTwistCoordinates_map]
  simp only [tateTwistChange, LinearEquiv.symm_trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  congr 2
  apply (tateTwistCoordinates (V := HX q) (tateLineCoordinate hL) d).injective
  rw [LinearEquiv.apply_symm_apply, ← tateTwistCoordinates_add hL d (n - d) n (by omega),
    LinearEquiv.apply_symm_apply]

/-- Pushforward whose source is the untwisted cohomology group.  This composes with the canonical
zero-twist identification; in degree zero it accepts the unit `1 : H⁰(X)` directly. -/
noncomputable def poincareDualPushforwardFromUntwisted :
    HX q →ₗ[F] tateTwist F L (HY (q + 2 * ((e : ℤ) - d))) ((e : ℤ) - d) :=
  (congrArg (fun m => HX q →ₗ[F] tateTwist F L (HY (q + 2 * ((e : ℤ) - d))) m)
    (show 0 + (e : ℤ) - d = (e : ℤ) - d by omega)).mp
    ((tateTwistedPoincareDualPushforward hL d e q 0
      cupX cupY integrationX integrationY pullback).comp
        (tateTwistZero (F := F) (L := L)).symm.toLinearMap)

end ShiftedPushforward

/-- The Poincaré-dual pushforward between the complementary graded pieces `H²ᵈ⁻ⁱ(X)(d)` and
`H²ᵉ⁻ⁱ(Y)(e)`.  The two pairings are obtained by following cup product with the appropriate
trace map.

The first index of `HX` and `HY` is cohomological degree and the second is Tate twist. -/
noncomputable abbrev gradedPoincareDualPushforward
    {R : Type uR} [CommSemiring R]
    {HX : ℤ → ℤ → Type uHX} {HY : ℤ → ℤ → Type uHY}
    (d e : ℕ) (i : ℤ)
    [AddCommMonoid (HX i 0)] [Module R (HX i 0)]
    [AddCommMonoid (HX (2 * (d : ℤ) - i) d)] [Module R (HX (2 * (d : ℤ) - i) d)]
    [AddCommMonoid (HX (2 * (d : ℤ)) d)] [Module R (HX (2 * (d : ℤ)) d)]
    [AddCommMonoid (HY i 0)] [Module R (HY i 0)]
    [AddCommMonoid (HY (2 * (e : ℤ) - i) e)] [Module R (HY (2 * (e : ℤ) - i) e)]
    [AddCommMonoid (HY (2 * (e : ℤ)) e)] [Module R (HY (2 * (e : ℤ)) e)]
    (cupX : HX i 0 →ₗ[R] HX (2 * (d : ℤ) - i) d →ₗ[R] HX (2 * (d : ℤ)) d)
    (cupY : HY i 0 →ₗ[R] HY (2 * (e : ℤ) - i) e →ₗ[R] HY (2 * (e : ℤ)) e)
    (integrationX : HX (2 * (d : ℤ)) d →ₗ[R] R)
    (integrationY : HY (2 * (e : ℤ)) e →ₗ[R] R)
    [(cupY.compr₂ integrationY).IsPerfPair]
    (pullback : HY i 0 →ₗ[R] HX i 0) :
    HX (2 * (d : ℤ) - i) d →ₗ[R] HY (2 * (e : ℤ) - i) e :=
  poincareDualPushforward (cupX.compr₂ integrationX)
    (cupY.compr₂ integrationY) pullback

/-- The cup-product-and-trace formula defining the pushforward on complementary graded
pieces. -/
theorem gradedPoincareDualPushforward_trace_cup
    {R : Type uR} [CommSemiring R]
    {HX : ℤ → ℤ → Type uHX} {HY : ℤ → ℤ → Type uHY}
    (d e : ℕ) (i : ℤ)
    [AddCommMonoid (HX i 0)] [Module R (HX i 0)]
    [AddCommMonoid (HX (2 * (d : ℤ) - i) d)] [Module R (HX (2 * (d : ℤ) - i) d)]
    [AddCommMonoid (HX (2 * (d : ℤ)) d)] [Module R (HX (2 * (d : ℤ)) d)]
    [AddCommMonoid (HY i 0)] [Module R (HY i 0)]
    [AddCommMonoid (HY (2 * (e : ℤ) - i) e)] [Module R (HY (2 * (e : ℤ) - i) e)]
    [AddCommMonoid (HY (2 * (e : ℤ)) e)] [Module R (HY (2 * (e : ℤ)) e)]
    (cupX : HX i 0 →ₗ[R] HX (2 * (d : ℤ) - i) d →ₗ[R] HX (2 * (d : ℤ)) d)
    (cupY : HY i 0 →ₗ[R] HY (2 * (e : ℤ) - i) e →ₗ[R] HY (2 * (e : ℤ)) e)
    (integrationX : HX (2 * (d : ℤ)) d →ₗ[R] R)
    (integrationY : HY (2 * (e : ℤ)) e →ₗ[R] R)
    [(cupY.compr₂ integrationY).IsPerfPair]
    (pullback : HY i 0 →ₗ[R] HX i 0) (b : HY i 0)
    (a : HX (2 * (d : ℤ) - i) d) :
    integrationX (cupX (pullback b) a) =
      integrationY (cupY b
        (gradedPoincareDualPushforward d e i cupX cupY integrationX integrationY pullback a)) :=
  poincareDualPushforward_pairing (cupX.compr₂ integrationX)
    (cupY.compr₂ integrationY) pullback b a

/-- Simplification-oriented cup-product-and-trace formula for the pushforward on complementary
graded pieces. -/
@[simp]
theorem trace_cup_gradedPoincareDualPushforward
    {R : Type uR} [CommSemiring R]
    {HX : ℤ → ℤ → Type uHX} {HY : ℤ → ℤ → Type uHY}
    (d e : ℕ) (i : ℤ)
    [AddCommMonoid (HX i 0)] [Module R (HX i 0)]
    [AddCommMonoid (HX (2 * (d : ℤ) - i) d)] [Module R (HX (2 * (d : ℤ) - i) d)]
    [AddCommMonoid (HX (2 * (d : ℤ)) d)] [Module R (HX (2 * (d : ℤ)) d)]
    [AddCommMonoid (HY i 0)] [Module R (HY i 0)]
    [AddCommMonoid (HY (2 * (e : ℤ) - i) e)] [Module R (HY (2 * (e : ℤ) - i) e)]
    [AddCommMonoid (HY (2 * (e : ℤ)) e)] [Module R (HY (2 * (e : ℤ)) e)]
    (cupX : HX i 0 →ₗ[R] HX (2 * (d : ℤ) - i) d →ₗ[R] HX (2 * (d : ℤ)) d)
    (cupY : HY i 0 →ₗ[R] HY (2 * (e : ℤ) - i) e →ₗ[R] HY (2 * (e : ℤ)) e)
    (integrationX : HX (2 * (d : ℤ)) d →ₗ[R] R)
    (integrationY : HY (2 * (e : ℤ)) e →ₗ[R] R)
    [(cupY.compr₂ integrationY).IsPerfPair]
    (pullback : HY i 0 →ₗ[R] HX i 0) (b : HY i 0)
    (a : HX (2 * (d : ℤ) - i) d) :
    integrationY (cupY b
        (gradedPoincareDualPushforward d e i cupX cupY integrationX integrationY pullback a)) =
      integrationX (cupX (pullback b) a) :=
  (gradedPoincareDualPushforward_trace_cup d e i cupX cupY integrationX integrationY
    pullback b a).symm

/-- A map between complementary graded pieces is the Poincaré-dual pushforward if and only if it
satisfies the trace formula. -/
theorem eq_gradedPoincareDualPushforward_iff
    {R : Type uR} [CommSemiring R]
    {HX : ℤ → ℤ → Type uHX} {HY : ℤ → ℤ → Type uHY}
    (d e : ℕ) (i : ℤ)
    [AddCommMonoid (HX i 0)] [Module R (HX i 0)]
    [AddCommMonoid (HX (2 * (d : ℤ) - i) d)] [Module R (HX (2 * (d : ℤ) - i) d)]
    [AddCommMonoid (HX (2 * (d : ℤ)) d)] [Module R (HX (2 * (d : ℤ)) d)]
    [AddCommMonoid (HY i 0)] [Module R (HY i 0)]
    [AddCommMonoid (HY (2 * (e : ℤ) - i) e)] [Module R (HY (2 * (e : ℤ) - i) e)]
    [AddCommMonoid (HY (2 * (e : ℤ)) e)] [Module R (HY (2 * (e : ℤ)) e)]
    (cupX : HX i 0 →ₗ[R] HX (2 * (d : ℤ) - i) d →ₗ[R] HX (2 * (d : ℤ)) d)
    (cupY : HY i 0 →ₗ[R] HY (2 * (e : ℤ) - i) e →ₗ[R] HY (2 * (e : ℤ)) e)
    (integrationX : HX (2 * (d : ℤ)) d →ₗ[R] R)
    (integrationY : HY (2 * (e : ℤ)) e →ₗ[R] R)
    [(cupY.compr₂ integrationY).IsPerfPair]
    (pullback : HY i 0 →ₗ[R] HX i 0)
    (pushforward : HX (2 * (d : ℤ) - i) d →ₗ[R] HY (2 * (e : ℤ) - i) e) :
    pushforward =
        gradedPoincareDualPushforward d e i cupX cupY integrationX integrationY pullback ↔
      ∀ b a, integrationX (cupX (pullback b) a) =
        integrationY (cupY b (pushforward a)) :=
  eq_poincareDualPushforward_iff (cupX.compr₂ integrationX)
    (cupY.compr₂ integrationY) pullback pushforward

end Stacks.WeilCohomology

end
