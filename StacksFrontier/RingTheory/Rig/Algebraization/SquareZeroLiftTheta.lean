module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Multiplication by a square-zero ideal of the base

Let `N` be an ideal of a commutative ring `R` with `N ^ 2 = 0` and let `B` be an `R`-algebra.
For `n ∈ N` and `b ∈ B` the product `n b` only depends on `b` modulo `N B`, so multiplication
gives an `R`-bilinear map `(B ⧸ N B) × N → B`. Composing with an `R`-algebra map
`λ : X → B ⧸ N B` gives the `R`-linear map `θ_λ : X ⊗[R] N → B`, `x ⊗ n ↦ n · b` for any lift `b`
of `λ x`. This file records the basic properties of `θ_λ`: naturality, multiplicativity, its
values lie in `N B`, and, when `B` is flat over `R` and `λ` identifies `B ⧸ N B` with a
localization of `X`, a description of its kernel and of its image.

## Main definitions

* `Rig.SquareZeroLift.multQ`: the multiplication `(B ⧸ N B) →ₗ[R] N →ₗ[R] B`.
* `Rig.SquareZeroLift.theta`: the map `θ_λ : X ⊗[R] N →ₗ[R] B`.
* `Rig.SquareZeroLift.redMap`: the map `B ⧸ N B → B' ⧸ N B'` induced by an algebra map.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct

universe u v w

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)

section Basic

variable (B : Type v) [CommRing B] [Algebra R B]

/-- Multiplication by the elements of `N`, as a `B`-linear map `B → Hom_R(N, B)`. -/
def mulN : B →ₗ[B] (N →ₗ[R] B) where
  toFun b := (LinearMap.lsmul R B).flip b ∘ₗ N.subtype
  map_add' b c := by ext n; simp
  map_smul' c b := by ext n; simp

/-- `mulN N B b` sends `n ∈ N` to `n • b`. -/
@[simp]
theorem mulN_apply (b : B) (n : N) : mulN N B b n = (n : R) • b := rfl

include hN in
/-- If `N ^ 2 = 0`, then `N B` lies in the kernel of `mulN N B`. -/
theorem le_ker_mulN : N.map (algebraMap R B) ≤ LinearMap.ker (mulN N B) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  simp only [Ideal.mem_comap, LinearMap.mem_ker]
  ext n
  have hnx : (n : R) * x = 0 := by
    have : (n : R) * x ∈ N ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul n.2 hx
    rwa [hN] at this
  simp [Algebra.smul_def, ← map_mul, hnx]

/-- Multiplication `(B ⧸ N B) × N → B`, well defined because `N ^ 2 = 0`. -/
noncomputable def multQ : (B ⧸ N.map (algebraMap R B)) →ₗ[R] N →ₗ[R] B :=
  ((N.map (algebraMap R B)).liftQ (mulN N B) (le_ker_mulN N hN B)).restrictScalars R

/-- `multQ` sends the class of `b` and `n ∈ N` to `n • b`. -/
@[simp]
theorem multQ_mk (b : B) (n : N) :
    multQ N hN B (Ideal.Quotient.mk _ b) n = (n : R) • b := rfl

/-- Multiplication `(B ⧸ N B) ⊗[R] N → B`. -/
noncomputable def multT : (B ⧸ N.map (algebraMap R B)) ⊗[R] N →ₗ[R] B :=
  TensorProduct.lift (multQ N hN B)

/-- Multiplication `B ⊗[R] N → B`. -/
noncomputable def mulT0 : B ⊗[R] N →ₗ[R] B :=
  TensorProduct.lift ((mulN N B).restrictScalars R)

/-- `mulT0` is the composite `B ⊗[R] N → B ⊗[R] R ≃ B` of the inclusion `N → R` with the
right unitor. -/
theorem mulT0_eq : mulT0 N B = (TensorProduct.rid R B).toLinearMap ∘ₗ N.subtype.lTensor B := by
  ext b n
  simp [mulT0]

/-- Precomposing `multT` with the quotient map `B ⊗[R] N → (B ⧸ N B) ⊗[R] N` gives `mulT0`. -/
theorem multT_comp_mk :
    multT N hN B ∘ₗ (Ideal.Quotient.mkₐ R (N.map (algebraMap R B))).toLinearMap.rTensor N =
      mulT0 N B := by
  ext b n
  simp [multT, mulT0]

/-- `mulT0` is `B`-linear: `mulT0 (c • z) = c * mulT0 z`. -/
theorem mulT0_smul (c : B) (z : B ⊗[R] N) : mulT0 N B (c • z) = c * mulT0 N B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [mulT0]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

/-- If `B` is flat over `R`, then `multT : (B ⧸ N B) ⊗[R] N → B` is injective. -/
theorem multT_injective [Module.Flat R B] : Function.Injective (multT N hN B) := by
  have h0 : Function.Injective (mulT0 N B) := by
    rw [mulT0_eq]
    exact (TensorProduct.rid R B).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨z', rfl⟩ := LinearMap.rTensor_surjective N
    (g := (Ideal.Quotient.mkₐ R (N.map (algebraMap R B))).toLinearMap)
    (Ideal.Quotient.mkₐ_surjective R (N.map (algebraMap R B))) z
  have : mulT0 N B z' = 0 := by rw [← multT_comp_mk N hN B, LinearMap.comp_apply, hz]
  rw [h0 (this.trans (map_zero _).symm), map_zero]

/-- Every element of `N B` is a value of `mulT0 : B ⊗[R] N → B`. -/
theorem exists_mulT0_eq (y : B) (hy : y ∈ N.map (algebraMap R B)) :
    ∃ z, mulT0 N B z = y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, hn, rfl⟩ := hx
    exact ⟨1 ⊗ₜ ⟨n, hn⟩, by simp [mulT0, Algebra.algebraMap_eq_smul_one]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨c • a, mulT0_smul N B c a⟩

/-- Every element of `N B` is a value of `multT : (B ⧸ N B) ⊗[R] N → B`. -/
theorem exists_multT_eq (y : B) (hy : y ∈ N.map (algebraMap R B)) :
    ∃ z, multT N hN B z = y := by
  obtain ⟨z, rfl⟩ := exists_mulT0_eq N B y hy
  exact ⟨_, LinearMap.congr_fun (multT_comp_mk N hN B) z⟩

/-- The values of `multT` lie in `N B`. -/
theorem multT_mem (z : (B ⧸ N.map (algebraMap R B)) ⊗[R] N) :
    multT N hN B z ∈ N.map (algebraMap R B) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [multT, TensorProduct.lift.tmul, multQ_mk, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ n.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end Basic

/-- An element whose image in an algebra is a unit acts invertibly on it. -/
theorem isUnit_end_of_isUnit {B : Type v} [CommRing B] [Algebra R B] {r : R}
    (h : IsUnit (algebraMap R B r)) : IsUnit (algebraMap R (Module.End R B) r) := by
  rw [Module.End.isUnit_iff]
  obtain ⟨u, hu⟩ := h
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(↑u⁻¹ : B) * y, ?_⟩⟩
  · simp only [Module.algebraMap_end_apply, Algebra.smul_def, ← hu] at hxy
    simpa using congrArg ((↑u⁻¹ : B) * ·) hxy
  · simp [Module.algebraMap_end_apply, Algebra.smul_def, ← hu, ← mul_assoc]

section Theta

variable {X : Type w} [CommRing X] [Algebra R X]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The map `θ_λ : X ⊗[R] N → B`, `x ⊗ n ↦ n · b` for any lift `b` of `λ x`. -/
noncomputable def theta (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) : X ⊗[R] N →ₗ[R] B :=
  multT N hN B ∘ₗ L.toLinearMap.rTensor N

/-- `θ_λ (x ⊗ n) = n • b` for any `b ∈ B` lifting `λ x`. -/
theorem theta_tmul (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) (x : X) (n : N) (b : B)
    (hb : Ideal.Quotient.mk _ b = L x) : theta N hN L (x ⊗ₜ n) = (n : R) • b := by
  simp [theta, multT, ← hb]

/-- The values of `θ_λ` lie in `N B`. -/
theorem theta_mem (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) (z : X ⊗[R] N) :
    theta N hN L z ∈ N.map (algebraMap R B) :=
  multT_mem N hN B _

/-- `θ_λ (x x' ⊗ n) = b · θ_λ (x' ⊗ n)` for any `b ∈ B` lifting `λ x`. -/
theorem theta_mul (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) (x x' : X) (n : N) (b : B)
    (hb : Ideal.Quotient.mk _ b = L x) :
    theta N hN L ((x * x') ⊗ₜ n) = b * theta N hN L (x' ⊗ₜ n) := by
  obtain ⟨b', hb'⟩ := Ideal.Quotient.mk_surjective (L x')
  rw [theta_tmul N hN L x' n b' hb', theta_tmul N hN L (x * x') n (b * b')
    (by rw [map_mul, hb, hb', map_mul]), mul_smul_comm]

/-- The map `B ⧸ N B → B' ⧸ N B'` induced by an algebra map `B → B'`. -/
noncomputable def redMap {B' : Type*} [CommRing B'] [Algebra R B'] (β : B →ₐ[R] B') :
    B ⧸ N.map (algebraMap R B) →ₐ[R] B' ⧸ N.map (algebraMap R B') :=
  Ideal.quotientMapₐ _ β (by
    rw [Ideal.map_le_iff_le_comap]
    intro n hn
    simp only [Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hn)

/-- `redMap β` sends the class of `b` to the class of `β b`. -/
@[simp]
theorem redMap_mk {B' : Type*} [CommRing B'] [Algebra R B'] (β : B →ₐ[R] B') (b : B) :
    redMap N β (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (β b) := rfl

/-- Naturality of `θ` in `B`: if `λ' = redMap β ∘ λ` for an algebra map `β : B → B'`, then
`β ∘ θ_λ = θ_λ'`. -/
theorem theta_naturality {B' : Type*} [CommRing B'] [Algebra R B'] (β : B →ₐ[R] B')
    (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) (L' : X →ₐ[R] B' ⧸ N.map (algebraMap R B'))
    (h : (redMap N β).comp L = L') (z : X ⊗[R] N) :
    β (theta N hN L z) = theta N hN L' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n =>
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (L x)
    rw [theta_tmul N hN L x n b hb, theta_tmul N hN L' x n (β b)
      (by rw [← h, AlgHom.comp_apply, ← hb, redMap_mk]), map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- Naturality of `θ` in `X`: `θ_{λ ∘ γ} = θ_λ ∘ (γ ⊗ id_N)` for an algebra map `γ : X → X'`. -/
theorem theta_comp {X' : Type*} [CommRing X'] [Algebra R X'] (γ : X →ₐ[R] X')
    (L : X' →ₐ[R] B ⧸ N.map (algebraMap R B)) (z : X ⊗[R] N) :
    theta N hN (L.comp γ) z = theta N hN L (γ.toLinearMap.rTensor N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp [theta]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- `θ_λ` is `multT` composed with `λ ⊗ id_N`, the latter as a map of `X`-modules. -/
theorem theta_eq_multT_rTensor (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) (z : X ⊗[R] N) :
    theta N hN L z =
      multT N hN B (TensorProduct.AlgebraTensorModule.rTensor R N L.toLinearMap z) := rfl

/-- If `λ` is a localization at the powers of `r` and `B` is flat, then the kernel of `θ_λ`
consists of `r`-power torsion. -/
theorem exists_pow_smul_eq_zero_of_theta_eq_zero [Module.Flat R B] (r : R)
    (L : X →ₐ[R] B ⧸ N.map (algebraMap R B))
    [IsLocalizedModule (Submonoid.powers r) L.toLinearMap] (z : X ⊗[R] N)
    (hz : theta N hN L z = 0) : ∃ n : ℕ, r ^ n • z = 0 := by
  rw [theta_eq_multT_rTensor] at hz
  have h1 := multT_injective N hN B (hz.trans (map_zero _).symm)
  rw [← map_zero (TensorProduct.AlgebraTensorModule.rTensor R N L.toLinearMap)] at h1
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) h1
  exact ⟨n, by simpa [Submonoid.smul_def] using hc⟩

/-- In a localization at the powers of `r`, every element becomes a value of the localization map
after multiplication by a power of `r`. -/
private theorem exists_pow_smul_eq {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (r : R) (f : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers r) f] (m : M') : ∃ (z : M) (n : ℕ), r ^ n • m = f z := by
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalizedModule.surj (Submonoid.powers r) f m
  exact ⟨z, n, hz⟩

/-- In a localization at the powers of `r`, multiplication by `r ^ n` is bijective. -/
private theorem pow_smul_bijective {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (r : R) (f : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers r) f] (n : ℕ) :
    Function.Bijective (fun m : M' => r ^ n • m) := by
  have hu := IsLocalizedModule.map_units f (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
  rw [Module.End.isUnit_iff] at hu
  exact hu

/-- If `λ` is a localization at the powers of `r`, then every element of `N B` becomes a value of
`θ_λ` after multiplication by a power of `r`. -/
theorem exists_theta_eq_pow_mul (r : R) (L : X →ₐ[R] B ⧸ N.map (algebraMap R B))
    [IsLocalizedModule (Submonoid.powers r) L.toLinearMap]
    (y : B) (hy : y ∈ N.map (algebraMap R B)) :
    ∃ (z : X ⊗[R] N) (n : ℕ), algebraMap R B r ^ n * y = theta N hN L z := by
  obtain ⟨w, rfl⟩ := exists_multT_eq N hN B y hy
  obtain ⟨z, n, hz⟩ := exists_pow_smul_eq r
    (TensorProduct.AlgebraTensorModule.rTensor R N L.toLinearMap) w
  refine ⟨z, n, ?_⟩
  rw [theta_eq_multT_rTensor, ← hz, map_smul, ← map_pow, Algebra.smul_def]

/-- Units lift along a surjection with square-zero kernel. -/
theorem isUnit_of_isUnit_quotient {B : Type v} [CommRing B] (J : Ideal B) (hJ : J ^ 2 = ⊥)
    {b : B} (h : IsUnit (Ideal.Quotient.mk J b)) : IsUnit b := by
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (((h.unit⁻¹ : (B ⧸ J)ˣ)) : B ⧸ J)
  have h1 : Ideal.Quotient.mk J (b * c) = 1 := by rw [map_mul, hc, IsUnit.mul_val_inv]
  have h2 : b * c - 1 ∈ J := Ideal.Quotient.eq.mp (by rw [h1, map_one])
  have h3 : (b * c - 1) * (b * c - 1) = 0 := by
    have : (b * c - 1) * (b * c - 1) ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul h2 h2
    rwa [hJ] at this
  refine IsUnit.of_mul_eq_one (c * (1 - (b * c - 1))) ?_
  have h4 : b * (c * (1 - (b * c - 1))) = 1 - (b * c - 1) * (b * c - 1) := by ring
  rw [h4, h3, sub_zero]

/-- Comparison of a localization of `X ⊗[R] N` with `B`, induced by `θ_λ`. -/
noncomputable def cmp (r : R) (hr : IsUnit (algebraMap R B r))
    (L : X →ₐ[R] B ⧸ N.map (algebraMap R B)) {M' : Type*} [AddCommGroup M'] [Module R M']
    (ℓ : X ⊗[R] N →ₗ[R] M') [IsLocalizedModule (Submonoid.powers r) ℓ] : M' →ₗ[R] B :=
  IsLocalizedModule.lift (Submonoid.powers r) ℓ (theta N hN L) (by
    rintro ⟨_, n, rfl⟩
    exact isUnit_end_of_isUnit (by rw [map_pow]; exact hr.pow n))

variable (r : R) (hr : IsUnit (algebraMap R B r)) (L : X →ₐ[R] B ⧸ N.map (algebraMap R B))
  {M' : Type*} [AddCommGroup M'] [Module R M'] (ℓ : X ⊗[R] N →ₗ[R] M')
  [IsLocalizedModule (Submonoid.powers r) ℓ]

/-- `cmp` sends the image `ℓ z` of `z ∈ X ⊗[R] N` to `θ_λ z`. -/
theorem cmp_apply (z : X ⊗[R] N) : cmp N hN r hr L ℓ (ℓ z) = theta N hN L z :=
  IsLocalizedModule.lift_apply _ _ _ _ z

/-- The values of `cmp` lie in `N B`. -/
theorem cmp_mem (m : M') : cmp N hN r hr L ℓ m ∈ N.map (algebraMap R B) := by
  obtain ⟨z, n, hz⟩ := exists_pow_smul_eq r ℓ m
  have h := cmp_apply N hN r hr L ℓ z
  rw [← hz, map_smul, Algebra.smul_def, map_pow] at h
  have hu : IsUnit (algebraMap R B r ^ n) := hr.pow n
  have : cmp N hN r hr L ℓ m = ((hu.unit⁻¹ : Bˣ) : B) * theta N hN L z := by
    rw [← h, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (theta_mem N hN L z)

/-- If `B` is flat over `R` and `λ` is a localization at the powers of `r`, then `cmp` is
injective. -/
theorem cmp_injective [Module.Flat R B] [IsLocalizedModule (Submonoid.powers r) L.toLinearMap] :
    Function.Injective (cmp N hN r hr L ℓ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  obtain ⟨z, n, hz⟩ := exists_pow_smul_eq r ℓ m
  have h : theta N hN L z = 0 := by
    rw [← cmp_apply N hN r hr L ℓ, ← hz, map_smul, hm, smul_zero]
  obtain ⟨e, he⟩ := exists_pow_smul_eq_zero_of_theta_eq_zero N hN r L z h
  have h2 : r ^ e • r ^ n • m = 0 := by rw [hz, ← map_smul, he, map_zero]
  rw [smul_smul, ← pow_add] at h2
  exact (pow_smul_bijective r ℓ (e + n)).1 (h2.trans (smul_zero _).symm)

/-- If `λ` is a localization at the powers of `r`, then every element of `N B` is a value of
`cmp`. -/
theorem exists_cmp_eq (y : B) (hy : y ∈ N.map (algebraMap R B))
    [IsLocalizedModule (Submonoid.powers r) L.toLinearMap] :
    ∃ m, cmp N hN r hr L ℓ m = y := by
  obtain ⟨z, n, hz⟩ := exists_theta_eq_pow_mul N hN r L y hy
  obtain ⟨m, hm⟩ := (pow_smul_bijective r ℓ n).2 (ℓ z)
  refine ⟨m, ?_⟩
  have h := cmp_apply N hN r hr L ℓ z
  rw [← hm, ← hz] at h
  rw [map_smul, Algebra.smul_def, map_pow] at h
  exact (hr.pow n).mul_left_cancel h

end Theta

end Rig.SquareZeroLift

end
