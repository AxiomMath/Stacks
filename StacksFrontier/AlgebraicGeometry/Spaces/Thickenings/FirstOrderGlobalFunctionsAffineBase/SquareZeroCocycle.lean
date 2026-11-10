module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Correcting a lift along a square-zero thickening of a Čech nerve

Let `C → D₀` be faithfully flat and let `D → D₀` be a surjection of rings with square-zero
kernel.  Think of `D₀` as the ring of an affine étale covering `W₀ → X₀ = Spec C`, of `D` as the
ring of an étale space `W` of which `W₀` is a first-order thickening, and of `E`, `E₂` as the rings
of `W ×_U W` and `W ×_U W ×_U W` for a space `U` with `W ⟶ U` étale, with the reductions
`E → E₀`, `E₂ → E₂₀` to the corresponding fibre products over `X₀`.  An element `a` of `D`
whose reduction is equalized by the two projections `D₀ ⇉ E₀` then differs, by an element of the
kernel of `D → D₀`, from an element equalized by the two projections `D ⇉ E` themselves.

This is the vanishing of the first Čech cohomology of the quasi-coherent module `ker(D → D₀)`
along the faithfully flat covering `C → D₀`, and the proof is the one by faithfully flat descent:
after base change along `C → D₀` the covering acquires a section, and the cocycle becomes a
coboundary.

## Main results

* `SquareZeroCech.mem_range_of_lTensor_eq`: membership in the range of a linear map descends from
  a base-changed square whose comparison maps are only required to be a surjective, respectively
  an injective, function.
* `SquareZeroCech.Data`: the rings and maps of the two truncated Čech nerves, with the
  cartesian-square conditions that relate them.
* `SquareZeroCech.Data.exists_sub_mem_ker_eq`: **the correction**: an element of `D` with
  equalized reduction is, up to the kernel of `D → D₀`, equalized by `s, t : D ⇉ E`.

## Implementation notes

The kernels of the reductions are modules over the reduced rings because they square to zero.
That module structure is put on the kernel subtype by choosing a lift, through
`Function.Surjective.moduleLeft`; its value on any other lift is the same, which is
`SquareZeroCech.kerSMul_val`.  These structures are `def`s, installed with `letI` where they are
used, and never instances.

The descent step `SquareZeroCech.mem_range_of_lTensor_eq` is the argument of
`TensorProduct.mem_range_of_lTensor_square` with its comparison maps weakened from linear maps to
functions: the second comparison here lands in the ring `E₂`, which is not a module over `C`.
-/

@[expose] public noncomputable section

open TensorProduct

namespace SquareZeroCech

/-! ### The descent step -/

/-- **Membership in the image of `φ` descends from the base-changed square**, with the comparison
maps only a surjective and an injective function.  If `ι₀ : B ⊗ M₀ → M₁` is surjective,
`ι₁ : B ⊗ M₁ → P` is injective and `ι₁ ∘ (B ⊗ φ) = ψ ∘ ι₀`, then every `d` with
`ψ d = ι₁ (1 ⊗ d)` is in the range of `φ`. -/
theorem mem_range_of_lTensor_eq {C B M₀ M₁ P : Type*} [CommRing C] [CommRing B] [Algebra C B]
    [Module.FaithfullyFlat C B] [AddCommGroup M₀] [Module C M₀] [AddCommGroup M₁] [Module C M₁]
    (φ : M₀ →ₗ[C] M₁) (ψ : M₁ → P) (ι₀ : B ⊗[C] M₀ → M₁) (ι₁ : B ⊗[C] M₁ → P)
    (h₀ : Function.Surjective ι₀) (h₁ : Function.Injective ι₁)
    (hc : ∀ y, ι₁ (φ.lTensor B y) = ψ (ι₀ y)) (d : M₁) (hd : ψ d = ι₁ ((1 : B) ⊗ₜ d)) :
    d ∈ LinearMap.range φ := by
  obtain ⟨y, rfl⟩ := h₀ d
  have hy : φ.lTensor B y = (1 : B) ⊗ₜ ι₀ y := h₁ (by rw [hc, hd])
  let π := (LinearMap.range φ).mkQ
  have h0 : (π.comp φ).lTensor B y = 0 := by
    have : π.comp φ = 0 := by
      ext x
      simp [π]
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have h1 : (1 : B) ⊗ₜ[C] π (ι₀ y) = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hy] at h0
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h1
  simpa [π] using h1

/-- Elements of the image of a square-zero ideal under a ring map multiply to zero. -/
private theorem mul_eq_zero_of_mem_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {I : Ideal A} (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) {x y : B} (hx : x ∈ I.map f)
    (hy : y ∈ I.map f) : x * y = 0 := by
  have hI' : I * I = ⊥ :=
    le_bot_iff.1 (Ideal.mul_le.2 fun x hx y hy => by
      rw [hI x hx y hy]; exact Submodule.zero_mem _)
  have h : x * y ∈ I.map f * I.map f := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul, hI', Ideal.map_bot] at h
  exact (Submodule.mem_bot _).1 h

/-! ### The kernel of a square-zero surjection as a module over the quotient -/

section Kernel

variable {R R₀ : Type*} [CommRing R] [CommRing R₀] {π : R →+* R₀} (hπ : Function.Surjective π)

/-- The action of `R₀` on the kernel of `π : R → R₀` through a chosen lift. -/
abbrev kerSMul : SMul R₀ (RingHom.ker π) :=
  ⟨fun r m => ⟨Function.surjInv hπ r * m, Ideal.mul_mem_left _ _ m.2⟩⟩

variable (hsq : ∀ x ∈ RingHom.ker π, ∀ y ∈ RingHom.ker π, x * y = 0)
include hsq

/-- Two lifts of the same element act in the same way on the kernel. -/
theorem mul_eq_mul_of_eq {x x' : R} (h : π x = π x') (m : RingHom.ker π) :
    x * (m : R) = x' * m := by
  have hk : x - x' ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, h, sub_self]
  have := hsq _ hk _ m.2
  rwa [sub_mul, sub_eq_zero] at this

/-- The action of `R₀` on the kernel is multiplication by any lift. -/
theorem kerSMul_val (r : R₀) (m : RingHom.ker π) (x : R) (hx : π x = r) :
    ((letI := kerSMul hπ; r • m : RingHom.ker π) : R) = x * m :=
  mul_eq_mul_of_eq hsq (by rw [Function.surjInv_eq hπ, hx]) m

/-- **The kernel of a square-zero surjection is a module over the quotient.** -/
abbrev kerModule : Module R₀ (RingHom.ker π) :=
  letI := kerSMul hπ
  hπ.moduleLeft π fun c m => Subtype.ext <| by
    rw [kerSMul_val hπ hsq (π c) m c rfl]
    rfl

/-- In the module structure `kerModule`, `r • m` is the product of `m` with any lift of `r`. -/
theorem kerModule_val (r : R₀) (m : RingHom.ker π) (x : R) (hx : π x = r) :
    ((letI := kerModule hπ hsq; r • m : RingHom.ker π) : R) = x * m :=
  kerSMul_val hπ hsq r m x hx

/-- The kernel of a square-zero surjection onto an algebra over `C` is a `C`-module. -/
abbrev kerModuleOver (C : Type*) [CommRing C] [Algebra C R₀] : Module C (RingHom.ker π) :=
  letI := kerModule hπ hsq
  Module.compHom _ (algebraMap C R₀)

/-- In the module structure `kerModuleOver`, `c • m` is the product of `m` with any lift of the
image of `c` in `R₀`. -/
theorem kerModuleOver_val (C : Type*) [CommRing C] [Algebra C R₀] (c : C) (m : RingHom.ker π)
    (x : R) (hx : π x = algebraMap C R₀ c) :
    ((letI := kerModuleOver hπ hsq C; c • m : RingHom.ker π) : R) = x * m :=
  kerSMul_val hπ hsq _ m x hx

end Kernel

/-! ### The data of two truncated Čech nerves -/

/-- The rings and maps of a truncated Čech nerve `D ⇉ E ⇛ E₂` and of its reduction
`D₀ ⇉ E₀ ⇛ E₂₀`, with the conditions under which a lift of an equalized element can be corrected.

The fields `ker_πE` and `ker_πE₂` say that the reductions of `E` and `E₂` are the base changes of
the reductions of `D` and `E` along `t` and `d₀`; `gen` and `push` say that `E₀` and `E₂₀` are the
tensor products `D₀ ⊗_C D₀` and `D₀ ⊗_C E₀` (only surjectivity is needed of the first). -/
structure Data (C D E E₂ D₀ E₀ E₂₀ : Type*) [CommRing C] [CommRing D] [CommRing E] [CommRing E₂]
    [CommRing D₀] [CommRing E₀] [CommRing E₂₀] [Algebra C D₀] [Algebra C E₀] [Algebra C E₂₀] where
  /-- The reduction of `D`. -/
  πD : D →+* D₀
  /-- The reduction of `E`. -/
  πE : E →+* E₀
  /-- The reduction of `E₂`. -/
  πE₂ : E₂ →+* E₂₀
  surj_πD : Function.Surjective πD
  surj_πE : Function.Surjective πE
  /-- The first projection `W ×_U W ⟶ W`, on rings. -/
  s : D →+* E
  /-- The second projection `W ×_U W ⟶ W`, on rings. -/
  t : D →+* E
  /-- The projection onto the factors `(2,3)`, on rings. -/
  d₀ : E →+* E₂
  /-- The projection onto the factors `(1,3)`, on rings. -/
  d₁ : E →+* E₂
  /-- The projection onto the factors `(1,2)`, on rings. -/
  d₂ : E →+* E₂
  /-- The projection onto the first factor, on rings. -/
  q : D →+* E₂
  /-- The reduction of `s`. -/
  s₀ : D₀ →ₐ[C] E₀
  /-- The reduction of `t`. -/
  t₀ : D₀ →ₐ[C] E₀
  /-- The reduction of `q`. -/
  q₀ : D₀ →ₐ[C] E₂₀
  /-- The reduction of `d₀`. -/
  e₀ : E₀ →ₐ[C] E₂₀
  πE_s : ∀ x, πE (s x) = s₀ (πD x)
  πE_t : ∀ x, πE (t x) = t₀ (πD x)
  πE₂_q : ∀ x, πE₂ (q x) = q₀ (πD x)
  πE₂_d₀ : ∀ x, πE₂ (d₀ x) = e₀ (πE x)
  d₁_s : ∀ x, d₁ (s x) = q x
  d₂_s : ∀ x, d₂ (s x) = q x
  d₁_t : ∀ x, d₁ (t x) = d₀ (t x)
  d₂_t : ∀ x, d₂ (t x) = d₀ (s x)
  sq_zero : ∀ x ∈ RingHom.ker πD, ∀ y ∈ RingHom.ker πD, x * y = 0
  ker_πE : RingHom.ker πE ≤ (RingHom.ker πD).map t
  ker_πE₂ : RingHom.ker πE₂ ≤ (RingHom.ker πE).map d₀
  flat : d₀.Flat
  gen : Function.Surjective (Algebra.TensorProduct.productMap s₀ t₀)
  push : Function.Bijective (Algebra.TensorProduct.productMap q₀ e₀)

namespace Data

variable {C D E E₂ D₀ E₀ E₂₀ : Type*} [CommRing C] [CommRing D] [CommRing E] [CommRing E₂]
  [CommRing D₀] [CommRing E₀] [CommRing E₂₀] [Algebra C D₀] [Algebra C E₀] [Algebra C E₂₀]
  (X : Data C D E E₂ D₀ E₀ E₂₀)

/-- `s` maps the kernel of `D → D₀` into the kernel of `E → E₀`. -/
theorem s_mem {k : D} (hk : k ∈ RingHom.ker X.πD) : X.s k ∈ RingHom.ker X.πE := by
  rw [RingHom.mem_ker] at hk ⊢
  rw [X.πE_s, hk, map_zero]

/-- `t` maps the kernel of `D → D₀` into the kernel of `E → E₀`. -/
theorem t_mem {k : D} (hk : k ∈ RingHom.ker X.πD) : X.t k ∈ RingHom.ker X.πE := by
  rw [RingHom.mem_ker] at hk ⊢
  rw [X.πE_t, hk, map_zero]

/-- The kernel of `E → E₀` squares to zero. -/
theorem sq_zero_E : ∀ x ∈ RingHom.ker X.πE, ∀ y ∈ RingHom.ker X.πE, x * y = 0 := by
  intro x hx y hy
  exact mul_eq_zero_of_mem_map X.t X.sq_zero (X.ker_πE hx) (X.ker_πE hy)

/-- If the reduction of `x` comes from `C`, then `t x - s x` lies in the kernel of `E → E₀`. -/
theorem t_sub_s_mem {c : C} (x : D) (hx : X.πD x = algebraMap C D₀ c) :
    X.t x - X.s x ∈ RingHom.ker X.πE := by
  rw [RingHom.mem_ker, map_sub, X.πE_t, X.πE_s, hx, AlgHom.commutes, AlgHom.commutes, sub_self]

/-- The kernel of `E₂ → E₂₀` kills the image of the kernel of `E → E₀` under `d₀`. -/
theorem mul_d₀_eq_zero {κ : E₂} (hκ : κ ∈ RingHom.ker X.πE₂) {n : E} (hn : n ∈ RingHom.ker X.πE) :
    κ * X.d₀ n = 0 := by
  exact mul_eq_zero_of_mem_map X.d₀ X.sq_zero_E (X.ker_πE₂ hκ) (Ideal.mem_map_of_mem _ hn)

/-! ### The kernels, as modules -/

/-- The kernel of `D → D₀`, a type carrying its `C`-module structure as an instance. -/
abbrev KD : Type _ := RingHom.ker X.πD

/-- The kernel of `E → E₀`, a type carrying its `C`-module structure as an instance. -/
abbrev KE : Type _ := RingHom.ker X.πE

/-- The `C`-module structure on the kernel of `D → D₀`, given by `kerModuleOver`. -/
instance : Module C X.KD := kerModuleOver X.surj_πD X.sq_zero C

/-- The `C`-module structure on the kernel of `E → E₀`, given by `kerModuleOver`. -/
instance : Module C X.KE := kerModuleOver X.surj_πE X.sq_zero_E C

/-- The element of `D` underlying an element of the kernel. -/
def KD.val (m : X.KD) : D := m.1

/-- The element of `E` underlying an element of the kernel. -/
def KE.val (n : X.KE) : E := n.1

/-- The element underlying an element of `KD` lies in the kernel of `D → D₀`. -/
theorem KD.mem (m : X.KD) : KD.val X m ∈ RingHom.ker X.πD := m.2

/-- The element underlying an element of `KE` lies in the kernel of `E → E₀`. -/
theorem KE.mem (n : X.KE) : KE.val X n ∈ RingHom.ker X.πE := n.2

/-- An element of the kernel of `D → D₀`. -/
def KD.mk (k : D) (hk : k ∈ RingHom.ker X.πD) : X.KD := ⟨k, hk⟩

/-- An element of the kernel of `E → E₀`. -/
def KE.mk (k : E) (hk : k ∈ RingHom.ker X.πE) : X.KE := ⟨k, hk⟩

/-- The element underlying `KD.mk X k hk` is `k`. -/
@[simp] theorem KD.val_mk (k : D) (hk) : KD.val X (KD.mk X k hk) = k := rfl

/-- The element underlying `KE.mk X k hk` is `k`. -/
@[simp] theorem KE.val_mk (k : E) (hk) : KE.val X (KE.mk X k hk) = k := rfl

/-- Two elements of `KD` with the same underlying element of `D` are equal. -/
theorem KD.ext {m m' : X.KD} (h : KD.val X m = KD.val X m') : m = m' := Subtype.ext h

/-- Two elements of `KE` with the same underlying element of `E` are equal. -/
theorem KE.ext {n n' : X.KE} (h : KE.val X n = KE.val X n') : n = n' := Subtype.ext h

/-- `KD.val` is additive. -/
@[simp] theorem KD.val_add (m m' : X.KD) : KD.val X (m + m') = KD.val X m + KD.val X m' := rfl

/-- `KE.val` is additive. -/
@[simp] theorem KE.val_add (n n' : X.KE) : KE.val X (n + n') = KE.val X n + KE.val X n' := rfl

/-- `KD.val` sends `0` to `0`. -/
@[simp] theorem KD.val_zero : KD.val X 0 = 0 := rfl

/-- `KE.val` sends `0` to `0`. -/
@[simp] theorem KE.val_zero : KE.val X 0 = 0 := rfl

/-- `KE.val` commutes with subtraction. -/
@[simp] theorem KE.val_sub (n n' : X.KE) : KE.val X (n - n') = KE.val X n - KE.val X n' := rfl

/-- `c • m` in `KD` is the product of `m` with any lift to `D` of the image of `c` in `D₀`. -/
theorem KD.val_smul (c : C) (m : X.KD) (x : D) (hx : X.πD x = algebraMap C D₀ c) :
    KD.val X (c • m) = x * KD.val X m :=
  kerModuleOver_val X.surj_πD X.sq_zero C c m x hx

/-- `c • n` in `KE` is the product of `n` with any lift to `E` of the image of `c` in `E₀`. -/
theorem KE.val_smul (c : C) (n : X.KE) (x : E) (hx : X.πE x = algebraMap C E₀ c) :
    KE.val X (c • n) = x * KE.val X n :=
  kerModuleOver_val X.surj_πE X.sq_zero_E C c n x hx

/-! ### The Čech differential and the two comparison maps -/

/-- The Čech differential `m ↦ t m - s m` on the kernels. -/
def φ : X.KD →ₗ[C] X.KE where
  toFun m := KE.mk X (X.t (KD.val X m) - X.s (KD.val X m))
    (sub_mem (X.t_mem (KD.mem X m)) (X.s_mem (KD.mem X m)))
  map_add' m m' := KE.ext X (by simp only [KE.val_mk, KD.val_add, KE.val_add, map_add]; ring)
  map_smul' c m := by
    obtain ⟨x, hx⟩ := X.surj_πD (algebraMap C D₀ c)
    have hE : X.πE (X.t x) = algebraMap C E₀ c := by rw [X.πE_t, hx, AlgHom.commutes]
    apply KE.ext
    rw [RingHom.id_apply, KE.val_smul X c _ (X.t x) hE, KE.val_mk, KE.val_mk,
      KD.val_smul X c m x hx]
    have h0 := X.sq_zero_E _ (X.t_sub_s_mem x hx) _ (X.s_mem (KD.mem X m))
    simp only [map_mul]
    linear_combination h0

/-- The element of `E` underlying `φ m` is `t m - s m`. -/
theorem φ_val (m : X.KD) : KE.val X (X.φ m) = X.t (KD.val X m) - X.s (KD.val X m) := rfl

/-- `s x * t m` depends only on the reduction of `x`. -/
theorem s_mul_t_eq {x x' : D} (h : X.πD x = X.πD x') (m : D) (hm : m ∈ RingHom.ker X.πD) :
    X.s x * X.t m = X.s x' * X.t m :=
  mul_eq_mul_of_eq X.sq_zero_E (by rw [X.πE_s, X.πE_s, h]) ⟨X.t m, X.t_mem hm⟩

/-- The first comparison `D₀ ⊗_C ker(D → D₀) → ker(E → E₀)`, `b ⊗ m ↦ s(b) t(m)`. -/
def ι₀ : D₀ ⊗[C] X.KD →+ X.KE :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun m => KE.mk X (X.s (Function.surjInv X.surj_πD b) * X.t (KD.val X m))
          (Ideal.mul_mem_left _ _ (X.t_mem (KD.mem X m))))
        (fun m m' => KE.ext X (by simp only [KE.val_mk, KD.val_add, KE.val_add, map_add,
          mul_add])))
      (fun b b' => by
        refine AddMonoidHom.ext fun m => KE.ext X ?_
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, KE.val_mk, KE.val_add]
        rw [X.s_mul_t_eq (x := Function.surjInv X.surj_πD (b + b'))
          (x' := Function.surjInv X.surj_πD b + Function.surjInv X.surj_πD b')
          (by rw [Function.surjInv_eq X.surj_πD, X.πD.map_add, Function.surjInv_eq X.surj_πD,
            Function.surjInv_eq X.surj_πD])
          _ (KD.mem X m), map_add, add_mul]))
    (fun c b m => by
      obtain ⟨x, hx⟩ := X.surj_πD (algebraMap C D₀ c)
      apply KE.ext
      simp only [AddMonoidHom.mk'_apply, KE.val_mk]
      rw [KD.val_smul X c m x hx, X.s_mul_t_eq (x := Function.surjInv X.surj_πD (c • b))
        (x' := x * Function.surjInv X.surj_πD b)
        (by rw [Function.surjInv_eq X.surj_πD, X.πD.map_mul, Function.surjInv_eq X.surj_πD, hx,
          Algebra.smul_def])
        _ (KD.mem X m)]
      have h0 := X.sq_zero_E _ (X.t_sub_s_mem x hx) _
        (Ideal.mul_mem_left _ (X.s (Function.surjInv X.surj_πD b)) (X.t_mem (KD.mem X m)))
      simp only [map_mul]
      linear_combination -h0)

/-- `ι₀ (b ⊗ m) = s x * t m` for any lift `x` of `b` to `D`. -/
theorem ι₀_tmul (b : D₀) (m : X.KD) (x : D) (hx : X.πD x = b) :
    KE.val X (X.ι₀ (b ⊗ₜ m)) = X.s x * X.t (KD.val X m) :=
  X.s_mul_t_eq ((Function.surjInv_eq X.surj_πD b).trans hx.symm) _ (KD.mem X m)

/-- The image of `ι₀` is stable under multiplication by elements of `E`. -/
theorem exists_ι₀_eq_mul (e : E) (y : D₀ ⊗[C] X.KD) :
    ∃ y' : D₀ ⊗[C] X.KD, KE.val X (X.ι₀ y') = e * KE.val X (X.ι₀ y) := by
  obtain ⟨z, hz⟩ := X.gen (X.πE e)
  induction z using TensorProduct.inductionOn generalizing e with
  | tmul b b' =>
    obtain ⟨x, rfl⟩ := X.surj_πD b
    obtain ⟨x', rfl⟩ := X.surj_πD b'
    have hκ : e - X.s x * X.t x' ∈ RingHom.ker X.πE := by
      rw [RingHom.mem_ker, map_sub, ← hz, map_mul, X.πE_s, X.πE_t,
        Algebra.TensorProduct.productMap_apply_tmul, sub_self]
    induction y using TensorProduct.inductionOn with
    | tmul b'' m =>
      obtain ⟨x'', rfl⟩ := X.surj_πD b''
      refine ⟨(X.πD x * X.πD x'') ⊗ₜ KD.mk X (x' * KD.val X m)
        (Ideal.mul_mem_left _ _ (KD.mem X m)), ?_⟩
      rw [X.ι₀_tmul _ _ (x * x'') (map_mul _ _ _), X.ι₀_tmul _ _ x'' rfl, KD.val_mk]
      have h0 := X.sq_zero_E _ hκ _
        (Ideal.mul_mem_left _ (X.s x'') (X.t_mem (KD.mem X m)))
      simp only [map_mul]
      linear_combination -h0
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨y₁', h₁'⟩ := h₁
      obtain ⟨y₂', h₂'⟩ := h₂
      exact ⟨y₁' + y₂', by rw [map_add, map_add, KE.val_add, KE.val_add, h₁', h₂', mul_add]⟩
  | add z₁ z₂ h₁ h₂ =>
    set e₁ := Function.surjInv X.surj_πE (Algebra.TensorProduct.productMap X.s₀ X.t₀ z₁)
    have he₁ : Algebra.TensorProduct.productMap X.s₀ X.t₀ z₁ = X.πE e₁ :=
      (Function.surjInv_eq X.surj_πE _).symm
    have he₂ : Algebra.TensorProduct.productMap X.s₀ X.t₀ z₂ = X.πE (e - e₁) := by
      rw [map_sub, ← hz, ← he₁, map_add, add_sub_cancel_left]
    obtain ⟨y₁', h₁'⟩ := h₁ e₁ he₁
    obtain ⟨y₂', h₂'⟩ := h₂ (e - e₁) he₂
    exact ⟨y₁' + y₂', by rw [map_add, KE.val_add, h₁', h₂']; ring⟩

/-- The first comparison `ι₀` is surjective. -/
theorem surjective_ι₀ : Function.Surjective X.ι₀ := by
  intro n
  have key : ∀ κ ∈ (RingHom.ker X.πD).map X.t,
      ∃ y : D₀ ⊗[C] X.KD, KE.val X (X.ι₀ y) = κ := by
    intro κ hκ
    change κ ∈ Submodule.span E (X.t '' (RingHom.ker X.πD : Set D)) at hκ
    induction hκ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨1 ⊗ₜ KD.mk X k hk, by rw [X.ι₀_tmul _ _ 1 (map_one _), map_one, one_mul,
        KD.val_mk]⟩
    | zero => exact ⟨0, by rw [map_zero, KE.val_zero]⟩
    | add a b _ _ ha hb =>
      obtain ⟨ya, ha⟩ := ha
      obtain ⟨yb, hb⟩ := hb
      exact ⟨ya + yb, by rw [map_add, KE.val_add, ha, hb]⟩
    | smul a b _ hb =>
      obtain ⟨yb, hb⟩ := hb
      obtain ⟨y', hy'⟩ := X.exists_ι₀_eq_mul a yb
      exact ⟨y', by rw [hy', hb, smul_eq_mul]⟩
  obtain ⟨y, hy⟩ := key (KE.val X n) (X.ker_πE (KE.mem X n))
  exact ⟨y, KE.ext X hy⟩

/-- `q x - q x'` lies in the kernel of `E₂ → E₂₀` when `x` and `x'` have the same reduction. -/
private theorem q_sub_mem {x x' : D} (h : X.πD x = X.πD x') :
    X.q x - X.q x' ∈ RingHom.ker X.πE₂ := by
  rw [RingHom.mem_ker, map_sub, X.πE₂_q, X.πE₂_q, h, sub_self]

/-- `q x * d₀ n` depends only on the reduction of `x`. -/
theorem q_mul_d₀_eq {x x' : D} (h : X.πD x = X.πD x') (n : E) (hn : n ∈ RingHom.ker X.πE) :
    X.q x * X.d₀ n = X.q x' * X.d₀ n := by
  have := X.mul_d₀_eq_zero (X.q_sub_mem h) hn
  rwa [sub_mul, sub_eq_zero] at this

/-- The second comparison `D₀ ⊗_C ker(E → E₀) → E₂`, `b ⊗ n ↦ q(b) d₀(n)`. -/
def ι₁ : D₀ ⊗[C] X.KE →+ E₂ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun n => X.q (Function.surjInv X.surj_πD b) * X.d₀ (KE.val X n))
        (fun n n' => by simp only [KE.val_add, map_add, mul_add]))
      (fun b b' => by
        refine AddMonoidHom.ext fun n => ?_
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        rw [X.q_mul_d₀_eq (x := Function.surjInv X.surj_πD (b + b'))
          (x' := Function.surjInv X.surj_πD b + Function.surjInv X.surj_πD b')
          (by rw [Function.surjInv_eq X.surj_πD, X.πD.map_add, Function.surjInv_eq X.surj_πD,
            Function.surjInv_eq X.surj_πD])
          _ (KE.mem X n), map_add, add_mul]))
    (fun c b n => by
      obtain ⟨x, hx⟩ := X.surj_πD (algebraMap C D₀ c)
      obtain ⟨x', hx'⟩ := X.surj_πE (algebraMap C E₀ c)
      simp only [AddMonoidHom.mk'_apply]
      rw [KE.val_smul X c n x' hx', X.q_mul_d₀_eq (x := Function.surjInv X.surj_πD (c • b))
        (x' := x * Function.surjInv X.surj_πD b)
        (by rw [Function.surjInv_eq X.surj_πD, X.πD.map_mul, Function.surjInv_eq X.surj_πD, hx,
          Algebra.smul_def])
        _ (KE.mem X n)]
      have hk : X.q x - X.d₀ x' ∈ RingHom.ker X.πE₂ := by
        rw [RingHom.mem_ker, map_sub, X.πE₂_q, X.πE₂_d₀, hx, hx', AlgHom.commutes,
          AlgHom.commutes, sub_self]
      have h0 := X.mul_d₀_eq_zero hk (KE.mem X n)
      simp only [map_mul]
      linear_combination (X.q (Function.surjInv X.surj_πD b)) * h0)

/-- `ι₁ (b ⊗ n) = q x * d₀ n` for any lift `x` of `b` to `D`. -/
theorem ι₁_tmul (b : D₀) (n : X.KE) (x : D) (hx : X.πD x = b) :
    X.ι₁ (b ⊗ₜ n) = X.q x * X.d₀ (KE.val X n) :=
  X.q_mul_d₀_eq ((Function.surjInv_eq X.surj_πD b).trans hx.symm) _ (KE.mem X n)

/-- **The second comparison is injective.**  It factors as
`D₀ ⊗_C ker(E → E₀) → E₂ ⊗_E ker(E → E₀) → E₂`; the second map is injective because `d₀` is flat,
and the first has a left inverse, built from the identification `E₂₀ ≅ D₀ ⊗_C E₀` of `push`. -/
theorem injective_ι₁ : Function.Injective X.ι₁ := by
  let : Algebra E E₂ := X.d₀.toAlgebra
  have : Module.Flat E E₂ := X.flat
  let mE₀ : Module E₀ X.KE := kerModule X.surj_πE X.sq_zero_E
  have kill : ∀ κ ∈ RingHom.ker X.πE₂, ∀ n : X.KE, κ ⊗ₜ[E] n = (0 : E₂ ⊗[E] X.KE) := by
    intro κ hκ n
    have hκ' := X.ker_πE₂ hκ
    change κ ∈ Submodule.span E₂ (X.d₀ '' (RingHom.ker X.πE : Set E)) at hκ'
    clear hκ
    induction hκ' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 : X.d₀ k = k • (1 : E₂) := by rw [Algebra.smul_def, mul_one]; rfl
      have hkn : (k • n : X.KE) = 0 := Subtype.ext (X.sq_zero_E k hk n n.2)
      rw [h1, TensorProduct.smul_tmul, hkn, TensorProduct.tmul_zero]
    | zero => rw [TensorProduct.zero_tmul]
    | add a b _ _ ha hb => rw [TensorProduct.add_tmul, ha, hb, add_zero]
    | smul a b _ hb => rw [← TensorProduct.smul_tmul', hb, smul_zero]
  have hqlift : ∀ {x x' : D}, X.πD x = X.πD x' → ∀ n : X.KE,
      X.q x ⊗ₜ[E] n = X.q x' ⊗ₜ[E] n := by
    intro x x' h n
    rw [← sub_eq_zero, ← TensorProduct.sub_tmul]
    exact kill _ (X.q_sub_mem h) n
  let mult : E₂ ⊗[E] X.KE →ₗ[E] E₂ :=
    (TensorProduct.rid E E₂).toLinearMap ∘ₗ (RingHom.ker X.πE).subtype.lTensor E₂
  have hmult : Function.Injective mult :=
    (TensorProduct.rid E E₂).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have mult_tmul : ∀ (e : E₂) (n : X.KE), mult (e ⊗ₜ n) = X.d₀ (KE.val X n) * e := by
    intro e n
    change TensorProduct.rid E E₂ (e ⊗ₜ (n : E)) = _
    rw [TensorProduct.rid_tmul, Algebra.smul_def]
    rfl
  let α : D₀ ⊗[C] X.KE →+ E₂ ⊗[E] X.KE :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
          (fun n => X.q (Function.surjInv X.surj_πD b) ⊗ₜ[E] n)
          (fun n n' => TensorProduct.tmul_add _ _ _))
        (fun b b' => by
          refine AddMonoidHom.ext fun n => ?_
          simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
          rw [hqlift (x := Function.surjInv X.surj_πD (b + b'))
            (x' := Function.surjInv X.surj_πD b + Function.surjInv X.surj_πD b')
            (by rw [Function.surjInv_eq X.surj_πD, X.πD.map_add, Function.surjInv_eq X.surj_πD,
              Function.surjInv_eq X.surj_πD]),
            map_add, TensorProduct.add_tmul]))
      (fun c b n => by
        obtain ⟨x, hx⟩ := X.surj_πD (algebraMap C D₀ c)
        obtain ⟨x', hx'⟩ := X.surj_πE (algebraMap C E₀ c)
        simp only [AddMonoidHom.mk'_apply]
        have hcn : (c • n : X.KE) = (x' • n : X.KE) :=
          Subtype.ext (KE.val_smul X c n x' hx')
        rw [hcn, ← TensorProduct.smul_tmul,
          hqlift (x := Function.surjInv X.surj_πD (c • b))
            (x' := x * Function.surjInv X.surj_πD b)
            (by rw [Function.surjInv_eq X.surj_πD, X.πD.map_mul, Function.surjInv_eq X.surj_πD,
              hx, Algebra.smul_def]),
          ← sub_eq_zero, ← TensorProduct.sub_tmul]
        refine kill _ ?_ n
        change X.πE₂ (X.q (x * _) - X.d₀ x' * X.q _) = 0
        rw [map_sub, map_mul, map_mul, map_mul, X.πE₂_q, X.πE₂_q, X.πE₂_d₀, hx, hx',
          AlgHom.commutes, AlgHom.commutes, sub_self])
  have α_tmul : ∀ b n, α (b ⊗ₜ n) = X.q (Function.surjInv X.surj_πD b) ⊗ₜ[E] n :=
    fun _ _ => rfl
  have hι : ∀ y, X.ι₁ y = mult (α y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b n =>
      rw [X.ι₁_tmul b n _ (Function.surjInv_eq X.surj_πD b), α_tmul, mult_tmul, mul_comm]
    | add y y' h h' => rw [map_add, map_add, map_add, h, h']
  let σ := (AlgEquiv.ofBijective (Algebra.TensorProduct.productMap X.q₀ X.e₀) X.push).symm
  have hσq : ∀ b, σ (X.q₀ b) = b ⊗ₜ 1 := fun b => by
    rw [show X.q₀ b = AlgEquiv.ofBijective _ X.push (b ⊗ₜ 1) by
      rw [AlgEquiv.ofBijective_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
        mul_one]]
    exact AlgEquiv.symm_apply_apply _ _
  have hσe : ∀ y, σ (X.e₀ y) = 1 ⊗ₜ y := fun y => by
    rw [show X.e₀ y = AlgEquiv.ofBijective _ X.push (1 ⊗ₜ y) by
      rw [AlgEquiv.ofBijective_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
        one_mul]]
    exact AlgEquiv.symm_apply_apply _ _
  let yAct : E₀ → (X.KE →ₗ[C] X.KE) := fun y =>
    { toFun := fun n => y • n
      map_add' := fun n n' => smul_add y n n'
      map_smul' := fun c n => by
        change y • (algebraMap C E₀ c • n) = algebraMap C E₀ c • (y • n)
        rw [smul_smul, smul_smul, mul_comm] }
  have homext : ∀ f g : D₀ ⊗[C] X.KE →+ D₀ ⊗[C] X.KE,
      (∀ b n, f (b ⊗ₜ n) = g (b ⊗ₜ n)) → f = g := by
    intro f g h
    refine AddMonoidHom.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | tmul b n => exact h b n
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  let Φ : D₀ ⊗[C] E₀ →+ (D₀ ⊗[C] X.KE →+ D₀ ⊗[C] X.KE) :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
          (fun y => (TensorProduct.map (LinearMap.mulLeft C b) (yAct y)).toAddMonoidHom)
          (fun y y' => homext _ _ fun b' n => by
            change (b * b') ⊗ₜ ((y + y') • n) = (b * b') ⊗ₜ (y • n) + (b * b') ⊗ₜ (y' • n)
            rw [add_smul, TensorProduct.tmul_add]))
        (fun b b' => by
          refine AddMonoidHom.ext fun y => homext _ _ fun b'' n => ?_
          change ((b + b') * b'') ⊗ₜ (y • n) = (b * b'') ⊗ₜ (y • n) + (b' * b'') ⊗ₜ (y • n)
          rw [add_mul, TensorProduct.add_tmul]))
      (fun c b y => homext _ _ fun b' n => by
        change ((c • b) * b') ⊗ₜ (y • n) = (b * b') ⊗ₜ ((c • y) • n)
        rw [smul_mul_assoc, TensorProduct.smul_tmul, Algebra.smul_def, mul_smul]
        rfl)
  have Φ_tmul : ∀ b y b' n, Φ (b ⊗ₜ y) (b' ⊗ₜ n) = (b * b') ⊗ₜ (y • n) :=
    fun _ _ _ _ => rfl
  have Φ3 : ∀ u y n, Φ ((1 ⊗ₜ y) * u) (1 ⊗ₜ n) = Φ u (1 ⊗ₜ (y • n)) := by
    intro u y n
    induction u using TensorProduct.inductionOn with
    | tmul b y' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Φ_tmul, Φ_tmul, one_mul, mul_smul, smul_comm]
    | add u u' hu hu' =>
      rw [mul_add, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, hu, hu']
  let ρ : E₂ ⊗[E] X.KE →+ D₀ ⊗[C] X.KE :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun e => AddMonoidHom.mk'
          (fun n => Φ (σ (X.πE₂ e)) (1 ⊗ₜ n))
          (fun n n' => by rw [TensorProduct.tmul_add, map_add]))
        (fun e e' => by
          refine AddMonoidHom.ext fun n => ?_
          simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
          rw [map_add, map_add, map_add, AddMonoidHom.add_apply]))
      (fun r e n => by
        simp only [AddMonoidHom.mk'_apply]
        have hrn : (r • n : X.KE) = (X.πE r • n : X.KE) :=
          Subtype.ext (kerModule_val X.surj_πE X.sq_zero_E (X.πE r) n r rfl).symm
        have hre : X.πE₂ (r • e) = X.e₀ (X.πE r) * X.πE₂ e := by
          rw [Algebra.smul_def, map_mul, ← X.πE₂_d₀]
          rfl
        rw [hrn, hre, map_mul, hσe, Φ3])
  have hρ : ∀ y, ρ (α y) = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b n =>
      rw [α_tmul]
      change Φ (σ (X.πE₂ (X.q (Function.surjInv X.surj_πD b)))) (1 ⊗ₜ n) = b ⊗ₜ n
      rw [X.πE₂_q, Function.surjInv_eq X.surj_πD, hσq, Φ_tmul, mul_one, one_smul]
    | add y y' h h' => rw [map_add, map_add, h, h']
  intro y y' h
  rw [hι, hι] at h
  rw [← hρ y, ← hρ y', hmult h]

/-- **Correction of a lift along a square-zero thickening of a Čech nerve.**  An element `a` of
`D` whose reduction is equalized by `s₀, t₀ : D₀ ⇉ E₀` differs, by an element of the kernel of
`D → D₀`, from an element equalized by `s, t : D ⇉ E`. -/
theorem exists_sub_mem_ker_eq [Module.FaithfullyFlat C D₀] (a : D)
    (ha : X.s₀ (X.πD a) = X.t₀ (X.πD a)) :
    ∃ m ∈ RingHom.ker X.πD, X.t (a - m) = X.s (a - m) := by
  have hd : X.t a - X.s a ∈ RingHom.ker X.πE := by
    rw [RingHom.mem_ker, map_sub, X.πE_t, X.πE_s, ha, sub_self]
  let ψ : X.KE → E₂ := fun n => X.d₁ (KE.val X n) - X.d₂ (KE.val X n)
  have hc : ∀ y, X.ι₁ (X.φ.lTensor D₀ y) = ψ (X.ι₀ y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b m =>
      obtain ⟨x, rfl⟩ := X.surj_πD b
      rw [LinearMap.lTensor_tmul, X.ι₁_tmul _ _ x rfl, X.φ_val]
      change _ = X.d₁ (KE.val X (X.ι₀ _)) - X.d₂ (KE.val X (X.ι₀ _))
      rw [X.ι₀_tmul _ _ x rfl, map_mul, map_mul, X.d₁_s, X.d₂_s, X.d₁_t, X.d₂_t, map_sub]
      ring
    | add y y' h h' =>
      rw [map_add, map_add, h, h', map_add]
      simp only [ψ, KE.val_add, map_add]
      ring
  obtain ⟨m, hm⟩ := mem_range_of_lTensor_eq X.φ ψ X.ι₀ X.ι₁ X.surjective_ι₀ X.injective_ι₁ hc
    (KE.mk X _ hd) (by
      simp only [ψ, KE.val_mk]
      rw [X.ι₁_tmul _ _ 1 (map_one _), map_one, one_mul, KE.val_mk, map_sub, map_sub, map_sub,
        X.d₁_t, X.d₂_t, X.d₁_s, X.d₂_s]
      ring)
  refine ⟨KD.val X m, KD.mem X m, ?_⟩
  have h := congrArg (KE.val X) hm
  rw [X.φ_val, KE.val_mk] at h
  rw [map_sub, map_sub]
  linear_combination (-1 : E) * h

end Data

end SquareZeroCech

end
