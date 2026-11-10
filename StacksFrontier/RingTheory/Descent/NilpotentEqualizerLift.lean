module

public import StacksFrontier.RingTheory.Descent.CocycleOfComparisonMaps
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Torsion.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting invariant functions along a nilpotent thickening of a descent situation

Let `X` be a thickening of an affine scheme `Spec A`, presented by an affine étale chart
`V = Spec B'` with self-intersection `V ×_X V = Spec C'` and triple intersection `Spec D'`, and let
`B`, `C`, `D` be the rings of the reductions, so that `A → B` is faithfully flat, `C = B ⊗[A] B`
and `D = B ⊗[A] C`. This file proves the ring-theoretic content of the surjectivity of
`Γ(X, 𝒪) → A` (Stacks 05ZQ, the proof for finite order thickenings): when the kernel `J` of
`B' → B` is nilpotent, every `a ∈ A` lifts to an element of `B'` with equal images under the two
projections `B' → C'`.

The source argues with the long exact cohomology sequence of `0 → 𝓘 → 𝒪_{X'} → 𝒪_X → 0` and the
vanishing of `H¹` of a quasi-coherent module on an affine. Here the same vanishing is used on one
chart, for the Čech complex of each graded piece `J ^ k / J ^ (k + 1)`, and the lift is improved
one power of the kernel at a time.

## Main definitions

* `Module.Descent.grPiece`: the graded piece `I ^ k / I ^ (k + 1)` of the kernel of a ring map,
  and `Module.Descent.grMap` the map of graded pieces induced by a ring map.
* `Module.Descent.pushoutTensorMap`, `Module.Descent.pushoutMap`: comparison maps out of tensor
  products along a pushout square of rings.

## Main results

* `Module.Descent.bijective_idealBaseChangeMap`: flat base change of an ideal.
* `Module.Descent.bijective_pushoutTensorMap`: `B ⊗[A] K ≅ E ⊗[B₂] K` for a pushout
  `E = B ⊗[A] B₂` and a `B₂`-module `K`.
* `Module.Descent.bijective_tensor_grMap`: flat base change of the graded pieces of an ideal.
* `Module.Descent.exists_grMap_sub_grMap_eq`: every one-cocycle in a graded piece on the double
  overlap is a coboundary, by `Module.Descent.exists_sub_eq_of_cocycle`.
* `Module.Descent.exists_eq_of_isNilpotent_ker`: **every element of `A` lifts to an invariant
  element of the chart ring**.

## Implementation notes

The reductions are abstract rings with surjections `B' → B`, `C' → C`, `D' → D` rather than
quotient rings, because in geometry they are rings of global functions of closed subschemes. The
graded pieces are quotients of `R'`-modules; their module structures over the reductions are
supplied as instance arguments together with the compatibility `π r • x = r • x`, and built with
`Module.Descent.grPiece.module` where they are needed, so that no statement contains a `letI`.

The pushout hypotheses are stated in `CommRingCat`, because a pushout square with two copies of
the same ring `B` cannot be expressed with `Algebra.IsPushout`.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/
@[expose] public section

open TensorProduct

universe u

namespace Module.Descent

/-! ### Flat base change of an ideal -/

section Flat

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The `S`-linear map `S ⊗[R] I → I S`, `s ⊗ x ↦ s • x`. -/
noncomputable def idealBaseChangeMap (I : Ideal R) :
    S ⊗[R] I →ₗ[S] I.map (algebraMap R S) :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton S (I →ₗ[R] I.map (algebraMap R S))
    { toFun := fun x => ⟨algebraMap R S x, Ideal.mem_map_of_mem _ x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by
        ext
        simp [Algebra.smul_def] })

/-- `Module.Descent.idealBaseChangeMap` sends `s ⊗ x` to `s * x`. -/
@[simp]
lemma idealBaseChangeMap_tmul (I : Ideal R) (s : S) (x : I) :
    (idealBaseChangeMap I (s ⊗ₜ x) : S) = s * algebraMap R S x := by
  simp [idealBaseChangeMap]

/-- **Flat base change of an ideal.** For `S` flat over `R`, `S ⊗[R] I → I S` is bijective. -/
theorem bijective_idealBaseChangeMap [Module.Flat R S] (I : Ideal R) :
    Function.Bijective (idealBaseChangeMap (S := S) I) := by
  constructor
  · -- composing with the inclusion into `S` gives `S ⊗[R] I → S ⊗[R] R ≅ S`, injective by flatness
    intro y z hyz
    have hinj : Function.Injective ((TensorProduct.rid R S).toLinearMap ∘ₗ
        LinearMap.lTensor S I.subtype) :=
      (TensorProduct.rid R S).injective.comp
        (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
    have key : ∀ w : S ⊗[R] I, (idealBaseChangeMap I w : S) =
        ((TensorProduct.rid R S).toLinearMap ∘ₗ LinearMap.lTensor S I.subtype) w := by
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul s x =>
        simp [Algebra.smul_def, mul_comm]
      | add w w' hw hw' => simp only [map_add, Submodule.coe_add, hw, hw']
    apply hinj
    rw [← key, ← key, hyz]
  · rintro ⟨x, hx⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨1 ⊗ₜ ⟨r, hr⟩, Subtype.ext (by simp)⟩
    | zero => exact ⟨0, by rw [map_zero]; rfl⟩
    | add x y hx hy hx' hy' =>
      obtain ⟨u, hu⟩ := hx'
      obtain ⟨v, hv⟩ := hy'
      exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩
    | smul s x hx hx' =>
      obtain ⟨u, hu⟩ := hx'
      exact ⟨s • u, by rw [LinearMap.map_smul, hu]; rfl⟩

/-- `Module.Descent.idealBaseChangeMap` as a linear equivalence, for `S` flat over `R`. -/
noncomputable def idealBaseChangeEquiv [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  LinearEquiv.ofBijective _ (bijective_idealBaseChangeMap I)

/-- `Module.Descent.idealBaseChangeEquiv` sends `s ⊗ x` to `s * x`. -/
@[simp]
lemma idealBaseChangeEquiv_tmul [Module.Flat R S] (I : Ideal R) (s : S) (x : I) :
    (idealBaseChangeEquiv I (s ⊗ₜ x) : S) = s * algebraMap R S x :=
  idealBaseChangeMap_tmul I s x

end Flat

/-! ### Cancelling a pushout of rings against a tensor product -/

section Pushout

variable {A B B₂ E : Type u} [CommRing A] [CommRing B] [CommRing B₂] [CommRing E] [Algebra A B]
  [Algebra A B₂] [Algebra B₂ E]

/-- The map `B ⊗[A] K → E ⊗[B₂] K`, `b ⊗ k ↦ j b ⊗ k`, for a ring map `j : B → E` agreeing with
`B₂ → E` on `A`. -/
noncomputable def pushoutTensorMap (j : B →+* E)
    (hj : ∀ a, j (algebraMap A B a) = algebraMap B₂ E (algebraMap A B₂ a))
    (K : Type*) [AddCommGroup K] [Module B₂ K] [Module A K] [IsScalarTower A B₂ K] :
    B ⊗[A] K →+ E ⊗[B₂] K :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => j b ⊗ₜ[B₂] k)
        (fun k k' => TensorProduct.tmul_add _ _ _))
      (fun b b' => by ext k; simp [TensorProduct.add_tmul]))
    (fun a b k => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, hj, ← algebraMap_smul B₂ a k, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.smul_def])

/-- `Module.Descent.pushoutTensorMap` sends `b ⊗ k` to `j b ⊗ k`. -/
@[simp]
lemma pushoutTensorMap_tmul (j : B →+* E)
    (hj : ∀ a, j (algebraMap A B a) = algebraMap B₂ E (algebraMap A B₂ a))
    (K : Type*) [AddCommGroup K] [Module B₂ K] [Module A K] [IsScalarTower A B₂ K]
    (b : B) (k : K) : pushoutTensorMap j hj K (b ⊗ₜ k) = j b ⊗ₜ k := rfl

/-- **Base change along a pushout.** If `E` is the pushout `B ⊗[A] B₂`, with `B → E` given by
`j`, then for every `B₂`-module `K` the map `B ⊗[A] K → E ⊗[B₂] K`, `b ⊗ k ↦ j b ⊗ k`, is
bijective. -/
theorem bijective_pushoutTensorMap (j : B →+* E)
    (hj : ∀ a, j (algebraMap A B a) = algebraMap B₂ E (algebraMap A B₂ a))
    (hpush : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A B₂)) (CommRingCat.ofHom j)
      (CommRingCat.ofHom (algebraMap B₂ E)))
    (K : Type*) [AddCommGroup K] [Module B₂ K] [Module A K] [IsScalarTower A B₂ K] :
    Function.Bijective (pushoutTensorMap j hj K) := by
  classical
  let iso := (CommRingCat.isPushout_tensorProduct A B B₂).isoIsPushout _ _ hpush
  let e : B ⊗[A] B₂ →+* E := iso.hom.hom
  let e' : E →+* B ⊗[A] B₂ := iso.inv.hom
  have he'e : ∀ z, e' (e z) = z := fun z => congr($(iso.hom_inv_id).hom z)
  have hee' : ∀ y, e (e' y) = y := fun y => congr($(iso.inv_hom_id).hom y)
  have hel : ∀ b : B, e (b ⊗ₜ 1) = j b := fun b =>
    congr($((CommRingCat.isPushout_tensorProduct A B B₂).inl_isoIsPushout_hom _ _ hpush).hom b)
  have her : ∀ x : B₂, e (1 ⊗ₜ x) = algebraMap B₂ E x := fun x =>
    congr($((CommRingCat.isPushout_tensorProduct A B B₂).inr_isoIsPushout_hom _ _ hpush).hom x)
  have he : ∀ (b : B) (x : B₂), e (b ⊗ₜ x) = j b * algebraMap B₂ E x := by
    intro b x
    rw [← hel, ← her, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  -- The inverse.
  let Φ : B ⊗[A] B₂ →+ K →+ B ⊗[A] K :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
            (fun k => b ⊗ₜ[A] (x • k)) (fun k k' => by rw [smul_add, TensorProduct.tmul_add]))
          (fun x x' => by ext k; simp [add_smul, TensorProduct.tmul_add]))
        (fun b b' => by ext x k; simp [TensorProduct.add_tmul]))
      (fun a b x => by
        ext k
        simp only [AddMonoidHom.mk'_apply]
        rw [smul_assoc, TensorProduct.smul_tmul])
  have hΦ : ∀ (b : B) (x : B₂) (k : K), Φ (b ⊗ₜ x) k = b ⊗ₜ (x • k) := fun _ _ _ => rfl
  have hΦmul : ∀ (z : B ⊗[A] B₂) (x : B₂) (k : K),
      Φ ((1 ⊗ₜ x) * z) k = Φ z (x • k) := by
    intro z x k
    induction z using TensorProduct.inductionOn with
    | tmul b x' => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hΦ, hΦ, mul_comm, mul_smul]
    | add z z' hz hz' => rw [mul_add, map_add, map_add, AddMonoidHom.add_apply,
        AddMonoidHom.add_apply, hz, hz']
  let χ : E ⊗[B₂] K →+ B ⊗[A] K :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun k => Φ (e' y) k)
          (fun k k' => map_add _ _ _))
        (fun y y' => by ext k; simp))
      (fun x y k => by
        simp only [AddMonoidHom.mk'_apply]
        rw [Algebra.smul_def, map_mul, ← her, he'e, hΦmul])
  have hχ : ∀ (y : E) (k : K), χ (y ⊗ₜ k) = Φ (e' y) k := fun _ _ => rfl
  have hleft : ∀ w, χ (pushoutTensorMap j hj K w) = w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul b k =>
      rw [pushoutTensorMap_tmul, hχ, ← hel, he'e, hΦ, one_smul]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  have htw : ∀ (z : B ⊗[A] B₂) (k : K), pushoutTensorMap j hj K (Φ z k) = e z ⊗ₜ k := by
    intro z k
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      rw [hΦ, pushoutTensorMap_tmul, he, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_comm]
    | add z z' hz hz' => rw [map_add, AddMonoidHom.add_apply, map_add, hz, hz', map_add,
        TensorProduct.add_tmul]
  have hright : ∀ w, pushoutTensorMap j hj K (χ w) = w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul y k => rw [hχ, htw, hee']
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

end Pushout

/-! ### A general comparison map out of a tensor product -/

section PushoutMap

variable {R S : Type*} [CommRing R] [CommRing S] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B] {N N' : Type*} [AddCommGroup N] [Module A N] [Module R N] [AddCommGroup N']
  [Module S N']

/-- A general comparison map `B ⊗[A] N → N'`, `b ⊗ n ↦ j b • g n`, for `g` semilinear over a ring
map `ψ : R → S` and a ring map `j : B → S` agreeing with `ψ` on `A`. -/
noncomputable def pushoutMap (ρ : A →+* R) (hN : ∀ (a : A) (n : N), a • n = ρ a • n)
    (j : B →+* S) (ψ : R →+* S) (hsq : ∀ a, j (algebraMap A B a) = ψ (ρ a)) (g : N →+ N')
    (hg : ∀ (r : R) (n : N), g (r • n) = ψ r • g n) : B ⊗[A] N →+ N' :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun n => j b • g n)
        (fun n n' => by rw [map_add, smul_add]))
      (fun b b' => by ext n; simp [add_smul]))
    (fun a b n => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, hsq, hN, hg, smul_smul, mul_comm (j b)])

/-- `Module.Descent.pushoutMap` sends `b ⊗ n` to `j b • g n`. -/
@[simp]
lemma pushoutMap_tmul (ρ : A →+* R) (hN : ∀ (a : A) (n : N), a • n = ρ a • n)
    (j : B →+* S) (ψ : R →+* S) (hsq : ∀ a, j (algebraMap A B a) = ψ (ρ a)) (g : N →+ N')
    (hg : ∀ (r : R) (n : N), g (r • n) = ψ r • g n) (b : B) (n : N) :
    pushoutMap ρ hN j ψ hsq g hg (b ⊗ₜ n) = j b • g n := rfl

end PushoutMap

/-! ### Graded pieces of the kernel of a surjection -/

section Graded

/-- The `k`-th graded piece `I ^ k / I ^ (k + 1)` of the kernel `I` of a ring map `π`, written as
the quotient of `I ^ k` by `I • I ^ k`. -/
abbrev grPiece {R' R : Type*} [CommRing R'] [CommRing R] (π : R' →+* R) (k : ℕ) : Type _ :=
  ↥(RingHom.ker π ^ k) ⧸ (RingHom.ker π • (⊤ : Submodule R' ↥(RingHom.ker π ^ k)))

variable {R' R S' S : Type*} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]

/-- The module structure of `Module.Descent.grPiece` over the target of a surjection. -/
noncomputable abbrev grPiece.module {π : R' →+* R} (hπ : Function.Surjective π) (k : ℕ) :
    Module R (grPiece π k) :=
  Module.compHom _ (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/-- In `Module.Descent.grPiece.module`, `π r` acts on a graded piece as `r` does. -/
lemma grPiece.module_smul {π : R' →+* R} (hπ : Function.Surjective π) (k : ℕ) (r : R')
    (x : grPiece π k) :
    (grPiece.module hπ k).toSMul.smul (π r) x = r • x := by
  change (RingHom.quotientKerEquivOfSurjective hπ).symm (π r) • x = r • x
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply hπ r]
  exact Module.IsTorsionBySet.mk_smul _ r x

/-- A ring map carrying `ker π` into `ker π'` carries `(ker π) ^ k` into `(ker π') ^ k`. -/
lemma mem_ker_pow_map {π : R' →+* R} {π' : S' →+* S} (φ : R' →+* S')
    (h : ∀ x ∈ RingHom.ker π, φ x ∈ RingHom.ker π') (k : ℕ) {x : R'}
    (hx : x ∈ RingHom.ker π ^ k) : φ x ∈ RingHom.ker π' ^ k := by
  have hle : (RingHom.ker π).map φ ≤ RingHom.ker π' := Ideal.map_le_iff_le_comap.2 h
  have : φ x ∈ (RingHom.ker π ^ k).map φ := Ideal.mem_map_of_mem φ hx
  rw [Ideal.map_pow] at this
  exact pow_le_pow_left' hle k this

/-- The map of graded pieces induced by a ring map carrying one kernel into the other. -/
noncomputable def grMap {π : R' →+* R} {π' : S' →+* S} (φ : R' →+* S')
    (h : ∀ x ∈ RingHom.ker π, φ x ∈ RingHom.ker π') (k : ℕ) :
    grPiece π k →ₛₗ[φ] grPiece π' k :=
  Submodule.mapQ _ _
    { toFun := fun x => ⟨φ x, mem_ker_pow_map φ h k x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp }
    (Submodule.smul_le.2 fun r hr n _ => by
      refine Submodule.mem_comap.2 ?_
      have : (⟨φ (r • n : ↥(RingHom.ker π ^ k)), mem_ker_pow_map φ h k (r • n).2⟩ :
          ↥(RingHom.ker π' ^ k)) = φ r • ⟨φ n, mem_ker_pow_map φ h k n.2⟩ := by
        ext; simp
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [this]
      exact Submodule.smul_mem_smul (h r hr) trivial)

/-- `Module.Descent.grMap φ` sends the class of `x ∈ I ^ k` to the class of `φ x`. -/
@[simp]
lemma grMap_mk {π : R' →+* R} {π' : S' →+* S} (φ : R' →+* S')
    (h : ∀ x ∈ RingHom.ker π, φ x ∈ RingHom.ker π') (k : ℕ) (x : ↥(RingHom.ker π ^ k)) :
    grMap φ h k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨φ x, mem_ker_pow_map φ h k x.2⟩ := rfl

/-- An element of `I ^ k` is zero in the `k`-th graded piece exactly when it lies in
`I ^ (k + 1)`. -/
lemma grPiece_mk_eq_zero_iff {π : R' →+* R} (k : ℕ) (x : ↥(RingHom.ker π ^ k)) :
    (Submodule.Quotient.mk x : grPiece π k) = 0 ↔ (x : R') ∈ RingHom.ker π ^ (k + 1) := by
  rw [Submodule.Quotient.mk_eq_zero]
  have hmap : (RingHom.ker π • (⊤ : Submodule R' ↥(RingHom.ker π ^ k))).map
      (RingHom.ker π ^ k).subtype = RingHom.ker π ^ (k + 1) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Ideal.smul_eq_mul,
      pow_succ']
  rw [← hmap]
  constructor
  · exact fun hx => Submodule.mem_map_of_mem hx
  · rintro ⟨y, hy, hyx⟩
    rwa [show y = x from Subtype.ext hyx] at hy

/-- `Module.Descent.grMap φ` is semilinear over a ring map `ψ : R → S` compatible with `φ`
and the surjections `π`, `π'`. -/
lemma grMap_smul {π : R' →+* R} {π' : S' →+* S} (k : ℕ) [Module R (grPiece π k)]
    [Module S (grPiece π' k)]
    (hπ : Function.Surjective π) (hR : ∀ (r : R') (x : grPiece π k), π r • x = r • x)
    (hS : ∀ (s : S') (x : grPiece π' k), π' s • x = s • x) (φ : R' →+* S') (ψ : R →+* S)
    (hψ : π'.comp φ = ψ.comp π) (h : ∀ x ∈ RingHom.ker π, φ x ∈ RingHom.ker π') (r : R)
    (x : grPiece π k) : grMap φ h k (r • x) = ψ r • grMap φ h k x := by
  obtain ⟨r', rfl⟩ := hπ r
  rw [hR, LinearMap.map_smulₛₗ, ← RingHom.comp_apply ψ π, ← hψ, RingHom.comp_apply, hS]

/-- **Flat base change of the graded pieces of an ideal.** For `φ : R' → S'` flat and
`ker π' = (ker π) S'`, the map `S ⊗[R] grₖ(ker π) → grₖ(ker π')`, `s ⊗ x ↦ s • φ x`, is
bijective. -/
@[ega "IV 16.4.6" "special case"]
theorem bijective_tensor_grMap {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S']
    [CommRing S] [Algebra R S] {π : R' →+* R} {π' : S' →+* S} (k : ℕ)
    [Module R (grPiece π k)] [Module S (grPiece π' k)]
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hR : ∀ (r : R') (x : grPiece π k), π r • x = r • x)
    (hS : ∀ (s : S') (x : grPiece π' k), π' s • x = s • x) (φ : R' →+* S') (hφ : φ.Flat)
    (hψ : π'.comp φ = (algebraMap R S).comp π)
    (hker : RingHom.ker π' = (RingHom.ker π).map φ)
    (h : ∀ x ∈ RingHom.ker π, φ x ∈ RingHom.ker π') :
    Function.Bijective (pushoutMap (RingHom.id R) (fun _ _ => rfl) (RingHom.id S)
      (algebraMap R S) (fun _ => rfl) (grMap φ h k).toAddMonoidHom
      (grMap_smul k hπ hR hS φ (algebraMap R S) hψ h)) := by
  classical
  let : Algebra R' S' := φ.toAlgebra
  have : Module.Flat R' S' := hφ
  set Φ₀ := pushoutMap (RingHom.id R) (fun _ _ => rfl) (RingHom.id S)
      (algebraMap R S) (fun _ => rfl) (grMap φ h k).toAddMonoidHom
      (grMap_smul k hπ hR hS φ (algebraMap R S) hψ h)
  have hpow : ∀ m, (RingHom.ker π ^ m).map (algebraMap R' S') = RingHom.ker π' ^ m :=
    fun m => by rw [Ideal.map_pow, hker]; rfl
  -- `E m : S' ⊗[R'] I ^ m ≅ (ker π') ^ m`.
  let E : ∀ m, S' ⊗[R'] ↥(RingHom.ker π ^ m) ≃ₗ[S'] ↥(RingHom.ker π' ^ m) := fun m =>
    (idealBaseChangeEquiv (S := S') (RingHom.ker π ^ m)).trans (LinearEquiv.ofEq _ _ (hpow m))
  have hEval : ∀ m (y : S' ⊗[R'] ↥(RingHom.ker π ^ m)),
      ((E m y : ↥(RingHom.ker π' ^ m)) : S') =
        idealBaseChangeEquiv (S := S') (RingHom.ker π ^ m) y := fun _ _ => rfl
  -- `π₀ : S' ⊗[R'] I ^ k → S ⊗[R] grₖ`.
  let π₀ : S' ⊗[R'] ↥(RingHom.ker π ^ k) →+ S ⊗[R] grPiece π k :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun s => AddMonoidHom.mk'
          (fun x => π' s ⊗ₜ[R] (Submodule.Quotient.mk x : grPiece π k))
          (fun x x' => by rw [Submodule.Quotient.mk_add, TensorProduct.tmul_add]))
        (fun s s' => by ext x; simp [TensorProduct.add_tmul]))
      (fun r s x => by
        simp only [AddMonoidHom.mk'_apply]
        rw [Algebra.smul_def, map_mul, show algebraMap R' S' r = φ r from rfl,
          ← RingHom.comp_apply π' φ, hψ, RingHom.comp_apply, ← Algebra.smul_def,
          TensorProduct.smul_tmul, hR, Submodule.Quotient.mk_smul])
  have hπ₀ : ∀ (s : S') (x : ↥(RingHom.ker π ^ k)),
      π₀ (s ⊗ₜ x) = π' s ⊗ₜ (Submodule.Quotient.mk x : grPiece π k) := fun _ _ => rfl
  have hπ₀surj : Function.Surjective π₀ := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s n =>
      obtain ⟨s', rfl⟩ := hπ' s
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ n
      exact ⟨s' ⊗ₜ x, rfl⟩
    | add y z hy hz =>
      obtain ⟨Y, rfl⟩ := hy
      obtain ⟨Z, rfl⟩ := hz
      exact ⟨Y + Z, map_add _ _ _⟩
  have hkey : ∀ Y, Φ₀ (π₀ Y) = Submodule.Quotient.mk (E k Y) := by
    intro Y
    induction Y using TensorProduct.inductionOn with
    | tmul s x =>
      rw [hπ₀]
      change (RingHom.id S (π' s)) • grMap φ h k (Submodule.Quotient.mk x) = _
      rw [RingHom.id_apply, grMap_mk, hS, ← Submodule.Quotient.mk_smul]
      congr 1
    | add Y Z hY hZ => simp only [map_add, hY, hZ, Submodule.Quotient.mk_add]
  let incl : ↥(RingHom.ker π ^ (k + 1)) →ₗ[R'] ↥(RingHom.ker π ^ k) :=
    Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ k))
  have hπ₀incl : ∀ Z, π₀ (LinearMap.lTensor S' incl Z) = 0 := by
    intro Z
    induction Z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [LinearMap.lTensor_tmul, hπ₀, (grPiece_mk_eq_zero_iff k _).2 x.2,
        TensorProduct.tmul_zero]
    | add Z Z' hZ hZ' => rw [map_add, map_add, hZ, hZ', add_zero]
  have hEincl : ∀ Z, ((E k (LinearMap.lTensor S' incl Z) : ↥(RingHom.ker π' ^ k)) : S') =
      ((E (k + 1) Z : ↥(RingHom.ker π' ^ (k + 1))) : S') := by
    intro Z
    simp only [hEval]
    induction Z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [LinearMap.lTensor_tmul, idealBaseChangeEquiv_tmul, idealBaseChangeEquiv_tmul]
      rfl
    | add Z Z' hZ hZ' => rw [map_add, map_add, Submodule.coe_add, hZ, hZ', map_add,
        Submodule.coe_add]
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun n => ?_⟩
  · obtain ⟨Y, rfl⟩ := hπ₀surj y
    rw [hkey, grPiece_mk_eq_zero_iff] at hy
    obtain ⟨Z, hZ⟩ := (E (k + 1)).surjective ⟨_, hy⟩
    rw [← (E k).injective (Subtype.ext ((hEincl Z).trans (congrArg Subtype.val hZ)))]
    exact hπ₀incl Z
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨Y, rfl⟩ := (E k).surjective z
    exact ⟨π₀ Y, hkey Y⟩

end Graded

/-! ### Lifting invariant functions along a nilpotent thickening of a descent situation -/

section Lift

variable {R' R S : Type*} [CommRing R'] [CommRing R] [CommRing S]

/-- A ring map `R' → S` killing the kernel of a surjection `π : R' → R`, descended to `R`. -/
noncomputable def descendHom {π : R' →+* R} (hπ : Function.Surjective π) (f : R' →+* S)
    (h : RingHom.ker π ≤ RingHom.ker f) : R →+* S :=
  (Ideal.Quotient.lift (RingHom.ker π) f h).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/-- `Module.Descent.descendHom` composed with `π` is the original ring map. -/
lemma descendHom_comp {π : R' →+* R} (hπ : Function.Surjective π) (f : R' →+* S)
    (h : RingHom.ker π ≤ RingHom.ker f) : (descendHom hπ f h).comp π = f := by
  ext r
  change Ideal.Quotient.lift _ f h ((RingHom.quotientKerEquivOfSurjective hπ).symm (π r)) = f r
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply hπ r]
  rfl

/-- If `ker π' = (ker π) R''` along `f`, then `f` carries `ker π` into `ker π'`. -/
lemma map_mem_ker_of_map_eq {R'' S'' : Type*} [CommRing R''] [CommRing S''] {π : R' →+* R}
    {π' : R'' →+* S''} (f : R' →+* R'') (h : RingHom.ker π' = (RingHom.ker π).map f)
    (x : R') (hx : x ∈ RingHom.ker π) : f x ∈ RingHom.ker π' := by
  rw [h]
  exact Ideal.mem_map_of_mem f hx

end Lift

section MainLift

variable {A B' C' D' B C D : Type u} [CommRing A] [CommRing B'] [CommRing C'] [CommRing D']
  [CommRing B] [CommRing C] [CommRing D] [Algebra A B]

/-- For a pushout square of rings `u ∘ f = v ∘ g`, `u (f x) = v (g x)` for every `x`. -/
lemma comp_apply_of_isPushout {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    {P : Type u} [CommRing P] {f : X →+* Y} {g : X →+* Z} {u : Y →+* P} {v : Z →+* P}
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom u) (CommRingCat.ofHom v)) (x : X) : u (f x) = v (g x) := by
  simpa using congrArg (fun φ => φ.hom x) h.w

/-- **One step of the lift.** In the situation of
`Module.Descent.exists_eq_of_isNilpotent_ker`, every one-cocycle in the `m`-th graded piece of the
kernel on the double overlap is the coboundary of an element of the `m`-th graded piece of the
kernel on the chart. -/
theorem exists_grMap_sub_grMap_eq [Module.FaithfullyFlat A B]
    (s t : B' →+* C') (μ : C' →+* B') (f₁₂ f₁₃ f₂₃ : C' →+* D')
    {πB : B' →+* B} (hπB : Function.Surjective πB) {πC : C' →+* C}
    (hπC : Function.Surjective πC) {πD : D' →+* D} (hπD : Function.Surjective πD)
    (i₁ i₂ : B →+* C) (g₁₂ g₂₃ : C →+* D)
    (hi₁ : πC.comp s = i₁.comp πB) (hi₂ : πC.comp t = i₂.comp πB)
    (hg₁₂ : πD.comp f₁₂ = g₁₂.comp πC) (hg₂₃ : πD.comp f₂₃ = g₂₃.comp πC)
    (hμs : μ.comp s = RingHom.id B') (hμt : μ.comp t = RingHom.id B')
    (h₁₂₁₃ : f₁₂.comp s = f₁₃.comp s) (h₁₂₂₃ : f₁₂.comp t = f₂₃.comp s)
    (h₁₃₂₃ : f₁₃.comp t = f₂₃.comp t)
    (_hKs : RingHom.ker πC = (RingHom.ker πB).map s)
    (hKt : RingHom.ker πC = (RingHom.ker πB).map t)
    (hL : RingHom.ker πD = (RingHom.ker πC).map f₂₃) (htflat : t.Flat) (hflat : f₂₃.Flat)
    (P1 : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom i₁) (CommRingCat.ofHom i₂))
    (P2 : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (i₁.comp (algebraMap A B))) (CommRingCat.ofHom (g₁₂.comp i₁))
      (CommRingCat.ofHom g₂₃))
    (m : ℕ)
    (hs : ∀ x ∈ RingHom.ker πB, s x ∈ RingHom.ker πC)
    (ht : ∀ x ∈ RingHom.ker πB, t x ∈ RingHom.ker πC)
    (h12 : ∀ x ∈ RingHom.ker πC, f₁₂ x ∈ RingHom.ker πD)
    (h13 : ∀ x ∈ RingHom.ker πC, f₁₃ x ∈ RingHom.ker πD)
    (h23 : ∀ x ∈ RingHom.ker πC, f₂₃ x ∈ RingHom.ker πD)
    (ξ : grPiece πC m)
    (hξ : grMap f₁₂ h12 m ξ - grMap f₁₃ h13 m ξ + grMap f₂₃ h23 m ξ = 0) :
    ∃ x : grPiece πB m, grMap s hs m x - grMap t ht m x = ξ := by
  classical
  -- Kernel inclusions for the diagonal.
  have hμ : ∀ x ∈ RingHom.ker πC, μ x ∈ RingHom.ker πB :=
    map_mem_ker_of_map_eq μ (by rw [hKt, Ideal.map_map, hμt, Ideal.map_id])
  -- The reduced diagonal and third partial projection.
  let μ₀ : C →+* B := descendHom hπC (πB.comp μ) (fun x hx => by
    simpa [RingHom.mem_ker] using hμ x hx)
  have hμ₀ : μ₀.comp πC = πB.comp μ := descendHom_comp _ _ _
  let g₁₃ : C →+* D := descendHom hπC (πD.comp f₁₃) (fun x hx => by
    simpa [RingHom.mem_ker] using h13 x hx)
  have hg₁₃ : g₁₃.comp πC = πD.comp f₁₃ := descendHom_comp _ _ _
  -- Module structures on the graded pieces.
  let mB : Module B (grPiece πB m) := grPiece.module hπB m
  let mC : Module C (grPiece πC m) := grPiece.module hπC m
  let mD : Module D (grPiece πD m) := grPiece.module hπD m
  let mA : Module A (grPiece πB m) := Module.compHom _ (algebraMap A B)
  have : IsScalarTower A B (grPiece πB m) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hRB : ∀ (r : B') (x : grPiece πB m), πB r • x = r • x := grPiece.module_smul hπB m
  have hRC : ∀ (r : C') (x : grPiece πC m), πC r • x = r • x := grPiece.module_smul hπC m
  have hRD : ∀ (r : D') (x : grPiece πD m), πD r • x = r • x := grPiece.module_smul hπD m
  have hA : ∀ a : A, i₁ (algebraMap A B a) = i₂ (algebraMap A B a) :=
    comp_apply_of_isPushout P1
  -- Ring identities on the reduced rings.
  have hμ₁ : ∀ b, μ₀ (i₁ b) = b := by
    intro b
    obtain ⟨b', rfl⟩ := hπB b
    rw [← RingHom.comp_apply i₁ πB, ← hi₁, RingHom.comp_apply, ← RingHom.comp_apply μ₀ πC,
      hμ₀, RingHom.comp_apply, ← RingHom.comp_apply μ s, hμs, RingHom.id_apply]
  have hr₁₂₁₃ : ∀ b, g₁₂ (i₁ b) = g₁₃ (i₁ b) := by
    intro b
    obtain ⟨b', rfl⟩ := hπB b
    rw [← RingHom.comp_apply i₁ πB, ← hi₁, RingHom.comp_apply, ← RingHom.comp_apply g₁₂ πC,
      ← hg₁₂, ← RingHom.comp_apply g₁₃ πC, hg₁₃, RingHom.comp_apply, RingHom.comp_apply,
      ← RingHom.comp_apply f₁₂ s, h₁₂₁₃, RingHom.comp_apply]
  have hr₁₂₂₃ : ∀ b, g₁₂ (i₂ b) = g₂₃ (i₁ b) := by
    intro b
    obtain ⟨b', rfl⟩ := hπB b
    rw [← RingHom.comp_apply i₂ πB, ← hi₂, ← RingHom.comp_apply i₁ πB, ← hi₁,
      RingHom.comp_apply, RingHom.comp_apply, ← RingHom.comp_apply g₁₂ πC, ← hg₁₂,
      ← RingHom.comp_apply g₂₃ πC, ← hg₂₃, RingHom.comp_apply, RingHom.comp_apply,
      ← RingHom.comp_apply f₁₂ t, h₁₂₂₃, RingHom.comp_apply]
  -- The pullback maps on graded pieces.
  let α₁ := (grMap s hs m).toAddMonoidHom
  let α₂ := (grMap t ht m).toAddMonoidHom
  let Δ := (grMap μ hμ m).toAddMonoidHom
  let γ₁₂ := (grMap f₁₂ h12 m).toAddMonoidHom
  let γ₁₃ := (grMap f₁₃ h13 m).toAddMonoidHom
  let γ₂₃ := (grMap f₂₃ h23 m).toAddMonoidHom
  have hα₁ : ∀ (b : B) (k : grPiece πB m), α₁ (b • k) = i₁ b • α₁ k :=
    grMap_smul m hπB hRB hRC s i₁ hi₁ hs
  have hα₂ : ∀ (b : B) (k : grPiece πB m), α₂ (b • k) = i₂ b • α₂ k :=
    grMap_smul m hπB hRB hRC t i₂ hi₂ ht
  have hΔ : ∀ (c : C) (l : grPiece πC m), Δ (c • l) = μ₀ c • Δ l :=
    grMap_smul m hπC hRC hRB μ μ₀ hμ₀.symm hμ
  have hγ₁₂ : ∀ (c : C) (l : grPiece πC m), γ₁₂ (c • l) = g₁₂ c • γ₁₂ l :=
    grMap_smul m hπC hRC hRD f₁₂ g₁₂ hg₁₂ h12
  have hγ₁₃ : ∀ (c : C) (l : grPiece πC m), γ₁₃ (c • l) = g₁₃ c • γ₁₃ l :=
    grMap_smul m hπC hRC hRD f₁₃ g₁₃ hg₁₃.symm h13
  have hγ₂₃ : ∀ (c : C) (l : grPiece πC m), γ₂₃ (c • l) = g₂₃ c • γ₂₃ l :=
    grMap_smul m hπC hRC hRD f₂₃ g₂₃ hg₂₃ h23
  -- Compatibilities, checked on representatives.
  have hcomp : ∀ {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z] {πX : X →+* B}
      {πY : Y →+* C} {πZ : Z →+* D} (u : X →+* Y) (u' : X →+* Y) (v : Y →+* Z) (v' : Y →+* Z)
      (hu : ∀ x ∈ RingHom.ker πX, u x ∈ RingHom.ker πY)
      (hu' : ∀ x ∈ RingHom.ker πX, u' x ∈ RingHom.ker πY)
      (hv : ∀ x ∈ RingHom.ker πY, v x ∈ RingHom.ker πZ)
      (hv' : ∀ x ∈ RingHom.ker πY, v' x ∈ RingHom.ker πZ)
      (huv : v.comp u = v'.comp u') (k : grPiece πX m),
      grMap v hv m (grMap u hu m k) = grMap v' hv' m (grMap u' hu' m k) := by
    intro X Y Z _ _ _ πX πY πZ u u' v v' hu hu' hv hv' huv k
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ k
    simp only [grMap_mk]
    congr 2
    exact congrArg (fun φ : X →+* Z => φ x) huv
  have hΔ₁ : ∀ k, Δ (α₁ k) = k := by
    intro k
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ k
    change grMap μ hμ m (grMap s hs m (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
    simp only [grMap_mk]
    congr 2
    exact congrArg (fun φ : B' →+* B' => φ x) hμs
  have hΔ₂ : ∀ k, Δ (α₂ k) = k := by
    intro k
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ k
    change grMap μ hμ m (grMap t ht m (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
    simp only [grMap_mk]
    congr 2
    exact congrArg (fun φ : B' →+* B' => φ x) hμt
  have hγα₁ : ∀ k, γ₁₂ (α₁ k) = γ₁₃ (α₁ k) := fun k =>
    hcomp s s f₁₂ f₁₃ hs hs h12 h13 h₁₂₁₃ k
  have hγα₂ : ∀ k, γ₁₂ (α₂ k) = γ₂₃ (α₁ k) := fun k =>
    hcomp t s f₁₂ f₂₃ ht hs h12 h23 h₁₂₂₃ k
  have hγα₃ : ∀ k, γ₁₃ (α₂ k) = γ₂₃ (α₂ k) := fun k =>
    hcomp t t f₁₃ f₂₃ ht ht h13 h23 h₁₃₂₃ k
  -- The first comparison map is bijective.
  have hLbij : Function.Bijective (cmpLeft i₁ i₂ hA α₂ hα₂) := by
    let : Algebra B C := i₂.toAlgebra
    have h0 := bijective_tensor_grMap m hπB hπC hRB hRC t htflat hi₂ hKt ht
    have h1 := bijective_pushoutTensorMap (A := A) (B₂ := B) i₁ hA P1 (grPiece πB m)
    convert h0.comp h1 using 1
    ext y
    induction y using TensorProduct.inductionOn with
    | tmul b k => rfl
    | add y z hy hz =>
      simp only [map_add, Function.comp_apply] at hy hz ⊢
      rw [hy, hz]
  -- The second comparison map is injective.
  have hPinj : Function.Injective
      (cmpRight i₁ i₂ hA α₂ hα₂ g₁₂ g₂₃ hr₁₂₂₃ γ₂₃ hγ₂₃) := by
    let : Algebra A C := (i₁.comp (algebraMap A B)).toAlgebra
    let : Algebra C D := g₂₃.toAlgebra
    let mAC : Module A (grPiece πC m) := Module.compHom _ (i₁.comp (algebraMap A B))
    have : IsScalarTower A C (grPiece πC m) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let θ : B ⊗[A] grPiece πB m →ₗ[A] grPiece πC m :=
      { toFun := cmpLeft i₁ i₂ hA α₂ hα₂
        map_add' := map_add _
        map_smul' := fun a y => by
          rw [RingHom.id_apply, ← algebraMap_smul B a y, cmpLeft_smul]
          rfl }
    let eθ : B ⊗[A] grPiece πB m ≃ₗ[A] grPiece πC m := LinearEquiv.ofBijective θ hLbij
    have h0 := bijective_tensor_grMap m hπC hπD hRC hRD f₂₃ hflat hg₂₃ hL h23
    have h1 := bijective_pushoutTensorMap (A := A) (B₂ := C) (g₁₂.comp i₁)
      (comp_apply_of_isPushout P2) P2 (grPiece πC m)
    convert (h0.comp (h1.comp (eθ.lTensor B).bijective)).1 using 1
    ext y
    induction y using TensorProduct.inductionOn with
    | tmul b k => rfl
    | add y z hy hz =>
      simp only [map_add, Function.comp_apply] at hy hz ⊢
      rw [hy, hz]
  exact exists_sub_eq_of_cocycle i₁ i₂ μ₀ g₁₂ g₁₃ g₂₃ hA hμ₁ hr₁₂₁₃ hr₁₂₂₃ α₁ α₂ hα₁ hα₂ Δ hΔ
    hΔ₁ hΔ₂ γ₁₂ γ₁₃ γ₂₃ hγ₁₂ hγ₁₃ hγ₂₃ hγα₁ hγα₂ hγα₃ hLbij hPinj ξ hξ

/-- **Invariant lifts along a nilpotent thickening of a descent situation.** Let `A → B` be
faithfully flat, and let `B' → B`, `C' → C`, `D' → D` be surjections with nilpotent kernel `J` on
`B'`, standing for the rings of an affine chart `V`, its self-intersection `V ×_X V` and triple
intersection of a thickening `X` of `Spec A`, with `B`, `C`, `D` the rings of the reductions. Let
`s t : B' → C'` be the two projections, `μ` the diagonal and `f₁₂ f₁₃ f₂₃ : C' → D'` the partial
projections, satisfying the simplicial identities. Suppose the kernel on `C'` is `J C'` along
either projection and the kernel on `D'` is extended along `f₂₃`, that `t` and `f₂₃` are flat,
and that the reductions are the tensor products `C = B ⊗[A] B` and `D = B ⊗[A] C`. Then every
`a ∈ A` lifts to an element of `B'` with equal images under the two projections. -/
theorem exists_eq_of_isNilpotent_ker [Module.FaithfullyFlat A B]
    (s t : B' →+* C') (μ : C' →+* B') (f₁₂ f₁₃ f₂₃ : C' →+* D')
    {πB : B' →+* B} (hπB : Function.Surjective πB) {πC : C' →+* C}
    (hπC : Function.Surjective πC) {πD : D' →+* D} (hπD : Function.Surjective πD)
    (i₁ i₂ : B →+* C) (g₁₂ g₂₃ : C →+* D)
    (hi₁ : πC.comp s = i₁.comp πB) (hi₂ : πC.comp t = i₂.comp πB)
    (hg₁₂ : πD.comp f₁₂ = g₁₂.comp πC) (hg₂₃ : πD.comp f₂₃ = g₂₃.comp πC)
    (hμs : μ.comp s = RingHom.id B') (hμt : μ.comp t = RingHom.id B')
    (h₁₂₁₃ : f₁₂.comp s = f₁₃.comp s) (h₁₂₂₃ : f₁₂.comp t = f₂₃.comp s)
    (h₁₃₂₃ : f₁₃.comp t = f₂₃.comp t)
    (hKs : RingHom.ker πC = (RingHom.ker πB).map s)
    (hKt : RingHom.ker πC = (RingHom.ker πB).map t)
    (hL : RingHom.ker πD = (RingHom.ker πC).map f₂₃) (htflat : t.Flat) (hflat : f₂₃.Flat)
    (hnil : IsNilpotent (RingHom.ker πB))
    (P1 : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom i₁) (CommRingCat.ofHom i₂))
    (P2 : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (i₁.comp (algebraMap A B))) (CommRingCat.ofHom (g₁₂.comp i₁))
      (CommRingCat.ofHom g₂₃))
    (a : A) : ∃ b : B', s b = t b ∧ πB b = algebraMap A B a := by
  classical
  have hs : ∀ x ∈ RingHom.ker πB, s x ∈ RingHom.ker πC := map_mem_ker_of_map_eq s hKs
  have ht : ∀ x ∈ RingHom.ker πB, t x ∈ RingHom.ker πC := map_mem_ker_of_map_eq t hKt
  have h23 : ∀ x ∈ RingHom.ker πC, f₂₃ x ∈ RingHom.ker πD := map_mem_ker_of_map_eq f₂₃ hL
  have h12 : ∀ x ∈ RingHom.ker πC, f₁₂ x ∈ RingHom.ker πD := by
    refine map_mem_ker_of_map_eq f₁₂ ?_
    symm
    rw [hKt, Ideal.map_map, h₁₂₂₃, ← Ideal.map_map, ← hKs, hL]
  have h13 : ∀ x ∈ RingHom.ker πC, f₁₃ x ∈ RingHom.ker πD := by
    refine map_mem_ker_of_map_eq f₁₃ ?_
    symm
    rw [hKt, Ideal.map_map, h₁₃₂₃, ← Ideal.map_map, ← hKt, hL]
  have hA : ∀ a : A, i₁ (algebraMap A B a) = i₂ (algebraMap A B a) :=
    comp_apply_of_isPushout P1
  have hcoc : ∀ b : B', f₁₂ (s b - t b) - f₁₃ (s b - t b) + f₂₃ (s b - t b) = 0 := by
    intro b
    have e1 := RingHom.congr_fun h₁₂₁₃ b
    have e2 := RingHom.congr_fun h₁₂₂₃ b
    have e3 := RingHom.congr_fun h₁₃₂₃ b
    simp only [RingHom.comp_apply] at e1 e2 e3
    simp only [map_sub, e1, e2, e3]
    ring
  have key : ∀ m : ℕ, ∃ b : B', πB b = algebraMap A B a ∧
      s b - t b ∈ RingHom.ker πC ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨b, hb⟩ := hπB (algebraMap A B a)
      refine ⟨b, hb, ?_⟩
      rw [zero_add, pow_one, RingHom.mem_ker, map_sub, ← RingHom.comp_apply πC s,
        ← RingHom.comp_apply πC t, hi₁, hi₂, RingHom.comp_apply, RingHom.comp_apply, hb, hA,
        sub_self]
    | succ m ih =>
      obtain ⟨b, hb, hδ⟩ := ih
      let ξ : grPiece πC (m + 1) := Submodule.Quotient.mk ⟨s b - t b, hδ⟩
      have hξ : grMap f₁₂ h12 (m + 1) ξ - grMap f₁₃ h13 (m + 1) ξ +
          grMap f₂₃ h23 (m + 1) ξ = 0 := by
        simp only [ξ, grMap_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
        rw [← Submodule.Quotient.mk_zero]
        congr 1
        exact Subtype.ext (hcoc b)
      obtain ⟨x, hx⟩ := exists_grMap_sub_grMap_eq s t μ f₁₂ f₁₃ f₂₃ hπB hπC hπD i₁ i₂ g₁₂
        g₂₃ hi₁ hi₂ hg₁₂ hg₂₃ hμs hμt h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hKs hKt hL htflat hflat P1 P2 (m + 1)
        hs ht h12 h13 h23 ξ hξ
      obtain ⟨j, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine ⟨b - j, ?_, ?_⟩
      · rw [map_sub, RingHom.mem_ker.1 (Ideal.pow_le_self (Nat.succ_ne_zero m) j.2), sub_zero, hb]
      · simp only [ξ, grMap_mk, ← Submodule.Quotient.mk_sub] at hx
        have h0 : (Submodule.Quotient.mk
            (⟨s j, mem_ker_pow_map s hs (m + 1) j.2⟩ - ⟨t j, mem_ker_pow_map t ht (m + 1) j.2⟩ -
              ⟨s b - t b, hδ⟩) : grPiece πC (m + 1)) = 0 := by
          rw [Submodule.Quotient.mk_sub, hx, sub_self]
        rw [grPiece_mk_eq_zero_iff] at h0
        have h1 : s (b - j) - t (b - j) = -((s j - t j) - (s b - t b)) := by
          rw [map_sub, map_sub]
          ring
        rw [h1]
        refine (Ideal.neg_mem_iff _).2 ?_
        simpa using h0
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨b, hb, hbN⟩ := key N
  refine ⟨b, ?_, hb⟩
  have hKN : RingHom.ker πC ^ N = ⊥ := by
    rw [hKt, ← Ideal.map_pow, hN, Submodule.zero_eq_bot, Ideal.map_bot]
  have : s b - t b ∈ RingHom.ker πC ^ N := Ideal.pow_le_pow_right (Nat.le_succ N) hbN
  rwa [hKN, Ideal.mem_bot, sub_eq_zero] at this

end MainLift

end Module.Descent

end
