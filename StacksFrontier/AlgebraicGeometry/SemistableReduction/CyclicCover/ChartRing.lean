module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit

/-!
# The chart ring of a cyclic cover

Let `k` be a field, `A` and `S` two `k`-algebras, `n` a natural number, `f, g ∈ A` with `g f = 1`
and `c ∈ S`. Write `Q = A ⊗_k S`. The *chart ring* is

`B = Q[x]/(xⁿ - c f)`.

It is the ring of functions of the cyclic cover `Spec_{Z_S}(Sym(L_S)/(φ - c))` over an affine open
of the base on which the invertible module is trivialized: there the total space of the line
bundle is `Spec A[T]`, the function `φ⁻¹(1)` is `g Tⁿ`, and `B` is the pushout of
`A[T] ← k[y] → S` along `y ↦ g Tⁿ` and `y ↦ c`.

## Main definitions

* `Stacks.CyclicCover.chartRing`: the ring `Q[x]/(xⁿ - c f)`.
* `Stacks.CyclicCover.totalHom`, `Stacks.CyclicCover.pointHom`: the maps `y ↦ g Tⁿ` and `y ↦ c`
  out of `k[y]`.
* `Stacks.CyclicCover.chartLeft`, `Stacks.CyclicCover.chartRight`: the maps `A[T] → B`,
  `T ↦ x`, and `S → B`.

## Main results

* `Stacks.CyclicCover.isPushout_chart`: `B` is the pushout of `A[T] ← k[y] → S`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Polynomial TensorProduct

universe u

namespace Stacks.CyclicCover

variable {k A S : Type u} [Field k] [CommRing A] [Algebra k A] [CommRing S] [Algebra k S]

variable (k) in
/-- The chart ring `(A ⊗_k S)[x]/(xⁿ - c f)`. -/
abbrev chartRing (n : ℕ) (f : A) (c : S) : Type u :=
  AdjoinRoot (X ^ n - C (f ⊗ₜ[k] c) : (A ⊗[k] S)[X])

variable (k) in
/-- The map `k[y] → A[T]`, `y ↦ g Tⁿ`. -/
def totalHom (n : ℕ) (g : A) : k[X] →+* A[X] :=
  (aeval (R := k) (C g * X ^ n : A[X])).toRingHom

/-- The map `k[y] → S`, `y ↦ c`. -/
def pointHom (c : S) : k[X] →+* S :=
  (aeval (R := k) c).toRingHom

variable (n : ℕ) (f g : A) (c : S)

variable (k) in
/-- The map `A[T] → (A ⊗_k S)[x]/(xⁿ - c f)`, `a ↦ a ⊗ 1`, `T ↦ x`. -/
def chartLeft : A[X] →+* chartRing k n f c :=
  eval₂RingHom ((algebraMap (A ⊗[k] S) (chartRing k n f c)).comp
    Algebra.TensorProduct.includeLeftRingHom) (AdjoinRoot.root _)

variable (k) in
/-- The map `S → (A ⊗_k S)[x]/(xⁿ - c f)`, `s ↦ 1 ⊗ s`. -/
def chartRight : S →+* chartRing k n f c :=
  (algebraMap (A ⊗[k] S) (chartRing k n f c)).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := S)).toRingHom

/-- `chartLeft` sends the constant `a` to the image of `a ⊗ 1`. -/
theorem chartLeft_C (a : A) :
    chartLeft k n f c (C a) = algebraMap (A ⊗[k] S) (chartRing k n f c) (a ⊗ₜ 1) := by
  simp [chartLeft]

/-- `chartLeft` sends `T` to the root `x`. -/
theorem chartLeft_X : chartLeft k n f c X = AdjoinRoot.root _ := by
  simp [chartLeft]

/-- `chartRight` sends `s` to the image of `1 ⊗ s`. -/
theorem chartRight_apply (s : S) :
    chartRight k n f c s = algebraMap (A ⊗[k] S) (chartRing k n f c) (1 ⊗ₜ s) := rfl

/-- In `Q[x]/(xⁿ - u)`, `xⁿ = u`. -/
private theorem root_pow_eq {Q : Type u} [CommRing Q] (n : ℕ) (u : Q) :
    (AdjoinRoot.root (X ^ n - C u)) ^ n = AdjoinRoot.of _ u := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- In the chart ring, `xⁿ = c f`. -/
theorem root_pow : (AdjoinRoot.root (X ^ n - C (f ⊗ₜ[k] c) : (A ⊗[k] S)[X])) ^ n =
    algebraMap (A ⊗[k] S) (chartRing k n f c) (f ⊗ₜ c) :=
  root_pow_eq n _

variable {n f g c} in
/-- **`c = g xⁿ`** in the chart ring, when `g f = 1`. -/
theorem chartRight_eq_mul_root_pow (hgf : g * f = 1) :
    chartRight k n f c c =
      algebraMap (A ⊗[k] S) (chartRing k n f c) (g ⊗ₜ 1) * AdjoinRoot.root _ ^ n := by
  rw [root_pow, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hgf, one_mul, chartRight_apply]

variable {n f g c} in
/-- The square `k[y] → A[T] → B` and `k[y] → S → B` commutes when `g f = 1`. -/
theorem totalHom_comp_chartLeft (hgf : g * f = 1) :
    (chartLeft k n f c).comp (totalHom k n g) = (chartRight k n f c).comp (pointHom c) := by
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simp only [RingHom.comp_apply, totalHom, pointHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_C, chartRight_apply]
    rw [Polynomial.algebraMap_apply, chartLeft_C, Algebra.algebraMap_eq_smul_one (A := A),
      Algebra.algebraMap_eq_smul_one (A := S), TensorProduct.smul_tmul]
  · simp only [RingHom.comp_apply, totalHom, pointHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X, chartRight_apply]
    rw [map_mul, map_pow, chartLeft_C, chartLeft_X, root_pow, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, hgf, one_mul]


section Desc

variable {n f g c} {T : Type u} [CommRing T] (α : A[X] →+* T) (β : S →+* T)
  (h : α.comp (totalHom k n g) = β.comp (pointHom c))

include h in
/-- A compatible pair `α`, `β` agrees on the image of `k`. -/
theorem desc_C_algebraMap (r : k) : α (C (algebraMap k A r)) = β (algebraMap k S r) := by
  have := congrArg (fun φ => φ (C r)) h
  simpa [totalHom, pointHom, Polynomial.algebraMap_apply] using this

/-- The map `A ⊗_k S → T` induced by a compatible pair `α : A[T] → T`, `β : S → T`. -/
def descBase : A ⊗[k] S →+* T :=
  letI : Algebra k T := (β.comp (algebraMap k S)).toAlgebra
  (Algebra.TensorProduct.productMap
    { toRingHom := α.comp C, commutes' := fun r => desc_C_algebraMap α β h r }
    { toRingHom := β, commutes' := fun _ => rfl }).toRingHom

/-- `descBase α β h` sends `a ⊗ s` to `α a * β s`. -/
theorem descBase_tmul (a : A) (s : S) : descBase α β h (a ⊗ₜ s) = α (C a) * β s := by
  simp [descBase]

include h in
/-- The element `α T` is a root of `xⁿ - c f` under `descBase α β h`, when `g f = 1`. -/
theorem eval₂_descBase (hgf : g * f = 1) :
    eval₂ (descBase α β h) (α X) (X ^ n - C (f ⊗ₜ[k] c)) = 0 := by
  have hX := congrArg (fun φ => φ X) h
  simp only [RingHom.comp_apply, totalHom, pointHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_X, map_mul, map_pow] at hX
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, descBase_tmul, ← hX, ← mul_assoc, ← map_mul, ← map_mul,
    mul_comm f g, hgf]
  simp

/-- The map out of the chart ring induced by a compatible pair. -/
def chartDesc (hgf : g * f = 1) : chartRing k n f c →+* T :=
  AdjoinRoot.lift (descBase α β h) (α X) (eval₂_descBase α β h hgf)

/-- `chartDesc α β h hgf` composed with `chartLeft` is `α`. -/
theorem chartDesc_chartLeft (hgf : g * f = 1) :
    (chartDesc α β h hgf).comp (chartLeft k n f c) = α := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [chartDesc, chartLeft_C, descBase_tmul]
  · simp [chartDesc, chartLeft_X]

/-- `chartDesc α β h hgf` composed with `chartRight` is `β`. -/
theorem chartDesc_chartRight (hgf : g * f = 1) :
    (chartDesc α β h hgf).comp (chartRight k n f c) = β := by
  ext s
  simp [chartDesc, chartRight_apply, descBase_tmul]

/-- Two ring maps out of the chart ring agree if they agree after composing with `chartLeft`
and with `chartRight`. -/
theorem chartRing_ringHom_ext {m₁ m₂ : chartRing k n f c →+* T}
    (h₁ : m₁.comp (chartLeft k n f c) = m₂.comp (chartLeft k n f c))
    (h₂ : m₁.comp (chartRight k n f c) = m₂.comp (chartRight k n f c)) : m₁ = m₂ := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s =>
        have ha := congrArg (fun φ => φ (C a)) h₁
        have hs := congrArg (fun φ => φ s) h₂
        simp only [RingHom.comp_apply, chartLeft_C, chartRight_apply] at ha hs
        have hm : (a ⊗ₜ[k] s : A ⊗[k] S) = (a ⊗ₜ 1) * (1 ⊗ₜ s) := by simp
        simp only [RingHom.comp_apply, AdjoinRoot.of]
        rw [hm, map_mul, map_mul, map_mul, map_mul]
        exact congrArg₂ (· * ·) ha hs
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  · have := congrArg (fun φ => φ X) h₁
    simpa [chartLeft_X] using this

end Desc

variable {n f g c} in
/-- **The chart ring is the pushout of `A[T] ← k[y] → S`**, along `y ↦ g Tⁿ` and `y ↦ c`. -/
theorem isPushout_chart (hgf : g * f = 1) :
    IsPushout (CommRingCat.ofHom (totalHom k n g)) (CommRingCat.ofHom (pointHom (k := k) c))
      (CommRingCat.ofHom (chartLeft k n f c)) (CommRingCat.ofHom (chartRight k n f c)) := by
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk
    (congrArg CommRingCat.ofHom (totalHom_comp_chartLeft hgf))
    (fun s => CommRingCat.ofHom (chartDesc s.inl.hom s.inr.hom
      (congrArg CommRingCat.Hom.hom s.condition) hgf))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · exact CommRingCat.hom_ext (chartDesc_chartLeft _ _ _ hgf)
  · exact CommRingCat.hom_ext (chartDesc_chartRight _ _ _ hgf)
  · refine CommRingCat.hom_ext (chartRing_ringHom_ext ?_ ?_)
    · simp only [CommRingCat.hom_ofHom]
      rw [chartDesc_chartLeft]; exact congrArg CommRingCat.Hom.hom h₁
    · simp only [CommRingCat.hom_ofHom]
      rw [chartDesc_chartRight]; exact congrArg CommRingCat.Hom.hom h₂


/-! ### Freeness and étaleness -/

section Structure

variable {Q : Type u} [CommRing Q] {n : ℕ} (u : Q)

/-- The basis `1, x, …, xⁿ⁻¹` of `Q[x]/(xⁿ - u)` over `Q`. -/
def rootPowerBasis (hn : n ≠ 0) : PowerBasis Q (AdjoinRoot (X ^ n - C u)) :=
  AdjoinRoot.powerBasis' (monic_X_pow_sub_C u hn)

/-- The power basis `rootPowerBasis u hn` has dimension `n`. -/
theorem rootPowerBasis_dim [Nontrivial Q] (hn : n ≠ 0) : (rootPowerBasis u hn).dim = n := by
  simp [rootPowerBasis, AdjoinRoot.powerBasis']

/-- **`Q[x]/(xⁿ - u)` is free of rank `n` over `Q`.** -/
theorem free_adjoinRoot (hn : n ≠ 0) : Module.Free Q (AdjoinRoot (X ^ n - C u)) :=
  Module.Free.of_basis (rootPowerBasis u hn).basis

/-- `Q[x]/(xⁿ - u)` is a finite `Q`-module. -/
theorem finite_adjoinRoot (hn : n ≠ 0) : Module.Finite Q (AdjoinRoot (X ^ n - C u)) :=
  (rootPowerBasis u hn).finite

/-- `Q[x]/(xⁿ - u)` has rank `n` over `Q`. -/
theorem finrank_adjoinRoot [Nontrivial Q] (hn : n ≠ 0) :
    Module.finrank Q (AdjoinRoot (X ^ n - C u)) = n := by
  rw [(rootPowerBasis u hn).finrank, rootPowerBasis_dim]

/-- **`Q[x]/(xⁿ - u)` is étale over `Q` when `n` and `u` are units.** -/
theorem etale_adjoinRoot (hn : n ≠ 0) (hnu : IsUnit (n : Q)) (hu : IsUnit u) :
    Algebra.Etale Q (AdjoinRoot (X ^ n - C u)) := by
  refine Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot (monic_X_pow_sub_C u hn) ?_
  have hr : IsUnit (AdjoinRoot.root (X ^ n - C u)) :=
    (isUnit_pow_iff hn).mp (root_pow_eq n u ▸ hu.map _)
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow,
    AdjoinRoot.mk_X, map_natCast]
  exact (hnu.map (AdjoinRoot.of _)).mul (hr.pow _)

end Structure

end Stacks.CyclicCover
