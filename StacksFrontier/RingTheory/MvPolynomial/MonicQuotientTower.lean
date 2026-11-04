module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.RingTheory.Dualizing.PowerBasisSelfDual
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One monic polynomial per variable: a finite free self-dual quotient

Let `R` be a commutative ring and let `f₀, …, fₙ₋₁ ∈ R[T]` be monic polynomials in one variable.
This file proves that

`C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))`

is a finite free `R`-module which is moreover *self-dual* over `R`: some `R`-linear functional on
`C` makes multiplication a perfect pairing, i.e. `C ≅ Hom_R(C, R)` as `C`-modules
(`Dualizing.IsSelfDualAlgebra`).

This is the algebra through which a finite ring map factors in the proof of [Stacks, Tag 0C0G],
and the three conclusions are what that proof asks of it: finiteness and freeness make `C` a
well-behaved relative object over `R`, and self-duality is the statement that the relative
dualizing module of `C` over `R` is `C` itself.

## Main results

* `MvPolynomial.finite_free_selfDual_quotient_span_range_aeval_X_of_monic` — **the quotient of
  `R[T₀, …, Tₙ₋₁]` by one monic polynomial per variable is finite, free and self-dual over `R`**.
* `Dualizing.IsSelfDualAlgebra.of_algEquiv` — self-duality transports along an `R`-algebra
  equivalence.

## Implementation notes

The induction on the number of variables splits off the first one, and its step is an explicit
`R`-algebra equivalence

`R[T₀, …, Tₙ]/(f₀(T₀), …, fₙ(Tₙ)) ≃ₐ[R] AdjoinRoot (f₀ over R[T₁, …, Tₙ]/(f₁(T₁), …, fₙ(Tₙ)))`

built from `MvPolynomial.aeval` and `AdjoinRoot.lift` in the two directions, rather than by
composing `Mathlib`'s iterated-quotient ring equivalences: the two round trips are then checked on
the variables alone, by `Ideal.Quotient.algHom_ext`, `MvPolynomial.algHom_ext` and
`AdjoinRoot.algHom_ext`, and everything stays at the level of `R`-algebra homomorphisms.  The
only point needing care is that the composite in the direction `AdjoinRoot → AdjoinRoot` must
first be recognised as a homomorphism over the lower quotient before `AdjoinRoot.algHom_ext`
applies to it.

Over that equivalence the three conclusions come from `Polynomial.Monic.finite_adjoinRoot`,
`Polynomial.Monic.free_adjoinRoot` and `Dualizing.isSelfDualAlgebra_adjoinRoot`, composed down
the tower by `Module.Finite.trans`, `Module.Free.trans` and
`Dualizing.IsSelfDualAlgebra.trans`.  No hypothesis is placed on `R`.

## References

* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
-/

@[expose] public section

universe u

namespace Dualizing

/-- **Self-duality transports along an algebra equivalence.**  If `A` is a self-dual `R`-algebra
and `e : A ≃ₐ[R] B`, then `B` is a self-dual `R`-algebra: the functional `l_A ∘ e⁻¹` makes
multiplication on `B` a perfect pairing, because the pairing of `B` is the pairing of `A`
conjugated by `e`. -/
theorem IsSelfDualAlgebra.of_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (h : IsSelfDualAlgebra R A) :
    IsSelfDualAlgebra R B := by
  obtain ⟨l, hinj, hsurj⟩ := h
  have key : ∀ x z : B, ((LinearMap.mul R B).compr₂ (l ∘ₗ e.symm.toLinearMap)) x z
      = ((LinearMap.mul R A).compr₂ l) (e.symm x) (e.symm z) := fun x z => by
    show l (e.symm (x * z)) = l (e.symm x * e.symm z)
    rw [map_mul]
  refine ⟨l ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  · intro x y hxy
    refine e.symm.injective (hinj (LinearMap.ext fun w => ?_))
    have h1 := LinearMap.congr_fun hxy (e w)
    rw [key, key, e.symm_apply_apply] at h1
    exact h1
  · intro k
    obtain ⟨a, ha⟩ := hsurj (k ∘ₗ e.toLinearMap)
    refine ⟨e a, LinearMap.ext fun z => ?_⟩
    rw [key, e.symm_apply_apply, LinearMap.congr_fun ha (e.symm z)]
    show k (e (e.symm z)) = k z
    rw [e.apply_symm_apply]

end Dualizing

namespace MonicQuotientTower

variable {R : Type u} [CommRing R]

/-- The ideal `(f₀(T₀), …, fₘ₋₁(Tₘ₋₁))` of `R[T₀, …, Tₘ₋₁]`. -/
@[ega "0 22.4.1" "partial",
  ega "0 22.4.4" "more general",
  ega "0 22.4.7" "defining ideal of B",
  ega "0 22.5.3",
  ega "0 22.5.4" "defining ideal"]
private noncomputable abbrev monicIdeal {m : ℕ} (f : Fin m → Polynomial R) :
    Ideal (MvPolynomial (Fin m) R) :=
  Ideal.span (Set.range fun i : Fin m =>
    Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) R) (f i))

/-- The quotient `R[T₀, …, Tₘ₋₁]/(f₀(T₀), …, fₘ₋₁(Tₘ₋₁))`. -/
@[ega "0 22.4.4" "more general", ega "0 22.5.4" "more general"]
private noncomputable abbrev MonicQuot {m : ℕ} (f : Fin m → Polynomial R) : Type u :=
  MvPolynomial (Fin m) R ⧸ monicIdeal f

/-- The `i`-th relation lies in the ideal it generates. -/
private theorem aeval_X_mem_monicIdeal {m : ℕ} (f : Fin m → Polynomial R) (i : Fin m) :
    Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) R) (f i) ∈ monicIdeal f :=
  Ideal.subset_span ⟨i, rfl⟩

/-- The `i`-th relation vanishes in the quotient. -/
private theorem mk_aeval_X {m : ℕ} (f : Fin m → Polynomial R) (i : Fin m) :
    Ideal.Quotient.mk (monicIdeal f)
      (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) R) (f i)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (aeval_X_mem_monicIdeal f i)

/-- Evaluating the `i`-th relation at a point `v` of an `R`-algebra: only `vᵢ` is seen. -/
private theorem aeval_aeval_X {m : ℕ} {A : Type*} [CommRing A] [Algebra R A]
    (v : Fin m → A) (f : Fin m → Polynomial R) (i : Fin m) :
    MvPolynomial.aeval v (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) R) (f i))
      = Polynomial.aeval (v i) (f i) := by
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]

/-- Evaluation at the class of a point is the class of the evaluation. -/
private theorem aeval_mk {A : Type*} [CommRing A] [Algebra R A] (K : Ideal A) (x : A)
    (P : Polynomial R) : Polynomial.aeval (Ideal.Quotient.mk K x) P
      = Ideal.Quotient.mk K (Polynomial.aeval x P) :=
  Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R K) x P

/-- Evaluation at the image of a point of a subring is the image of the evaluation. -/
private theorem aeval_algebraMap {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : A) (P : Polynomial R) :
    Polynomial.aeval (algebraMap A B x) P = algebraMap A B (Polynomial.aeval x P) :=
  Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R A B) x P

/-- The universal property of the quotient: `R[T₀, …, Tₘ₋₁]/(f₀(T₀), …, fₘ₋₁(Tₘ₋₁))` maps to any
`R`-algebra `A` given points `vᵢ` of `A` at which the `fᵢ` vanish. -/
private noncomputable def lift {m : ℕ} {A : Type*} [CommRing A] [Algebra R A]
    (f : Fin m → Polynomial R) (v : Fin m → A) (hv : ∀ i, Polynomial.aeval (v i) (f i) = 0) :
    MonicQuot f →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v) fun a ha => by
    have hle : monicIdeal f ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i =>
        RingHom.mem_ker.mpr ((aeval_aeval_X v f i).trans (hv i)))
    exact RingHom.mem_ker.mp (hle ha)

/-- `MonicQuotientTower.lift` sends the class of `Tᵢ` to `vᵢ`. -/
private theorem lift_mk_X {m : ℕ} {A : Type*} [CommRing A] [Algebra R A]
    (f : Fin m → Polynomial R) (v : Fin m → A) (hv : ∀ i, Polynomial.aeval (v i) (f i) = 0)
    (i : Fin m) : lift f v hv (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i)) = v i := by
  show MvPolynomial.aeval v (MvPolynomial.X i) = v i
  rw [MvPolynomial.aeval_X]

/-- Two `R`-algebra maps out of `MonicQuot f` agreeing on the classes of the variables are
equal. -/
private theorem algHom_ext_mk_X {m : ℕ} {A : Type*} [CommRing A] [Algebra R A]
    {f : Fin m → Polynomial R} {g h : MonicQuot f →ₐ[R] A}
    (H : ∀ i, g (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i))
      = h (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i))) : g = h :=
  Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext H)

section Step

variable {n : ℕ}

/-- `f₀`, with its coefficients pushed into `R[T₁, …, Tₙ]/(f₁(T₁), …, fₙ(Tₙ))`. -/
private noncomputable abbrev stepPoly (f : Fin (n + 1) → Polynomial R) :
    Polynomial (MonicQuot fun i : Fin n => f i.succ) :=
  (f 0).map (algebraMap R (MonicQuot fun i : Fin n => f i.succ))

/-- The lower quotient maps into the upper one by `Tᵢ ↦ Tᵢ₊₁`. -/
private noncomputable def lowerHom (f : Fin (n + 1) → Polynomial R) :
    (MonicQuot fun i : Fin n => f i.succ) →ₐ[R] MonicQuot f :=
  lift _ (fun i : Fin n => Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i.succ)) fun i => by
    rw [aeval_mk]
    exact mk_aeval_X f i.succ

/-- `MonicQuotientTower.lowerHom` sends the class of `Tᵢ` to the class of `Tᵢ₊₁`. -/
private theorem lowerHom_mk_X (f : Fin (n + 1) → Polynomial R) (i : Fin n) :
    lowerHom f (Ideal.Quotient.mk (monicIdeal fun j : Fin n => f j.succ) (MvPolynomial.X i))
      = Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i.succ) :=
  lift_mk_X _ _ _ i

/-- The point of `AdjoinRoot f₀` at which the variables are evaluated: `T₀` goes to the adjoined
root and `Tᵢ₊₁` to the image of the class of `Tᵢ`. -/
private noncomputable def point (f : Fin (n + 1) → Polynomial R) :
    Fin (n + 1) → AdjoinRoot (stepPoly f) :=
  Fin.cons (AdjoinRoot.root (stepPoly f)) fun i : Fin n =>
    algebraMap (MonicQuot fun j : Fin n => f j.succ) (AdjoinRoot (stepPoly f))
      (Ideal.Quotient.mk (monicIdeal fun j : Fin n => f j.succ) (MvPolynomial.X i))

/-- `T₀` is evaluated at the adjoined root. -/
private theorem point_zero (f : Fin (n + 1) → Polynomial R) :
    point f 0 = AdjoinRoot.root (stepPoly f) := rfl

/-- `Tᵢ₊₁` is evaluated at the image of the class of `Tᵢ`. -/
private theorem point_succ (f : Fin (n + 1) → Polynomial R) (i : Fin n) :
    point f i.succ = algebraMap (MonicQuot fun j : Fin n => f j.succ) (AdjoinRoot (stepPoly f))
      (Ideal.Quotient.mk (monicIdeal fun j : Fin n => f j.succ) (MvPolynomial.X i)) := rfl

/-- The relations vanish at `MonicQuotientTower.point`: the first one because the adjoined root is
a root of `f₀`, the others because they are already relations of the lower quotient. -/
private theorem aeval_point (f : Fin (n + 1) → Polynomial R) (i : Fin (n + 1)) :
    Polynomial.aeval (point f i) (f i) = 0 := by
  induction i using Fin.cases with
  | zero =>
    rw [point_zero, Polynomial.aeval_def, IsScalarTower.algebraMap_eq R
      (MonicQuot fun j : Fin n => f j.succ) (AdjoinRoot (stepPoly f)), ← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root _
  | succ i =>
    rw [point_succ, aeval_algebraMap, aeval_mk, mk_aeval_X (fun j : Fin n => f j.succ) i,
      map_zero]

/-- The forward map of the step: `T₀ ↦ root f₀`, `Tᵢ₊₁ ↦` the class of `Tᵢ`. -/
private noncomputable def fwd (f : Fin (n + 1) → Polynomial R) :
    MonicQuot f →ₐ[R] AdjoinRoot (stepPoly f) :=
  lift f (point f) (aeval_point f)

/-- `MonicQuotientTower.fwd` on the class of `Tᵢ`. -/
private theorem fwd_mk_X (f : Fin (n + 1) → Polynomial R) (i : Fin (n + 1)) :
    fwd f (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i)) = point f i :=
  lift_mk_X f (point f) (aeval_point f) i

/-- `f₀` kills the class of `T₀` in the upper quotient. -/
private theorem eval₂_lowerHom (f : Fin (n + 1) → Polynomial R) :
    Polynomial.eval₂ (lowerHom f).toRingHom
      (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X 0)) (stepPoly f) = 0 := by
  rw [Polynomial.eval₂_map, show (lowerHom f).toRingHom.comp
      (algebraMap R (MonicQuot fun i : Fin n => f i.succ)) = algebraMap R (MonicQuot f) from
    RingHom.ext fun r => (lowerHom f).commutes r, ← Polynomial.aeval_def, aeval_mk]
  exact mk_aeval_X f 0

/-- The root-adjoining lift defining `MonicQuotientTower.bwd` restricts to
`MonicQuotientTower.lowerHom` on the lower quotient. -/
private theorem lift_algebraMap (f : Fin (n + 1) → Polynomial R)
    (c : MonicQuot fun i : Fin n => f i.succ) :
    AdjoinRoot.lift (lowerHom f).toRingHom (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X 0))
      (eval₂_lowerHom f) (algebraMap (MonicQuot fun i : Fin n => f i.succ)
        (AdjoinRoot (stepPoly f)) c) = lowerHom f c := by
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  rfl

/-- The backward map of the step: the adjoined root goes to the class of `T₀`, and the lower
quotient by `MonicQuotientTower.lowerHom`. -/
private noncomputable def bwd (f : Fin (n + 1) → Polynomial R) :
    AdjoinRoot (stepPoly f) →ₐ[R] MonicQuot f :=
  { AdjoinRoot.lift (lowerHom f).toRingHom
      (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X 0)) (eval₂_lowerHom f) with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply R (MonicQuot fun i : Fin n => f i.succ)]
      exact (lift_algebraMap f _).trans ((lowerHom f).commutes r) }

/-- `MonicQuotientTower.bwd` on the lower quotient is `MonicQuotientTower.lowerHom`. -/
private theorem bwd_algebraMap (f : Fin (n + 1) → Polynomial R)
    (c : MonicQuot fun i : Fin n => f i.succ) :
    bwd f (algebraMap (MonicQuot fun i : Fin n => f i.succ) (AdjoinRoot (stepPoly f)) c)
      = lowerHom f c :=
  lift_algebraMap f c

/-- `MonicQuotientTower.bwd` sends the adjoined root to the class of `T₀`. -/
private theorem bwd_root (f : Fin (n + 1) → Polynomial R) :
    bwd f (AdjoinRoot.root (stepPoly f))
      = Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X 0) := by
  show AdjoinRoot.lift (lowerHom f).toRingHom _ (eval₂_lowerHom f) (AdjoinRoot.root _) = _
  rw [AdjoinRoot.lift_root]

/-- The forward map undoes `MonicQuotientTower.lowerHom`: on the lower quotient it is the
structure map of `AdjoinRoot f₀`.  Both sides are `R`-algebra maps out of a quotient of a
polynomial ring, so it is enough to compare them on the variables. -/
private theorem fwd_lowerHom (f : Fin (n + 1) → Polynomial R)
    (c : MonicQuot fun i : Fin n => f i.succ) :
    fwd f (lowerHom f c)
      = algebraMap (MonicQuot fun i : Fin n => f i.succ) (AdjoinRoot (stepPoly f)) c := by
  have h : (fwd f).comp (lowerHom f) = IsScalarTower.toAlgHom R
      (MonicQuot fun i : Fin n => f i.succ) (AdjoinRoot (stepPoly f)) := by
    refine algHom_ext_mk_X fun i => ?_
    show fwd f (lowerHom f (Ideal.Quotient.mk
        (monicIdeal fun j : Fin n => f j.succ) (MvPolynomial.X i)))
      = algebraMap (MonicQuot fun j : Fin n => f j.succ) (AdjoinRoot (stepPoly f))
        (Ideal.Quotient.mk (monicIdeal fun j : Fin n => f j.succ) (MvPolynomial.X i))
    rw [lowerHom_mk_X, fwd_mk_X, point_succ]
  exact AlgHom.congr_fun h c

/-- Backward then forward is the identity of the upper quotient. -/
private theorem bwd_comp_fwd (f : Fin (n + 1) → Polynomial R) :
    (bwd f).comp (fwd f) = AlgHom.id R (MonicQuot f) := by
  refine algHom_ext_mk_X fun i => ?_
  show bwd f (fwd f (Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i)))
    = Ideal.Quotient.mk (monicIdeal f) (MvPolynomial.X i)
  rw [fwd_mk_X]
  induction i using Fin.cases with
  | zero => rw [point_zero, bwd_root]
  | succ i => rw [point_succ, bwd_algebraMap, lowerHom_mk_X]

/-- Forward then backward is the identity of `AdjoinRoot f₀`.  The composite is a homomorphism
over the lower quotient by `MonicQuotientTower.bwd_algebraMap` and
`MonicQuotientTower.fwd_lowerHom`, so `AdjoinRoot.algHom_ext` reduces the claim to its value at
the adjoined root. -/
private theorem fwd_comp_bwd (f : Fin (n + 1) → Polynomial R) :
    (fwd f).comp (bwd f) = AlgHom.id R (AdjoinRoot (stepPoly f)) := by
  have hθ : (⟨((fwd f).comp (bwd f)).toRingHom, fun c => by
        show fwd f (bwd f (algebraMap (MonicQuot fun i : Fin n => f i.succ)
            (AdjoinRoot (stepPoly f)) c)) = _
        rw [bwd_algebraMap, fwd_lowerHom]⟩ :
      AdjoinRoot (stepPoly f) →ₐ[MonicQuot fun i : Fin n => f i.succ] AdjoinRoot (stepPoly f))
      = AlgHom.id _ _ := by
    refine AdjoinRoot.algHom_ext ?_
    show fwd f (bwd f (AdjoinRoot.root (stepPoly f))) = AdjoinRoot.root (stepPoly f)
    rw [bwd_root, fwd_mk_X, point_zero]
  exact AlgHom.ext fun z => AlgHom.congr_fun hθ z

/-- **One step of the tower.**  Splitting off the first variable identifies

`R[T₀, …, Tₙ]/(f₀(T₀), …, fₙ(Tₙ))`

with the root extension of `R[T₁, …, Tₙ]/(f₁(T₁), …, fₙ(Tₙ))` along `f₀`.  No monicity is
needed. -/
private noncomputable def stepEquiv (f : Fin (n + 1) → Polynomial R) :
    MonicQuot f ≃ₐ[R] AdjoinRoot (stepPoly f) :=
  AlgEquiv.ofAlgHom (fwd f) (bwd f) (fwd_comp_bwd f) (bwd_comp_fwd f)

end Step

/-- Finiteness, freeness and self-duality over `R` transfer from `B` to `A` along `A ≃ₐ[R] B`. -/
private theorem finite_free_selfDual_of_algEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B)
    (h : Module.Finite R B ∧ Module.Free R B ∧ Dualizing.IsSelfDualAlgebra R B) :
    Module.Finite R A ∧ Module.Free R A ∧ Dualizing.IsSelfDualAlgebra R A := by
  obtain ⟨_, _, hd⟩ := h
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv, Module.Free.of_equiv e.symm.toLinearEquiv,
    Dualizing.IsSelfDualAlgebra.of_algEquiv e.symm hd⟩

/-- **The quotient by one monic polynomial per variable is finite, free and self-dual.**  The
induction on the number of variables peels off the first one with
`MonicQuotientTower.stepEquiv`. -/
@[ega "0 10.3.1.2" "more general"]
private theorem finite_free_selfDual :
    ∀ (n : ℕ) (f : Fin n → Polynomial R), (∀ i, (f i).Monic) →
      Module.Finite R (MonicQuot f) ∧ Module.Free R (MonicQuot f) ∧
        Dualizing.IsSelfDualAlgebra R (MonicQuot f) := by
  intro n
  induction n with
  | zero =>
    intro f _
    exact finite_free_selfDual_of_algEquiv
      (AlgEquiv.ofAlgHom (lift f Fin.elim0 fun i => i.elim0) (Algebra.ofId R (MonicQuot f))
        (AlgHom.ext fun r => by simp) (algHom_ext_mk_X fun i => i.elim0))
      ⟨inferInstance, inferInstance, Dualizing.isSelfDualAlgebra_self R⟩
  | succ n ih =>
    intro f hf
    obtain ⟨hfin, hfree, hdual⟩ := ih (fun i : Fin n => f i.succ) fun i => hf i.succ
    have := hfin
    have := hfree
    have hmonic : (stepPoly f).Monic := (hf 0).map _
    have : Module.Finite (MonicQuot fun i : Fin n => f i.succ) (AdjoinRoot (stepPoly f)) :=
      hmonic.finite_adjoinRoot
    have : Module.Free (MonicQuot fun i : Fin n => f i.succ) (AdjoinRoot (stepPoly f)) :=
      hmonic.free_adjoinRoot
    have : Module.Finite R (AdjoinRoot (stepPoly f)) :=
      Module.Finite.trans (MonicQuot fun i : Fin n => f i.succ) (AdjoinRoot (stepPoly f))
    have : Module.Free R (AdjoinRoot (stepPoly f)) :=
      Module.Free.trans (S := MonicQuot fun i : Fin n => f i.succ)
    have hdual' : Dualizing.IsSelfDualAlgebra R (AdjoinRoot (stepPoly f)) :=
      hdual.trans (Dualizing.isSelfDualAlgebra_adjoinRoot _ hmonic)
    exact finite_free_selfDual_of_algEquiv (stepEquiv f) ⟨inferInstance, inferInstance, hdual'⟩

end MonicQuotientTower

/-- **One monic polynomial per variable gives a finite free self-dual quotient.**  For monic
`f₀, …, fₙ₋₁ ∈ R[T]` over a commutative ring `R`, the `R`-algebra

`C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))`

is a finite free `R`-module, and is self-dual over `R`: some `R`-linear functional on `C` makes
multiplication a perfect pairing.

This is the intermediate algebra of the proof of [Stacks, Tag 0C0G] for a finite ring map, with
the three properties that proof needs of it. -/
@[ega "0 10.3.1.2" "more general", ega "0 22.4.1" "(i)", ega "0 22.5.2" "B′ = B[T₁"]
theorem MvPolynomial.finite_free_selfDual_quotient_span_range_aeval_X_of_monic
    {R : Type u} [CommRing R] (n : ℕ) (f : Fin n → Polynomial R) (hf : ∀ i, (f i).Monic) :
    letI C := MvPolynomial (Fin n) R ⧸ Ideal.span
      (Set.range fun i : Fin n => Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) R)
        (f i))
    Module.Finite R C ∧ Module.Free R C ∧ Dualizing.IsSelfDualAlgebra R C :=
  MonicQuotientTower.finite_free_selfDual n f hf

end
