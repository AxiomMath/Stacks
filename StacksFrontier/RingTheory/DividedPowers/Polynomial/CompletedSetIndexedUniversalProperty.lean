module

public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexedUniversalProperty

/-!
# The universal property of the completed divided power polynomial algebra

Let `(A, I, γ)` be a divided power ring in which `p` is nilpotent modulo `I`, and let `W` be an
arbitrary type of divided power variables.  The divided power polynomial algebra
`A⟨ξ_w : w ∈ W⟩` of [Stacks, Tag 07H6] then has `p` nilpotent modulo its own divided power ideal
`I A⟨ξ⟩ + A⟨ξ⟩₊`, so [Stacks, Tag 07KD] makes its `p`-adic completion `A⟨ξ_w⟩^∧` a divided power
ring.  This file proves the universal property of that completion:

> a divided power morphism out of `A⟨ξ_w⟩^∧` is determined by, and exists for, any divided power
> morphism `A → C` together with any choice of images of the `ξ_w` in the divided power ideal of
> a `p`-adically complete divided power ring `C`.

This is the universal property the source's proof of [Stacks, Lemma 60.21.4, Tag 07LH] appeals
to when it writes "This uses the universal properties of polynomial algebra, divided power
polynomial algebras, divided power envelopes, and `p`-adic completion": the divided power
`A`-algebra map `τ : A⟨ξ_i⟩^∧ → A` sending `ξ_i` to a prescribed element `z_i` of the divided
power ideal of `A` is exactly what it produces.

## Main definitions

* `DividedPowers.completedSetIndexedDividedPowerPolynomialCoefficientDPMorphism` — the
  structure map `ν : A → A⟨ξ_w⟩^∧`.
* `DividedPowers.completedSetIndexedDividedPowerPolynomialVariable` — the variable `ξ_w` read
  in the completion.
* `DividedPowers.completedSetIndexedDividedPowerPolynomialLift` — the divided power morphism
  `A⟨ξ_w⟩^∧ → C` with prescribed restriction to coefficients and prescribed values on the
  variables.

## Main results

* `DividedPowers.isNilpotent_mk_dividedPowerPolynomialIdeal` — `p` is nilpotent modulo the
  divided power ideal of `A⟨ξ_w⟩` as soon as it is nilpotent modulo `I`.
* `DividedPowers.existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial` —
  **the universal property of `A⟨ξ_w⟩^∧`.**
* `DividedPowers.completedSetIndexedDividedPowerPolynomialVariable_mem` — the variables lie in
  the completed divided power ideal, so they are legitimate arguments of the divided powers.

## Implementation notes

The proof is the uncompleted universal property
`DividedPowers.existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial` of
[Stacks, Tag 07H6] followed by `DividedPowers.existsUnique_dPMorphism_from_completion`, and
uniqueness is the same two steps read backwards: a morphism out of the completion restricts
along the structure map `A⟨ξ⟩ → A⟨ξ⟩^∧` to a morphism out of `A⟨ξ⟩` with the same restriction
to coefficients and the same values on the variables.

The `ℤ_(p)`-algebra structure that `DividedPowers.eventually_isDividedPowerCompletionLimit`
needs on `A⟨ξ_w⟩` is not a hypothesis: it is constructed inside the proof from the one on `A`.

The underlying ring `AdicCompletion (p) A⟨ξ_w⟩` is the ring that
`Crystalline.DividedPowerPolynomial.completedDividedPowerPolynomialRing A W p` abbreviates.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

namespace DividedPowers

universe u v w

/-! ### Nilpotence of `p` in the divided power polynomial algebra -/

/-- If `p` is nilpotent modulo the divided power ideal `I` of `A`, it is nilpotent modulo the
divided power ideal `I A⟨ξ_w⟩ + A⟨ξ_w⟩₊` of the divided power polynomial algebra: the coefficient
map carries `I` into that ideal. -/
public theorem isNilpotent_mk_dividedPowerPolynomialIdeal (A : DividedPowerRing.{u})
    (W : Type w) (p : ℕ) (hp : IsNilpotent (Ideal.Quotient.mk A.ideal (p : A))) :
    IsNilpotent (Ideal.Quotient.mk (dividedPowerPolynomialIdeal A.ideal W)
      (p : setIndexedDividedPowerPolynomialAlgebra A W)) := by
  obtain ⟨n, hn⟩ := hp
  refine ⟨n, ?_⟩
  have hmem : (p : A) ^ n ∈ A.ideal := Ideal.Quotient.eq_zero_iff_mem.mp (by rwa [map_pow])
  have himg : algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) ((p : A) ^ n) ∈
      dividedPowerPolynomialIdeal A.ideal W :=
    coefficient_mem_polynomialIdeal A hmem
  rw [map_pow, map_natCast] at himg
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr himg

/-! ### The structure map and the variables of the completion -/

section Data

variable (A : DividedPowerRing.{u}) (W : Type w) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk A.ideal (p : A)))

/-- The structure map `A⟨ξ_w⟩ → A⟨ξ_w⟩^∧` of the `p`-adic completion, as a divided power
morphism. -/
public abbrev completedSetIndexedDividedPowerPolynomialInclusion :
    DPMorphism (setIndexedDividedPowerPolynomialDividedPowers A W)
      (completedDividedPowers (dividedPowerPolynomialIdeal A.ideal W)
        (setIndexedDividedPowerPolynomialDividedPowers A W) p
        (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).1 :=
  completionDPMorphism (dividedPowerPolynomialIdeal A.ideal W)
    (setIndexedDividedPowerPolynomialDividedPowers A W) p
    (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)

/-- **The structure map `ν : A → A⟨ξ_w⟩^∧`**: the coefficient map of the divided power
polynomial algebra followed by the structure map of the `p`-adic completion. -/
public def completedSetIndexedDividedPowerPolynomialCoefficientDPMorphism :
    DPMorphism A.dividedPowers
      (completedDividedPowers (dividedPowerPolynomialIdeal A.ideal W)
        (setIndexedDividedPowerPolynomialDividedPowers A W) p
        (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).1 :=
  (completionDPMorphism (dividedPowerPolynomialIdeal A.ideal W)
      (setIndexedDividedPowerPolynomialDividedPowers A W) p
      (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).comp
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W)

/-- **The variable `ξ_w` read in the completion `A⟨ξ_w⟩^∧`.** -/
public def completedSetIndexedDividedPowerPolynomialVariable (w : W) :
    AdicCompletion (pAdicIdeal (A := setIndexedDividedPowerPolynomialAlgebra A W) p)
      (setIndexedDividedPowerPolynomialAlgebra A W) :=
  algebraMap (setIndexedDividedPowerPolynomialAlgebra A W) _
    (dividedPowerPolynomialVariable A w)

/-- The variables lie in the completed divided power ideal of `A⟨ξ_w⟩^∧`. -/
public theorem completedSetIndexedDividedPowerPolynomialVariable_mem (w : W) :
    completedSetIndexedDividedPowerPolynomialVariable A W p w ∈
      completionIdeal (dividedPowerPolynomialIdeal A.ideal W) p
        (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp) :=
  (completionDPMorphism (dividedPowerPolynomialIdeal A.ideal W)
      (setIndexedDividedPowerPolynomialDividedPowers A W) p
      (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).ideal_comp
    (Ideal.mem_map_of_mem _ (variable_mem_polynomialIdeal A w))

end Data

/-! ### The universal property -/

/-- **The universal property of the completed divided power polynomial algebra
`A⟨ξ_w : w ∈ W⟩^∧`.**

Let `(A, I, γ)` be a divided power ring with `p` nilpotent modulo `I`, let `W` be any type of
variables and let `(C, J, δ)` be a `p`-adically complete divided power ring with `p` nilpotent
modulo `J`.  Then for every divided power morphism `f : A → C` and every family `k : W → J` of
elements of the divided power ideal of `C` there is exactly one divided power morphism
`φ : A⟨ξ_w⟩^∧ → C` with `φ ∘ ν = f` and `φ(ξ_w) = k w`.

This is the completed form of [Stacks, Tag 07H6]; it is the universal property the source's
proof of [Stacks, Lemma 60.21.4, Tag 07LH] uses to produce the retraction `τ` of the
factorization `ρ = τ ∘ σ`. -/
public theorem existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial
    (A : DividedPowerRing.{u}) (W : Type w) (C : DividedPowerRing.{v}) (p : ℕ) [Fact p.Prime]
    [Algebra (IntegersAtPrime p) A] [Algebra (IntegersAtPrime p) C]
    (hp : IsNilpotent (Ideal.Quotient.mk A.ideal (p : A)))
    (hpC : IsNilpotent (Ideal.Quotient.mk C.ideal (p : C)))
    [IsAdicComplete (pAdicIdeal (A := C) p) C]
    (f : DPMorphism A.dividedPowers C.dividedPowers) (k : W → C.ideal) :
    ∃! φ : DPMorphism (completedDividedPowers (dividedPowerPolynomialIdeal A.ideal W)
        (setIndexedDividedPowerPolynomialDividedPowers A W) p
        (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).1 C.dividedPowers,
      φ.comp (completedSetIndexedDividedPowerPolynomialCoefficientDPMorphism A W p hp) = f ∧
        ∀ w : W, φ (completedSetIndexedDividedPowerPolynomialVariable A W p w) = (k w : C) := by
  classical
  let : Algebra (IntegersAtPrime p) (setIndexedDividedPowerPolynomialAlgebra A W) :=
    ((algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W)).comp
      (algebraMap (IntegersAtPrime p) A)).toAlgebra
  obtain ⟨ψ, ⟨hψcoeff, hψvar⟩, hψuniq⟩ :=
    existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial A W C f k
  obtain ⟨φ, hφ, hφuniq⟩ :=
    existsUnique_dPMorphism_comp_completionDPMorphism
      (dividedPowerPolynomialIdeal A.ideal W)
      (setIndexedDividedPowerPolynomialDividedPowers A W) C.ideal C.dividedPowers p
      (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp) hpC ψ
  refine ⟨φ, ⟨?_, fun w => ?_⟩, ?_⟩
  · apply DPMorphism.ext
    funext a
    exact (congrArg (fun q : DPMorphism (setIndexedDividedPowerPolynomialDividedPowers A W)
      C.dividedPowers => q (setIndexedDividedPowerPolynomialCoefficientDPMorphism A W a)) hφ).trans
      (congrArg (fun q : DPMorphism A.dividedPowers C.dividedPowers => q a) hψcoeff)
  · exact (congrArg (fun q : DPMorphism (setIndexedDividedPowerPolynomialDividedPowers A W)
      C.dividedPowers => q (dividedPowerPolynomialVariable A w)) hφ).trans (hψvar w)
  · rintro φ' ⟨hc, hv⟩
    exact hφuniq φ' (hψuniq _ ⟨hc, hv⟩)

/-! ### The universal property as a construction -/

section Lift

variable (A : DividedPowerRing.{u}) (W : Type w) (C : DividedPowerRing.{v}) (p : ℕ)
  [Fact p.Prime] [Algebra (IntegersAtPrime p) A] [Algebra (IntegersAtPrime p) C]
  (hp : IsNilpotent (Ideal.Quotient.mk A.ideal (p : A)))
  (hpC : IsNilpotent (Ideal.Quotient.mk C.ideal (p : C)))
  [IsAdicComplete (pAdicIdeal (A := C) p) C]
  (f : DPMorphism A.dividedPowers C.dividedPowers) (k : W → C.ideal)

/-- **The divided power morphism `A⟨ξ_w⟩^∧ → C` with prescribed restriction to coefficients and
prescribed values on the variables**, supplied by
`DividedPowers.existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial`. -/
public def completedSetIndexedDividedPowerPolynomialLift :
    DPMorphism (completedDividedPowers (dividedPowerPolynomialIdeal A.ideal W)
      (setIndexedDividedPowerPolynomialDividedPowers A W) p
      (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).1 C.dividedPowers :=
  (existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial
    A W C p hp hpC f k).choose

/-- The lift restricts to `f` on the coefficients. -/
public theorem completedSetIndexedDividedPowerPolynomialLift_comp_coefficient :
    (completedSetIndexedDividedPowerPolynomialLift A W C p hp hpC f k).comp
        (completedSetIndexedDividedPowerPolynomialCoefficientDPMorphism A W p hp) = f :=
  ((existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial
    A W C p hp hpC f k).choose_spec).1.1

/-- The lift sends the variable `ξ_w` to `k w`. -/
public theorem completedSetIndexedDividedPowerPolynomialLift_variable (w : W) :
    completedSetIndexedDividedPowerPolynomialLift A W C p hp hpC f k
        (completedSetIndexedDividedPowerPolynomialVariable A W p w) = (k w : C) :=
  ((existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial
    A W C p hp hpC f k).choose_spec).1.2 w

/-- The lift is the only divided power morphism with those two properties. -/
public theorem eq_completedSetIndexedDividedPowerPolynomialLift
    (φ : DPMorphism (completedDividedPowers (dividedPowerPolynomialIdeal A.ideal W)
      (setIndexedDividedPowerPolynomialDividedPowers A W) p
      (isNilpotent_mk_dividedPowerPolynomialIdeal A W p hp)).1 C.dividedPowers)
    (hcoeff : φ.comp
      (completedSetIndexedDividedPowerPolynomialCoefficientDPMorphism A W p hp) = f)
    (hvar : ∀ w : W,
      φ (completedSetIndexedDividedPowerPolynomialVariable A W p w) = (k w : C)) :
    φ = completedSetIndexedDividedPowerPolynomialLift A W C p hp hpC f k :=
  ((existsUnique_dPMorphism_from_completedSetIndexedDividedPowerPolynomial
    A W C p hp hpC f k).choose_spec).2 φ ⟨hcoeff, hvar⟩

end Lift

end DividedPowers

end
