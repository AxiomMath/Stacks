module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Completion

/-!
# The two shapes of the differentials of a completed divided power ring, at a finite level

Let `A → B` be a ring map, let an ideal `J` of `B` carry divided powers `δ`, and let `p` be
nilpotent modulo `J`.  There are two modules of differentials attached to the `p`-adic completion
`B̂` of `B`:

* `Ω_{B̂/A,γ̂}`, the *universal* divided power differentials of `B̂` with its completed divided
  powers — the object `Crystalline.tensorFormsLevelEquiv` of
  `ModuleDifferentials/QuotientForms.lean` speaks in; and
* `Ω̂_{B/A,δ}`, the `p`-adic *completion* of the differentials of `B` — the object
  `Crystalline.completedTensorPowerDifferentials` of `Cosimplicial/CompletedDifferentials.lean`
  is, and therefore the degreewise value of the cosimplicial module `Ω_{D(*)}` the source of
  [Stacks, Tag 07LF] works with.

These are not isomorphic: the first is not `p`-adically complete.  What is true, and what the
level-`e` argument of [Stacks, Tag 07LF] uses, is that they agree **modulo `pᵏ`** for every
sufficiently large `k` — and that is an identification of *uncompleted* quotients, so it survives
tensoring with a module killed by `pᵏ`.
`Crystalline.dividedPowerDifferentialsCompletionComparison` of
`ModuleDifferentials/Completion.lean` — [Stacks, Tag 07KK] — already carries both finite-level
comparisons into the inverse system of the differentials of the quotients `B/pᵏ`; composing them
against each other is the identification wanted, and that is what this module does.

`Crystalline.completedDifferentialsLevelEquiv` is that identification.  It is additive by
construction and `B̂`-linear by `Crystalline.completedDifferentialsLevelEquiv_smul`; the
`B̂`-action on `Ω̂_B / pᵏ` factors through `B̂ → B/pᵏ`, which is
`Crystalline.smul_eq_smul_of_sub_mem`, and the two comparisons of [Stacks, Tag 07KK] are
respectively semilinear over that projection and linear over `B`.  It is pinned by
`Crystalline.completedDifferentialsLevelEquiv_d`, which says it carries
the universal differential of a section coming from `B` to the universal differential of that
section; those sections are dense modulo `pᵏ`, so no second identification can satisfy the same
equation.

## Main definitions

* `Crystalline.completionDifferentialsModPow` — the completion `Ω̂_{B/A,δ}` modulo `pᵏ`.
* `Crystalline.completionDifferentialsModPowEquiv` — it is `Ω_{B/A,δ}` modulo `pᵏ`, which is
  [Stacks, Tag 05GG] for the module of differentials.
* `Crystalline.completedDifferentialsLevelEquiv` — **the two shapes of the differentials of `B̂`
  agree modulo `pᵏ`.**
* `Crystalline.completedDifferentialsLevelLinearEquiv` — the same identification as a `B̂`-linear
  equivalence, which is the form the level-`e` tensor product consumes.

## Main results

* `Crystalline.pAdicPow_smul_top_restrictScalars` — the submodule `pᵏ · M` of a module over a ring
  extension is the same whether `pᵏ` is read in the base or in the extension.
* `Crystalline.smul_eq_smul_of_sub_mem` — on `M / I · M` two scalars differing by an element of
  `I` act alike.
* `Crystalline.completedDifferentialsLevelEquiv_d` — the identification carries `d b` to `d b`.
* `Crystalline.completedDifferentialsLevelEquiv_smul` — the identification is `B̂`-linear.

## Implementation notes

`completionDifferentialsModPow` divides by `pᵏ · ⊤` taken as a submodule over the completion `B̂`,
not over `B`: that is the quotient the tensor product `M ⊗_{B̂} Ω̂_B` of the source's level-`e`
step sees, and it is a `B̂`-module.  `Crystalline.pAdicPow_smul_top_restrictScalars` says the two
submodules have the same carrier, and a quotient by a submodule and by its restriction of scalars
are the *same type*, so `Submodule.quotEquivOfEq` crosses between them and nothing has to be
transported by hand.

Both halves of [Stacks, Tag 07KK] are read at the same index `cutoff + e`, the cutoff being the
one the comparison carries: beneath it the quotients `B/pᵏ` need not carry divided powers at all,
so there is no statement to make there.  For the application that is no restriction, the uniform
level of [Stacks, Tag 07JN] being already past every cutoff in sight.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public section

universe u v

namespace Crystalline

/-! ### The `p`-adic power submodule over a ring extension -/

/-- An element lies in `(p)ᵏ` exactly when it is a multiple of `pᵏ`. -/
private theorem mem_pAdicIdeal_pow_iff {R : Type*} [CommRing R] (p k : ℕ) {x : R} :
    x ∈ DividedPowers.pAdicIdeal (A := R) p ^ k ↔ ∃ c, c * (p : R) ^ k = x := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton'

/-- **The submodule `pᵏ · M` does not depend on which of two rings `pᵏ` is read in.**  For a
module over a commutative `R`-algebra `S`, the `S`-submodule `pᵏ · M` and the `R`-submodule
`pᵏ · M` have the same carrier: the set of multiples of `pᵏ`, which is already stable under all
of `S`. -/
public theorem pAdicPow_smul_top_restrictScalars {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (p k : ℕ) :
    (DividedPowers.pAdicIdeal (A := S) p ^ k • (⊤ : Submodule S M)).restrictScalars R =
      DividedPowers.pAdicIdeal (A := R) p ^ k • (⊤ : Submodule R M) := by
  have hmemR : ((p : R) ^ k) ∈ DividedPowers.pAdicIdeal (A := R) p ^ k :=
    (mem_pAdicIdeal_pow_iff p k).2 ⟨1, one_mul _⟩
  have hmemS : ((p : S) ^ k) ∈ DividedPowers.pAdicIdeal (A := S) p ^ k :=
    (mem_pAdicIdeal_pow_iff p k).2 ⟨1, one_mul _⟩
  have hps : algebraMap R S ((p : R) ^ k) = (p : S) ^ k := by simp
  apply le_antisymm
  · intro x hx
    refine Submodule.smul_induction_on (p := fun y ↦
      y ∈ DividedPowers.pAdicIdeal (A := R) p ^ k • (⊤ : Submodule R M))
      ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ fun y z hy hz ↦ Submodule.add_mem _ hy hz
    intro s hs m _
    obtain ⟨c, rfl⟩ := (mem_pAdicIdeal_pow_iff p k).1 hs
    rw [mul_comm, mul_smul, ← hps, algebraMap_smul]
    exact Submodule.smul_mem_smul hmemR Submodule.mem_top
  · rw [Submodule.smul_le]
    intro r hr m _
    obtain ⟨c, rfl⟩ := (mem_pAdicIdeal_pow_iff p k).1 hr
    rw [Submodule.restrictScalars_mem, algebra_compatible_smul S (c * (p : R) ^ k) m, map_mul, hps,
      mul_comm, mul_smul]
    exact Submodule.smul_mem_smul hmemS Submodule.mem_top

/-! ### The completion of the differentials at a finite level -/

section Level

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)

/-- **The completion `Ω̂_{B/A,δ}` of the divided power differentials, modulo `pᵏ`.**  The
quotient is by the `pᵏ`-multiples taken as a submodule over the completion `B̂`, so that it is a
`B̂`-module; by `Crystalline.pAdicPow_smul_top_restrictScalars` the carrier is the same as over
`B`. -/
public noncomputable abbrev completionDifferentialsModPow (k : ℕ) : Type v :=
  AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta) ⧸
    (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k •
      (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
          (dividedPowerDifferentials (A := A) delta))))

/-- **[Stacks, Tag 05GG] for the divided power differentials**: the completion of
`Ω_{B/A,δ}` modulo `pᵏ` is `Ω_{B/A,δ}` modulo `pᵏ`.  The quotient on the left is over the
completion and the one on the right over `B`; the two submodules have the same carrier, so the
identification is `AdicCompletion.quotPowSMulTopEquiv` after
`Crystalline.pAdicPow_smul_top_restrictScalars`. -/
public noncomputable def completionDifferentialsModPowEquiv (k : ℕ) :
    completionDifferentialsModPow (A := A) J delta p k ≃ₗ[B]
      differentialsModPow (A := A) J delta p k :=
  (Submodule.quotEquivOfEq _ _
      (pAdicPow_smul_top_restrictScalars (R := B)
        (S := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
        (M := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
          (dividedPowerDifferentials (A := A) delta)) p k)).trans
    (AdicCompletion.quotPowSMulTopEquiv (Submodule.fg_span_singleton _)
      (dividedPowerDifferentials (A := A) delta) k)

/-- The identification of [Stacks, Tag 05GG] sends the class of the image of a differential to
the class of that differential. -/
@[simp]
public theorem completionDifferentialsModPowEquiv_mk_of (k : ℕ)
    (omega : dividedPowerDifferentials (A := A) delta) :
    completionDifferentialsModPowEquiv (A := A) J delta p k
        (Submodule.Quotient.mk
          (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) _ omega)) =
      Submodule.Quotient.mk omega :=
  rfl

end Level

/-- **On `M / I · M` two scalars differing by an element of `I` act alike.**  Their difference
annihilates the quotient. -/
public theorem smul_eq_smul_of_sub_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {r r' : R} (h : r - r' ∈ I) (x : M ⧸ (I • (⊤ : Submodule R M))) :
    r • x = r' • x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← sub_smul]
  exact Submodule.smul_mem_smul h Submodule.mem_top

section Level

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)

/-! ### The two shapes of the differentials of the completion -/

variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The universal differentials of `B̂` and the completion of the differentials of `B` agree
modulo `pᵏ`.**

`Ω_{B̂/A,γ̂} / pᵏ ≃ Ω̂_{B/A,δ} / pᵏ`  for `k = cutoff + e`.

Both sides are computed by [Stacks, Tag 07KK]: the left is `Crystalline.
DifferentialsCompletionComparison.fromCompletionAt` of the differentials of the quotient
`B/pᵏ`, the right — after [Stacks, Tag 05GG] — is `...fromOriginalAt` of the same, so the
identification is one composed with the inverse of the other.  **The tensor products this
survives are the uncompleted ones**, which is what the level-`e` step of the source's proof of
[Stacks, Tag 07LF] needs; no `p`-adic completion of a tensor product occurs. -/
public noncomputable def completedDifferentialsLevelEquiv
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) :
    completedDifferentialsModPow (A := A) J delta p hp (cmp.quotientSystem.cutoff + e) ≃+
      completionDifferentialsModPow (A := A) J delta p (cmp.quotientSystem.cutoff + e) :=
  ((cmp.fromCompletionAt e).trans (cmp.fromOriginalAt e).toAddEquiv.symm).trans
    (completionDifferentialsModPowEquiv (A := A) J delta p
      (cmp.quotientSystem.cutoff + e)).symm.toAddEquiv

/-- **The identification carries `d b` to `d b`.**  For a section `b` of `B`, the class of the
universal divided power differential of its image in `B̂` goes to the class of the image of the
universal divided power differential of `b`.  Those classes generate, so this pins the
identification. -/
public theorem completedDifferentialsLevelEquiv_d
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) (b : B) :
    completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e
        (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1
          (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b))) =
      Submodule.Quotient.mk
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) _
          (dividedPowerDifferential (A := A) delta b)) := by
  have hcomp := cmp.fromCompletionAt_d e
    (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)
  rw [AdicCompletion.evalₐ_of] at hcomp
  have horig := cmp.fromOriginalAt_d e b
  apply (completionDifferentialsModPowEquiv (A := A) J delta p
    (cmp.quotientSystem.cutoff + e)).injective
  rw [completionDifferentialsModPowEquiv_mk_of]
  change (completionDifferentialsModPowEquiv (A := A) J delta p _)
    ((completionDifferentialsModPowEquiv (A := A) J delta p _).symm
      ((cmp.fromOriginalAt e).symm (cmp.fromCompletionAt e _))) = _
  rw [LinearEquiv.apply_symm_apply, hcomp, ← horig, LinearEquiv.symm_apply_apply]

/-- **The identification modulo `pᵏ` is linear over the completion `B̂`.**

The `B̂`-action on `Ω̂_{B/A,δ} / pᵏ` factors through `B̂ → B/pᵏ`, by
`Crystalline.smul_eq_smul_of_sub_mem` and `Crystalline.pAdicIdeal_eq_ker_eval`; and the two
comparisons of [Stacks, Tag 07KK] it is composed of are respectively semilinear over that
projection — `Crystalline.DifferentialsCompletionComparison.fromCompletionAt_smul` — and linear
over `B`.  So the composite is `B̂`-linear, which is what the level-`e` tensor product of the
source's proof of [Stacks, Tag 07LF] needs. -/
public theorem completedDifferentialsLevelEquiv_smul
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ)
    (r : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (omega : completedDifferentialsModPow (A := A) J delta p hp
      (cmp.quotientSystem.cutoff + e)) :
    completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e (r • omega) =
      r • completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e omega := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p)
      (cmp.quotientSystem.cutoff + e) r)
  have hsub : r - AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b ∈
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
        (cmp.quotientSystem.cutoff + e) := by
    rw [pAdicIdeal_eq_ker_eval (B := B) p (cmp.quotientSystem.cutoff + e), RingHom.mem_ker]
    change (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p)
      (cmp.quotientSystem.cutoff + e)) _ = 0
    rw [map_sub, AdicCompletion.evalₐ_of, ← hb, sub_self]
  rw [smul_eq_smul_of_sub_mem hsub]
  change (completionDifferentialsModPowEquiv (A := A) J delta p _).symm
      ((cmp.fromOriginalAt e).symm (cmp.fromCompletionAt e (_ • omega))) = _
  rw [cmp.fromCompletionAt_smul e _ omega, AdicCompletion.evalₐ_of]
  change (completionDifferentialsModPowEquiv (A := A) J delta p _).symm
      ((cmp.fromOriginalAt e).symm ((Ideal.Quotient.mk _ b) • _)) = _
  have hmk : ∀ y : QuotientDifferentialsSystem.term (A := A) J delta p
      cmp.quotientSystem e,
      (Ideal.Quotient.mk
        (DividedPowers.pAdicIdeal (A := B) p ^ (cmp.quotientSystem.cutoff + e)) b) • y =
        b • y := fun y ↦ IsScalarTower.algebraMap_smul _ b y
  rw [hmk, (cmp.fromOriginalAt e).symm.map_smul,
    (completionDifferentialsModPowEquiv (A := A) J delta p
      (cmp.quotientSystem.cutoff + e)).symm.map_smul]
  rw [smul_eq_smul_of_sub_mem hsub]
  exact (IsScalarTower.algebraMap_smul
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) b
    (completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e omega)).symm

/-- **The identification of the two shapes modulo `pᵏ`, as a `B̂`-linear equivalence.**  This is
`Crystalline.completedDifferentialsLevelEquiv` with
`Crystalline.completedDifferentialsLevelEquiv_smul` folded in; it is the form a tensor product
over `B̂` consumes. -/
public noncomputable def completedDifferentialsLevelLinearEquiv
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) :
    completedDifferentialsModPow (A := A) J delta p hp (cmp.quotientSystem.cutoff + e) ≃ₗ[
        AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
      completionDifferentialsModPow (A := A) J delta p (cmp.quotientSystem.cutoff + e) :=
  (completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e).toLinearEquiv
    (completedDifferentialsLevelEquiv_smul (A := A) J delta p hp cmp e)

end Level

end Crystalline

end
