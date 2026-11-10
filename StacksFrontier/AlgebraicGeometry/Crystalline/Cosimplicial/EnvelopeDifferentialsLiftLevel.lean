module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeDifferentialsLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeDifferentialsLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamExterior
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelForms

/-!
# The level identification of the two shapes of `Ω_{D(n)}` is the canonical map, mod `pᵏ`

Work in an affine crystalline situation `(A, I, γ)` with target `C`, choose a surjection
`P = A[x_i] → C`, let `E(n)` be the divided power envelope of the kernel of the `(n + 1)`-fold
tensor power `P ⊗_A ⋯ ⊗_A P → C` and `D(n)` its `p`-adic completion.  Two modules of
differentials attach to `D(n)` — the universal `Ω_{D(n)/A,γ̄(n)}` and the completed
`Ω̂_{E(n)/A,δ(n)}` of `Crystalline.completedTensorPowerDifferentials` — and the proof of
[Stacks, Tag 07LF] meets both:

* `Crystalline.tensorPowerDifferentialsToCompleted` is **the canonical `D(n)`-linear map** from
  the first to the second, the one [Stacks, Tag 07HZ] produces out of the divided power
  derivation `d : D(n) → Ω_{D(n)}` of [Stacks, Tag 07L1];
* `Crystalline.completedDifferentialsLevelMap` is the reduction of the first modulo `pᵏ` **read
  into the second modulo `pᵏ`** through the identification
  `Crystalline.completedDifferentialsLevelLinearEquiv` of [Stacks, Tag 07KK].  That is the map
  `Crystalline.tensorFormsCompletionLevelEquiv` exhibits as a base change, and therefore the map
  which carries the level identification up the exterior powers.

This file proves the two are the same: **the level identification is the canonical map reduced
modulo `p^{N + e}`, and nothing else.**  That is what makes
`Crystalline.tensorFormsCompletionLevelEquiv` — and hence the degreewise comparison of the
source's proof of [Stacks, Tag 07LF] — the canonical comparison rather than some bijection.

## Main definitions

* `Crystalline.completedTensorPowerDifferentialsMk` — the reduction
  `Ω̂_{E(n)/A,δ(n)} → Ω̂_{E(n)/A,δ(n)} / pᵏ`, with its target spelled as
  `Crystalline.completionDifferentialsModPow` of the envelope.
* `Crystalline.tensorPowerDifferentialsToCompletedOfEnvelope` —
  `Crystalline.tensorPowerDifferentialsToCompleted` with its source spelled through
  `DividedPowers.completedDividedPowers` of the envelope rather than through
  `Crystalline.completedTensorPowerDividedPowerRing`.

## Main results

* `Crystalline.completedDifferentialsLevelMap_eq_tensorPowerDifferentialsToCompleted` — **the
  level identification is the canonical map reduced modulo `p^{N + e}`**, as an equality of
  `D(n)`-linear maps.
* `Crystalline.exists_approx_pAdicCompletedTensorPowerEnvelope` — every section of `D(n)` agrees
  modulo `pᵏ` with a section of `E(n)`.
* `Crystalline.completedEnvelopeDifferential_sub_mem_pAdicPow` — two sections of `D(n)` agreeing
  modulo `pᵏ` have universal differentials agreeing modulo `pᵏ`.

## Implementation notes

The two shapes of the divided powers of `D(n)` —
`(Crystalline.completedTensorPowerDividedPowerRing s f hf n).dividedPowers`, which
`Crystalline.tensorPowerDifferentialsToCompleted` is stated over, and
`(DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal … ).1`, which
`Crystalline.completedDifferentialsLevelMap` is stated over — are definitionally equal but not
syntactically so: the first goes through `DividedPowerRing.of`, and the two proofs that `p` is
nilpotent modulo the divided power ideal are different terms.  The same holds of the two shapes
of `Ω̂_{E(n)/A,δ(n)}` modulo `pᵏ`.

**Every such identification is paid once, in a definition or in a declaration whose statement is
the identification, and no proof below crosses between two spellings.**  That is the whole
content of `completedTensorPowerDifferentialsMk` and
`tensorPowerDifferentialsToCompletedOfEnvelope`, neither of which does anything but name an
existing map in the other spelling, and of
`completedEnvelopeDifferential_sub`, `completedEnvelopeDifferential_mem_pAdicPow` and
`exists_approx_pAdicCompletedTensorPowerEnvelope`, which restate library lemmas at `E(n)`.
Performed inside a proof instead, the same identification exhausts the heartbeat budget at
`whnf` or overflows the recursion depth.  This is the discipline
`Crystalline.dividedPowerDeRham` and `...crysFormSectionsTop` are written with.

For the same reason the proofs below use `Eq.subst` with an explicit motive, and `Eq.trans`,
where a rewrite would read more naturally: `rw` abstracts the goal over the term being
rewritten, and the instance arguments of the submodules and quotients here make that abstraction
unaffordable even when both sides are already in the right spelling.  `Exists.elim` is used in
place of `obtain` for the same reason.

The `A`-algebra structure on `E(n)` is a `letI` rather than an instance, following
`Cosimplicial/EnvelopeDifferentialsLevel.lean`, so every statement mentioning it opens with that
`letI`.

## What is and is not proved

Everything here is proved and nothing is assumed.  **No tag attribute is placed and
[Stacks, Tag 07LF] is not proved.**  What is proved is the faithfulness half of one input of
that tag's remaining step: that the degreewise comparison the source's proof makes is the
canonical one.  The cosimplicial isomorphism `ε` of
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` is **not** constructed here, and
nothing here mentions the crystalline site.

## References

* [Stacks Project, Lemma 60.6.5, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07L1](https://stacks.math.columbia.edu/tag/07L1)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

universe u v w

namespace Crystalline

/-! ### Two facts about a quotient by `I · M` -/

/-- **A scalar from `I` kills `M ⧸ I · M`.** -/
public theorem smul_quotient_smul_top_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Ideal R} {r : R} (hr : r ∈ I)
    (x : M ⧸ (I • (⊤ : Submodule R M))) : r • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- **A linear map into a module killed by `I` kills `I · M`.** -/
public theorem linearMap_eq_zero_of_mem_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {I : Ideal R} (L : M →ₗ[R] N)
    (hN : ∀ r ∈ I, ∀ y : N, r • y = 0) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    L x = 0 := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
  · rw [map_smul]; exact hN r hr _
  · rw [map_add, hy, hz, add_zero]

/-- A linear map into a module killed by `I` agrees on elements differing by `I · M`. -/
private theorem linearMap_eq_of_sub_mem_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {I : Ideal R} (L : M →ₗ[R] N)
    (hN : ∀ r ∈ I, ∀ y : N, r • y = 0) {x y : M} (h : x - y ∈ I • (⊤ : Submodule R M)) :
    L x = L y :=
  sub_eq_zero.mp ((map_sub L x y).symm.trans (linearMap_eq_zero_of_mem_smul_top L hN h))

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-! ### Approximating a section of `D(n)` by a section of `E(n)` -/

/-- **Every section of `D(n)` agrees modulo `pᵏ` with a section of `E(n)`.**  The evaluation
`D(n) → E(n)/pᵏ` is surjective, so the class of the given section is the class of some section
of `E(n)`, and the difference lies in `(p)ᵏ` because that ideal is the kernel of the
evaluation. -/
public theorem exists_approx_pAdicCompletedTensorPowerEnvelope (n k : ℕ)
    (b : AdicCompletion (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p) (tensorPowerEnvelope s f n).object) :
    ∃ b' : (tensorPowerEnvelope s f n).object,
      b - AdicCompletion.of (DividedPowers.pAdicIdeal
          (A := (tensorPowerEnvelope s f n).object) s.p) _ b' ∈
        DividedPowers.pAdicIdeal (A := AdicCompletion (DividedPowers.pAdicIdeal
          (A := (tensorPowerEnvelope s f n).object) s.p)
          (tensorPowerEnvelope s f n).object) s.p ^ k := by
  obtain ⟨b', hb'⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p) k b)
  refine ⟨b', ?_⟩
  rw [pAdicIdeal_eq_ker_eval (B := (tensorPowerEnvelope s f n).object) s.p k, RingHom.mem_ker]
  change (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal
    (A := (tensorPowerEnvelope s f n).object) s.p) k) _ = 0
  rw [map_sub, AdicCompletion.evalₐ_of, ← hb', sub_self]

/-- The universal divided power differential of `D(n)` read on a difference. -/
public theorem completedEnvelopeDifferential_sub (n : ℕ)
    (x y : AdicCompletion (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p) (tensorPowerEnvelope s f n).object) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    dividedPowerDifferential (A := (s.A : Type u))
        (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
          (tensorPowerEnvelope s f n).object.dividedPowers s.p
          (polynomialDividedPowerEnvelope_prime_nilpotent s
            (tensorPowerPresentation s f n))).1 (x - y) =
      dividedPowerDifferential (A := (s.A : Type u))
          (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
            (tensorPowerEnvelope s f n).object.dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s
              (tensorPowerPresentation s f n))).1 x -
        dividedPowerDifferential (A := (s.A : Type u))
          (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
            (tensorPowerEnvelope s f n).object.dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s
              (tensorPowerPresentation s f n))).1 y := by
  let : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  exact dividedPowerDifferential_sub _ x y

/-- The universal divided power differential of a section of `(p)ᵏ D(n)` lies in `pᵏ` times the
universal differentials of `D(n)`. -/
public theorem completedEnvelopeDifferential_mem_pAdicPow (n k : ℕ)
    (z : AdicCompletion (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p) (tensorPowerEnvelope s f n).object)
    (hz : z ∈ DividedPowers.pAdicIdeal (A := AdicCompletion (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p)
      (tensorPowerEnvelope s f n).object) s.p ^ k) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    dividedPowerDifferential (A := (s.A : Type u))
        (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
          (tensorPowerEnvelope s f n).object.dividedPowers s.p
          (polynomialDividedPowerEnvelope_prime_nilpotent s
            (tensorPowerPresentation s f n))).1 z ∈
      DividedPowers.pAdicIdeal (A := AdicCompletion (DividedPowers.pAdicIdeal
          (A := (tensorPowerEnvelope s f n).object) s.p)
          (tensorPowerEnvelope s f n).object) s.p ^ k •
        (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal
            (A := (tensorPowerEnvelope s f n).object) s.p)
            (tensorPowerEnvelope s f n).object)
          (dividedPowerDifferentials (A := (s.A : Type u))
            (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
              (tensorPowerEnvelope s f n).object.dividedPowers s.p
              (polynomialDividedPowerEnvelope_prime_nilpotent s
                (tensorPowerPresentation s f n))).1)) := by
  let : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  exact dividedPowerDifferential_mem_pAdicPow _ _ s.p k hz

/-- **Two sections of `D(n)` agreeing modulo `pᵏ` have universal differentials agreeing modulo
`pᵏ`.** -/
public theorem completedEnvelopeDifferential_sub_mem_pAdicPow (n k : ℕ)
    (x y : AdicCompletion (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p) (tensorPowerEnvelope s f n).object)
    (hz : x - y ∈ DividedPowers.pAdicIdeal (A := AdicCompletion (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p)
      (tensorPowerEnvelope s f n).object) s.p ^ k) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    dividedPowerDifferential (A := (s.A : Type u))
          (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
            (tensorPowerEnvelope s f n).object.dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s
              (tensorPowerPresentation s f n))).1 x -
        dividedPowerDifferential (A := (s.A : Type u))
          (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
            (tensorPowerEnvelope s f n).object.dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s
              (tensorPowerPresentation s f n))).1 y ∈
      DividedPowers.pAdicIdeal (A := AdicCompletion (DividedPowers.pAdicIdeal
          (A := (tensorPowerEnvelope s f n).object) s.p)
          (tensorPowerEnvelope s f n).object) s.p ^ k •
        (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal
            (A := (tensorPowerEnvelope s f n).object) s.p)
            (tensorPowerEnvelope s f n).object)
          (dividedPowerDifferentials (A := (s.A : Type u))
            (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
              (tensorPowerEnvelope s f n).object.dividedPowers s.p
              (polynomialDividedPowerEnvelope_prime_nilpotent s
                (tensorPowerPresentation s f n))).1)) := by
  let : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  exact Eq.subst (motive := fun wq => wq ∈ _) (completedEnvelopeDifferential_sub s f n x y)
    (completedEnvelopeDifferential_mem_pAdicPow s f n k (x - y) hz)

/-! ### The two maps, in one spelling -/

/-- **The reduction of `Ω̂_{E(n)/A,δ(n)}` modulo `pᵏ`**, with its target spelled as
`Crystalline.completionDifferentialsModPow` of the envelope, which is where
`Crystalline.completedDifferentialsLevelMap` lands.  The identification of that spelling with
the quotient of `Crystalline.completedTensorPowerDifferentials` is paid here, once. -/
public noncomputable def completedTensorPowerDifferentialsMk (n k : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    completedTensorPowerDifferentials s f n →ₗ[pAdicCompletedTensorPowerEnvelope s f hf n]
      completionDifferentialsModPow (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.ideal
        (tensorPowerEnvelope s f n).object.dividedPowers s.p k := by
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  exact Submodule.mkQ _

/-- The reduction is the quotient map. -/
public theorem completedTensorPowerDifferentialsMk_apply (n k : ℕ)
    (x : completedTensorPowerDifferentials s f n) :
    completedTensorPowerDifferentialsMk s f hf n k x = Submodule.Quotient.mk x :=
  rfl

/-- **The canonical map `Ω_{D(n)/A,γ̄(n)} → Ω̂_{E(n)/A,δ(n)}`**, with its source spelled through
`DividedPowers.completedDividedPowers` of the envelope rather than through
`Crystalline.completedTensorPowerDividedPowerRing`.  The two divided power structures on `D(n)`
are the same; the identification is paid here, once. -/
public noncomputable def tensorPowerDifferentialsToCompletedOfEnvelope (n : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    dividedPowerDifferentials (A := (s.A : Type u))
        (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
          (tensorPowerEnvelope s f n).object.dividedPowers s.p
          (polynomialDividedPowerEnvelope_prime_nilpotent s
            (tensorPowerPresentation s f n))).1 →ₗ[pAdicCompletedTensorPowerEnvelope s f hf n]
      completedTensorPowerDifferentials s f n := by
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  exact tensorPowerDifferentialsToCompleted s f hf n

/-- **The canonical map carries `d b` to `d b`**, in the envelope spelling. -/
public theorem tensorPowerDifferentialsToCompletedOfEnvelope_d (n : ℕ)
    (b : pAdicCompletedTensorPowerEnvelope s f hf n) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    tensorPowerDifferentialsToCompletedOfEnvelope s f hf n
        (dividedPowerDifferential (A := (s.A : Type u))
          (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
            (tensorPowerEnvelope s f n).object.dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s
              (tensorPowerPresentation s f n))).1 b) =
      tensorPowerDerivation s f hf n b :=
  tensorPowerDifferentialsToCompleted_d s f hf n b

/-! ### The level identification is the canonical map -/

/-- **The level identification of the two shapes of `Ω_{D(n)}` is the canonical map, reduced
modulo `p^{N + e}`.**

`Crystalline.completedDifferentialsLevelMap` read at the envelope `E(n)` — the map
`Crystalline.tensorFormsCompletionLevelEquiv` exhibits as a base change, and therefore the map
which carries the level identification of [Stacks, Tag 07KK] up the exterior powers — is
`Crystalline.tensorPowerDifferentialsToCompleted`, the canonical `D(n)`-linear map of
[Stacks, Tag 07HZ], followed by the reduction modulo `p^{N + e}`.

Both sides are `D(n)`-linear and agree on the universal differential of every section of `D(n)`,
which is all `Crystalline.differentials_hom_ext` needs.  On the universal differential of a
section of the *envelope* they agree because both carry it to the class of that section's
differential: `Crystalline.completedDifferentialsLevelEquiv_d` on one side, and
`tensorPowerDifferentialsToCompletedOfEnvelope_d` together with the defining equation of
`Crystalline.tensorPowerDerivation` on the other.  A general section of `D(n)` agrees with one
of the envelope modulo `p^{N + e}` by `exists_approx_pAdicCompletedTensorPowerEnvelope`, so
their universal differentials agree modulo `p^{N + e}` by
`completedEnvelopeDifferential_sub_mem_pAdicPow`, and both maps kill
`p^{N + e} · Ω_{D(n)/A,γ̄(n)}`.

**No tag attribute is placed**: this is the faithfulness half of one input of the remaining step
of [Stacks, Tag 07LF], not a clause of that tag. -/
public theorem completedDifferentialsLevelMap_eq_tensorPowerDifferentialsToCompleted (n e : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    completedDifferentialsLevelMap (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.ideal
        (tensorPowerEnvelope s f n).object.dividedPowers s.p
        (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))
        (tensorPowerEnvelopeCompletionComparison s f n) e =
      (completedTensorPowerDifferentialsMk s f hf n
          ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e)).comp
        (tensorPowerDifferentialsToCompletedOfEnvelope s f hf n) := by
  let : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  refine LinearMap.ext fun omega => DFunLike.congr_fun (differentials_hom_ext (J := _)
    (delta := (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f n).object.ideal
      (tensorPowerEnvelope s f n).object.dividedPowers s.p
      (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))).1)
    (RingHom.id (pAdicCompletedTensorPowerEnvelope s f hf n))
    (completedDifferentialsLevelMap (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.ideal
        (tensorPowerEnvelope s f n).object.dividedPowers s.p
        (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))
        (tensorPowerEnvelopeCompletionComparison s f n) e).toAddMonoidHom
    (((completedTensorPowerDifferentialsMk s f hf n
          ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e)).comp
        (tensorPowerDifferentialsToCompletedOfEnvelope s f hf n)).toAddMonoidHom)
    (fun _ _ => by simp only [LinearMap.toAddMonoidHom_coe, map_smul, RingHom.id_apply])
    (fun _ _ => by simp only [LinearMap.toAddMonoidHom_coe, map_smul, RingHom.id_apply])
    ?_) omega
  intro b
  refine Exists.elim (exists_approx_pAdicCompletedTensorPowerEnvelope s f n
    ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e) b)
    fun b' hsub => ?_
  have hmem := completedEnvelopeDifferential_sub_mem_pAdicPow s f n
    ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e) b
    (AdicCompletion.of (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelope s f n).object) s.p) _ b') hsub
  have heq1 := linearMap_eq_of_sub_mem_smul_top
    (completedDifferentialsLevelMap (A := (s.A : Type u))
      (tensorPowerEnvelope s f n).object.ideal
      (tensorPowerEnvelope s f n).object.dividedPowers s.p
      (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))
      (tensorPowerEnvelopeCompletionComparison s f n) e)
    (fun _ hr y => smul_quotient_smul_top_eq_zero hr y) hmem
  have heq2 := linearMap_eq_of_sub_mem_smul_top
    ((completedTensorPowerDifferentialsMk s f hf n
        ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e)).comp
      (tensorPowerDifferentialsToCompletedOfEnvelope s f hf n))
    (fun _ hr y => smul_quotient_smul_top_eq_zero hr y) hmem
  have hbase1 := completedDifferentialsLevelEquiv_d (A := (s.A : Type u))
    (tensorPowerEnvelope s f n).object.ideal
    (tensorPowerEnvelope s f n).object.dividedPowers s.p
    (polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s f n))
    (tensorPowerEnvelopeCompletionComparison s f n) e b'
  have hbase2 := (congrArg (completedTensorPowerDifferentialsMk s f hf n
      ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e))
    ((tensorPowerDifferentialsToCompletedOfEnvelope_d s f hf n
        (AdicCompletion.of (DividedPowers.pAdicIdeal
          (A := (tensorPowerEnvelope s f n).object) s.p) _ b')).trans
      ((completedTensorPowerDifferential s f hf n).2.2 b'))).trans
    (completedTensorPowerDifferentialsMk_apply s f hf n
      ((tensorPowerEnvelopeCompletionComparison s f n).quotientSystem.cutoff + e) _)
  exact heq1.trans ((hbase1.trans hbase2.symm).trans heq2.symm)

end Crystalline

end
