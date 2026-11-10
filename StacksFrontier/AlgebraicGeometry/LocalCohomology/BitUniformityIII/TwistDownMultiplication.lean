module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientTwistDown
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistShiftMultiplication

/-!
# Twisting down `c` steps against multiplication by `(b⁽¹⁾)^c`

Let `A` be a commutative ring, `I ⊆ A` an ideal, `S = ⨁_{n ≥ 0} Iⁿ` the Rees algebra and
`X = Proj(S)` the blowup of `Spec(A)` in `I`.
`BitUniformityIII/TwistShiftMultiplication.lean` proves the *one-step* laws: for `b ∈ I`,
multiplication by the degree-one element `b⁽¹⁾ = bX` and the single twisting-down map
`𝒪_X(t+1) ⟶ 𝒪_X(t)` compose, in either order, to multiplication by `b`. This file proves the
`c`-step laws, against the family `Stacks.Blowup.twistDownMap I q q'` of
`BitUniformityIII/AmbientTwistDown.lean`: multiplication by `(b⁽¹⁾)^c` and twisting down from
`q = c + q'` to `q'` compose, in either order, to multiplication by `b^c`.

That is the form the cohomological clauses of [Stacks, Tag 0GAA] consume. On the basic open
`D₊(b⁽¹⁾)` of a degree-one generator multiplication by `(b⁽¹⁾)^c` is invertible, so there
twisting down `c` steps differs from an isomorphism by multiplication by `b^c ∈ I^c` — and `I^c`
annihilates the twisted pullback of a presented module
(`Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero`).

Of the two orders it is the second,
`Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOnePow`, that the local argument
consumes: it is the one that can be precomposed with a morphism *into* `𝒪_X(q)`, so it turns the
annihilation of a subsheaf of `𝒪_X(q) ⊗ p^*M` by `I^c` into a statement about the image of that
subsheaf under twisting down.

## Why this is an induction and not a second construction

The one-step law is not a statement about `divX` that could be iterated: it is an equation
between *morphisms of twisting sheaves*, and the degree bookkeeping of
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap` is already a parameter with an
equation. So the `c`-step law follows from the one-step law, the composition law
`Stacks.Blowup.twistDownMap_comp`, and the multiplicativity
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_mul` of the scalar action, by
induction on `c` with the *bottom* degree `q'` generalised. No iterate of `divX` is computed
here; all of that lives in `Stacks.Blowup.reesShiftDown`, inside degree-preservation `Prop`s.

The one place arithmetic would have forced a transport is the intermediate degree:
`twistScalarSheafMap_mul` produces `((1 : ℕ) : ℤ) + q'`, which is not `q' + 1`, and
`Stacks.Blowup.twistDownMap_succ` is stated at `q' + 1`. So the one-step law is first restated
with its target degree as a parameter carrying an equation
(`Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistDownMap`), proved by `subst` onto the
canonical shape. Nothing is transported and no `eqToHom` appears.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_mul_of_eq`: the
  multiplicativity of the scalar action with the *intermediate degree* supplied as a parameter
  carrying an equation, rather than fixed at `(j : ℤ) + n`.
* `Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistDownMap` and
  `Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOne`: the two one-step laws of
  [Stacks, Tag 02OS] part (3) at a degree supplied as a parameter, and against
  `Stacks.Blowup.twistDownMap` rather than `Stacks.Blowup.twistShiftMap`.
* `Stacks.Blowup.twistScalarSheafMap_reesDegOnePow_comp_twistDownMap`: **the `c`-step law** —
  multiplication by `(b⁽¹⁾)^c` as a morphism `𝒪_X(q') ⟶ 𝒪_X(q)`, followed by
  `twistDownMap I q q'`, is multiplication by `b^c`, for every `b ∈ I`, every `c : ℕ` and every
  pair of integers with `c + q' = q`.
* `Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOnePow`: **the `c`-step law in the
  other order** — `twistDownMap I q q'` followed by multiplication by `(b⁽¹⁾)^c` is
  multiplication by `b^c`, as morphisms `𝒪_X(q) ⟶ 𝒪_X(q)`. It is the special case `a = 1` of
  `Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesConstMulDegOnePow`, which carries an
  extra degree-zero factor `a : A`.

## Implementation notes

**No `rw` is applied to an equation between morphisms**, for the reason
`BitUniformityIII/TwistShiftMultiplication.lean` records: `Stacks.Blowup.twistDownMap` is
`irreducible` and a `rw` inside a `≫` is where this subtree's heartbeat budget goes. The chain is
built from `CategoryTheory.whisker_eq`, `CategoryTheory.eq_whisker` and
`CategoryTheory.Category.assoc`, which take a morphism first-order.

**The scalar `(b⁽¹⁾)^{c+1}` is split as `(b⁽¹⁾)^c · b⁽¹⁾`, not as `b⁽¹⁾ · (b⁽¹⁾)^c.** The degree
index of `twistScalarSheafMap_mul` is `i + j`, and `c + 1` is the index the goal carries; `1 + c`
is not definitionally equal to it for a variable `c`, so the other order would need a transport
along an equation between the `ℕ` arguments of a grading.

**The first induction closes on the one-step law for a new generator.** After the inductive
hypothesis is used, the remaining composite is multiplication by `b^c` followed by multiplication
by `b⁽¹⁾`, which is multiplication by the single degree-one element `(b^{c+1})⁽¹⁾`
(`Stacks.Blowup.reesConst_mul_reesDegOne`); the one-step law at `b^{c+1} ∈ I` then finishes it.

**The second induction carries a degree-zero factor instead.** There the degree-one factor is
peeled off at the *bottom*, so the `b` it produces appears between the remaining twisting-down map
and the remaining scalar, where neither of the two generators' laws reaches it. It is absorbed into
the scalar rather than commuted past the twisting-down map, which is why the statement proved by
induction is the one with a free `a : A` in it; the absorption is where
`twistScalarSheafMap_mul_of_eq` is needed, because the degree it must absorb at is `q₁` and
`twistScalarSheafMap_mul` offers only `((0 : ℕ) : ℤ) + q₁`. Neither induction needs a lemma
commuting a degree-zero scalar past `twistDownMap`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistedDegree_zero
  twistScalarSheafMap_mul twistScalarSheafMap_one)

universe u v

/-! ### Multiplicativity of the scalar action, at a chosen intermediate degree -/

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

variable {S : Type u} {σ : Type v} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **A product of homogeneous scalars of degrees `i` and `j` acts as the composite of the two
morphisms of twisting sheaves, through an intermediate degree the caller chooses.**

`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_mul` fixes that degree at
`(j : ℤ) + n`. A caller that has to meet a morphism `𝒪(m) ⟶ 𝒪(k)` already written at some other
spelling `m` of the same integer therefore cannot use it: `m` and `(j : ℤ) + n` are arguments of
the twisting sheaves, not `Prop`s, so they are not interchangeable by proof irrelevance, and
`((0 : ℕ) : ℤ) + m` is not definitionally `m`. Taking the intermediate degree as a parameter with
an equation removes the obstruction; the equation is discharged by `subst` and the existing lemma
applies. -/
theorem twistScalarSheafMap_mul_of_eq (i j : ℕ) (n m k : ℤ) (hm : (j : ℤ) + n = m)
    (hk : ((i + j : ℕ) : ℤ) + n = k) (hik : (i : ℤ) + m = k) (a : 𝒮 i) (b : 𝒮 j) :
    twistScalarSheafMap 𝒮 (i + j) n k hk
        ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ =
      twistScalarSheafMap 𝒮 j n m hm b ≫ twistScalarSheafMap 𝒮 i m k hik a := by
  subst hm
  exact twistScalarSheafMap_mul 𝒮 i j n k hk hik a b

end Stacks.AlgebraicGeometry.ProjTwistedSections

open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap_mul_of_eq)

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Powers of a degree-one generator -/

/-- **`(b⁽¹⁾)^c` is homogeneous of degree `c`.** This is `SetLike.pow_mem_graded` with the
`ℕ`-arithmetic `c • 1 = c` discharged. -/
theorem reesDegOnePow_mem_reesGrading {b : A} (hb : b ∈ I) (c : ℕ) :
    (reesDegOne I hb : reesAlgebra I) ^ c ∈ reesGrading I c := by
  simpa using SetLike.pow_mem_graded c (reesDegOne_mem_reesGrading I hb)

/-- **`a · (b⁽¹⁾)^c` is homogeneous of degree `c`** for every `a : A`: the constant `a` is
homogeneous of degree zero, and `c + 0 = c`. -/
theorem reesConstMulDegOnePow_mem_reesGrading {b : A} (hb : b ∈ I) (c : ℕ) (a : A) :
    (reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I) ∈ reesGrading I c :=
  SetLike.mul_mem_graded (reesDegOnePow_mem_reesGrading I hb c)
    (SetLike.algebraMap_mem_graded (reesGrading I) a)

/-- **`b^c · b⁽¹⁾ = (b^{c+1})⁽¹⁾`**: the product of a degree-zero constant and a degree-one
monomial is again a degree-one monomial. This is what lets the inductive step close on the
one-step law for the generator `b^{c+1}` instead of on a commutation lemma. -/
theorem reesConst_mul_reesDegOne (c : ℕ) {b : A} (hb : b ∈ I) (hb' : b ^ (c + 1) ∈ I) :
    (reesConst I (b ^ c) : reesAlgebra I) * (reesDegOne I hb : reesAlgebra I) =
      (reesDegOne I hb' : reesAlgebra I) := by
  refine Subtype.ext ?_
  change (C (b ^ c) : A[X]) * (monomial 1 b) = monomial 1 (b ^ (c + 1))
  rw [C_mul_monomial, pow_succ]

/-! ### The one-step law, at a target degree supplied as a parameter -/

/-- **Multiplication by `b⁽¹⁾` followed by twisting down one step is multiplication by `b`**,
with the target degree `t'` carried as a parameter satisfying `1 + t = t'` and with the
twisting-down map taken from the family `Stacks.Blowup.twistDownMap` rather than from the single
step `Stacks.Blowup.twistShiftMap`.

This is `Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` restated so that it
applies at the intermediate degree `((1 : ℕ) : ℤ) + t` that
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_mul` produces; the equation is
discharged by `subst` onto the canonical shape `t + 1`, where
`Stacks.Blowup.twistDownMap_succ` identifies the family with the single step. -/
theorem twistScalarSheafMap_reesDegOne_comp_twistDownMap (t t' : ℤ)
    (ht : ((1 : ℕ) : ℤ) + t = t') (hle : t ≤ t') {b : A} (hb : b ∈ I) :
    twistScalarSheafMap (reesGrading I) 1 t t' ht
          ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ ≫
        twistDownMap I t' t hle =
      twistScalarSheafMap (reesGrading I) 0 t t (twistedDegree_zero t)
        ⟨(reesConst I b : reesAlgebra I), SetLike.algebraMap_mem_graded (reesGrading I) b⟩ := by
  have ht' : t' = t + 1 := by omega
  subst ht'
  exact (whisker_eq _ (twistDownMap_succ I t hle)).trans
    (twistScalarSheafMap_reesDegOne_comp_twistShiftMap I t hb)

/-! ### The `c`-step law -/

set_option maxHeartbeats 600000 in
-- the inductive step elaborates long `Eq.trans` chains of `twistScalarSheafMap` morphisms
/-- **Multiplication by `(b⁽¹⁾)^c` followed by twisting down `c` steps is multiplication by
`b^c`**, as morphisms `𝒪_X(q') ⟶ 𝒪_X(q')`, for every `b ∈ I`, every `c : ℕ` and every pair of
integers `q' ≤ q` with `c + q' = q`.

This is the `c`-step form of [Stacks, Tag 02OS] part (3) that the cohomological clauses of
[Stacks, Tag 0GAA] consume: on the basic open `D₊(b⁽¹⁾)` the left-hand factor is invertible, so
there twisting down `c` steps agrees with multiplication by `b^c ∈ I^c` up to an isomorphism.

The induction is on `c`, with the bottom degree `q'` generalised; the step uses the
multiplicativity of the scalar action, the composition law `Stacks.Blowup.twistDownMap_comp`, and
the one-step law for the generator `b^{c+1}`. -/
theorem twistScalarSheafMap_reesDegOnePow_comp_twistDownMap (c : ℕ) :
    ∀ (q q' : ℤ) (hq : (c : ℤ) + q' = q) (hle : q' ≤ q) {b : A} (hb : b ∈ I),
      twistScalarSheafMap (reesGrading I) c q' q hq
            ⟨(reesDegOne I hb : reesAlgebra I) ^ c, reesDegOnePow_mem_reesGrading I hb c⟩ ≫
          twistDownMap I q q' hle =
        twistScalarSheafMap (reesGrading I) 0 q' q' (twistedDegree_zero q')
          ⟨(reesConst I (b ^ c) : reesAlgebra I),
            SetLike.algebraMap_mem_graded (reesGrading I) (b ^ c)⟩ := by
  induction c with
  | zero =>
    intro q q' hq hle b hb
    obtain rfl : q = q' := by omega
    have h1 : twistScalarSheafMap (reesGrading I) 0 q q hq
        ⟨(reesDegOne I hb : reesAlgebra I) ^ 0, reesDegOnePow_mem_reesGrading I hb 0⟩ = 𝟙 _ :=
      twistScalarSheafMap_one (reesGrading I) q _ (pow_zero _)
    have h2 : twistScalarSheafMap (reesGrading I) 0 q q (twistedDegree_zero q)
        ⟨(reesConst I (b ^ 0) : reesAlgebra I),
          SetLike.algebraMap_mem_graded (reesGrading I) (b ^ 0)⟩ = 𝟙 _ :=
      twistScalarSheafMap_one (reesGrading I) q _ (by simp)
    exact (eq_whisker h1 (twistDownMap I q q hle)).trans
      ((Category.id_comp _).trans ((twistDownMap_self I q).trans h2.symm))
  | succ c ih =>
    intro q q' hq hle b hb
    have hb' : b ^ (c + 1) ∈ I := I.pow_mem_of_mem hb (c + 1) (Nat.succ_pos c)
    have h1 : q' ≤ ((1 : ℕ) : ℤ) + q' := by omega
    have h2 : ((1 : ℕ) : ℤ) + q' ≤ q := by omega
    have hsplit :
        twistScalarSheafMap (reesGrading I) (c + 1) q' q hq
            ⟨(reesDegOne I hb : reesAlgebra I) ^ (c + 1),
              reesDegOnePow_mem_reesGrading I hb (c + 1)⟩ =
          twistScalarSheafMap (reesGrading I) 1 q' (((1 : ℕ) : ℤ) + q') rfl
              ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ ≫
            twistScalarSheafMap (reesGrading I) c (((1 : ℕ) : ℤ) + q') q (by omega)
              ⟨(reesDegOne I hb : reesAlgebra I) ^ c,
                reesDegOnePow_mem_reesGrading I hb c⟩ :=
      (congrArg
            (fun a : reesGrading I (c + 1) =>
              twistScalarSheafMap (reesGrading I) (c + 1) q' q hq a)
            (Subtype.ext (pow_succ (reesDegOne I hb : reesAlgebra I) c))).trans
        (twistScalarSheafMap_mul (reesGrading I) c 1 q' q hq (by omega) _ _)
    have hmerge :
        twistScalarSheafMap (reesGrading I) 1 q' (((1 : ℕ) : ℤ) + q') rfl
              ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ ≫
            twistScalarSheafMap (reesGrading I) 0 (((1 : ℕ) : ℤ) + q') (((1 : ℕ) : ℤ) + q')
              (twistedDegree_zero _)
              ⟨(reesConst I (b ^ c) : reesAlgebra I),
                SetLike.algebraMap_mem_graded (reesGrading I) (b ^ c)⟩ =
          twistScalarSheafMap (reesGrading I) 1 q' (((1 : ℕ) : ℤ) + q') rfl
            ⟨(reesDegOne I hb' : reesAlgebra I), reesDegOne_mem_reesGrading I hb'⟩ :=
      (twistScalarSheafMap_mul (reesGrading I) 0 1 q' (((1 : ℕ) : ℤ) + q') (by omega) (by omega)
            ⟨(reesConst I (b ^ c) : reesAlgebra I),
              SetLike.algebraMap_mem_graded (reesGrading I) (b ^ c)⟩
            ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩).symm.trans
        (congrArg
          (fun a : reesGrading I 1 =>
            twistScalarSheafMap (reesGrading I) 1 q' (((1 : ℕ) : ℤ) + q') rfl a)
          (Subtype.ext (reesConst_mul_reesDegOne I c hb hb')))
    refine Eq.trans (eq_whisker hsplit (twistDownMap I q q' hle)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (twistDownMap_comp I q (((1 : ℕ) : ℤ) + q') q' h1 h2 hle).symm)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker
      (ih q (((1 : ℕ) : ℤ) + q') (by omega) h2 hb)
      (twistDownMap I (((1 : ℕ) : ℤ) + q') q' h1))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker hmerge
      (twistDownMap I (((1 : ℕ) : ℤ) + q') q' h1)) ?_
    exact twistScalarSheafMap_reesDegOne_comp_twistDownMap I q' (((1 : ℕ) : ℤ) + q') rfl h1 hb'

/-! ### The `c`-step law in the other order -/

/-- **Twisting down one step followed by multiplication by `b⁽¹⁾` is multiplication by `b`**,
with the source degree `t'` carried as a parameter satisfying `1 + t = t'` and with the
twisting-down map taken from the family `Stacks.Blowup.twistDownMap`.

This is `Stacks.Blowup.twistShiftMap_comp_twistScalarSheafMap_reesDegOne` restated the way
`Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistDownMap` restates the other order. -/
theorem twistDownMap_comp_twistScalarSheafMap_reesDegOne (t t' : ℤ)
    (ht : ((1 : ℕ) : ℤ) + t = t') (hle : t ≤ t') {b : A} (hb : b ∈ I) :
    twistDownMap I t' t hle ≫
        twistScalarSheafMap (reesGrading I) 1 t t' ht
          ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ =
      twistScalarSheafMap (reesGrading I) 0 t' t' (twistedDegree_zero t')
        ⟨(reesConst I b : reesAlgebra I), SetLike.algebraMap_mem_graded (reesGrading I) b⟩ := by
  have ht' : t' = t + 1 := by omega
  subst ht'
  exact (eq_whisker (twistDownMap_succ I t hle) _).trans
    (twistShiftMap_comp_twistScalarSheafMap_reesDegOne I t hb)

set_option maxHeartbeats 600000 in
-- the inductive step elaborates long `Eq.trans` chains of `twistScalarSheafMap` morphisms
/-- **Twisting down `c` steps followed by multiplication by `a · (b⁽¹⁾)^c` is multiplication by
`a · b^c`**, as morphisms `𝒪_X(q) ⟶ 𝒪_X(q)`, for every `a : A`, every `b ∈ I`, every `c : ℕ` and
every pair of integers `q' ≤ q` with `c + q' = q`.

The extra degree-zero factor `a` is what makes the induction go through, and it costs nothing: the
inductive step turns the degree-one factor peeled off the bottom into multiplication by `b` (by
`Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOne`), and that factor has to be
absorbed *into the scalar* rather than commuted past the remaining twisting-down map. With `a`
present the absorbed scalar is again of the form the statement allows, at `a · b`. The special
case `a = 1` is `Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOnePow`.

Absorbing it needs the multiplicativity of the scalar action at an intermediate degree the
statement chooses, which is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_mul_of_eq`:
`twistScalarSheafMap_mul` fixes that degree at `((0 : ℕ) : ℤ) + q₁`, where the one-step law
delivers `q₁`, and the two are not definitionally equal. -/
theorem twistDownMap_comp_twistScalarSheafMap_reesConstMulDegOnePow (c : ℕ) :
    ∀ (q q' : ℤ) (hq : (c : ℤ) + q' = q) (hle : q' ≤ q) {b : A} (hb : b ∈ I) (a : A),
      twistDownMap I q q' hle ≫
          twistScalarSheafMap (reesGrading I) c q' q hq
            ⟨(reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I),
              reesConstMulDegOnePow_mem_reesGrading I hb c a⟩ =
        twistScalarSheafMap (reesGrading I) 0 q q (twistedDegree_zero q)
          ⟨(reesConst I (a * b ^ c) : reesAlgebra I),
            SetLike.algebraMap_mem_graded (reesGrading I) (a * b ^ c)⟩ := by
  induction c with
  | zero =>
    intro q q' hq hle b hb a
    obtain rfl : q = q' := by omega
    have helem : (reesDegOne I hb : reesAlgebra I) ^ 0 * (reesConst I a : reesAlgebra I) =
        (reesConst I (a * b ^ 0) : reesAlgebra I) := by
      rw [pow_zero, one_mul, pow_zero, mul_one]
    exact (eq_whisker (twistDownMap_self I q) _).trans
      ((Category.id_comp _).trans
        (congrArg
          (fun z : reesGrading I 0 => twistScalarSheafMap (reesGrading I) 0 q q hq z)
          (Subtype.ext helem)))
  | succ c ih =>
    intro q q' hq hle b hb a
    have h1 : q' ≤ ((1 : ℕ) : ℤ) + q' := by omega
    have h2 : ((1 : ℕ) : ℤ) + q' ≤ q := by omega
    have helem : (reesDegOne I hb : reesAlgebra I) ^ (c + 1) * (reesConst I a : reesAlgebra I) =
        ((reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I)) *
          (reesDegOne I hb : reesAlgebra I) := by
      rw [pow_succ]
      ring
    have hsplit :
        twistScalarSheafMap (reesGrading I) (c + 1) q' q hq
            ⟨(reesDegOne I hb : reesAlgebra I) ^ (c + 1) * (reesConst I a : reesAlgebra I),
              reesConstMulDegOnePow_mem_reesGrading I hb (c + 1) a⟩ =
          twistScalarSheafMap (reesGrading I) 1 q' (((1 : ℕ) : ℤ) + q') rfl
              ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ ≫
            twistScalarSheafMap (reesGrading I) c (((1 : ℕ) : ℤ) + q') q (by omega)
              ⟨(reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I),
                reesConstMulDegOnePow_mem_reesGrading I hb c a⟩ :=
      (congrArg
            (fun z : reesGrading I (c + 1) =>
              twistScalarSheafMap (reesGrading I) (c + 1) q' q hq z)
            (Subtype.ext helem)).trans
        (twistScalarSheafMap_mul (reesGrading I) c 1 q' q hq (by omega) _ _)
    have hassoc : ((reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I)) *
          (reesConst I b : reesAlgebra I) =
        (reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I (a * b) : reesAlgebra I) := by
      rw [mul_assoc, ← map_mul]
    have hfin : (a * b) * b ^ c = a * b ^ (c + 1) := by
      rw [pow_succ]
      ring
    have habsorb :
        twistScalarSheafMap (reesGrading I) 0 (((1 : ℕ) : ℤ) + q') (((1 : ℕ) : ℤ) + q')
              (twistedDegree_zero _)
              ⟨(reesConst I b : reesAlgebra I), SetLike.algebraMap_mem_graded (reesGrading I) b⟩ ≫
            twistScalarSheafMap (reesGrading I) c (((1 : ℕ) : ℤ) + q') q (by omega)
              ⟨(reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I),
                reesConstMulDegOnePow_mem_reesGrading I hb c a⟩ =
          twistScalarSheafMap (reesGrading I) c (((1 : ℕ) : ℤ) + q') q (by omega)
            ⟨(reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I (a * b) : reesAlgebra I),
              reesConstMulDegOnePow_mem_reesGrading I hb c (a * b)⟩ :=
      (twistScalarSheafMap_mul_of_eq (reesGrading I) c 0 (((1 : ℕ) : ℤ) + q')
            (((1 : ℕ) : ℤ) + q') q (twistedDegree_zero _) (by omega) (by omega)
            ⟨(reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I a : reesAlgebra I),
              reesConstMulDegOnePow_mem_reesGrading I hb c a⟩
            ⟨(reesConst I b : reesAlgebra I),
              SetLike.algebraMap_mem_graded (reesGrading I) b⟩).symm.trans
        (congrArg
          (fun z : reesGrading I c =>
            twistScalarSheafMap (reesGrading I) c (((1 : ℕ) : ℤ) + q') q (by omega) z)
          (Subtype.ext hassoc))
    refine Eq.trans (eq_whisker
      (twistDownMap_comp I q (((1 : ℕ) : ℤ) + q') q' h1 h2 hle).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _ hsplit)) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker
      (twistDownMap_comp_twistScalarSheafMap_reesDegOne I q' (((1 : ℕ) : ℤ) + q') rfl h1 hb) _)) ?_
    refine Eq.trans (whisker_eq _ habsorb) ?_
    refine Eq.trans (ih q (((1 : ℕ) : ℤ) + q') (by omega) h2 hb (a * b)) ?_
    exact congrArg
      (fun z : reesGrading I 0 =>
        twistScalarSheafMap (reesGrading I) 0 q q (twistedDegree_zero q) z)
      (Subtype.ext (congrArg (fun z : A => (reesConst I z : reesAlgebra I)) hfin))

/-- **Twisting down `c` steps followed by multiplication by `(b⁽¹⁾)^c` is multiplication by
`b^c`**, as morphisms `𝒪_X(q) ⟶ 𝒪_X(q)`.

Together with `Stacks.Blowup.twistScalarSheafMap_reesDegOnePow_comp_twistDownMap` this says that
multiplication by `(b⁽¹⁾)^c` and twisting down `c` steps are inverse to one another up to `b^c`,
which is the `c`-step form of what a local argument on `D₊(b⁽¹⁾)` consumes: this order is the one
that composes with a morphism *into* `𝒪_X(q)`, so it is what turns the annihilation of a subsheaf
of `𝒪_X(q) ⊗ p^*M` by `I^c` into the vanishing of its image under twisting down. -/
theorem twistDownMap_comp_twistScalarSheafMap_reesDegOnePow (c : ℕ) (q q' : ℤ)
    (hq : (c : ℤ) + q' = q) (hle : q' ≤ q) {b : A} (hb : b ∈ I) :
    twistDownMap I q q' hle ≫
        twistScalarSheafMap (reesGrading I) c q' q hq
          ⟨(reesDegOne I hb : reesAlgebra I) ^ c, reesDegOnePow_mem_reesGrading I hb c⟩ =
      twistScalarSheafMap (reesGrading I) 0 q q (twistedDegree_zero q)
        ⟨(reesConst I (b ^ c) : reesAlgebra I),
          SetLike.algebraMap_mem_graded (reesGrading I) (b ^ c)⟩ := by
  have hone : (reesConst I (1 : A) : reesAlgebra I) = 1 := map_one _
  have hA : (reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I (1 : A) : reesAlgebra I) =
      (reesDegOne I hb : reesAlgebra I) ^ c := by
    rw [hone, mul_one]
  have hB : (reesConst I (1 * b ^ c) : reesAlgebra I) = (reesConst I (b ^ c) : reesAlgebra I) :=
    congrArg (fun z : A => (reesConst I z : reesAlgebra I)) (one_mul (b ^ c))
  have hAsub : (⟨(reesDegOne I hb : reesAlgebra I) ^ c,
        reesDegOnePow_mem_reesGrading I hb c⟩ : reesGrading I c) =
      ⟨(reesDegOne I hb : reesAlgebra I) ^ c * (reesConst I (1 : A) : reesAlgebra I),
        reesConstMulDegOnePow_mem_reesGrading I hb c 1⟩ :=
    Subtype.ext hA.symm
  refine Eq.trans (whisker_eq _ (congrArg
    (fun z : reesGrading I c => twistScalarSheafMap (reesGrading I) c q' q hq z) hAsub)) ?_
  refine Eq.trans
    (twistDownMap_comp_twistScalarSheafMap_reesConstMulDegOnePow I c q q' hq hle hb 1) ?_
  exact congrArg
    (fun z : reesGrading I 0 =>
      twistScalarSheafMap (reesGrading I) 0 q q (twistedDegree_zero q) z)
    (Subtype.ext hB)

end Stacks.Blowup

end
