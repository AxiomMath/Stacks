module

public import StacksFrontier.Deformation.FlatAlgebraLiftHenselization
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative
public import StacksFrontier.Deformation.SquareZero.ConormalCokernelBaseChange
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleTorsion
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative.Converse

/-!
# Stacks 0DZB: the `Ext¹` surjectivity a dévissage would need

**Why the dévissage from nilpotent to square-zero needs smoothness and not syntomy.** Running
the square-zero case along a filtration of a nilpotent kernel needs surjectivity of
`Ext¹_B(NL_{B/A}, N) → Ext¹_{Bʰ}(NL_{Bʰ/A}, Bʰ ⊗_B N)`, which by Stacks 05EC holds once the
source is `𝔟`-power torsion. `Deformation.surjective_one_tmul_henselization_of_pow_le_annihilator`
proves that for any module killed by a power of `𝔟`, and
`Deformation.surjective_one_tmul_henselization_conormalCokernel_of_isSmoothAt` discharges it
under smoothness off `V(𝔟)`. Syntomy does not suffice, and that is not a gap in the argument:
`Deformation.surjective_precomp_cotangentComplex_iff_formallySmooth` proves the vanishing *equal*
to formal smoothness, and `Deformation.syntomic_quotient_X_sq` together with
`Deformation.not_formallySmooth_quotient_X_sq` exhibits `A[x]/(x²)` as syntomic and not formally
smooth. So the hypothesis that would replace `hsyn` is smoothness, which Stacks 0DZC and Stacks
0DZD carry and Stacks 0DZB does not.

## Main results

* `Deformation.surjective_one_tmul_henselization_conormalCokernel_of_isSmoothAt`: the `Ext¹`
  surjectivity the dévissage needs, under smoothness off `V(𝔟)`.
* `Deformation.surjective_precomp_cotangentComplex_iff_formallySmooth`: that surjectivity *is*
  formal smoothness.

## References

* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### What the matching of lifts would need -/

/-- **Extension of scalars to the henselization of a pair does nothing to a module killed by a
power of the ideal.** Let `(Bʰ, 𝔟Bʰ)` be the henselization of the pair `(B, 𝔟)` and let `E` be a
`B`-module with `𝔟ⁿ ⊆ Ann(E)` for some `n`. Then `x ↦ 1 ⊗ x` is a surjection `E → Bʰ ⊗_B E`.

**This is the `Ext¹` gap of the second implication, turned into a checkable condition.** The
implementation note *Why the second implication does not follow from the square-zero case* above
identifies what the induction up the filtration of `I = ker(A' → A)` is missing: surjectivity of

`Ext¹_B(NL_{B/A}, B ⊗_A Iʲ/Iʲ⁺¹) → Ext¹_{Bʰ}(NL_{Bʰ/A}, Bʰ ⊗_A Iʲ/Iʲ⁺¹)`,

which is a base change along `B → Bʰ` — flat by `flat_henselization_and_bijective_quotientMap`,
and **not** faithfully flat, so no descent argument makes it onto. By Stacks 0A6A the target is
`Bʰ ⊗_B Ext¹_B(NL_{B/A}, B ⊗_A Iʲ/Iʲ⁺¹)` and the map is `x ↦ 1 ⊗ x`. So *what would have to
hold* is exactly the hypothesis of this theorem at `E = Ext¹_B(NL_{B/A}, B ⊗_A Iʲ/Iʲ⁺¹)`: that
this `Ext` group is `𝔟`-power torsion. That is the Stacks 05EC reading recorded in the note, in
a form that can be checked rather than argued, and this theorem discharges the rest of the step
from it.

Nothing here asserts the hypothesis, and Stacks 0DZB's own hypotheses do not supply it. They
give that `A → B_h` is syntomic for `h ∈ 𝔟`, hence that `NL_{B/A}` is a two-term complex of
finite locally free modules off `V(𝔟)`, which kills `Ext²` and above there — enough for the
square-zero case — while `Ext¹` is that complex's cokernel and does not vanish. Smoothness off
`V(𝔟)`, which Stacks 0DZC and Stacks 0DZD carry and Stacks 0DZB does not, annihilates
`Ext¹` off `V(𝔟)` and so makes it `𝔟`-power torsion for `B` Noetherian — and by
`Deformation.surjective_precomp_cotangentComplex_iff_formallySmooth` below it is the *only*
hypothesis that does, the vanishing of `Ext¹_B(NL_{B/A}, -)` being equivalent to formal
smoothness. Noetherian support theory does not route around that: finiteness of this `Ext` and
the passage from support in `V(𝔟)` to an annihilator are both available already, and it is the
support containment itself that is the smoothness hypothesis. See the implementation note *The
Noetherian-support route to the annihilator hypothesis, and why it closes*. The `Ext` groups
themselves are not in this module's import closure; the quantified `E` is what makes the
condition statable here, and the step it leaves open is the identification of the comparison map
with `x ↦ 1 ⊗ x`, which is Stacks 0A6A.

The proof is the only thing the henselization contributes: the pair gives
`B/𝔟ⁿ ≅ Bʰ/𝔟ⁿBʰ` for every `n`, so every element of `Bʰ` differs from one of `B` by an element
of `𝔟ⁿBʰ`, and `𝔟ⁿ` annihilates `E`. No flatness and no Noetherian hypothesis are used. -/
theorem surjective_one_tmul_henselization_of_pow_le_annihilator
    (B : Type u) [CommRing B] (b : Ideal B) (Bh : Type u) [CommRing Bh] [Algebra B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g)
    (E : Type v) [AddCommGroup E] [Module B E] (n : ℕ)
    (hann : b ^ n ≤ Module.annihilator B E) :
    Function.Surjective fun x : E => (1 : Bh) ⊗ₜ[B] x := by
  obtain ⟨-, hpow⟩ := flat_henselization_and_bijective_quotientMap B b Bh hhens huniv
  -- an element of `𝔟ⁿBʰ` kills every element of `E` in the tensor product
  have key : ∀ (x : E), ∀ s ∈ (b ^ n).map (algebraMap B Bh),
      (s ⊗ₜ[B] x : Bh ⊗[B] E) = 0 := by
    intro x s hs
    induction hs using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨j, hj, rfl⟩ := ht
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Module.mem_annihilator.mp
        (hann hj) x, TensorProduct.tmul_zero]
    | zero => exact TensorProduct.zero_tmul _ _
    | add s t _ _ hs ht => rw [TensorProduct.add_tmul, hs, ht, add_zero]
    | smul c s _ hs => rw [← TensorProduct.smul_tmul', hs, smul_zero]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul y x =>
    obtain ⟨q, hq⟩ := (hpow n).surjective (Ideal.Quotient.mk _ y)
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨y₀ • x, ?_⟩
    have hmem : algebraMap B Bh y₀ - y ∈ (b ^ n).map (algebraMap B Bh) := by
      rw [Ideal.quotientMap_mk] at hq
      exact Ideal.Quotient.eq.mp hq
    show (1 : Bh) ⊗ₜ[B] (y₀ • x) = y ⊗ₜ[B] x
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, ← sub_eq_zero, ← TensorProduct.sub_tmul]
    exact key x _ hmem
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, TensorProduct.tmul_add _ _ _⟩

/-- **The annihilator hypothesis of
`Deformation.surjective_one_tmul_henselization_of_pow_le_annihilator`, discharged from the
support condition.** Let `(Bʰ, 𝔟Bʰ)` be the henselization of the pair `(B, 𝔟)` with `𝔟`
finitely generated, and let `E` be a *finite* `B`-module whose support lies in `V(𝔟)`. Then
`x ↦ 1 ⊗ x` is a surjection `E → Bʰ ⊗_B E`.

This is step (3) of the implementation note *The Noetherian-support route to the annihilator
hypothesis, and why it closes* composed with the previous theorem: Stacks 0953
(`isIPowerTorsion_of_support_subset`, which needs only `𝔟.FG`) turns support inside `V(𝔟)` into
elementwise `𝔟`-power torsion, and
`Stacks.AdicCompletion.FiniteModule.ideal_smul_eq_bot_of_finite_power_torsion` makes the
exponent uniform on a finite module.

**So the `Ext¹` step of the second implication is closed by smoothness off `V(𝔟)` and left open
by syntomy, with nothing in between.** At `E = Ext¹_B(NL_{B/A}, B ⊗_A Iʲ/Iʲ⁺¹)` the two
hypotheses here are exactly the two support-theoretic inputs of that note: finiteness, which
Stacks 08YR supplies for `B` Noetherian of finite type over `A`, and support inside `V(𝔟)`,
which `Deformation.surjective_precomp_cotangentComplex_iff_formallySmooth` below identifies —
in *both* directions, which is what makes the identification sharp — with formal smoothness of
`A → B_h` for every `h ∈ 𝔟`. The syntomy this lemma assumes does not give it:
`Deformation.not_surjective_precomp_cotangentComplex_quotient_X_sq` below is a syntomic algebra
whose `Ext¹` does not vanish. What is still unformalized on this route is therefore neither of
the two steps this theorem composes, but the two pieces named in the implementation note *Why
the second implication does not follow from the square-zero case*: the identification of the
`Ext` comparison map along `B → Bʰ` with `x ↦ 1 ⊗ x`, which is Stacks 0A6A, and the torsor
structure on the set of flat lifts. -/
theorem surjective_one_tmul_henselization_of_support_subset
    (B : Type u) [CommRing B] (b : Ideal B) (hbFG : b.FG) (Bh : Type u) [CommRing Bh]
    [Algebra B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g)
    (E : Type v) [AddCommGroup E] [Module B E] [Module.Finite B E]
    (hsupp : Module.support B E ⊆ PrimeSpectrum.zeroLocus (b : Set B)) :
    Function.Surjective fun x : E => (1 : Bh) ⊗ₜ[B] x := by
  obtain ⟨n, hn⟩ := Stacks.AdicCompletion.FiniteModule.ideal_smul_eq_bot_of_finite_power_torsion
    b hbFG E (isIPowerTorsion_of_support_subset hbFG hsupp)
  refine surjective_one_tmul_henselization_of_pow_le_annihilator B b Bh hhens huniv E n ?_
  intro a ha
  refine Module.mem_annihilator.mpr fun m => ?_
  have hmem : a • m ∈ (b ^ n) • (⊤ : Submodule B E) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rw [hn] at hmem
  simpa using hmem

/-- **The `Ext¹` step of the second implication, closed by smoothness off `V(𝔟)` at an arbitrary
Noetherian base.** Let `A → B` be essentially of finite type with `B` Noetherian, let `P` be a
presentation of `B` over `A` with `P.Ring` formally smooth, `P.Cotangent` finite and
`P.CotangentSpace` of finite presentation — which a finite presentation of `B` by generators and
relations supplies — and let `𝔟 ⊆ B` be an ideal outside whose zero set `A → B` is smooth. Then
for every coefficient module `N` the scalar extension `x ↦ 1 ⊗ x` of

`Ext¹_B(NL_{B/A}, N) = coker(Hom_B(P.CotangentSpace, N) → Hom_B(P.Cotangent, N))`

to the henselization of the pair `(B, 𝔟)` is **surjective**.

So the comparison that the implementation note *Why the second implication does not follow from
the square-zero case* identifies as the missing step of Stacks 0DZB's converse at a nilpotent
kernel is available, in the degree it lives in, as soon as `A → B` is smooth off `V(𝔟)` — and
with no field hypothesis, which is what distinguishes this from the step inside Stacks 0DZC.
The two inputs are `Deformation.Examples.exists_pow_le_conormalSplittingIdeal`, which is
Stacks 00S1 over an arbitrary base ring and is where smoothness is spent, and
`Deformation.surjective_one_tmul_henselization_of_pow_le_annihilator` above, which is where the
henselian pair is spent. Syntomy does not substitute for the first: by
`Deformation.surjective_precomp_cotangentComplex_iff_formallySmooth` below the vanishing of this
cokernel *is* formal smoothness, and
`Deformation.not_surjective_precomp_cotangentComplex_quotient_X_sq` is a syntomic algebra at
which it fails.

**This does not discharge `h0DZ2` below, and the two reasons are named.** What stands between
this surjectivity and the induction up the filtration of `ker(A' → A)` is the torsor structure
on the set of flat lifts — the identification of the fibres of
`Deformation.HasFlatAlgebraLift` over a square-zero step with this cokernel, which this tree
does not have at an arbitrary base — together with the identification of the `Ext` comparison
map along `B → Bʰ` with `x ↦ 1 ⊗ x`, which is Stacks 0A6A. Both are listed in that note; what
this theorem removes from the list is the `Ext¹` vanishing itself, and
`Deformation.surjective_homCokernelPush_henselization_of_isSmoothAt` below removes the
coefficient half of the 0A6A identification. The two inputs that remain are the ring half of
that identification — Stacks 0D08 computed on a conormal functional's class, which no lemma does
at any base — and the bridge from `Deformation.HasFlatAlgebraLift` to the solutions of a
`Stacks.Deformation.SquareZeroExtensionProblem`, the torsor itself being available. See the note
*What each of those two now is, precisely*. -/
theorem surjective_one_tmul_henselization_conormalCokernel_of_isSmoothAt
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Algebra.EssFiniteType A B]
    (P : Algebra.Extension.{w} A B) [Algebra.FormallySmooth A P.Ring]
    [Module.Finite B P.Cotangent] [Module.FinitePresentation B P.CotangentSpace]
    (b : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ b ≤ q.asIdeal → Algebra.IsSmoothAt A q.asIdeal)
    (Bh : Type u) [CommRing Bh] [Algebra B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g)
    (N : Type v) [AddCommGroup N] [Module B N] :
    Function.Surjective fun x : Examples.conormalCokernelAt P N => (1 : Bh) ⊗ₜ[B] x := by
  obtain ⟨n, hn⟩ := Examples.exists_pow_le_conormalSplittingIdeal P b hsm
  refine surjective_one_tmul_henselization_of_pow_le_annihilator B b Bh hhens huniv _ n ?_
  intro a ha
  refine Module.mem_annihilator.mpr fun x => ?_
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (LinearMap.lcomp B N P.cotangentComplex)) x
  rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Examples.smul_mem_range_lcomp_of_mem_conormalSplittingIdeal P (hn ha) N φ

/-- **The coefficient half of Stacks 0A6A for this comparison, at an arbitrary Noetherian base.**
Under the hypotheses of the previous theorem the *`Ext`-functorial* map

`Ext¹_B(NL_{B/A}, N) → Ext¹_B(NL_{B/A}, Bʰ ⊗_B N)`

— postcomposition of a conormal functional with `n ↦ 1 ⊗ n`, read on the cokernels, which is
`Deformation.Examples.homCokernelPush` — is **surjective**.

This is the previous theorem with the scalar extension `x ↦ 1 ⊗ x` traded for the map that the
deformation comparison actually induces, and the trade is exactly the flat base change of the
cokernel in its coefficients: `Deformation.Examples.homCokernelBaseChangeEquiv` identifies the
target with `Bʰ ⊗_B Ext¹_B(NL_{B/A}, N)`, and
`Deformation.Examples.homCokernelBaseChangeEquiv_compRight` says that under that identification
`homCokernelPush` *is* `x ↦ 1 ⊗ x`. Flatness of `B → Bʰ` comes from the henselian pair
(Stacks 0AGU) and finite presentation of the conormal module from `Module.Finite` over the
Noetherian `B`, so no hypothesis is added to the previous theorem.

**What this removes from the list, and what it does not.** Stacks 0A6A as the implementation note
*Why the second implication does not follow from the square-zero case* needs it is the
identification of
`Ext¹_B(NL_{B/A}, N) → Ext¹_{Bʰ}(NL_{Bʰ/A}, Bʰ ⊗_B N)` with `x ↦ 1 ⊗ x`, and that map factors as
a *coefficient* change over `B` followed by a *ring* change `B → Bʰ`. This theorem is the first
factor, at an arbitrary Noetherian base; the field-only form of it is
`Deformation.Examples.extOneCokernelBaseChangeEquiv`, and the field-only form of the whole
composite is `Stacks.Deformation.extOneCokernelHenselizationFlatBaseChangeEquiv`, which is what
Stacks 0DZC runs on. The second factor is Stacks 0D08, available at an arbitrary base as
`Stacks.Deformation.naiveCotangentExtOneHenselizationSourceEquiv` — but only as an isomorphism of
derived `Ext` groups, with no lemma computing it on a conormal functional's class, which is why
that composite is marked `irreducible` in
`StacksFrontier.RingTheory.Henselian.HenselizationExtBaseChange`. So the ring-change factor is still
open at every base, and with it Stacks 0A6A in the shape the induction needs. -/
theorem surjective_homCokernelPush_henselization_of_isSmoothAt
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Algebra.EssFiniteType A B]
    (P : Algebra.Extension.{w} A B) [Algebra.FormallySmooth A P.Ring]
    [Module.Finite B P.Cotangent] [Module.FinitePresentation B P.CotangentSpace]
    (b : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ b ≤ q.asIdeal → Algebra.IsSmoothAt A q.asIdeal)
    (Bh : Type u) [CommRing Bh] [Algebra B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g)
    (N : Type v) [AddCommGroup N] [Module B N] :
    Function.Surjective (Examples.homCokernelPush Bh P.cotangentComplex (N := N)) := by
  have hflat : Module.Flat B Bh :=
    (flat_henselization_and_bijective_quotientMap B b Bh hhens huniv).1
  have hfp : Module.FinitePresentation B P.Cotangent :=
    Module.finitePresentation_of_finite B P.Cotangent
  have hone := surjective_one_tmul_henselization_conormalCokernel_of_isSmoothAt A B P b hsm
    Bh hhens huniv N
  -- `homCokernelPush` exhibits its target as the base change of its source, and on `1 ⊗ x` it is
  -- the scalar extension the previous theorem makes onto
  have hbc := Examples.isBaseChange_homCokernelPush Bh P.cotangentComplex (N := N)
  intro y
  obtain ⟨z, hz⟩ := hbc.equiv.surjective y
  obtain ⟨x, hx⟩ := hone z
  refine ⟨x, ?_⟩
  rw [← hz, ← hx, hbc.equiv_tmul, one_smul]

/-! ### The `Ext¹` hypothesis is formal smoothness, exactly -/

/-- **Formal smoothness makes `Ext¹_S(NL_{S/R}, N)` vanish, for every coefficient module `N` at
once.**

Let `P` be a presentation of `S` over `R` — an `Algebra.Extension R S`, i.e. a surjection
`P.Ring ↠ S` with kernel `I` — whose `P.Ring` is formally smooth over `R`, as a polynomial
algebra is. Then `NL_{S/R}` is the two-term complex
`P.cotangentComplex : I/I² → S ⊗_{P.Ring} Ω[P.Ring⁄R]`, i.e. `P.Cotangent → P.CotangentSpace`,
in degrees `-1` and `0`. Whenever `P.CotangentSpace` is projective — it is free for a presentation
coming from `Algebra.Generators`, by `Algebra.Generators.cotangentSpaceBasis` — the long exact
sequence of the triangle `P.CotangentSpace → NL_{S/R} → P.Cotangent[1]` collapses to

`Ext¹_S(NL_{S/R}, N) = coker(Hom_S(P.CotangentSpace, N) → Hom_S(P.Cotangent, N))`,

the map being precomposition with `P.cotangentComplex`; in this tree that cokernel presentation of
the first `Ext` module is `NaiveCotangent.extOne_naiveCotangentComplex_linearEquiv_cokernel` of
`StacksFrontier.RingTheory.NaiveCotangent.ExtCokernelLinear`, which is not in this module's import
closure. So the conclusion below says that `Ext` module vanishes. The proof is that a retraction
of `P.cotangentComplex`, which formal smoothness supplies by Stacks 031I, can be pushed forward
along any `ψ : P.Cotangent →ₗ[S] N`. -/
theorem surjective_precomp_cotangentComplex_of_formallySmooth
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (P : Algebra.Extension R S)
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R S]
    (N : Type v) [AddCommGroup N] [Module S N] :
    Function.Surjective fun φ : P.CotangentSpace →ₗ[S] N => φ ∘ₗ P.cotangentComplex := by
  obtain ⟨l, hl⟩ := (Algebra.Extension.formallySmooth_iff_split_injection P).mp ‹_›
  intro ψ
  refine ⟨ψ ∘ₗ l, ?_⟩
  show (ψ ∘ₗ l) ∘ₗ P.cotangentComplex = ψ
  rw [LinearMap.comp_assoc, hl, LinearMap.comp_id]

/-- **Conversely, the vanishing of `Ext¹_S(NL_{S/R}, I/I²)` at the single coefficient module
`I/I²` already forces `R → S` to be formally smooth.**

Surjectivity of precomposition with `P.cotangentComplex` at `N = P.Cotangent` applied to the
identity map produces `l` with `l ∘ P.cotangentComplex = id`, which is the split injectivity of
Stacks 031I. So the vanishing of the first `Ext` module of the naive cotangent complex is not a
consequence of smoothness that something weaker might also give: it is smoothness. -/
theorem formallySmooth_of_surjective_precomp_cotangentComplex
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (P : Algebra.Extension R S)
    [Algebra.FormallySmooth R P.Ring]
    (hsurj : Function.Surjective fun φ : P.CotangentSpace →ₗ[S] P.Cotangent =>
      φ ∘ₗ P.cotangentComplex) :
    Algebra.FormallySmooth R S :=
  (Algebra.Extension.formallySmooth_iff_split_injection P).mpr (hsurj LinearMap.id)

/-- **The vanishing of `Ext¹_S(NL_{S/R}, -)` is formal smoothness of `R → S`.** The two previous
results, read as one biconditional: it is enough that the first `Ext` module vanish at the
conormal module `I/I²` of one presentation with formally smooth `P.Ring`, and then it vanishes at
every coefficient module.

**This closes the Noetherian-support route to the annihilator hypothesis of
`Deformation.surjective_one_tmul_henselization_of_pow_le_annihilator`.** That route asks for
`Supp(Ext¹_B(NL_{B/A}, N)) ⊆ V(𝔟)`, i.e. for the `Ext` module to die after inverting any `h ∈ 𝔟`;
instantiated at `S = B_h`, the biconditional turns that into `Algebra.FormallySmooth A B_h` for
every `h ∈ 𝔟` — smoothness of `A → B` off `V(𝔟)`, which is the hypothesis of Stacks 0DZC and
Stacks 0DZD and is strictly stronger than the syntomy of `A → B_h` that Stacks 0DZB assumes. See
the implementation note *The Noetherian-support route to the annihilator hypothesis, and why it
closes*. -/
theorem surjective_precomp_cotangentComplex_iff_formallySmooth
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (P : Algebra.Extension R S)
    [Algebra.FormallySmooth R P.Ring] :
    (Function.Surjective fun φ : P.CotangentSpace →ₗ[S] P.Cotangent =>
        φ ∘ₗ P.cotangentComplex) ↔ Algebra.FormallySmooth R S :=
  ⟨formallySmooth_of_surjective_precomp_cotangentComplex R S P,
    fun _ => surjective_precomp_cotangentComplex_of_formallySmooth R S P P.Cotangent⟩

/-- **A syntomic algebra at which the `Ext¹` hypothesis fails: `A[x]/(x²)`.** No presentation of
`A[x]/(x²)` over `A` by a formally smooth algebra has `Ext¹_{A[x]/(x²)}(NL, I/I²) = 0`, because by
`Deformation.formallySmooth_of_surjective_precomp_cotangentComplex` that vanishing would make
`A[x]/(x²)` formally smooth over `A`, and `Deformation.not_formallySmooth_quotient_X_sq` above
says it is not.

`A → A[x]/(x²)` is nonetheless syntomic: it is flat, being free on `1, x`; of finite presentation,
by that same presentation; and its fibre over a prime `𝔭 ⊆ A` is `κ(𝔭)[x]/(x²)`, a global complete
intersection in the sense of Stacks 00SB — one variable, one relation, and fibre dimension
`0 = 1 − 1`, the ring being Artinian. **That syntomy is machine-checked, not cited**:
`Deformation.syntomic_quotient_X_sq` above, which discharges the `IsLocalCompleteIntersection`
Krull-dimension side-condition rather than asserting it, by way of Stacks 00SW for the square
presentation. So the two halves of the separating witness are both proved, and the only
implication between syntomy and smoothness in this tree is `Algebra.Smooth.syntomic`, in the
other direction. -/
theorem not_surjective_precomp_cotangentComplex_quotient_X_sq
    (A : Type u) [CommRing A] [Nontrivial A]
    (P : Algebra.Extension A
      (Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ 2}))
    [Algebra.FormallySmooth A P.Ring] :
    ¬ Function.Surjective fun φ : P.CotangentSpace →ₗ[Polynomial A ⧸
        Ideal.span {(Polynomial.X : Polynomial A) ^ 2}] P.Cotangent =>
      φ ∘ₗ P.cotangentComplex :=
  fun h => not_formallySmooth_quotient_X_sq A
    (formallySmooth_of_surjective_precomp_cotangentComplex A _ P h)

end Deformation

end
