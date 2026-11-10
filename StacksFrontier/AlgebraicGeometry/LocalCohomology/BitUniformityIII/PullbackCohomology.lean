module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import StacksFrontier.Algebra.Module.IProjective
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BoundQAndD
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the pullback of an `(A, n, c)`-module to a blowup

This file formalizes the vanishing clauses (1) and (2) of Stacks Project Tag 0GAA, the third
lemma of the section *A bit of uniformity, III* of the chapter *Local Cohomology* (Tag 0GA6).

## The Situation of Tag 0GA6

Fix a Noetherian ring `A` and an ideal `I ⊆ A`, let `p : X → Spec(A)` be the blowing up of
`Spec(A)` in `I`, let `Y` be the exceptional divisor and `Yₙ = nY`. Write `d = d(S)` for the
maximum of the dimensions of the fibres of `p` and `q₀ = q(S)` for the threshold attached to
`S = Gr_I(A)`; both are recorded in
`Stacks.LocalCohomology.UniformityIII.Situation`, where Tag 0GA7 is proved. For an `A`-module
`M` one writes `p^*M` for the pullback of the quasi-coherent module associated to `M`, so that
`𝒪_{Yₙ} = p^*(A/Iⁿ)`.

Given `n ≥ c ≥ 0`, an *`(A, n, c)`-module* is a finite `A`-module annihilated by `Iⁿ` which as
an `A/Iⁿ`-module is `I^c/Iⁿ`-projective. Here such a module is presented as a finite
`A ⧸ Iⁿ`-module that is `I^c/Iⁿ`-projective in the sense of Tag 0G93; being annihilated by `Iⁿ`
is then automatic.

## The statement of Tag 0GAA

With `q₀ = q(S)` and `d = d(S)`, given `n ≥ c ≥ 0`, an `(A, n, c)`-module `M`, an index
`i ∈ {0, 1, …, d}` and an integer `q`, Tag 0GAA distinguishes five cases:

1. `i = d ≥ 1` and `q ≥ q₀`: `H^d(X, p^*M(q)) = 0`;
2. `i = d - 1 ≥ 1` and `q ≥ q₀`: `H^{d-1}(X, p^*M(q)) = 0`;
3. `d - 1 > i > 0` and `q ≥ q₀ + (d - 1 - i)c`: the map
   `Hⁱ(X, p^*M(q)) → Hⁱ(X, p^*M(q - (d - 1 - i)c))` is zero;
4. `i = 0`, `d ∈ {0, 1}` and `q ≥ q₀`: there is a surjection `I^qM → H⁰(X, p^*M(q))`;
5. `i = 0`, `d > 1` and `q ≥ q₀ + (d - 1)c`: the map
   `H⁰(X, p^*M(q)) → H⁰(X, p^*M(q - (d - 1)c))` has image contained in the image of the
   canonical map `I^{q-(d-1)c}M → H⁰(X, p^*M(q - (d - 1)c))`.

The two vanishing clauses (1) and (2) are what this file establishes, as
`ModuleSituation.subsingleton_H_top` and `ModuleSituation.subsingleton_H_next`. Each carries
the tag with a suffix naming the clause it covers.

The remaining three clauses are established as well, as
`TwistedModuleSituation.Htr_eq_zero`, `TwistedModuleSituation.surjective_secM` and
`TwistedModuleSituation.range_Htr_le`. They are statements about the maps between *different*
twists, and about the canonical maps `I^qM → H⁰(X, p^*M(q))`, neither of which `ModuleSituation`
carries; so they are proved for the structure `TwistedModuleSituation`, which extends
`ModuleSituation` by exactly those maps and their naturality. Clause (3) is the induction that
drives the other two: clause (5) for `d > 1` and clause (4) for `d ≤ 1` are read off from the
auxiliary vanishing `TwistedModuleSituation.HGtr_eq_zero` that clause (3) is proved from.

In clauses (3) and (5) the two twists `q` and `q - (d - 1 - i)c` are carried as separate
parameters `q` and `r` tied by `r + (d - 1 - i)c = q`, so that no subtraction appears in a type;
`d - 1 - i` is likewise carried as a parameter `k` with `i + k + 1 = d`, which is `d - 1 > i`
together with `k = d - 1 - i`.

## What is formalized here, and what is assumed

The blowup, the twisting sheaves and the long exact cohomology sequences they produce are not
available in a form that lets the clauses be stated about the actual sheaves. Following
`Situation`, the cohomology groups and the maps between them are therefore carried as the
*data* of a structure `ModuleSituation`, together with exactly those properties of them that
the Stacks Project establishes *before* Tag 0GAA is stated. Clauses (1) and (2) are theorems
about such a `ModuleSituation`; they are not among its hypotheses.

Concretely, `ModuleSituation` extends `Situation` — so Tag 0GA7 is available, not reassumed —
and adds, for every `(A, n, c)`-module `M`: a chosen finite free presentation
`0 → K → (A/Iⁿ)^{⊕r} → M → 0`, the cohomology of the twists of `p^*M`, of the two sheaves `ℱ`
and `𝒢` into which the Stacks proof splits the pulled-back presentation, and of
`(𝒪_{Yₙ})^{⊕r}`; the exactness of the long exact sequences of
`0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0` and `0 → ℱ → p^*K → 𝒢 → 0` at the two spots the proof
uses; the additivity of cohomology over the finite direct sum `(𝒪_{Yₙ})^{⊕r}`; and the
vanishing of `Hⁱ` above the fibre dimension `d`.

That `K` is again an `(A, n, c)`-module — the one step of the Stacks proof that is pure algebra
— is *proved* here as `isANCModule_kernel`, from Tag 0G95
(`Module.isIProjective_of_injective_of_exact`). That such a presentation exists at all is
proved as `nonempty_ANCPresentation`. `topModuleSituation` exhibits a `ModuleSituation` for
`I = ⊤`, so the hypotheses are consistent.

`TwistedModuleSituation` adds to `ModuleSituation` the twisting-down maps on the cohomology of
the twists of `p^*M` and of `𝒢` with their naturality, the factorization of Tag 0GA9, and the
canonical maps `I^qM → H⁰(X, p^*M(q))` with their compatibility with the chosen presentation.
The submodule `I^qM` and the canonical surjection `(I^q/I^{q+n})^{⊕r} → I^qM` out of the free
module's sections are *built* here, as `powSmul` and `ANCPresentation.freeSections`, not
assumed. `topTwistedModuleSituation` extends `topModuleSituation` to the larger structure, so
its hypotheses are consistent too.

Both witnesses for `I = ⊤` are degenerate: `A ⧸ ⊤ⁿ` is the zero ring, so every
`(A, n, c)`-module and every cohomology module in sight vanishes there, and all five clauses of
Tag 0GAA become statements about zero modules. `affineModuleSituation` and
`affineTwistedModuleSituation` are witnesses that are not degenerate: they extend
`affineSituation`, the Situation in which the blowing up is an isomorphism, the cohomology
modules they supply are nonzero for a nonzero `(A, n, c)`-module, and the canonical map of
clause (4) is bijective rather than a map between zero modules. The `(A, n, c)`-modules they
apply to need not be free over `A ⧸ Iⁿ`: `quotPowANCModule` is a cyclic one which is not.

Their fibre dimension is `d(S) = 0`, so of the five clauses exactly clause (4) has a
satisfiable case hypothesis there: clauses (1), (2), (3) and (5) require `d ≥ 1`, `d ≥ 2`,
`d ≥ 3` and `d ≥ 2` respectively.

In those witnesses `H⁰(X, p^*M(q))` is `I^q ⊗_A M` and the canonical map of clause (4) is the
identity, which is correct for an isomorphism `p`.

## The source of the canonical map in clauses (4) and (5)

The Stacks Project writes the source of the canonical map of clauses (4) and (5) as `I^qM`.
Read as the submodule `I^q·M` of `M`, the clause is false. Take `A = ℤ` and `I = (2)`, so that
the blowing up is an isomorphism, `d(S) = 0` and `q(S) = 0`; take `n = 1`, `c = 0` and
`M = A ⧸ I`, an `(A, 1, 0)`-module. At `q = 1` the submodule `I·M` is zero, while Tag 0GA7(2)
gives `H⁰(X, p^*M(1)) = H⁰(X, 𝒪_{Y₁}(1)) = I/I² ≅ ℤ/2`, and there is no surjection
`0 → ℤ/2`.

What the proof of clause (4) produces is a surjection out of
`H⁰(X, (𝒪_{Yₙ})^{⊕r}(q)) = (I^q/I^{q+n})^{⊕r}`, which factors through
`(I^q/I^{q+n}) ⊗_{A} M = I^q ⊗_A M` — for `M = A ⧸ Iⁿ` this is `I^q/I^{q+n}` itself, as
Tag 0GA7(2) demands. So clauses (4) and (5) are formalized with the source `powTensor`, and
their tag attributes record the correction. The submodule `I^qM` survives as `powSmul`: it is
the image of `I^q ⊗_A M` in `M` under `mulPowTensor`, and the two are genuinely different
modules.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.IsANCModule`: the property of being an
  `(A, n, c)`-module.
* `Stacks.LocalCohomology.UniformityIII.ANCModule`: the `(A, n, c)`-modules.
* `Stacks.LocalCohomology.UniformityIII.ANCPresentation`: a finite free presentation
  `0 → K → (A/Iⁿ)^{⊕r} → M → 0`.
* `Stacks.LocalCohomology.UniformityIII.ANCModule.dual`: the dual `M^∨` of an
  `(A, n, c)`-module, as an `(A, n, c)`-module.
* `Stacks.LocalCohomology.UniformityIII.ModuleSituation`: the data and standing hypotheses
  used by Tag 0GAA.
* `Stacks.LocalCohomology.UniformityIII.powSmul`: the submodule `I^qM` of an
  `(A, n, c)`-module `M`.
* `Stacks.LocalCohomology.UniformityIII.ANCPresentation.freeSections`: the canonical surjection
  `(I^q/I^{q+n})^{⊕r} → I^qM` induced by a chosen finite free presentation.
* `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`: `ModuleSituation` together
  with the maps between different twists and the canonical maps `I^qM → H⁰(X, p^*M(q))`.
* `Stacks.LocalCohomology.UniformityIII.powTensor`: the module `I^q ⊗_A M`, the source of the
  canonical map of clauses (4) and (5).
* `Stacks.LocalCohomology.UniformityIII.mulPowTensor`: the canonical map `I^q ⊗_A M → M`, whose
  image is the submodule `I^qM`.
* `Stacks.LocalCohomology.UniformityIII.ANCPresentation.freeTensor`: the canonical surjection
  `(I^q/I^{q+n})^{⊕r} → I^q ⊗_A M` induced by a chosen finite free presentation.
* `Stacks.LocalCohomology.UniformityIII.affineModuleSituation`: the `ModuleSituation` built on
  `affineSituation`, in which the blowing up is an isomorphism.
* `Stacks.LocalCohomology.UniformityIII.affineTwistedModuleSituation`: its extension to a
  `TwistedModuleSituation`.
* `Stacks.LocalCohomology.UniformityIII.quotPowANCModule`: the cyclic `(A, n, c)`-module
  `(A ⧸ Iⁿ) ⧸ I^c(A ⧸ Iⁿ)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.isANCModule_kernel`: the kernel of a finite free
  presentation of an `(A, n, c)`-module is an `(A, n, c)`-module.
* `Stacks.LocalCohomology.UniformityIII.isANCModule_dual`: the dual
  `M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ)` of an `(A, n, c)`-module is an `(A, n, c)`-module.
* `Stacks.LocalCohomology.UniformityIII.ANCPresentation.freeSections_surjective`: the canonical
  map `(I^q/I^{q+n})^{⊕r} → I^qM` is surjective.
* `Stacks.LocalCohomology.UniformityIII.ModuleSituation.subsingleton_H_top`: clause (1).
* `Stacks.LocalCohomology.UniformityIII.ModuleSituation.subsingleton_H_next`: clause (2).
* `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation.Htr_eq_zero`: clause (3).
* `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation.surjective_secM`: clause (4).
* `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation.range_Htr_le`: clause (5).
* `Stacks.LocalCohomology.UniformityIII.ANCPresentation.freeTensor_surjective`: that canonical
  surjection is indeed surjective, which is the last step of the proof of clause (4).
* `Stacks.LocalCohomology.UniformityIII.nontrivial_affineTwistedModuleSituation_H` and
  `Stacks.LocalCohomology.UniformityIII.bijective_affineTwistedModuleSituation_secM`: the
  affine witness is not degenerate.
* `Stacks.LocalCohomology.UniformityIII.not_free_quotPowANCModule`: a cyclic
  `(A, n, c)`-module that is not free over `A ⧸ Iⁿ`.

## Implementation notes

A cohomology group is "zero" here in the form `Subsingleton`, as in `Situation`.

Twists of the pullbacks are indexed by `ℤ`, as in the source. The twists of `𝒪_{Yₙ}` supplied
by `Situation` are indexed by `ℕ`; the two are matched only at nonnegative twists, which is all
clauses (1) and (2) use, since there `q ≥ q₀ ≥ 0`.

Clause (2) is stated as `i + 1 = d` together with `1 ≤ i` rather than with a subtraction, which
in `ℕ` would be truncated.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public section

universe u

namespace Stacks.LocalCohomology.UniformityIII

section ANCModules

variable {A : Type u} [CommRing A]

/-- An *`(A, n, c)`-module*, in the sense of the section of Tag 0GA6: a finite `A`-module
annihilated by `Iⁿ` which as an `A/Iⁿ`-module is `I^c/Iⁿ`-projective.

It is presented here as an `A ⧸ Iⁿ`-module, which is the same thing as an `A`-module
annihilated by `Iⁿ`; the ideal `I^c/Iⁿ` of `A ⧸ Iⁿ` is the image of `I^c`, and
`I^c/Iⁿ`-projectivity is Tag 0G93. -/
def IsANCModule (I : Ideal A) (n c : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) : Prop :=
  Module.Finite (A ⧸ I ^ n) M ∧
    Module.IsIProjective (A ⧸ I ^ n) (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M

/-- The `(A, n, c)`-modules. -/
abbrev ANCModule (I : Ideal A) (n c : ℕ) : Type (u + 1) :=
  {M : ModuleCat.{u} (A ⧸ I ^ n) // IsANCModule I n c M}

/-- **Stacks Project, Section 0GA6.** The kernel of a finite free presentation
`0 → K → (A/Iⁿ)^{⊕r} → M → 0` of an `(A, n, c)`-module is again an `(A, n, c)`-module.

This is the step the proof of Tag 0GAA records as "we will use below that `K` is an
`(A, n, c)`-module": `I^c/Iⁿ`-projectivity of `K` is Tag 0G95, and `K` is finite because it is
a submodule of a finite free module over the Noetherian ring `A ⧸ Iⁿ`. -/
theorem isANCModule_kernel [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
    {M K : ModuleCat.{u} (A ⧸ I ^ n)} {r : ℕ}
    (incl : K →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n))
    (proj : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M)
    (hincl : Function.Injective incl) (hproj : Function.Surjective proj)
    (hex : LinearMap.range incl = LinearMap.ker proj)
    (hM : IsANCModule I n c M) : IsANCModule I n c K :=
  ⟨Module.Finite.of_injective incl hincl,
    Module.isIProjective_of_injective_of_exact _ incl proj hincl hproj hex hM.2⟩

/-- **Stacks Project, Section 0GA6.** The dual `M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ)` of an
`(A, n, c)`-module is again an `(A, n, c)`-module.

This is the step the proof of Tag 0GAC records as "the fact that `M^∨` is an
`(A, n, c)`-module by More on Algebra, Lemma 15.72.7": `I^c/Iⁿ`-projectivity of `M^∨` is
Tag 0G96, and `M^∨` is finite because dualizing a finite free presentation of `M` embeds it
into a finite free module over the Noetherian ring `A ⧸ Iⁿ`. -/
theorem isANCModule_dual [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
    {M : ModuleCat.{u} (A ⧸ I ^ n)} (hM : IsANCModule I n c M) :
    IsANCModule I n c (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) := by
  have hfin : Module.Finite (A ⧸ I ^ n) M := hM.1
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' (A ⧸ I ^ n) M.carrier
  exact ⟨Module.Finite.of_injective f.dualMap
      (LinearMap.dualMap_injective_of_surjective hf),
    Module.IsIProjective.dual (A ⧸ I ^ n) _ M hM.2⟩

/-- The dual of an `(A, n, c)`-module, as an `(A, n, c)`-module; see `isANCModule_dual`. -/
def ANCModule.dual [IsNoetherianRing A] {I : Ideal A} {n c : ℕ} (M : ANCModule I n c) :
    ANCModule I n c :=
  ⟨ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M.1), isANCModule_dual M.2⟩

/-- A chosen finite free presentation `0 → K → (A/Iⁿ)^{⊕r} → M → 0` of an `(A, n, c)`-module,
the "choose a short exact sequence" with which the proof of Tag 0GAA opens. -/
structure ANCPresentation (I : Ideal A) (n c : ℕ) (M : ANCModule I n c) where
  /-- The rank `r` of the chosen finite free module. -/
  rank : ℕ
  /-- The kernel `K` of the chosen presentation. -/
  kernel : ModuleCat.{u} (A ⧸ I ^ n)
  /-- The inclusion `K → (A/Iⁿ)^{⊕r}`. -/
  incl : kernel →ₗ[A ⧸ I ^ n] (Fin rank → A ⧸ I ^ n)
  /-- The surjection `(A/Iⁿ)^{⊕r} → M`. -/
  proj : (Fin rank → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M.1
  /-- The sequence starts with `0 → K`. -/
  incl_injective : Function.Injective incl
  /-- The sequence ends with `M → 0`. -/
  proj_surjective : Function.Surjective proj
  /-- The sequence is exact in the middle. -/
  range_incl_eq_ker_proj : LinearMap.range incl = LinearMap.ker proj

namespace ANCPresentation

variable [IsNoetherianRing A] {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}

/-- The kernel of a chosen presentation of an `(A, n, c)`-module, as an `(A, n, c)`-module;
see `isANCModule_kernel`. -/
def kernelANC (P : ANCPresentation I n c M) : ANCModule I n c :=
  ⟨P.kernel, isANCModule_kernel P.incl P.proj P.incl_injective P.proj_surjective
    P.range_incl_eq_ker_proj M.2⟩

/-- The underlying module of `kernelANC` is the kernel of the presentation. -/
@[simp] theorem kernelANC_coe (P : ANCPresentation I n c M) :
    (P.kernelANC : ModuleCat.{u} (A ⧸ I ^ n)) = P.kernel := rfl

end ANCPresentation

/-- **Stacks Project, Section 0GA6.** Every `(A, n, c)`-module admits a finite free
presentation, because it is a finite module over `A ⧸ Iⁿ`. So the "choose a short exact
sequence `0 → K → (A/Iⁿ)^{⊕r} → M → 0`" of the proof of Tag 0GAA is a genuine choice and not a
further hypothesis. -/
theorem nonempty_ANCPresentation [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
    (M : ANCModule I n c) : Nonempty (ANCPresentation I n c M) := by
  have : Module.Finite (A ⧸ I ^ n) M.1 := M.2.1
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' (A ⧸ I ^ n) M.1
  exact ⟨{ rank := r
           kernel := ModuleCat.of (A ⧸ I ^ n) (LinearMap.ker f)
           incl := Submodule.subtype _
           proj := f
           incl_injective := Subtype.coe_injective
           proj_surjective := hf
           range_incl_eq_ker_proj := Submodule.range_subtype _ }⟩

end ANCModules

section PowSmul

open scoped TensorProduct

variable {A : Type u} [CommRing A]

/-- An `A ⧸ Iⁿ`-module regarded as an `A`-module along `A → A ⧸ Iⁿ`. For an `(A, n, c)`-module
this is the underlying `A`-module, which is annihilated by `Iⁿ`. -/
noncomputable abbrev resModule (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M

/-- `Iⁿ` annihilates an `A ⧸ Iⁿ`-module, viewed over `A`. -/
theorem smul_resModule_eq_zero (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) {a : A}
    (ha : a ∈ I ^ n) (m : resModule I n M) : a • m = 0 := by
  rw [ModuleCat.restrictScalars.smul_def, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_smul]
  rfl

/-- The submodule `I^qM` of an `A ⧸ Iⁿ`-module `M`, viewed over `A`. -/
noncomputable def powSmul (I : Ideal A) (n q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    Submodule A (resModule I n M) :=
  (I ^ q) • (⊤ : Submodule A (resModule I n M))

/-- `I^{q+c}M = I^c(I^qM)`: the filtration of an `A ⧸ Iⁿ`-module by the submodules `I^qM` is
multiplicative, because `I^{q+c} = I^c·I^q` as ideals. In particular every element of
`I^{q+c}M` is a finite sum `∑ aᵢyᵢ` with `aᵢ ∈ I^c` and `yᵢ ∈ I^qM`. -/
theorem powSmul_add (I : Ideal A) (n q c : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    powSmul I n (q + c) M = (I ^ c) • powSmul I n q M := by
  rw [powSmul, powSmul, pow_add, mul_comm (I ^ q) (I ^ c), Submodule.mul_smul]

/-- Multiplication by a fixed element `m` of an `A ⧸ Iⁿ`-module `M`, as a map
`I^q/I^{q+n} → I^qM`. It is well defined because `I^{q+n} ⊆ Iⁿ` annihilates `M`. -/
noncomputable def powQuotSmulRight (I : Ideal A) (n q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))
    (m : resModule I n M) : powQuot I q n →ₗ[A] powSmul I n q M :=
  Submodule.liftQ _
    (LinearMap.codRestrict (powSmul I n q M)
      ((LinearMap.toSpanSingleton A (resModule I n M) m).comp (I ^ q : Ideal A).subtype)
      fun a => Submodule.smul_mem_smul a.2 Submodule.mem_top)
    fun a ha => by
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at ha
      rw [LinearMap.mem_ker]
      exact Subtype.ext
        (smul_resModule_eq_zero I n M (Ideal.pow_le_pow_right (Nat.le_add_left n q) ha) m)

/-- The canonical map `(I^q/I^{q+n})^{⊕r} → I^qM` induced by a chosen finite free presentation
`(A/Iⁿ)^{⊕r} → M` of an `(A, n, c)`-module: send the tuple of classes of `wⱼ ∈ I^q` to the
image of the tuple of their reductions. It is `ANCPresentation.freeTensor` followed by
`mulPowTensor`; the map clauses (4) and (5) of Tag 0GAA use is `freeTensor`, not this one. -/
noncomputable def ANCPresentation.freeSections {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q : ℕ) :
    (Fin P.rank → powQuot I q n) →ₗ[A] powSmul I n q M.1 :=
  ∑ j : Fin P.rank, (powQuotSmulRight I n q M.1 (P.proj (Pi.single j 1))).comp
    (LinearMap.proj (R := A) (φ := fun _ : Fin P.rank => powQuot I q n) j)

/-- `powQuotSmulRight` sends the class of `a ∈ I^q` to `am`. -/
theorem coe_powQuotSmulRight_mk (I : Ideal A) (n q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))
    (m : resModule I n M) (a : (I ^ q : Ideal A)) :
    ((powQuotSmulRight I n q M m (Submodule.Quotient.mk a) : powSmul I n q M) :
      resModule I n M) = Ideal.Quotient.mk (I ^ n) (a : A) • (m : M) := rfl

/-- `ANCPresentation.freeSections` sends a tuple of classes of elements `wⱼ ∈ I^q` to the image
under `(A/Iⁿ)^{⊕r} → M` of the tuple of their reductions. -/
theorem coe_freeSections {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q : ℕ) (w : Fin P.rank → (I ^ q : Ideal A)) :
    ((P.freeSections q fun j => Submodule.Quotient.mk (w j) : powSmul I n q M.1) :
      resModule I n M.1) = P.proj fun j => Ideal.Quotient.mk (I ^ n) (w j : A) := by
  rw [ANCPresentation.freeSections, LinearMap.sum_apply, Submodule.coe_sum,
    show (fun j => Ideal.Quotient.mk (I ^ n) (w j : A)) =
        ∑ j, Ideal.Quotient.mk (I ^ n) (w j : A) •
          Pi.single (M := fun _ : Fin P.rank => A ⧸ I ^ n) j 1 from pi_eq_sum_univ' _,
    map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

/-- The canonical map `(I^q/I^{q+n})^{⊕r} → I^qM` is surjective: every element of `I^qM` is a
sum of elements `am` with `a ∈ I^q`, and `m` is the image of some element of `(A/Iⁿ)^{⊕r}`.
Consequently `I^qM` is the image of `I^q ⊗_A M` in `M`. -/
theorem ANCPresentation.freeSections_surjective {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q : ℕ) : Function.Surjective (P.freeSections q) := by
  have key : ∀ x ∈ powSmul I n q M.1, ∃ v,
      ((P.freeSections q v : powSmul I n q M.1) : resModule I n M.1) = x := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha m _
      obtain ⟨y, hy⟩ := P.proj_surjective m
      choose t ht using fun j => Ideal.Quotient.mk_surjective (y j)
      have hy' : (fun j => Ideal.Quotient.mk (I ^ n) (a * t j)) =
          Ideal.Quotient.mk (I ^ n) a • y := by
        funext j
        rw [map_mul, ht j]
        rfl
      refine ⟨fun j => Submodule.Quotient.mk ⟨a * t j, Ideal.mul_mem_right _ _ ha⟩, ?_⟩
      rw [coe_freeSections]
      change P.proj (fun j => Ideal.Quotient.mk (I ^ n) (a * t j)) = a • m
      rw [hy', map_smul, hy, ModuleCat.restrictScalars.smul_def]
    · rintro x₁ x₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
      exact ⟨v₁ + v₂, by rw [map_add, Submodule.coe_add, h₁, h₂]⟩
  intro z
  obtain ⟨v, hv⟩ := key (z : resModule I n M.1) z.2
  exact ⟨v, Subtype.ext hv⟩

/-- `I^q ⊗_A M` for an `A ⧸ Iⁿ`-module `M`, written as `(I^q/I^{q+n}) ⊗_A M`. The two agree:
`I^{q+n} = Iⁿ·I^q`, so every generator `a ⊗ m` of the image of `I^{q+n} ⊗_A M → I^q ⊗_A M` can
be rewritten with the `Iⁿ`-part moved onto `m`, where it is killed.

This is the module out of which the canonical map of Tag 0GAA, clause (4) goes. For
`M = A ⧸ Iⁿ` it is `I^q/I^{q+n}`, which is exactly what Tag 0GA7(2) computes
`H⁰(X, 𝒪_{Yₙ}(q))` to be. The submodule `I^qM = powSmul I n q M` of `M` is a *different*
module — it is only the image of `I^q ⊗_A M` in `M` under `mulPowTensor`, and already for
`A = ℤ`, `I = (2)`, `n = 1` and `M = A ⧸ I` the two differ at `q = 1`, where `I^qM = 0` while
`I^q ⊗_A M ≅ I/I² ≅ ℤ/2`. -/
noncomputable abbrev powTensor (I : Ideal A) (n q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) : Type u :=
  powQuot I q n ⊗[A] resModule I n M

/-- The canonical map `I^q ⊗_A M → M`, `a ⊗ m ↦ am`. Its image is the submodule `I^qM`; it is
not injective, which is why `I^q ⊗_A M` rather than `I^qM` is the source of the canonical map
of Tag 0GAA, clause (4). -/
noncomputable def mulPowTensor (I : Ideal A) (n q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    powTensor I n q M →ₗ[A] resModule I n M :=
  TensorProduct.lift
    (Submodule.liftQ _ ((LinearMap.lsmul A (resModule I n M)).comp (I ^ q : Ideal A).subtype)
      fun a ha => by
        simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at ha
        rw [LinearMap.mem_ker]
        exact LinearMap.ext fun m =>
          smul_resModule_eq_zero I n M (Ideal.pow_le_pow_right (Nat.le_add_left n q) ha) m)

/-- `mulPowTensor` sends `a ⊗ m` to `a • m`. -/
@[simp] theorem mulPowTensor_tmul (I : Ideal A) (n q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))
    (a : (I ^ q : Ideal A)) (m : resModule I n M) :
    mulPowTensor I n q M (Submodule.Quotient.mk a ⊗ₜ[A] m) = (a : A) • m := rfl

/-- `I⁰ ⊗_A M → M` is surjective, since `1 ∈ I⁰`. -/
theorem surjective_mulPowTensor_zero (I : Ideal A) (n : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    Function.Surjective (mulPowTensor I n 0 M) := fun m =>
  ⟨Submodule.Quotient.mk ⟨1, by simp⟩ ⊗ₜ[A] m,
    one_smul A m⟩

/-- The canonical map `(I^q/I^{q+n})^{⊕r} = I^q ⊗_A (A/Iⁿ)^{⊕r} → I^q ⊗_A M` induced by a chosen
finite free presentation `(A/Iⁿ)^{⊕r} → M` of an `(A, n, c)`-module. This is the map Tag 0GAA's
clause (4) asserts to be surjective, after Tag 0GA7(2) identifies the source with the sections
of `(𝒪_{Yₙ})^{⊕r}(q)`. -/
noncomputable def ANCPresentation.freeTensor {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q : ℕ) :
    (Fin P.rank → powQuot I q n) →ₗ[A] powTensor I n q M.1 :=
  ∑ j : Fin P.rank,
    ((TensorProduct.mk A (powQuot I q n) (resModule I n M.1)).flip
      (P.proj (Pi.single j 1))).comp
        (LinearMap.proj (R := A) (φ := fun _ : Fin P.rank => powQuot I q n) j)

/-- `freeTensor` sends `v` to `∑ⱼ vⱼ ⊗ π(eⱼ)`, where `π` is the surjection of the presentation and
`eⱼ` the standard basis. -/
theorem ANCPresentation.freeTensor_apply {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q : ℕ) (v : Fin P.rank → powQuot I q n) :
    P.freeTensor q v =
      ∑ j, (v j ⊗ₜ[A] P.proj (Pi.single j 1) : powTensor I n q M.1) := by
  rw [ANCPresentation.freeTensor, LinearMap.sum_apply]
  rfl

/-- **Stacks Project, Tag 0GAA.** The canonical map `(I^q/I^{q+n})^{⊕r} → I^q ⊗_A M` is
surjective: `I^q ⊗_A M` is generated by the elements `a ⊗ m`, and `m` is the image of some
element of `(A/Iⁿ)^{⊕r}`, whose coordinates can be moved onto `a`. This is the identification
of the free module's sections that the Stacks proof of clause (4) ends with. -/
theorem ANCPresentation.freeTensor_surjective {I : Ideal A} {n c : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q : ℕ) : Function.Surjective (P.freeTensor q) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x m =>
    obtain ⟨y, hy⟩ := P.proj_surjective m
    choose t ht using fun j => Ideal.Quotient.mk_surjective (y j)
    refine ⟨fun j => t j • x, ?_⟩
    rw [P.freeTensor_apply]
    have step : ∀ j : Fin P.rank,
        ((t j • x) ⊗ₜ[A] P.proj (Pi.single j 1) : powTensor I n q M.1) =
          (x ⊗ₜ[A] P.proj (y j • Pi.single j 1) : powTensor I n q M.1) := by
      intro j
      rw [map_smul, ← ht j]
      exact TensorProduct.smul_tmul (t j) x _
    have hsum : (x ⊗ₜ[A] P.proj y : powTensor I n q M.1) =
        ∑ j, (x ⊗ₜ[A] P.proj (y j • Pi.single j 1) : powTensor I n q M.1) := by
      conv_lhs => rw [pi_eq_sum_univ' y]
      rw [map_sum]
      exact TensorProduct.tmul_sum _ _ _
    rw [Finset.sum_congr rfl fun j _ => step j, ← hsum, hy]
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨v₁, rfl⟩ := h₁
    obtain ⟨v₂, rfl⟩ := h₂
    exact ⟨v₁ + v₂, map_add _ _ _⟩

end PowSmul

/-- The data and the standing hypotheses used by Stacks Tag 0GAA: the Situation of Tag 0GA6
together with, for every `(A, n, c)`-module `M`, a chosen finite free presentation
`0 → K → (A/Iⁿ)^{⊕r} → M → 0` and the cohomology of the twists of the sheaves the proof builds
from it.

Pulling back `0 → K → (A/Iⁿ)^{⊕r} → M → 0` gives an exact sequence
`p^*K → (𝒪_{Yₙ})^{⊕r} → p^*M → 0`, which the proof splits into two short exact sequences
`0 → ℱ → p^*K → 𝒢 → 0` and `0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0`. The four families `H`, `Hfree`,
`HG`, `HF` are the cohomology of the twists of `p^*M`, `(𝒪_{Yₙ})^{⊕r}`, `𝒢` and `ℱ`.

The scheme `X` and its sheaves do not appear: what appears are the cohomology modules they
produce and the properties of these that the Stacks Project establishes before Tag 0GAA is
stated. -/
structure ModuleSituation (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) extends Situation A I where
  /-- The constraint `n ≥ c` on the two exponents. -/
  exponent_le : c ≤ n
  /-- The chosen finite free presentation of each `(A, n, c)`-module; one exists by
  `nonempty_ANCPresentation`. -/
  pres : ∀ M : ANCModule I n c, ANCPresentation I n c M
  /-- `H M i q` is `Hⁱ(X, p^*M(q))`. -/
  H : ANCModule I n c → ℕ → ℤ → ModuleCat.{u} A
  /-- `Hfree M i q` is `Hⁱ(X, (𝒪_{Yₙ})^{⊕r}(q))` for the rank `r` of the chosen
  presentation. -/
  Hfree : ANCModule I n c → ℕ → ℤ → ModuleCat.{u} A
  /-- `HG M i q` is `Hⁱ(X, 𝒢(q))`, for the image `𝒢` of `p^*K → (𝒪_{Yₙ})^{⊕r}`. -/
  HG : ANCModule I n c → ℕ → ℤ → ModuleCat.{u} A
  /-- `HF M i q` is `Hⁱ(X, ℱ(q))`, for the kernel `ℱ` of `p^*K → (𝒪_{Yₙ})^{⊕r}`. -/
  HF : ANCModule I n c → ℕ → ℤ → ModuleCat.{u} A
  /-- Cohomology commutes with the finite direct sum `(𝒪_{Yₙ})^{⊕r}`. Only nonnegative twists
  are matched, which is all clauses (1) and (2) use. -/
  freeIso : ∀ (M : ANCModule I n c) (i q : ℕ),
    Hfree M i (q : ℤ) ≃ₗ[A] (Fin (pres M).rank → toSituation.Hdiv n i q)
  /-- `𝒪_{Y₀} = 0`: the source defines `Yₙ` only for `n ≥ 1`, and `n = 0` makes `I⁰ = A`, the
  ring `A ⧸ I⁰` zero and every `(A, 0, c)`-module zero. -/
  subsingleton_Hdiv_zero : ∀ i q : ℕ, Subsingleton (toSituation.Hdiv 0 i q)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, applied to `p^*M(q)`. -/
  vanishing_H : ∀ M i q, toSituation.d < i → Subsingleton (H M i q)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, applied to `𝒢(q)`. -/
  vanishing_HG : ∀ M i q, toSituation.d < i → Subsingleton (HG M i q)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, applied to `ℱ(q)`. -/
  vanishing_HF : ∀ M i q, toSituation.d < i → Subsingleton (HF M i q)
  /-- `Hⁱ(X, (𝒪_{Yₙ})^{⊕r}(q)) → Hⁱ(X, p^*M(q))`, from
  `0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0`. -/
  freeToPullback : ∀ (M : ANCModule I n c) (i : ℕ) (q : ℤ), Hfree M i q →ₗ[A] H M i q
  /-- The connecting map `Hⁱ(X, p^*M(q)) → Hⁱ⁺¹(X, 𝒢(q))`, from the same sequence. -/
  pullbackToImage : ∀ (M : ANCModule I n c) (i : ℕ) (q : ℤ), H M i q →ₗ[A] HG M (i + 1) q
  /-- Exactness of that long exact sequence at `Hⁱ(X, p^*M(q))`. -/
  exact_pullback : ∀ M i q, Function.Exact (freeToPullback M i q) (pullbackToImage M i q)
  /-- `Hⁱ(X, p^*K(q)) → Hⁱ(X, 𝒢(q))`, from `0 → ℱ → p^*K → 𝒢 → 0`. -/
  kernelToImage : ∀ (M : ANCModule I n c) (i : ℕ) (q : ℤ),
    H (pres M).kernelANC i q →ₗ[A] HG M i q
  /-- The connecting map `Hⁱ(X, 𝒢(q)) → Hⁱ⁺¹(X, ℱ(q))`, from the same sequence. -/
  imageToSupported : ∀ (M : ANCModule I n c) (i : ℕ) (q : ℤ), HG M i q →ₗ[A] HF M (i + 1) q
  /-- Exactness of that long exact sequence at `Hⁱ(X, 𝒢(q))`. -/
  exact_image : ∀ M i q, Function.Exact (kernelToImage M i q) (imageToSupported M i q)

/-- The middle term of an exact sequence `M₁ → M₂ → M₃` vanishes if the outer terms do. -/
private theorem subsingleton_of_exact_of_subsingleton {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂]
    [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} (hfg : Function.Exact f g)
    [Subsingleton M₁] [Subsingleton M₃] : Subsingleton M₂ := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, rfl⟩ := (hfg y).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim x 0, map_zero]

namespace ModuleSituation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
  (S : ModuleSituation A I n c)

/-- `Hⁱ(X, (𝒪_{Yₙ})^{⊕r}(q)) = 0` for `i ≥ 1` and `q ≥ q₀`: by `freeIso` this is a finite
direct sum of copies of `Hⁱ(X, 𝒪_{Yₙ}(q))`, which vanishes by Tag 0GA7(1) when `n ≥ 1` and
by `subsingleton_Hdiv_zero` when `n = 0`. -/
theorem subsingleton_Hfree (M : ANCModule I n c) {i : ℕ} {q : ℤ}
    (hi : 1 ≤ i) (hq : (S.q₀ : ℤ) ≤ q) : Subsingleton (S.Hfree M i q) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) :=
    ⟨q.toNat, (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg _) hq)).symm⟩
  have hk : S.q₀ ≤ k := by exact_mod_cast hq
  have hdiv : Subsingleton (S.Hdiv n i k) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact S.subsingleton_Hdiv_zero i k
    · exact S.toSituation.subsingleton_Hdiv hn hi hk
  exact (S.freeIso M i k).toEquiv.subsingleton

/-- **Stacks Project, Tag 0GAA, clause (1).** For an `(A, n, c)`-module `M`, in the case
`i = d ≥ 1` and `q ≥ q₀` we have `H^d(X, p^*M(q)) = 0`.

The long exact sequence of `0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0` sits `H^d(X, p^*M(q))` between
`H^d(X, (𝒪_{Yₙ})^{⊕r}(q))`, which vanishes by Tag 0GA7(1), and `H^{d+1}(X, 𝒢(q))`, which
vanishes because `d` bounds the fibre dimensions. -/
@[stacks 0GAA "clause (1), H^d(X, p^*M(q)) = 0 for i = d ≥ 1 and q ≥ q₀"]
theorem subsingleton_H_top (M : ANCModule I n c) {q : ℤ}
    (hd : 1 ≤ S.d) (hq : (S.q₀ : ℤ) ≤ q) : Subsingleton (S.H M S.d q) := by
  have := S.subsingleton_Hfree M hd hq
  have := S.vanishing_HG M (S.d + 1) q (Nat.lt_succ_self _)
  exact subsingleton_of_exact_of_subsingleton (S.exact_pullback M S.d q)

/-- `H^d(X, 𝒢(q)) = 0` for `d ≥ 1` and `q ≥ q₀`, the intermediate step of clause (2): the long
exact sequence of `0 → ℱ → p^*K → 𝒢 → 0` sits `H^d(X, 𝒢(q))` between `H^d(X, p^*K(q))`, which
vanishes by clause (1) applied to the `(A, n, c)`-module `K`, and `H^{d+1}(X, ℱ(q))`, which
vanishes because `d` bounds the fibre dimensions. -/
theorem subsingleton_HG_top (M : ANCModule I n c) {q : ℤ}
    (hd : 1 ≤ S.d) (hq : (S.q₀ : ℤ) ≤ q) : Subsingleton (S.HG M S.d q) := by
  have := S.subsingleton_H_top (S.pres M).kernelANC hd hq
  have := S.vanishing_HF M (S.d + 1) q (Nat.lt_succ_self _)
  exact subsingleton_of_exact_of_subsingleton (S.exact_image M S.d q)

/-- **Stacks Project, Tag 0GAA, clause (2).** For an `(A, n, c)`-module `M`, in the case
`i = d - 1 ≥ 1` and `q ≥ q₀` we have `H^{d-1}(X, p^*M(q)) = 0`.

The long exact sequence of `0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0` sits `H^{d-1}(X, p^*M(q))`
between `H^{d-1}(X, (𝒪_{Yₙ})^{⊕r}(q))`, which vanishes by Tag 0GA7(1) since `d - 1 ≥ 1`, and
`H^d(X, 𝒢(q))`, which vanishes by `subsingleton_HG_top`.

The hypothesis `i = d - 1` is written `i + 1 = d` to avoid a truncated subtraction. -/
@[stacks 0GAA "clause (2), H^{d-1}(X, p^*M(q)) = 0 for i = d - 1 ≥ 1 and q ≥ q₀"]
theorem subsingleton_H_next (M : ANCModule I n c) {i : ℕ} {q : ℤ}
    (hi : 1 ≤ i) (hid : i + 1 = S.d) (hq : (S.q₀ : ℤ) ≤ q) : Subsingleton (S.H M i q) := by
  have := S.subsingleton_Hfree M hi hq
  have : Subsingleton (S.HG M (i + 1) q) := by
    rw [hid]
    exact S.subsingleton_HG_top M (by lia) hq
  exact subsingleton_of_exact_of_subsingleton (S.exact_pullback M i q)

/-- The canonical map `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))` is surjective for `q ≥ q₀`: for `n ≥ 1`
it is bijective by Tag 0GA7(2), and for `n = 0` the target vanishes. -/
theorem surjective_cdiv {q : ℕ} (hq : S.q₀ ≤ q) : Function.Surjective (S.cdiv n q) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : Subsingleton (S.Hdiv 0 0 q) := S.subsingleton_Hdiv_zero 0 q
    exact fun _ => ⟨0, Subsingleton.elim _ _⟩
  · exact (S.toSituation.bijective_cdiv hn hq).2

/-- The connecting map `Hⁱ(X, p^*M(q)) → Hⁱ⁺¹(X, 𝒢(q))` is injective for `i ≥ 1` and `q ≥ q₀`,
because the preceding term `Hⁱ(X, (𝒪_{Yₙ})^{⊕r}(q))` of the long exact sequence vanishes. -/
theorem injective_pullbackToImage (M : ANCModule I n c) {i : ℕ} {q : ℤ}
    (hi : 1 ≤ i) (hq : (S.q₀ : ℤ) ≤ q) : Function.Injective (S.pullbackToImage M i q) := by
  have hfree : Subsingleton (S.Hfree M i q) := S.subsingleton_Hfree M hi hq
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := (S.exact_pullback M i q y).1 hy
  rw [@Subsingleton.elim _ hfree x 0, map_zero]

end ModuleSituation

/-- The data and the standing hypotheses used by the remaining three clauses of Stacks
Tag 0GAA: a `ModuleSituation` together with the maps `Hⁱ(X, ℱ(q)) → Hⁱ(X, ℱ(q'))` induced by
`𝒪_X(q) → 𝒪_X(q')` for `q' ≤ q` on the cohomology of the twists of `p^*M` and of `𝒢`, the
naturality of the comparison maps of `ModuleSituation` against them, the factorization that
Tag 0GA9 supplies, and the canonical maps `I^qM → H⁰(X, p^*M(q))`.

None of these data is carried by `ModuleSituation`, and clauses (3), (4) and (5) — unlike
clauses (1) and (2) — are statements about them, so they are collected here. Clauses (1) and
(2) remain available, since this structure extends `ModuleSituation`; they are not reassumed.

The field `kernelToImage_dotted` is the dotted arrow of the diagram in the Stacks proof of
clause (3): the coherent module `ℱ` is scheme theoretically supported on `Y_c` by Tag 0GA8, so
by Tag 0GA9 the canonical map `𝒢(q) → 𝒢(q - c)` factors through `p^*K(q - c)`. Like every other
geometric input to this section it is carried as data; no clause of Tag 0GAA is.

**The first input of that dotted arrow is proved on `Proj (reesGrading I)` itself**, with no
comparison with the ideal-sheaf blowup anywhere:
`Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero` of
`BitUniformityIII/SupportedAnnihilation.lean` says that `I^c` annihilates
`ℱ(q) = ker(p^*K(q) → 𝒢(q))`, for every twist `q : ℤ`. That is Tag 0GA8 in this model.

For this input no transport across
`Stacks.Blowup.nonempty_over_iso_blowUpToBase` is needed, even though
`AlgebraicGeometry.exceptionalIdeal_pow_le_annihilator_kernel` — Tag 0GA8 of
`StacksFrontier/AlgebraicGeometry/Blowup/AlmostExactness.lean` — is stated on
`AlgebraicGeometry.blowUp` of the ideal sheaf `Ideal.map (Scheme.ΓSpecIso _).inv.hom I`:
its proof uses the blowup for exactly one thing, namely to be a
scheme over `Spec A` whose module sheaves carry the `A`-linear structure
`AlgebraicGeometry.modulesLinear`, and at that generality the statement instantiates at
`Stacks.Blowup.twistedGeometricFactor I q` directly. The twist is free on that route: nothing
has to know that an annihilator ideal sheaf does not see the invertible `𝒪_X(q)`, because the
twist sits inside the `A`-linear functor the statement is quantified over. Only the algebraic
step is shared, `AlgebraicGeometry.exists_scalar_retraction_of_projective_factorization`, whose two
hypotheses on the quotient — `Module.Finite` and `Module.IsIProjective` at the image of `I^c` —
are `IsANCModule I n c` on the nose.

What is still owed is the second input, Tag 0GA9, which is
`AlgebraicGeometry.schemeTheoreticSupport_iff_exceptionalTwistContraction_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalTwist.lean` and *is* stated on
`AlgebraicGeometry.blowUp` of the ideal sheaf. In the form `dotted` needs it, it says that the
composite `ℱ(q) → p^*K(q) → p^*K(q - c)` vanishes, i.e. that
`kernel.ι (S.map (twistedPullbackFunctor I q)).toCycles ≫ (twistDownFactorMap I q (q - c) _).app
S.X₁ = 0`; the dotted arrow is then the factorization of the twisting-down map through the
cokernel of `ℱ(q) → p^*K(q)`, which is `𝒢(q)`. Here too the comparison with the ideal-sheaf
blowup looks avoidable rather than necessary, by the chart route: on the standard open
`D₊(b⁽¹⁾)` attached to `b ∈ I` the twisting-down map by `c` becomes invertible after
multiplication by `b⁽¹⁾ ^ c`, and that composite is multiplication by `b ^ c ∈ I^c`, which
`smul_twistedPullbackSupported_eq_zero` kills. What that asks for is the `c`-step analogue of
`Stacks.LocalCohomology.UniformityIII.reesDegOneScalarMap_comp_twistShiftMap`, stated against
`Stacks.Blowup.twistDownMap`, and the standard opens of the degree-one elements as a cover.

**On `Htr` and `HGtr`.** These are the maps `𝒪_X(q) → 𝒪_X(q')` of `q' ≤ q` induce. The one-step
map `Stacks.Blowup.twistShiftMap I t : 𝒪_X(t+1) ⟶ 𝒪_X(t)` exists for every `t : ℤ`, but
iterating it does *not* produce the family: the successor sits in its source, so a chain of `k`
one-step maps has source `𝒪_X(q' + k)` with `q'` free and `k` a natural number, and a consumer
holding `q' ≤ q` can only reach that through a propositional equality of integers, i.e. a
transport. Carrying the transport as `CategoryTheory.eqToHom` does not work
here: the category of the twisting sheaves is
`SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj (… structureSheaf …))`,
whose unifier has to reconcile `TopCat.Sheaf CommRingCat _` with
`CategoryTheory.Sheaf (Opens.grothendieckTopology _) CommRingCat`, and already
`CategoryTheory.Category.id_comp` against an `eqToHom` exhausts the heartbeat budget. The route
that avoids a transport altogether is to build the family in one shot rather than by iteration:
generalize `Stacks.Blowup.reesTruncation I t` — the truncation of `S(t+1)` above degree `-t` —
to the truncation of `S(q)` above degree `-q'`, and `Stacks.Blowup.reesShift I t`, which is
`Polynomial.divX`, to its `(q - q').toNat`-fold iterate. The integer arithmetic then lives only
in the *proof* that the iterate is degree-preserving, which is a `Prop`, so nothing is
transported.

**That route has been taken.** The sheaf-level family is `Stacks.Blowup.twistDownMap I q q'` of
`BitUniformityIII/AmbientTwistDown.lean`, for every pair of integers `q' ≤ q`, with no
`eqToHom` and no transport anywhere. `Stacks.Blowup.twistDownMap_succ` identifies it with
`Stacks.Blowup.twistShiftMap I t` at `q = t + 1`, `q' = t`, so everything already proved about
the one-step map applies to it, and `Stacks.Blowup.twistDownMap_self` and
`Stacks.Blowup.twistDownMap_comp` are the identity and composition laws — the latter being the
sheaf-level content of `HGtr_trans`.

**Five of the nine fields are now discharged on the blowup**, namely exactly the five that are
about those maps. The remaining cohomological step was the morphism
`(twistedGeometricFactor I q).obj N ⟶ (twistedGeometricFactor I q').obj N` obtained by tensoring
`twistDownMap` into the fixed factor of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula`; it is
`Stacks.Blowup.twistDownFactorMap` of `BitUniformityIII/AmbientTwistDownFactor.lean`, built from
the general `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap`, and it needs
no comparison isomorphism because `Stacks.Blowup.blowUpTwist` is an abbreviation for
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (reesGrading I) q`, the very type
`twistDownMap` is stated at. `BitUniformityIII/BlowupTwistDownCohomology.lean` then pushes it
through `Hⁱ(X, -)`:

* `Htr` is `Stacks.LocalCohomology.UniformityIII.blowupHtr`;
* `HGtr` is `Stacks.LocalCohomology.UniformityIII.blowupHGtr`;
* `HGtr_trans` is `Stacks.LocalCohomology.UniformityIII.blowupHGtr_comp`;
* `pullbackToImage_tr` is `Stacks.LocalCohomology.UniformityIII.blowupHtr_comp_δ_free`;
* `kernelToImage_tr` is `Stacks.LocalCohomology.UniformityIII.toCycles_comp_blowupHGtr`.

What is still owed for a witness is the other four fields: `dotted` and `kernelToImage_dotted`,
whose first input Tag 0GA8 is proved on `Proj (reesGrading I)` as
`Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero` and whose second
input Tag 0GA9 is proved only on `AlgebraicGeometry.blowUp` of the ideal sheaf, so the one
remaining gap there is the vanishing of `ℱ(q) → p^*K(q) → p^*K(q - c)` — see the discussion
above; and `secM` and `secM_freeSections`. Note the direction of the dependence: `dotted` is
*downstream* of the
twisting-down family, not independent of it — the arrow `𝒢(q) → p^*K(q - c)` exists because
`ℱ(q) → ℱ(q - c)` is zero, and that map has to exist at the level of sheaves before Tag 0GA8 and
Tag 0GA9 say anything about it. -/
structure TwistedModuleSituation (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) extends ModuleSituation A I n c where
  /-- `Hⁱ(X, p^*M(q)) → Hⁱ(X, p^*M(q'))` for `q' ≤ q`, induced by `𝒪_X(q) → 𝒪_X(q')`. -/
  Htr : ∀ (M : ANCModule I n c) (i : ℕ) (q q' : ℤ), q' ≤ q →
    toModuleSituation.H M i q →ₗ[A] toModuleSituation.H M i q'
  /-- `Hⁱ(X, 𝒢(q)) → Hⁱ(X, 𝒢(q'))` for `q' ≤ q`, induced by the same map. -/
  HGtr : ∀ (M : ANCModule I n c) (i : ℕ) (q q' : ℤ), q' ≤ q →
    toModuleSituation.HG M i q →ₗ[A] toModuleSituation.HG M i q'
  /-- Functoriality of the twisting-down maps on the cohomology of the twists of `𝒢`. -/
  HGtr_trans : ∀ (M : ANCModule I n c) (i : ℕ) (q q' q'' : ℤ) (h : q' ≤ q) (h' : q'' ≤ q')
    (h'' : q'' ≤ q) (x : toModuleSituation.HG M i q),
    HGtr M i q' q'' h' (HGtr M i q q' h x) = HGtr M i q q'' h'' x
  /-- Naturality of the connecting map `Hⁱ(X, p^*M(q)) → Hⁱ⁺¹(X, 𝒢(q))` in the twist. -/
  pullbackToImage_tr : ∀ (M : ANCModule I n c) (i : ℕ) (q q' : ℤ) (h : q' ≤ q)
    (x : toModuleSituation.H M i q),
    HGtr M (i + 1) q q' h (toModuleSituation.pullbackToImage M i q x) =
      toModuleSituation.pullbackToImage M i q' (Htr M i q q' h x)
  /-- Naturality of `Hⁱ(X, p^*K(q)) → Hⁱ(X, 𝒢(q))` in the twist. -/
  kernelToImage_tr : ∀ (M : ANCModule I n c) (i : ℕ) (q q' : ℤ) (h : q' ≤ q)
    (x : toModuleSituation.H (toModuleSituation.pres M).kernelANC i q),
    HGtr M i q q' h (toModuleSituation.kernelToImage M i q x) =
      toModuleSituation.kernelToImage M i q'
        (Htr (toModuleSituation.pres M).kernelANC i q q' h x)
  /-- The dotted arrow of the diagram in the Stacks proof of clause (3), through which
  `𝒢(q) → 𝒢(q - c)` factors. -/
  dotted : ∀ (M : ANCModule I n c) (i : ℕ) (q : ℤ), toModuleSituation.HG M i q →ₗ[A]
    toModuleSituation.H (toModuleSituation.pres M).kernelANC i (q - c)
  /-- The dotted arrow does factor `𝒢(q) → 𝒢(q - c)` through `p^*K(q - c)`. -/
  kernelToImage_dotted : ∀ (M : ANCModule I n c) (i : ℕ) (q : ℤ) (h : q - (c : ℤ) ≤ q)
    (x : toModuleSituation.HG M i q),
    toModuleSituation.kernelToImage M i (q - c) (dotted M i q x) = HGtr M i q (q - c) h x
  /-- The canonical map `I^q ⊗_A M → H⁰(X, p^*M(q))`, induced by `p^*(I^q) → 𝒪_X(q)`. The
  source is `powTensor I n q M.1 = (I^q/I^{q+n}) ⊗_A M`, which is what Tag 0GAA writes `I^qM`:
  for `M = A ⧸ Iⁿ` it is `I^q/I^{q+n}`, as Tag 0GA7(2) requires. It is *not* the submodule
  `I^qM` of `M`; already for `A = ℤ`, `I = (2)`, `n = 1`, `M = A ⧸ I`, where the blowing up is
  an isomorphism, that submodule vanishes at `q = 1` while `H⁰(X, p^*M(1)) ≅ I/I² ≅ ℤ/2`, so
  no surjection out of it exists. See `powTensor`. -/
  secM : ∀ (M : ANCModule I n c) (q : ℕ),
    powTensor I n q M.1 →ₗ[A] toModuleSituation.H M 0 (q : ℤ)
  /-- The canonical maps are compatible with the chosen presentation: the composite
  `(I^q/I^{q+n})^{⊕r} → H⁰(X, (𝒪_{Yₙ})^{⊕r}(q)) → H⁰(X, p^*M(q))` agrees with the composite
  `(I^q/I^{q+n})^{⊕r} → I^q ⊗_A M → H⁰(X, p^*M(q))`. -/
  secM_freeSections : ∀ (M : ANCModule I n c) (q : ℕ)
    (v : Fin (toModuleSituation.pres M).rank → powQuot I q n),
    secM M q ((toModuleSituation.pres M).freeTensor q v) =
      toModuleSituation.freeToPullback M 0 (q : ℤ)
        ((toModuleSituation.freeIso M 0 q).symm fun j => toModuleSituation.cdiv n q (v j))

namespace TwistedModuleSituation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
  (S : TwistedModuleSituation A I n c)

/-- The reduction of clause (3) to the vanishing of `Hⁱ⁺¹(X, 𝒢(q)) → Hⁱ⁺¹(X, 𝒢(r))`: the
connecting map `Hⁱ(X, p^*M(r)) → Hⁱ⁺¹(X, 𝒢(r))` is injective for `i ≥ 1` and `r ≥ q₀`, and it
is natural in the twist. -/
private theorem Htr_eq_zero_of_HGtr_eq_zero {k : ℕ}
    (hG : ∀ (M : ANCModule I n c) (i : ℕ), i + k + 1 = S.d →
      ∀ (q r : ℤ) (h : r ≤ q), r + k * c = q → (S.q₀ : ℤ) + k * c ≤ q →
      ∀ x, S.HGtr M (i + 1) q r h x = 0)
    (M : ANCModule I n c) {i : ℕ} (hi : 1 ≤ i) (hik : i + k + 1 = S.d)
    {q r : ℤ} (h : r ≤ q) (hr : r + k * c = q) (hq : (S.q₀ : ℤ) + k * c ≤ q)
    (x : S.H M i q) : S.Htr M i q r h x = 0 := by
  have hq0 : (S.q₀ : ℤ) ≤ r := by linarith
  refine S.toModuleSituation.injective_pullbackToImage M hi hq0 ?_
  rw [map_zero, ← S.pullbackToImage_tr M i q r h x]
  exact hG M i hik q r h hr hq _

/-- The vanishing that drives clauses (3) and (5): for `k ≥ 1`, `i + k + 1 = d`, `r + kc = q`
and `q ≥ q₀ + kc`, the map `Hⁱ⁺¹(X, 𝒢(q)) → Hⁱ⁺¹(X, 𝒢(r))` is zero.

This is the induction of the Stacks proof of clause (3). By Tag 0GA9 the map
`𝒢(q) → 𝒢(q - c)` factors through `p^*K(q - c)`, so the map in question factors through
`Hⁱ⁺¹(X, p^*K(q - c)) → Hⁱ⁺¹(X, p^*K(r))`. For `k = 1` the source of the latter vanishes by
clause (2) applied to the `(A, n, c)`-module `K`, since `i + 1 + 1 = d` and `q - c ≥ q₀`; for
`k ≥ 2` the latter map is zero by clause (3) for `K` at the index `i + 1` and the shift
`k - 1`, which is the inductive hypothesis. -/
theorem HGtr_eq_zero : ∀ k : ℕ, 1 ≤ k → ∀ (M : ANCModule I n c) (i : ℕ), i + k + 1 = S.d →
    ∀ (q r : ℤ) (h : r ≤ q), r + k * c = q → (S.q₀ : ℤ) + k * c ≤ q →
    ∀ x, S.HGtr M (i + 1) q r h x = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro M i hik q r h hr hq x
    obtain rfl : r = q - (c : ℤ) := by push_cast at hr; linarith
    have hsub : Subsingleton (S.H (S.pres M).kernelANC (i + 1) (q - (c : ℤ))) :=
      S.toModuleSituation.subsingleton_H_next _ (Nat.le_add_left 1 i) (by lia)
        (by push_cast at hq; linarith)
    rw [← S.kernelToImage_dotted M (i + 1) q h x,
      @Subsingleton.elim _ hsub (S.dotted M (i + 1) q x) 0, map_zero]
  | succ k hk ih =>
    intro M i hik q r h hr hq x
    have hc : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
    have hkc : (0 : ℤ) ≤ (k : ℤ) * (c : ℤ) := by positivity
    have hr' : r + (k : ℤ) * (c : ℤ) + (c : ℤ) = q := by push_cast at hr; linarith
    have h1 : q - (c : ℤ) ≤ q := by linarith
    have h2 : r ≤ q - (c : ℤ) := by linarith
    have hrs : r + (k : ℤ) * (c : ℤ) = q - (c : ℤ) := by linarith
    rw [← S.HGtr_trans M (i + 1) q (q - (c : ℤ)) r h1 h2 h x,
      ← S.kernelToImage_dotted M (i + 1) q h1 x,
      S.kernelToImage_tr M (i + 1) (q - (c : ℤ)) r h2 _,
      S.Htr_eq_zero_of_HGtr_eq_zero ih (S.pres M).kernelANC (Nat.le_add_left 1 i) (by lia)
        h2 hrs (by push_cast at hq; linarith) _,
      map_zero]

/-- **Stacks Project, Tag 0GAA, clause (3).** For an `(A, n, c)`-module `M`, in the case
`d - 1 > i > 0` and `q ≥ q₀ + (d - 1 - i)c` the map
`Hⁱ(X, p^*M(q)) → Hⁱ(X, p^*M(q - (d - 1 - i)c))` is zero.

The case distinction `d - 1 > i > 0` is written `1 ≤ i` together with `i + k + 1 = d` and
`1 ≤ k`, which fixes `k = d - 1 - i`; the target twist `q - kc` is carried as a parameter `r`
with `r + kc = q`. The proof reduces the statement to `HGtr_eq_zero`, whose induction it is. -/
@[stacks 0GAA "clause (3), Hⁱ(X, p^*M(q)) → Hⁱ(X, p^*M(q-(d-1-i)c)) is zero for d-1 > i > 0"]
theorem Htr_eq_zero (M : ANCModule I n c) {i k : ℕ} {q r : ℤ} (h : r ≤ q)
    (hi : 1 ≤ i) (hk : 1 ≤ k) (hik : i + k + 1 = S.d) (hr : r + k * c = q)
    (hq : (S.q₀ : ℤ) + k * c ≤ q) : S.Htr M i q r h = 0 :=
  LinearMap.ext fun x =>
    S.Htr_eq_zero_of_HGtr_eq_zero (S.HGtr_eq_zero k hk) M hi hik h hr hq x

/-- Every element of `H⁰(X, p^*M(q))` that comes from `H⁰(X, (𝒪_{Yₙ})^{⊕r}(q))` comes from
`I^q ⊗_A M`, when `q ≥ q₀`: the free module's sections are `(I^q/I^{q+n})^{⊕r}` by Tag 0GA7(2),
and `(I^q/I^{q+n})^{⊕r} → I^q ⊗_A M → H⁰(X, p^*M(q))` is the same map. -/
private theorem mem_range_secM (M : ANCModule I n c) {q : ℕ} (hq : S.q₀ ≤ q)
    (y : S.Hfree M 0 (q : ℤ)) :
    ∃ t, S.secM M q t = S.freeToPullback M 0 (q : ℤ) y := by
  choose v hv using fun j => S.toModuleSituation.surjective_cdiv hq (S.freeIso M 0 q y j)
  have hvw : (fun j => S.cdiv n q (v j)) = S.freeIso M 0 q y := funext hv
  exact ⟨(S.pres M).freeTensor q v, by
    rw [S.secM_freeSections M q v, hvw, LinearEquiv.symm_apply_apply]⟩

/-- **Stacks Project, Tag 0GAA, clause (4).** For an `(A, n, c)`-module `M`, in the case
`i = 0`, `d ∈ {0, 1}` and `q ≥ q₀` the canonical map `I^q ⊗_A M → H⁰(X, p^*M(q))` is
surjective.

The long exact sequence of `0 → ℱ → p^*K → 𝒢 → 0` makes `H¹(X, p^*K(q)) → H¹(X, 𝒢(q))`
surjective, since `H²(X, ℱ(q)) = 0` for `d ≤ 1`; its source vanishes, by clause (1) if `d = 1`
and because `d` bounds the fibre dimensions if `d = 0`. So `H¹(X, 𝒢(q)) = 0` and the long exact
sequence of `0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0` makes `H⁰(X, (𝒪_{Yₙ})^{⊕r}(q)) → H⁰(X, p^*M(q))`
surjective; for `q ≥ q₀` the source is `(I^q/I^{q+n})^{⊕r}` by Tag 0GA7(2), and the composite
with it factors through `I^q ⊗_A M` by `ANCPresentation.freeTensor_surjective`.

The Stacks Project writes the source `I^qM`. Read as the submodule `I^q·M` of `M` the clause
is false: for `A = ℤ`, `I = (2)` (so the blowing up is an isomorphism, `d = 0`, `q₀ = 0`),
`n = 1`, `c = 0` and `M = A ⧸ I`, at `q = 1` that submodule is `0` while Tag 0GA7(2) gives
`H⁰(X, p^*M(1)) = H⁰(X, 𝒪_{Y₁}(1)) = I/I² ≅ ℤ/2`. What the proof produces, and what is
formalized, is the surjection out of `I^q ⊗_A M = (I^q/I^{q+n}) ⊗_A M`, which agrees with
`I^q/I^{q+n}` for `M = A ⧸ Iⁿ` as Tag 0GA7(2) demands. -/
@[stacks 0GAA "clause (4), surjectivity onto H⁰(X, p^*M(q)) for i = 0, d ≤ 1, q ≥ q₀; \
corrected: the source is I^q ⊗_A M, not the submodule I^qM, for which this is false"]
theorem surjective_secM (M : ANCModule I n c) {q : ℕ} (hd : S.d ≤ 1) (hq : S.q₀ ≤ q) :
    Function.Surjective (S.secM M q) := by
  have hqz : (S.q₀ : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hK : Subsingleton (S.H (S.pres M).kernelANC 1 (q : ℤ)) := by
    rcases Nat.lt_or_ge S.d 1 with hd1 | hd1
    · exact S.vanishing_H _ 1 _ (by lia)
    · have hd2 : S.d = 1 := by lia
      have h0 : Subsingleton (S.H (S.pres M).kernelANC S.d (q : ℤ)) :=
        S.toModuleSituation.subsingleton_H_top _ (by lia) hqz
      rwa [hd2] at h0
  have hG : Subsingleton (S.HG M 1 (q : ℤ)) := by
    have := S.vanishing_HF M 2 (q : ℤ) (by lia)
    exact subsingleton_of_exact_of_subsingleton (S.exact_image M 1 (q : ℤ))
  intro z
  obtain ⟨y, rfl⟩ := (S.exact_pullback M 0 (q : ℤ) z).1 (@Subsingleton.elim _ hG _ _)
  exact S.mem_range_secM M hq y

/-- **Stacks Project, Tag 0GAA, clause (5).** For an `(A, n, c)`-module `M`, in the case
`i = 0`, `d > 1` and `q ≥ q₀ + (d - 1)c` the image of
`H⁰(X, p^*M(q)) → H⁰(X, p^*M(q - (d - 1)c))` is contained in the image of the canonical map
`I^{q - (d-1)c} ⊗_A M → H⁰(X, p^*M(q - (d - 1)c))`, the map of clause (4); as there, the source
is the tensor product and not the submodule `I^{q-(d-1)c}M` of `M`.

The case `d > 1` is written `k + 1 = d` with `1 ≤ k`, which fixes `k = d - 1`; the target
twist `q - kc` is carried as a natural number `r` with `r + kc = q`, which is no restriction
since `q ≥ q₀ + kc` forces `q - kc ≥ q₀ ≥ 0`. Arguing as in clause (4)
it suffices that the image lie in the image of `H⁰(X, (𝒪_{Yₙ})^{⊕r}(q - (d-1)c))`, which by the
long exact sequence of `0 → 𝒢 → (𝒪_{Yₙ})^{⊕r} → p^*M → 0` holds as soon as the boundary in
`H¹(X, 𝒢(q))` dies in `H¹(X, 𝒢(q - (d-1)c))`; that is `HGtr_eq_zero` at `i = 0`. -/
@[stacks 0GAA "clause (5), H⁰(p^*M(q)) → H⁰(p^*M(q-(d-1)c)) lands in the image of the \
canonical map out of I^{q-(d-1)c} ⊗_A M; corrected as in clause (4)"]
theorem range_Htr_le (M : ANCModule I n c) {k r : ℕ} {q : ℤ} (h : (r : ℤ) ≤ q)
    (hk : 1 ≤ k) (hkd : k + 1 = S.d) (hr : (r : ℤ) + k * c = q)
    (hq : (S.q₀ : ℤ) + k * c ≤ q) :
    LinearMap.range (S.Htr M 0 q (r : ℤ) h) ≤ LinearMap.range (S.secM M r) := by
  have hq0 : (S.q₀ : ℤ) ≤ (r : ℤ) := by linarith
  have hr0 : S.q₀ ≤ r := by exact_mod_cast hq0
  rintro z ⟨x, rfl⟩
  have hb : S.pullbackToImage M 0 (r : ℤ) (S.Htr M 0 q (r : ℤ) h x) = 0 := by
    rw [← S.pullbackToImage_tr M 0 q (r : ℤ) h x]
    exact S.HGtr_eq_zero k hk M 0 (by lia) q (r : ℤ) h hr hq _
  obtain ⟨y, hy⟩ := (S.exact_pullback M 0 (r : ℤ) _).1 hb
  obtain ⟨t, ht⟩ := S.mem_range_secM M hr0 y
  exact ⟨t, by rw [ht, hy]⟩

end TwistedModuleSituation

section TopWitness

/-- `A ⧸ Aⁿ` is the zero ring, so every module over it vanishes. -/
theorem subsingleton_quotient_top_pow (A : Type u) [CommRing A] (n : ℕ) :
    Subsingleton (A ⧸ (⊤ : Ideal A) ^ n) := by
  rw [top_pow_eq_top]
  exact Ideal.Quotient.subsingleton_iff.2 rfl

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (n c : ℕ)

/-- The `ModuleSituation` for `I = A`, in which the blowup is `Spec(A)`, the exceptional
divisor is empty and every `(A, n, c)`-module is zero because `A ⧸ Aⁿ` is the zero ring. It
witnesses that the hypotheses of `ModuleSituation` are consistent. -/
def topModuleSituation (hcn : c ≤ n) : ModuleSituation A (⊤ : Ideal A) n c :=
  have _hss : Subsingleton (A ⧸ (⊤ : Ideal A) ^ n) := subsingleton_quotient_top_pow A n
  { topSituation A with
    exponent_le := hcn
    pres := fun M =>
      have : Subsingleton M.1 := Module.subsingleton (A ⧸ (⊤ : Ideal A) ^ n) M.1
      { rank := 0
        kernel := ModuleCat.of (A ⧸ (⊤ : Ideal A) ^ n) PUnit
        incl := 0
        proj := 0
        incl_injective := fun a b _ => Subsingleton.elim a b
        proj_surjective := fun _ => ⟨0, Subsingleton.elim _ _⟩
        range_incl_eq_ker_proj :=
          le_antisymm (fun _ _ => Subsingleton.elim _ _) fun _ _ => ⟨0, Subsingleton.elim _ _⟩ }
    H := fun _ _ _ => ModuleCat.of A PUnit
    Hfree := fun _ _ _ => ModuleCat.of A PUnit
    HG := fun _ _ _ => ModuleCat.of A PUnit
    HF := fun _ _ _ => ModuleCat.of A PUnit
    freeIso := fun _ _ _ =>
      { toFun := fun _ => 0
        map_add' := fun _ _ => funext fun i => i.elim0
        map_smul' := fun _ _ => funext fun i => i.elim0
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
    subsingleton_Hdiv_zero := fun _ _ => inferInstanceAs (Subsingleton PUnit)
    vanishing_H := fun _ _ _ _ => inferInstanceAs (Subsingleton PUnit)
    vanishing_HG := fun _ _ _ _ => inferInstanceAs (Subsingleton PUnit)
    vanishing_HF := fun _ _ _ _ => inferInstanceAs (Subsingleton PUnit)
    freeToPullback := fun _ _ _ => 0
    pullbackToImage := fun _ _ _ => 0
    exact_pullback := fun _ _ _ _ =>
      ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
    kernelToImage := fun _ _ _ => 0
    imageToSupported := fun _ _ _ => 0
    exact_image := fun _ _ _ _ =>
      ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩ }

/-- The `TwistedModuleSituation` for `I = A`, extending `topModuleSituation`: every cohomology
module in sight vanishes, so all the maps between twists are zero. It witnesses that the
hypotheses of `TwistedModuleSituation` are consistent. -/
noncomputable def topTwistedModuleSituation (hcn : c ≤ n) :
    TwistedModuleSituation A (⊤ : Ideal A) n c :=
  { topModuleSituation A n c hcn with
    Htr := fun _ _ _ _ _ => 0
    HGtr := fun _ _ _ _ _ => 0
    HGtr_trans := fun _ _ _ _ _ _ _ _ _ => rfl
    pullbackToImage_tr := fun _ _ _ _ _ _ => rfl
    kernelToImage_tr := fun _ _ _ _ _ _ => rfl
    dotted := fun _ _ _ => 0
    kernelToImage_dotted := fun _ _ _ _ _ => rfl
    secM := fun _ _ => 0
    secM_freeSections := fun _ _ _ => rfl }

end TopWitness

section QuotientModules

/-- An element of an ideal `J` of `R` annihilates `R ⧸ J`. -/
theorem smul_quotient_self_eq_zero {R : Type*} [CommRing R] (J : Ideal R) {a : R} (ha : a ∈ J)
    (m : R ⧸ J) : a • m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | H y =>
    change (Submodule.Quotient.mk (a • y) : R ⧸ J) = 0
    rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha

/-- For a nonzero proper ideal `J` of `R` the cyclic module `R ⧸ J` is not free: an element of
`J` annihilates `R ⧸ J`, hence annihilates a basis vector, hence vanishes; and `R ⧸ J` is
nonzero, so a basis is nonempty. -/
theorem not_free_quotient_self {R : Type*} [CommRing R] {J : Ideal R} (h0 : J ≠ ⊥)
    (h1 : J ≠ ⊤) : ¬ Module.Free R (R ⧸ J) := by
  intro _
  obtain ⟨a, haJ, ha0⟩ := J.ne_bot_iff.1 h0
  have := Ideal.Quotient.nontrivial_iff.2 h1
  let b := Module.Free.chooseBasis R (R ⧸ J)
  obtain ⟨i⟩ := b.index_nonempty
  have hann : b.repr (a • b i) = 0 := by rw [smul_quotient_self_eq_zero J haJ, map_zero]
  rw [map_smul, b.repr_self] at hann
  exact ha0 (by simpa using DFunLike.congr_fun hann i)

end QuotientModules

section AffineWitness

open scoped TensorProduct

variable {A : Type u} [CommRing A] (I : Ideal A) (n c : ℕ)

/-- `I^q/I^{q+0} = 0`: the subquotient of `A` with zero width vanishes. -/
theorem subsingleton_powQuot_zero (q : ℕ) : Subsingleton (powQuot I q 0) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero]
    simpa only [powSub, Submodule.mem_comap, Submodule.coe_subtype, Nat.add_zero] using x.2

/-- `I^qM ⊆ I^{q'}M` for `q' ≤ q`. -/
theorem powSmul_mono {q q' : ℕ} (h : q' ≤ q) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    powSmul I n q M ≤ powSmul I n q' M :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

/-- `I⁰M = M`. -/
theorem powSmul_zero_eq_top (M : ModuleCat.{u} (A ⧸ I ^ n)) : powSmul I n 0 M = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  rw [← one_smul A x]
  exact Submodule.smul_mem_smul (by simp) Submodule.mem_top

/-- The maps `I^q/I^{q+n} → I^{q'}/I^{q'+n}` are functorial in the twist. -/
theorem powQuotLe_powQuotLe {q q' q'' : ℕ} (h : q' ≤ q) (h' : q'' ≤ q') (x : powQuot I q n) :
    powQuotLe I h' (powQuotLe I h x) = powQuotLe I (h'.trans h) x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

/-- The cohomology of the twists of `p^*M` in the affine witness: concentrated in degree `0`,
where it is `I^q ⊗_A M` for `q ≥ 0` and `M` itself for `q < 0`.

In the Situation of `affineSituation` the blowing up `p` is an isomorphism and `𝒪_X(q)` is
`I^q𝒪_X`, so `p^*M(q)` is the quasi-coherent module attached to `I^q ⊗_A M`, its higher
cohomology vanishes and its sections are `I^q ⊗_A M` itself. -/
noncomputable def affineH (M : ModuleCat.{u} (A ⧸ I ^ n)) (i : ℕ) (q : ℤ) : ModuleCat.{u} A :=
  match i with
  | 0 => ModuleCat.of A (powTensor I n q.toNat M)
  | _ + 1 => ModuleCat.of A PUnit

/-- The positive-degree cohomology of the affine witness is zero. -/
theorem subsingleton_affineH_succ (M : ModuleCat.{u} (A ⧸ I ^ n)) (i : ℕ) (q : ℤ) :
    Subsingleton (affineH I n M (i + 1) q) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The twisting-down map `I^q ⊗_A M → I^{q'} ⊗_A M` for `q' ≤ q`, induced by
`I^q/I^{q+n} → I^{q'}/I^{q'+n}`. -/
noncomputable def powTensorLe (M : ModuleCat.{u} (A ⧸ I ^ n)) {q q' : ℕ} (h : q' ≤ q) :
    powTensor I n q M →ₗ[A] powTensor I n q' M :=
  LinearMap.rTensor (resModule I n M) (powQuotLe I h)

/-- The twisting-down maps compose: twisting down from `q` to `q'` and then to `q''` is twisting
down from `q` to `q''`. -/
theorem powTensorLe_powTensorLe (M : ModuleCat.{u} (A ⧸ I ^ n)) {q q' q'' : ℕ} (h : q' ≤ q)
    (h' : q'' ≤ q') (x : powTensor I n q M) :
    powTensorLe I n M h' (powTensorLe I n M h x) = powTensorLe I n M (h'.trans h) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp only [powTensorLe, LinearMap.rTensor_tmul, powQuotLe_powQuotLe]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The twisting-down map of the affine witness: `powTensorLe` in degree `0`, and zero in
positive degrees. -/
noncomputable def affineHtr (M : ModuleCat.{u} (A ⧸ I ^ n)) (i : ℕ) {q q' : ℤ} (h : q' ≤ q) :
    affineH I n M i q →ₗ[A] affineH I n M i q' :=
  match i with
  | 0 => powTensorLe I n M (show q'.toNat ≤ q.toNat by lia)
  | _ + 1 => 0

/-- The twisting-down maps of the affine witness compose: from `q` to `q'` and then to `q''` is
from `q` to `q''`. -/
theorem affineHtr_affineHtr (M : ModuleCat.{u} (A ⧸ I ^ n)) (i : ℕ) {q q' q'' : ℤ} (h : q' ≤ q)
    (h' : q'' ≤ q') (h'' : q'' ≤ q) (x : affineH I n M i q) :
    affineHtr I n M i h' (affineHtr I n M i h x) = affineHtr I n M i h'' x := by
  rcases i with _ | i
  · exact powTensorLe_powTensorLe I n M _ _ x
  · rfl

/-- `H⁰(X, p^*M)` is nonzero in the affine witness whenever `M` is, because the canonical map
`I⁰ ⊗_A M → M` is surjective. -/
theorem nontrivial_affineH_zero (M : ModuleCat.{u} (A ⧸ I ^ n))
    (h : Nontrivial (resModule I n M)) : Nontrivial (affineH I n M 0 0) := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨x, hx⟩ := surjective_mulPowTensor_zero I n M a
  obtain ⟨y, hy⟩ := surjective_mulPowTensor_zero I n M b
  exact ⟨x, y, fun hc => hab (by rw [← hx, ← hy, hc])⟩

/-- A finite `A ⧸ Iⁿ`-module annihilated by the image of `I^c` is an `(A, n, c)`-module: a
module annihilated by an ideal is projective relative to it, by Tag 0G94. -/
theorem isANCModule_of_smul_eq_zero {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hfin : Module.Finite (A ⧸ I ^ n) M)
    (hzero : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c), ∀ m : M, a • m = 0) :
    IsANCModule I n c M :=
  ⟨hfin, Module.isIProjective_of_smul_eq_zero _ _ hzero⟩

/-- The cyclic `(A, n, c)`-module `(A ⧸ Iⁿ) ⧸ I^c(A ⧸ Iⁿ)`. It is annihilated by the image of
`I^c`, hence `I^c/Iⁿ`-projective by Tag 0G94, and it is finite because it is cyclic. -/
noncomputable def quotPowANCModule : ANCModule I n c :=
  ⟨ModuleCat.of (A ⧸ I ^ n) ((A ⧸ I ^ n) ⧸ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)),
    isANCModule_of_smul_eq_zero I n c
      (Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _))
      fun _ ha m => smul_quotient_self_eq_zero _ ha m⟩

/-- `quotPowANCModule` is not free over `A ⧸ Iⁿ` when the image of `I^c` is a nonzero proper
ideal — for instance for `I = (p)` a nonzero prime in a Dedekind domain with `c = 1 < n`. So
the affine witness applies to `(A, n, c)`-modules that are not free, which is where clause (4)
of Tag 0GAA is not a restatement of Tag 0GA7(2). -/
theorem not_free_quotPowANCModule
    (h0 : Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c) ≠ ⊥)
    (h1 : Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c) ≠ ⊤) :
    ¬ Module.Free (A ⧸ I ^ n) (quotPowANCModule I n c).1 :=
  not_free_quotient_self h0 h1

/-- `quotPowANCModule` is nonzero when the image of `I^c` is a proper ideal, so
`nontrivial_affineTwistedModuleSituation_H` applies to it. -/
theorem nontrivial_quotPowANCModule
    (h1 : Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c) ≠ ⊤) :
    Nontrivial (quotPowANCModule I n c).1 :=
  Ideal.Quotient.nontrivial_iff.2 h1

variable [IsNoetherianRing A]

/-- A chosen finite free presentation of each `(A, n, c)`-module, used by the affine witness;
one exists by `nonempty_ANCPresentation`. -/
noncomputable def affinePres (M : ANCModule I n c) : ANCPresentation I n c M :=
  (nonempty_ANCPresentation M).some

/-- The `ModuleSituation` of Tag 0GA6 built on `affineSituation`: the blowing up is an
isomorphism, `d(S) = 0` and `q(S) = 0`, so every sheaf in the proof of Tag 0GAA has cohomology
concentrated in degree `0`. There `p^*M(q)` has sections `I^q ⊗_A M`, the pulled-back
presentation `p^*K → (𝒪_{Yₙ})^{⊕r} → p^*M → 0` stays exact, so `ℱ = 0` and `𝒢 = p^*K`, and the
comparison map `H⁰(X, (𝒪_{Yₙ})^{⊕r}(q)) → H⁰(X, p^*M(q))` is the canonical surjection
`ANCPresentation.freeTensor`.

Unlike `topModuleSituation`, the cohomology modules here are not all zero: see
`nontrivial_affineModuleSituation_H`. -/
noncomputable def affineModuleSituation (hcn : c ≤ n) : ModuleSituation A I n c :=
  { affineSituation I with
    exponent_le := hcn
    pres := affinePres I n c
    H := fun M i q => affineH I n M.1 i q
    Hfree := fun M i q =>
      ModuleCat.of A (Fin (affinePres I n c M).rank → (affineSituation I).Hdiv n i q.toNat)
    HG := fun M i q => affineH I n (affinePres I n c M).kernel i q
    HF := fun _ _ _ => ModuleCat.of A PUnit
    freeIso := fun _ _ _ => LinearEquiv.refl A _
    subsingleton_Hdiv_zero := fun i q => match i with
      | 0 => subsingleton_powQuot_zero I q
      | _ + 1 => inferInstanceAs (Subsingleton PUnit)
    vanishing_H := fun M i q hi => match i, hi with
      | 0, hi => absurd hi (Nat.not_lt_zero _)
      | i + 1, _ => subsingleton_affineH_succ I n M.1 i q
    vanishing_HG := fun M i q hi => match i, hi with
      | 0, hi => absurd hi (Nat.not_lt_zero _)
      | i + 1, _ => subsingleton_affineH_succ I n (affinePres I n c M).kernel i q
    vanishing_HF := fun _ _ _ _ => inferInstanceAs (Subsingleton PUnit)
    freeToPullback := fun M i q => match i with
      | 0 => (affinePres I n c M).freeTensor q.toNat
      | _ + 1 => 0
    pullbackToImage := fun _ _ _ => 0
    exact_pullback := fun M i q => by
      rcases i with _ | i
      · have := subsingleton_affineH_succ I n (affinePres I n c M).kernel 0 q
        exact fun y => ⟨fun _ => (affinePres I n c M).freeTensor_surjective q.toNat y,
          fun _ => Subsingleton.elim _ _⟩
      · have := subsingleton_affineH_succ I n M.1 i q
        have := subsingleton_affineH_succ I n (affinePres I n c M).kernel (i + 1) q
        exact fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
    kernelToImage := fun _ i _ => match i with
      | 0 => LinearMap.id
      | _ + 1 => 0
    imageToSupported := fun _ _ _ => 0
    exact_image := fun M i q => by
      rcases i with _ | i
      · exact fun y => ⟨fun _ => ⟨y, rfl⟩, fun _ => Subsingleton.elim _ _⟩
      · have := subsingleton_affineH_succ I n (affinePres I n c M).kernel i q
        exact fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩ }

/-- The `TwistedModuleSituation` of Tag 0GA6 built on `affineModuleSituation`. The twisting-down
maps are `I^q ⊗_A M → I^{q'} ⊗_A M` and `I^q ⊗_A K → I^{q'} ⊗_A K`, the dotted arrow of
Tag 0GA9 is `I^q ⊗_A K → I^{q-c} ⊗_A K` (the module `ℱ` is zero here, so the factorization is
automatic), and the canonical map `I^q ⊗_A M → H⁰(X, p^*M(q))` of clause (4) is the identity,
because for an isomorphism `p` the sections of `p^*M(q)` *are* `I^q ⊗_A M`.

Unlike `topTwistedModuleSituation`, this witness is not degenerate: the cohomology modules it
supplies are nonzero (`nontrivial_affineTwistedModuleSituation_H`), the canonical map of
clause (4) is bijective rather than a map between zero modules
(`bijective_affineTwistedModuleSituation_secM`), and the `(A, n, c)`-modules it is applied to
need not be free over `A ⧸ Iⁿ` (`not_free_quotPowANCModule`).

Since `d(S) = 0` here, the clauses of Tag 0GAA that this witness makes non-vacuous are
clause (4) — the one clause whose case hypothesis `d ∈ {0, 1}` it satisfies. Clauses (1), (2),
(3) and (5) require `d ≥ 1`, `d ≥ 2`, `d ≥ 3` and `d ≥ 2` respectively, so their case
hypotheses are unsatisfiable here and they say nothing about this witness. -/
noncomputable def affineTwistedModuleSituation (hcn : c ≤ n) :
    TwistedModuleSituation A I n c :=
  { affineModuleSituation I n c hcn with
    Htr := fun M i _ _ h => affineHtr I n M.1 i h
    HGtr := fun M i _ _ h => affineHtr I n (affinePres I n c M).kernel i h
    HGtr_trans := fun M i _ _ _ h h' h'' x =>
      affineHtr_affineHtr I n (affinePres I n c M).kernel i h h' h'' x
    pullbackToImage_tr := fun _ _ _ _ _ _ => rfl
    kernelToImage_tr := fun _ i _ _ _ _ => by cases i <;> rfl
    dotted := fun M i q =>
      affineHtr I n (affinePres I n c M).kernel i (sub_le_self q (Int.natCast_nonneg c))
    kernelToImage_dotted := fun _ i _ _ _ => by cases i <;> rfl
    secM := fun _ _ => LinearMap.id
    secM_freeSections := fun _ _ _ => rfl }

/-- The canonical map `I^q ⊗_A M → H⁰(X, p^*M(q))` of Tag 0GAA, clause (4), is bijective in the
affine witness: for an isomorphism `p` the comparison is the identity. In particular it is not
a map between zero modules, which is what makes clause (4) a statement with content there. -/
theorem bijective_affineTwistedModuleSituation_secM (hcn : c ≤ n) (M : ANCModule I n c)
    (q : ℕ) : Function.Bijective ((affineTwistedModuleSituation I n c hcn).secM M q) :=
  Function.bijective_id

/-- The affine witness is not degenerate: for a nonzero `(A, n, c)`-module `M` the module
`H⁰(X, p^*M)` it supplies is nonzero, so clause (4) of Tag 0GAA is not a statement about zero
modules there. -/
theorem nontrivial_affineModuleSituation_H (hcn : c ≤ n) (M : ANCModule I n c)
    [Nontrivial M.1] : Nontrivial ((affineModuleSituation I n c hcn).H M 0 0) :=
  nontrivial_affineH_zero I n M.1 ‹Nontrivial M.1›

/-- The same statement for the `TwistedModuleSituation`. -/
theorem nontrivial_affineTwistedModuleSituation_H (hcn : c ≤ n) (M : ANCModule I n c)
    [Nontrivial M.1] : Nontrivial ((affineTwistedModuleSituation I n c hcn).H M 0 0) :=
  nontrivial_affineModuleSituation_H I n c hcn M

end AffineWitness

end Stacks.LocalCohomology.UniformityIII

end
