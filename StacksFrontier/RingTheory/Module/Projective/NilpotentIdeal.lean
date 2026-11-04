module

import Mathlib.RingTheory.Smooth.Quotient

import StacksCore.RingTheory.Nakayama
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Module.Projective.Lifting
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# A flat module with projective reduction along a nilpotent ideal is projective

Let `R` be a commutative ring, `I ⊆ R` a nilpotent ideal and `M` a flat `R`-module whose
reduction `M/IM` is projective over `R ⧸ I`. Then `M` is projective over `R`.

Lifting the projective `R ⧸ I`-module `M/IM` to a projective `R`-module `P` with `P/IP ≅ M/IM`
(Stacks 07LV) and lifting `P → P/IP ≅ M/IM` through the surjection `M → M/IM` (projectivity of
`P`) produces an `R`-linear `f : P → M` which is an isomorphism modulo `I`. Such an `f` is
bijective, so `M ≅ P` is projective.

## Main results

* `LinearMap.ker_le_of_comp_mkQ_eq_of_injective`: a map whose reduction modulo a submodule is
  injective has its kernel inside that submodule.
* `LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top`: a map into a flat module which is
  surjective modulo a nilpotent ideal and whose kernel lies in `I • P` is bijective.
* `solution`: the statement of Stacks Tag 05CG.

## Implementation notes

Where the source compares the two `I`-adic filtrations of `P` and of `M` graded piece by piece,
identifying `IᵃP/Iᵃ⁺¹P → IᵃM/Iᵃ⁺¹M` with `Iᵃ/Iᵃ⁺¹ ⊗_{R ⧸ I} P/IP → Iᵃ/Iᵃ⁺¹ ⊗_{R ⧸ I} M/IM`, the
argument here reads the same input off `ker f` directly, and needs flatness of `M` only (not of
`P`): surjectivity of `f` is Nakayama for a nilpotent ideal
(`LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent`, Stacks 00DV (11)), and for the
kernel, `ker f ≤ I • P` holds because `f` is injective modulo `I`, while flatness of `M` gives
`ker f ⊓ I • P = I • ker f` (`LinearMap.ker_inf_smul_top_eq_smul_of_flat`, the vanishing of
`Tor₁(M, R ⧸ I)` in the form Mathlib states it), so `ker f = I • ker f` and nilpotence of `I`
forces `ker f = ⊥` (`Submodule.eq_bot_of_le_smul_of_isNilpotent`, Stacks 00DV (9)). Both readings
are the statement that the comparison map is an isomorphism in each degree of the filtration; the
kernel-side one is the one Mathlib has the API for.

The two halves of that comparison are separated as lemmas.
`LinearMap.ker_le_of_comp_mkQ_eq_of_injective` is the injectivity one: a map whose reduction
modulo a submodule is injective has its kernel inside that submodule, for arbitrary submodules of
arbitrary modules over an arbitrary ring, with no nilpotence and no flatness in sight. It is the
counterpart of Nakayama's surjectivity criterion, which is the surjectivity one.
`LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top` then combines them, stated for an
arbitrary map into a flat module with the two hypotheses it uses — surjectivity of `P → M/IM` and
`ker f ≤ I • P` — rather than for the isomorphism `P/IP ≅ M/IM` that the source produces, which
is a strictly stronger input: an isomorphism of reductions gives `f⁻¹(I • M) ≤ I • P`, of which
only `ker f ≤ I • P` is used.

Both are stated for an arbitrary map into an arbitrary flat module rather than privately for the
comparison map of 05CG, because the combination "surjection onto a flat module, injective modulo a
nilpotent ideal, hence bijective" is the standard way a deformation-theoretic presentation is shown
to be exact: the kernel of a lifted presentation of a deformation over a square-zero extension
vanishes for exactly this reason, and the only input beyond nilpotence is flatness of the target,
not projectivity or finiteness of anything.

## References

* [StacksProject 05CG](https://stacks.math.columbia.edu/tag/05CG)
-/

/-- A map that becomes injective after reduction modulo `N' ⊆ P` and `N ⊆ M` has its kernel
inside `N'`. This is the injectivity counterpart of Nakayama's surjectivity criterion
(`LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent`, Stacks 00DV (11)), and needs
no hypothesis on `N` and `N'`. -/
public theorem LinearMap.ker_le_of_comp_mkQ_eq_of_injective {R : Type*} [Ring R] {P : Type*}
    [AddCommGroup P] [Module R P] {M : Type*} [AddCommGroup M] [Module R M] {N' : Submodule R P}
    {N : Submodule R M} {f : P →ₗ[R] M} {g : (P ⧸ N') →ₗ[R] M ⧸ N}
    (hfg : N.mkQ ∘ₗ f = g ∘ₗ N'.mkQ) (hg : Function.Injective g) : LinearMap.ker f ≤ N' :=
  calc LinearMap.ker f ≤ LinearMap.ker (N.mkQ ∘ₗ f) := LinearMap.ker_le_ker_comp _ _
    _ = LinearMap.ker N'.mkQ := by
        rw [hfg, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_injective hg)]
    _ = N' := Submodule.ker_mkQ _

/-- A map into a flat module which is surjective modulo a nilpotent ideal `I` and whose kernel
is contained in `I • P` is bijective.

Surjectivity is Nakayama for a nilpotent ideal
(`LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent`, Stacks 00DV (11)). For injectivity,
flatness of `M` turns the containment `ker f ≤ I • P` into `ker f = I • ker f`
(`LinearMap.ker_inf_smul_top_eq_smul_of_flat`, which is the vanishing of `Tor₁(M, R ⧸ I)` in the
form Mathlib states it), and nilpotence of `I` kills that
(`Submodule.eq_bot_of_le_smul_of_isNilpotent`, Stacks 00DV (9)). The containment is the only thing
that needs flatness: without it one knows `ker f ≤ I • P` but has no equation for the nilpotence
induction to start from. -/
@[sga "3 III 3.3" "more general", sga "3 VIB 6.2.2" "more general", sga "3 VIIB 0.3.7" "partial"]
public theorem LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top
    {R : Type*} [CommRing R] {I : Ideal R}
    {P : Type*} [AddCommGroup P] [Module R P] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Flat R M] (hI : IsNilpotent I) (f : P →ₗ[R] M)
    (hsurj : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ ∘ₗ f))
    (hker : LinearMap.ker f ≤ I • (⊤ : Submodule R P)) :
    Function.Bijective f := by
  have hf := LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent I f hI hsurj
  refine ⟨LinearMap.ker_eq_bot.1 (Submodule.eq_bot_of_le_smul_of_isNilpotent I _ hI ?_), hf⟩
  rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I f hf]
  exact le_inf le_rfl hker

namespace Stacks.Projective.NilpotentDescent

/-- A flat module `M` over a commutative ring `R` whose reduction `M ⧸ IM` modulo a nilpotent
ideal `I` is projective over `R ⧸ I` is projective over `R`. -/
public theorem solution {R : Type u} [CommRing R] {I : Ideal R} {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Flat R M] (hI : IsNilpotent I)
    (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Projective R M := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ :=
    Module.exists_projective_quotient_smul_top_linearEquiv_of_isNilpotent
      (R := R) (I := I) (Q := M ⧸ I • (⊤ : Submodule R M)) hI
  -- `P` is projective, so `P → P/IP ≅ M/IM` lifts through the surjection `M → M/IM`.
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ
    (e.toLinearMap.restrictScalars R ∘ₗ (I • (⊤ : Submodule R P)).mkQ)
    (Submodule.mkQ_surjective _)
  refine Module.Projective.of_equiv (LinearEquiv.ofBijective f
    (LinearMap.bijective_of_isNilpotent_of_ker_le_smul_top hI f ?_
      (LinearMap.ker_le_of_comp_mkQ_eq_of_injective hf e.injective)))
  rw [hf]
  exact e.surjective.comp (Submodule.mkQ_surjective _)

end Stacks.Projective.NilpotentDescent

/-!
# A flat module with projective reduction along a nilpotent ideal is projective

Let `R` be a commutative ring, `I ⊆ R` a nilpotent ideal and `M` a flat `R`-module whose
reduction `M/IM` is a projective `R ⧸ I`-module. Then `M` is projective over `R`.

The mechanism is that `M` is forced to be the projective module lifting `M/IM`: choosing a
projective `R`-module `P` with `P/IP ≅ M/IM` and lifting `P → P/IP ≅ M/IM` through `M → M/IM`
gives an `R`-linear `P → M` which is an isomorphism modulo `I`. Comparing the finite filtrations
`0 = IⁿP ⊆ … ⊆ IP ⊆ P` and `0 = IⁿM ⊆ … ⊆ IM ⊆ M`, flatness of `P` and of `M` identifies
`IᵃP/Iᵃ⁺¹P → IᵃM/Iᵃ⁺¹M` with `Iᵃ/Iᵃ⁺¹ ⊗_{R ⧸ I} P/IP → Iᵃ/Iᵃ⁺¹ ⊗_{R ⧸ I} M/IM`, which is
bijective; hence `P → M` is an isomorphism.

## Main results

* `Module.Flat.projective_of_isNilpotent_of_projective_quotient_smul_top`: a flat module whose
  reduction modulo a nilpotent ideal is projective is projective.

## Implementation notes

`M/IM` is `M ⧸ I • (⊤ : Submodule R M)` with Mathlib's canonical `R ⧸ I`-action, in which the
class of `r` acts as the class of `r • ·`; this is the spelling the companion lifting result
(Stacks 07LV) uses, so the two compose without a translation lemma. Nilpotency is `IsNilpotent I`
in the monoid of ideals, i.e. `I ^ n = ⊥` for some `n`, the source's `I` nilpotent.

Unlike the lifting result 07LV, which holds over an arbitrary ring, this is stated for a
commutative ring: `Module.Flat` is defined over a commutative base, and the identification of
`IᵃM/Iᵃ⁺¹M` with `Iᵃ/Iᵃ⁺¹ ⊗_{R ⧸ I} M/IM` is a statement about that notion of flatness.

Flatness is an instance argument, which puts the result in the `Module.Flat` namespace beside
`Module.Flat.projective_of_finitePresentation`; projectivity of the reduction is an explicit
hypothesis, since instance search cannot be expected to see it for a derived module. No
finiteness hypothesis on `M` is imposed, the source needing none.

Faithfulness. (1) All three hypotheses are live. Nilpotency: for `R = ℤ`, `I = 2ℤ` and `M = ℚ`,
`M` is flat and `M/IM = 0` is projective over `ℤ ⧸ 2ℤ`, while `ℚ` is not projective over `ℤ`.
Flatness: for `R = k[x]/(x²)`, `I = (x)` and `M = k`, the reduction `M/IM = k` is projective over
`R ⧸ I = k`, but `M` is neither flat nor projective over `R`. Projectivity of the reduction: for
`I = 0` it is the conclusion itself, and `R = ℤ`, `M = ℚ` again shows flatness alone is not
enough. (2) The scalars are the source's: flatness and the conclusion are over `R`, and only the
reduction `M/IM` is a module over `R ⧸ I`. (3) The source names no canonical map — the content is
projectivity of `M` — but `M/IM` is pinned to `M ⧸ I • ⊤` with its canonical `R ⧸ I`-action rather
than to a module merely asserted to be a reduction of `M`. (4) A witness: `R = k[x]/(x²)`,
`I = (x)` and `M = R`, where `I` is nilpotent and nonzero, `M` is flat and `M/IM = k` is
projective over `R ⧸ I = k`; so the instantiation is not the degenerate `I = 0` or `M = 0` one.

## References

* [StackProject 05CG](https://stacks.math.columbia.edu/tag/05CG)

## Tags

projective module, flat module, nilpotent ideal
-/

@[expose] public section



/-- **Stacks 05CG.** Let `R` be a ring, let `I ⊆ R` be a nilpotent ideal and let `M` be a flat
`R`-module such that `M/IM` is a projective `R ⧸ I`-module. Then `M` is a projective
`R`-module. -/
@[stacks 05CG, sga "5 XV 3.Lemma3" "(ii) flat ⇒ projective"]
public theorem Module.Flat.projective_of_isNilpotent_of_projective_quotient_smul_top
    {R : Type u} [CommRing R] {I : Ideal R} {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Flat R M] (hI : IsNilpotent I)
    (hM : Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Projective R M := by exact Stacks.Projective.NilpotentDescent.solution (I := I) hI hM

end

/-!
# Flat, free and projective agree over a local ring with nilpotent maximal ideal

Let `(R, 𝔪)` be a local ring whose maximal ideal is nilpotent and let `M` be an `R`-module. This
file proves Stacks 051G: `M` is flat over `R` if and only if `M` is free if and only if `M` is
projective.

Two of the three implications hold over any ring and are instances in Mathlib: a free module is
projective, `Module.Projective.of_free`, and a projective module is flat,
`Module.Flat.of_projective` (a projective module is a direct summand of a free one, which is the
source's reason). The content is that a flat module is free, and it holds in the generality it has:
for a flat module `M` over any commutative ring and any nilpotent ideal `I`, freeness of `M`
descends from freeness of the reduction `M ⧸ IM` over `R ⧸ I`, since a family in `M` lifting a
basis of the reduction is already an `R`-basis of `M` by Stacks 051F,
`Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent`, which is where
nilpotence of `I` is spent. Locality of `R` enters only to make `R ⧸ 𝔪` a field, so that the
reduction, being a vector space, is free.

## Main results

* `Stacks.Projective.FlatImpliesFree.solution`: Stacks 051G, the `List.TFAE` of flatness, freeness
  and projectivity.

## Implementation notes

Flat implies free is the only implication with mathematical content; the other two are
`inferInstance`. It is split along its two hypotheses:
`Stacks.Projective.FlatImpliesFree.free_of_flat_of_isNilpotent_of_free_quotient` descends freeness
along the reduction map for an arbitrary nilpotent ideal of an arbitrary commutative ring, taking
flatness of `M` and freeness of the reduction as instance hypotheses, and
`Stacks.Projective.FlatImpliesFree.free_of_flat_of_isNilpotent_maximalIdeal` supplies the latter
over a local ring from the `Field` structure `Ideal.Quotient.field` on `R ⧸ 𝔪`, which is introduced
locally, Mathlib carrying it globally only on the type synonym `IsLocalRing.ResidueField R`.

Only the direction of 051F that has content is used. Its converse, that a basis of `M` reduces to a
basis of `M ⧸ IM`, needs neither flatness nor nilpotence, being a base change of a basis, so
descent of freeness is stated as an implication and not as an equivalence.

Lifting a basis of `M ⧸ IM` to a family in `M` uses only surjectivity of `Submodule.mkQ`, so that
family is not canonical and is obtained from a right inverse of that map.

## References

* [Stacks Project, Tag 051G](https://stacks.math.columbia.edu/tag/051G)
-/

@[expose] public section

namespace Stacks.Projective.FlatImpliesFree

/-- Freeness of a flat module descends along reduction modulo a nilpotent ideal: if `M` is a flat
module over a commutative ring `R`, if `I ⊆ R` is nilpotent and if the reduction `M ⧸ IM` is free
over `R ⧸ I`, then `M` is free over `R`.

A family in `M` lifting a basis of `M ⧸ IM` is an `R`-basis of `M` by Stacks 051F. -/
@[ega "0 10.1.2" "special case",
  sga "1 IV 4.1" "(a), special case",
  sga "3 VIII 6.2" "more general",
  sga "5 XV 3.Lemma3" "(ii), special case"]
private theorem free_of_flat_of_isNilpotent_of_free_quotient {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Flat R M] (I : Ideal R) (hI : IsNilpotent I)
    [Module.Free (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] : Module.Free R M := by
  obtain ⟨g, hg⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective.hasRightInverse
  let b := Module.Free.chooseBasis (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))
  obtain ⟨hli, hsp⟩ :=
    (Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent I hI (g ∘ b)).mp
      (by rw [show (I • (⊤ : Submodule R M)).mkQ ∘ (g ∘ b) = b from funext fun i => hg (b i)]
          exact ⟨b.linearIndependent, b.span_eq⟩)
  exact .of_basis (Module.Basis.mk hli hsp.ge)

/-- Over a local ring whose maximal ideal is nilpotent, every flat module is free: the residue
field makes the residual vector space `M ⧸ 𝔪M` free, and freeness descends.

This is the content of Stacks 051G; no finiteness hypothesis on `M` is needed, unlike in
`Module.free_of_flat_of_isLocalRing`. -/
@[ega "0 10.1.3" "(i): c ⇒ a, c ⇒ a",
  sga "1 IV 4.3" "case (a): (iii) ⇒ (i)",
  sga "3 VIB 6.2.2" "more general"]
private theorem free_of_flat_of_isNilpotent_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R)) : Module.Free R M := by
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  exact free_of_flat_of_isNilpotent_of_free_quotient _ hR

/-- Over a local ring whose maximal ideal is nilpotent, a module is flat if and only if it is
free if and only if it is projective. -/
public theorem solution {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (hR : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := by
  tfae_have 1 → 2 := fun _ => free_of_flat_of_isNilpotent_maximalIdeal hR
  tfae_have 2 → 3 := fun _ => inferInstance
  tfae_have 3 → 1 := fun _ => inferInstance
  tfae_finish

end Stacks.Projective.FlatImpliesFree

/-!
# Flat, free and projective modules over a local ring with nilpotent maximal ideal

Let `(R, 𝔪)` be a local ring whose maximal ideal is nilpotent — an Artinian local ring, for
instance. Then the three conditions "flat", "free" and "projective" on an `R`-module `M` agree,
with no finiteness hypothesis whatsoever on `M`: over such a ring flatness, the weakest of the
three, already produces a basis.

Two of the implications are formal and hold over any ring: a free module is projective, and a
projective module is flat, being a direct summand of a free one. The content is that a flat
module is free, and it is read off the residual vector space. The two hypotheses are spent in
different places: locality makes `R/𝔪` a field, so `M/𝔪M` is a vector space and has a basis,
and any family in `M` reducing to such a basis is already an `R`-basis of `M` by Lemma 051F,
which is where nilpotence of `𝔪` goes — that lemma holds for an arbitrary nilpotent ideal of an
arbitrary commutative ring, locality playing no part in it.

## Main results

* `Module.tfae_flat_free_projective_of_isNilpotent_maximalIdeal`: over a local ring with nilpotent
  maximal ideal, a module is flat if and only if it is free if and only if it is projective.

## Implementation notes

The equivalence is a `List.TFAE`, in the source's order — flat, free, projective — so that a user
recovers a single implication with `List.TFAE.out`, whose indices count from 1: `.out 1 2` is
"flat implies free", the content of the lemma, and `haveI` feeds it to instance search.
Its three entries are the `Prop`-valued classes `Module.Flat`, `Module.Free` and
`Module.Projective`, used here as propositions; `Module.Free R M` is Mathlib's reading of "`M` is
a free `R`-module", namely that `M` admits a basis indexed by some type, which is the source's
reading too.

Nilpotence of the maximal ideal is `IsNilpotent (IsLocalRing.maximalIdeal R)`, as in 051F: in the
monoid with zero `Ideal R` this says `𝔪 ^ n = ⊥` for some `n`. It is an explicit hypothesis rather
than an instance, matching 051F, since no class in Mathlib names it; the strictly stronger
`IsArtinianRing R` is deliberately not assumed, the source's remark that an Artinian local ring
has nilpotent maximal ideal being exactly what makes this the more useful form.

The Mathlib sibling is `Module.free_of_flat_of_isLocalRing`, which concludes `Module.Free R P`
from `Module.Finite R P` and `Module.Flat R P` over an arbitrary local ring. The statement below
trades that finiteness hypothesis for nilpotence of `𝔪`, and so is neither weaker nor stronger; it
is not obtained from the sibling by a limit argument but from 051F, the source's route.

Faithfulness. (1) Every hypothesis is used. Nilpotence of `𝔪`: over the discrete valuation ring
`ℤ_p`, local with `(p)` not nilpotent, `ℚ_p` is flat but neither free nor projective, so (1) holds
while (2) and (3) fail. Locality: over `k × k`, whose Jacobson radical is `⊥` and hence nilpotent,
`M = k × 0` is projective and flat, being a direct summand of `R`, but not free, so the variant of
the statement with `𝔪` replaced by a nilpotent Jacobson radical is false. (2) The scalars and base
are the source's: all three properties are asserted for `M` over `R` itself, no localization, no
completion and no base change to `R/𝔪` occurring in the statement — the residual vector space
`M/𝔪M` belongs to the proof, and to 051F. (3) The source names no canonical map here; what it does
pin, and what the statement pins, is that `𝔪` is `IsLocalRing.maximalIdeal R`, the unique maximal
ideal of the local ring `R`, not merely some maximal ideal, and that freeness means the existence
of a basis of `M` itself. The sharper statement, that a family lifting a basis of `M/𝔪M` *is* a
basis, is not folded in here: it is Lemma 051F, a separate tag, which this lemma consumes.
(4) The instantiation is not degenerate: `R = k[x]/(x ^ 2)` is local with `𝔪 ^ 2 = ⊥`, and there
`M = R` satisfies all three conditions while `M = R ⧸ (x)` satisfies none of them — it is not flat,
since tensoring `(x) ↪ R` with it kills the nonzero module `(x) ⊗_R M`. So the three properties are
each sometimes true and sometimes false over a ring satisfying the hypotheses.

## References

* [Stacks Project, Tag 051G](https://stacks.math.columbia.edu/tag/051G)
-/

namespace Module

/-- **Stacks 051G**: let `(R, 𝔪)` be a local ring whose maximal ideal is nilpotent — an Artinian
local ring, for instance — and let `M` be an `R`-module. Then `M` is flat over `R` if and only if
`M` is a free `R`-module if and only if `M` is a projective `R`-module. No finiteness hypothesis on
`M` is needed; compare `Module.free_of_flat_of_isLocalRing`, which assumes `Module.Finite R M` over
an arbitrary local ring, and `Module.Flat.projective_of_finitePresentation`. The proof is the
source's: a family of elements of `M` whose reductions form a basis of `M/𝔪M` over `R/𝔪` is a basis
of `M` over `R`, by Lemma 051F. -/
@[stacks 051G "The equivalence is a `List.TFAE` in the source's order (flat, free, projective);
nilpotence of the maximal ideal is `IsNilpotent (IsLocalRing.maximalIdeal R)`.",
  ega "0 10.1.3"
  "case (i)",
  sga "1 IV 4.3" "(i),(ii),(iii)",
  ega "0 10.1.3" "case (i)",
  ega "III 7.3.5" "commutative case",
  ega "IV 11.3.12" "special case",
  ega "IV 2.2.17" "special case",
  sga "3 VIA 2.1.3" "special case",
  sga "3 VIB 6.2.2" "more general",
  sga "3 VIIA 8.4" "partial",
  sga "3 VIIB 0.2.2" "special case",
  sga "3 VIIB 0.3.7" "local Artinian rings",
  sga "3 VIIB 1.2.1" "special case",
  sga "3 VIII 6.2" "more general"]
public theorem tfae_flat_free_projective_of_isNilpotent_maximalIdeal {R : Type*} [CommRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (hR : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] :=
      by apply Stacks.Projective.FlatImpliesFree.solution ; assumption

end Module
