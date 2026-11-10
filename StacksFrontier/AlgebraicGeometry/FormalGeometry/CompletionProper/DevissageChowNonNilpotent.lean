module

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Basic
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageContraction

/-!
# The ideal sheaf of the Chow step has no vanishing power

The last two results of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/DevissageContraction.lean` carry
an explicit hypothesis

  `∀ e, ℒ ᵉ⁺¹ ≠ ⊥`

on the ideal sheaf `ℒ` of the contracted scheme `V(𝒦)`. It is *not* a consequence of `ℒ ≠ ⊥`: an
ideal sheaf can be nonzero and nilpotent, as `(x) ⊆ 𝒪_{Spec k[x]/(x²)}` is. **This file discharges
it from the output of the Chow step of [Stacks, Tag 088C].**

## What the Chow step supplies

[Stacks, Tag 0200] is `AlgebraicGeometry.hasDenseChowModification`
(`StacksFrontier/AlgebraicGeometry/Segre/ChartSurjective.lean:465`), whose conclusion
`AlgebraicGeometry.HasDenseChowModification`
(`StacksFrontier/AlgebraicGeometry/ChowNoetherian/Basic.lean:93`) produces, besides the proper
surjective `π : X' ⟶ X` and the immersion into a projective space over the base, **an open
`U ⊆ X` with `Dense (U : Set X)` over which `π` is an isomorphism**. It produces no ideal sheaf:
the ideal sheaf `ℒ` of the source's argument is the one cutting out the complement of that dense
open, and the canonical such ideal sheaf is the vanishing ideal of the closed set `X \ U`, i.e. the
*reduced* induced structure on it, which is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`. So `ℒ = vanishingIdeal Uᶜ`, and the two
facts about it that the derivation uses are exactly the two the Chow step delivers: the support of
`ℒ` is `X \ U`, and `U` is dense (hence nonempty as soon as `X` is).

## Why no power of it vanishes

The support of an ideal sheaf is its zero locus, `V(ℒ)`, and the three facts

* `V(ℒ ᵉ⁺¹) = V(ℒ)` — a positive power has the same zero locus, Mathlib's
  `AlgebraicGeometry.Scheme.IdealSheafData.support_pow_succ`;
* `V(⊥) = X` — the zero ideal sheaf vanishes everywhere, Mathlib's
  `AlgebraicGeometry.Scheme.IdealSheafData.support_bot`;
* `V(vanishingIdeal Z) = Z` — Mathlib's
  `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`

settle it: if `ℒ ᵉ⁺¹ = ⊥` then `X \ U = V(ℒ) = V(ℒ ᵉ⁺¹) = X`, so `U = ∅`, contradicting density on
a nonempty scheme.

This is the minimal-primes argument of the informal proof, packaged. Affine-locally on
`U' = Spec R` the ideal `J = ℒ(U')` is radical, so it is an intersection of primes and therefore
contains the nilradical; `J ᵉ⁺¹ = 0` makes every element of `J` nilpotent, hence `J` is *contained*
in the nilradical, hence `J` is the nilradical and lies in every minimal prime, hence
`V(J) = Spec R`. That `V(J) = Spec R` is impossible is precisely density of `U`. Mathlib's
`support_pow_succ` and `support_bot` are the scheme-level form of the first and last steps, and no
Noetherian hypothesis is needed for the direction used here (`J ᵉ⁺¹ = 0 ⇒ J ⊆ nilradical` holds in
any commutative ring).

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_ne_bot_of_support_ne_top` — **the general
  fact.** An ideal sheaf whose zero locus is not the whole scheme has no vanishing positive power.
  `AlgebraicGeometry.Scheme.IdealSheafData.pow_ne_bot_of_support_ne_top` is the same with the
  exponent written as a nonzero natural number, and
  `AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_ne_bot_of_notMem_support` is the pointwise
  form: it is enough that `ℒ` fail to vanish at a single point.
* `AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_ne_bot_of_ne_bot_of_isReduced` — on a *reduced*
  scheme, `ℒ ≠ ⊥` does suffice. This is exactly where the gap between `ℒ ≠ ⊥` and
  `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` lives: the ambient scheme of the dévissage is not reduced, which is why the
  hypothesis has to come from the geometry rather than from nonvanishing.
* `AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot` and
  `AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot_of_dense` —
  **the hypothesis in the form the Chow step delivers it**: the reduced ideal sheaf of the
  complement of a dense open on a nonempty scheme has no vanishing positive power.
* `Stacks.Coherent.exists_pow_succ_ne_bot_of_hasDenseChowModification` — the Chow step with the
  ideal sheaf added to its output: from `AlgebraicGeometry.HasDenseChowModification f` on a
  nonempty `X` one gets the whole of [Stacks, Tag 0200] together with an ideal sheaf `ℒ` cutting
  out the complement of the dense open and satisfying `∀ e, ℒ ᵉ⁺¹ ≠ ⊥`.
* `Stacks.Coherent.isEquivalence_completionFunctor_pow_subscheme_of_lt_of_dense` and
  `Stacks.Coherent.essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel_of_dense` — **the
  two consumers with the hypothesis discharged.** They are
  `Stacks.Coherent.isEquivalence_completionFunctor_pow_subscheme_of_lt` and
  `Stacks.Coherent.essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel` with
  `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` replaced by a dense open of `V(𝒦)` and nonemptiness of `V(𝒦)`, and with `ℒ`
  specialized to the reduced ideal sheaf of its complement.

## Implementation notes

Nothing here is registered against a Stacks tag: like the contraction it sits inside, this is one
step of the proof of [Stacks, Tag 088C] and not a tag proved under its own hypotheses. The
stacks-0200 attribute stays on `AlgebraicGeometry.hasDenseChowModification`, which is the input
used below.

Nonemptiness of the scheme carrying `ℒ` is unavoidable, not an added hypothesis: on the empty
scheme every ideal sheaf is `⊥`, so `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` is false there, and the inductive step of
[Stacks, Tag 088C] disposes of `V(𝒦) = ∅` separately — the completion functor on the empty scheme
is an equivalence for want of anything to say. It is stated as `Nonempty` of the carrier, or as
nonemptiness of the dense open itself, which is the weaker of the two.

No local Noetherianity is used for the nonvanishing: the three support identities hold on an
arbitrary scheme. The hypothesis appears in the consumers only because the completion functor is
defined there, and on `V(𝒦)` it is supplied, as elsewhere in this directory, by
`AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion` through a `letI` in the statement.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### An ideal sheaf with a point outside its zero locus is not nilpotent -/

/-- **An ideal sheaf whose zero locus is not the whole scheme has no vanishing positive power.**

A positive power has the same zero locus as the ideal sheaf itself
(`AlgebraicGeometry.Scheme.IdealSheafData.support_pow_succ`), while the zero ideal sheaf vanishes
everywhere (`AlgebraicGeometry.Scheme.IdealSheafData.support_bot`); so a vanishing power would
force `V(ℒ) = X`.

Affine-locally this is the statement that an ideal `J` with `J ᵉ⁺¹ = 0` consists of nilpotents and
is therefore contained in — hence, when `J` is radical, equal to — the nilradical, so that `J` lies
in every minimal prime and `V(J)` is everything. -/
public theorem pow_succ_ne_bot_of_support_ne_top {L : X.IdealSheafData} (hL : L.support ≠ ⊤)
    (e : ℕ) : L ^ (e + 1) ≠ ⊥ := fun h =>
  hL (by rw [← support_pow_succ L e, h, support_bot])

/-- **An ideal sheaf whose zero locus is not the whole scheme has no vanishing positive power**,
with the exponent written as a nonzero natural number. -/
public theorem pow_ne_bot_of_support_ne_top {L : X.IdealSheafData} (hL : L.support ≠ ⊤) {n : ℕ}
    (hn : n ≠ 0) : L ^ n ≠ ⊥ := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact pow_succ_ne_bot_of_support_ne_top hL e

/-- **An ideal sheaf that fails to vanish at one point has no vanishing positive power.** The
pointwise form of `AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_ne_bot_of_support_ne_top`. -/
public theorem pow_succ_ne_bot_of_notMem_support {L : X.IdealSheafData} {x : X}
    (hx : x ∉ L.support) (e : ℕ) : L ^ (e + 1) ≠ ⊥ :=
  pow_succ_ne_bot_of_support_ne_top (fun h => hx (by rw [h]; trivial)) e

/-- **On a reduced scheme a nonzero ideal sheaf has no vanishing positive power.**

This is where the gap between `ℒ ≠ ⊥` and `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` lives. On a reduced scheme an ideal
sheaf with full zero locus is zero (`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`),
so the two are equivalent; on an arbitrary scheme they are not, `(x) ⊆ 𝒪_{Spec k[x]/(x²)}` being
nonzero with square zero. The ambient scheme of the dévissage of [Stacks, Tag 088C] is not
reduced, which is why the hypothesis there has to be read off the geometry of the Chow step
instead. -/
public theorem pow_succ_ne_bot_of_ne_bot_of_isReduced [IsReduced X] {L : X.IdealSheafData}
    (hL : L ≠ ⊥) (e : ℕ) : L ^ (e + 1) ≠ ⊥ :=
  pow_succ_ne_bot_of_support_ne_top (fun h => hL (support_eq_top_iff.mp h)) e

/-! ### The reduced complement of a dense open -/

/-- The zero locus of the reduced ideal sheaf of the complement of an open is that complement. -/
private theorem support_vanishingIdeal_compl (U : X.Opens) :
    (vanishingIdeal U.compl).support = U.compl :=
  TopologicalSpace.Closeds.ext (coe_support_vanishingIdeal U.compl)

/-- **The reduced ideal sheaf of the complement of a nonempty open has no vanishing positive
power.**

The zero locus of `vanishingIdeal Z` is `Z` itself
(`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`), so a point of `U` is a
point outside the zero locus. -/
public theorem pow_succ_vanishingIdeal_compl_ne_bot (U : X.Opens) (hU : (U : Set X).Nonempty)
    (e : ℕ) : vanishingIdeal U.compl ^ (e + 1) ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hU
  refine pow_succ_ne_bot_of_notMem_support (x := x) ?_ e
  rw [support_vanishingIdeal_compl]
  exact fun hmem => hmem hx

/-- **The reduced ideal sheaf of the complement of a dense open on a nonempty scheme has no
vanishing positive power.**

This is the hypothesis `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` of the `V(𝒦)` contraction of [Stacks, Tag 088C], in the
form in which the Chow step of the source supplies it: `ℒ` cuts out the reduced complement of the
dense open over which the Chow modification is an isomorphism. A dense subset of a nonempty space
is nonempty. -/
public theorem pow_succ_vanishingIdeal_compl_ne_bot_of_dense [Nonempty X] (U : X.Opens)
    (hU : Dense (U : Set X)) (e : ℕ) : vanishingIdeal U.compl ^ (e + 1) ≠ ⊥ :=
  pow_succ_vanishingIdeal_compl_ne_bot U hU.nonempty e

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Coherent

/-! ### The Chow step, with the ideal sheaf and its nonvanishing -/

/-- **Chow's lemma with the ideal sheaf of the source's argument added to its output.**

Let `f : X ⟶ S` be a morphism with a dense Chow modification — by [Stacks, Tag 0200],
`AlgebraicGeometry.hasDenseChowModification`, any separated morphism of finite type over a
Noetherian base — and let `X` be nonempty. Then there are a proper surjective `π : X' ⟶ X`, an
immersion `i : X' ⟶ 𝐏ⁿ_S` over `S`, a dense open `U ⊆ X` over which `π` is an isomorphism, **and a
quasi-coherent ideal sheaf `ℒ ⊆ 𝒪_X` whose zero locus is `X \ U` and no positive power of which
is zero**.

This is what the dévissage of [Stacks, Tag 088C] takes from the Chow step: the ideal sheaf is the
vanishing ideal of the closed complement of `U`, i.e. the reduced induced structure on it, and its
non-nilpotence is
`AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot_of_dense`.
Nonemptiness of `X` is needed and cannot be dropped: on the empty scheme every ideal sheaf is
`⊥`. -/
public theorem exists_pow_succ_ne_bot_of_hasDenseChowModification {X S : Scheme.{u}} [Nonempty X]
    (f : X ⟶ S) (h : HasDenseChowModification f) :
    ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S) (U : X.Opens)
      (L : X.IdealSheafData),
      IsProper π ∧ Surjective π ∧ IsImmersion i ∧
        π ≫ f = i ≫ (ProjectiveSpace n S ↘ S) ∧ Dense (U : Set X) ∧ IsIso (π ∣_ U) ∧
          L.support = U.compl ∧ ∀ e : ℕ, L ^ (e + 1) ≠ ⊥ := by
  obtain ⟨n, X', π, i, U, hπ, hsurj, himm, hcomm, hdense, hiso⟩ := h
  exact ⟨n, X', π, i, U, Scheme.IdealSheafData.vanishingIdeal U.compl, hπ, hsurj, himm, hcomm,
    hdense, hiso,
    Scheme.IdealSheafData.support_vanishingIdeal_compl U,
    fun e => Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot_of_dense U hdense e⟩

/-! ### The two consumers with the hypothesis discharged -/

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData)

/-- **Hypothesis (1) of [Stacks, Tag 088A] on the contracted scheme, from the induction hypothesis
of [Stacks, Tag 088C] on the ambient one and a dense open of the contracted one.**

This is `Stacks.Coherent.isEquivalence_completionFunctor_pow_subscheme_of_lt` with its hypothesis
`∀ e, ℒ ᵉ⁺¹ ≠ ⊥` discharged: `ℒ` is taken to be the reduced ideal sheaf of the complement of a
dense open `U` of `V(𝒦)`, which is what the Chow step of the source produces, and the
nonvanishing of its powers is then
`AlgebraicGeometry.Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot`. Only nonemptiness
of `U` is asked, which density gives as soon as `V(𝒦)` is nonempty. -/
public theorem isEquivalence_completionFunctor_pow_subscheme_of_lt_of_dense
    (hff : (completionFunctor X I).FullyFaithful)
    (hIH : ∀ K' : X.IdealSheafData, K < K' → ∀ 𝓖 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy K' 𝓖.obj → (completionFunctor X I).essImage 𝓖) :
    letI : IsLocallyNoetherian K.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion K.subschemeι
    ∀ U : K.subscheme.Opens, (U : Set K.subscheme).Nonempty → ∀ e : ℕ,
      letI : IsLocallyNoetherian
          (Scheme.IdealSheafData.vanishingIdeal U.compl ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian
          (Scheme.IdealSheafData.vanishingIdeal U.compl ^ (e + 1)).subschemeι
      (completionFunctor (Scheme.IdealSheafData.vanishingIdeal U.compl ^ (e + 1)).subscheme
        ((I.comap K.subschemeι).comap
          (Scheme.IdealSheafData.vanishingIdeal U.compl ^ (e + 1)).subschemeι)).IsEquivalence :=
  let : IsLocallyNoetherian K.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion K.subschemeι
  fun U hU => isEquivalence_completionFunctor_pow_subscheme_of_lt I K hff hIH
    (Scheme.IdealSheafData.vanishingIdeal U.compl)
    (Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot U hU)

/-- **[Stacks, Tag 088A] on the contracted scheme, with hypothesis (1) discharged by the induction
hypothesis of [Stacks, Tag 088C] and the Chow step.**

This is `Stacks.Coherent.essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel` with its
hypothesis `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` discharged, `ℒ` being the reduced ideal sheaf of the complement of a
nonempty — in the application, dense — open `U` of `V(𝒦)`. Only hypothesis (2) of
[Stacks, Tag 088A], the map `α` of [Stacks, Tag 088B], is left as an input. -/
public theorem essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel_of_dense
    [IsNoetherian X] (hff : (completionFunctor X I).FullyFaithful)
    (hIH : ∀ K' : X.IdealSheafData, K < K' → ∀ 𝓖 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy K' 𝓖.obj → (completionFunctor X I).essImage 𝓖) :
    letI : IsLocallyNoetherian K.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion K.subschemeι
    letI : CompactSpace K.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace K.subschemeι
    letI : IsNoetherian K.subscheme := { }
    ∀ U : K.subscheme.Opens, (U : Set K.subscheme).Nonempty →
      ∀ 𝓕 : CoherentAdicSystems (I.comap K.subschemeι),
        ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules K.subscheme.ringCatSheaf,
          ∀ α : 𝓕 ⟶ (completionFunctor K.subscheme (I.comap K.subschemeι)).obj H,
            IsKernelCokernelAnnihilatedByPower
                (Scheme.IdealSheafData.vanishingIdeal U.compl) α.hom →
              (completionFunctor K.subscheme (I.comap K.subschemeι)).essImage 𝓕 :=
  let : IsLocallyNoetherian K.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion K.subschemeι
  let : CompactSpace K.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace K.subschemeι
  let : IsNoetherian K.subscheme := { }
  fun U hU => essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel I K hff hIH
    (Scheme.IdealSheafData.vanishingIdeal U.compl)
    (Scheme.IdealSheafData.pow_succ_vanishingIdeal_compl_ne_bot U hU)

end

end Stacks.Coherent

end
