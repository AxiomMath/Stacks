module

public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.DiagonalChartPresentation.Basic

/-!
# Transporting `Ideal.Cotangent` along a ring isomorphism, and the chart's `I ⧸ I²`

For `f : X ⟶ S`, an affine open `V` of `S` and an affine open `U ≤ f ⁻¹ᵁ V` of `X`,
`StacksFrontier.AlgebraicGeometry.DiagonalChartPresentation.Basic` identifies the ring of
sections of the ambient chart of the diagonal with the tensor square,

  `Stacks.DiagonalChart.tensorIsoChart : A ⊗[R] A ≅ Γ(X ×_S X, ambientChart f U)`
  (`R = Γ(S, V)`, `A = Γ(X, U)`),

and matches the two ideals across it: `Stacks.DiagonalChart.kaehlerIdeal_eq_comap_ker_diagAppLE`
says Mathlib's Kähler ideal is the comap of `RingHom.ker (Stacks.DiagonalChart.diagAppLE f U)`,
the ideal of the diagonal in the chart. What was missing was the induced isomorphism of the two
*conormal modules* `I ⧸ I²`, which is what turns the chart's `I ⧸ I²` into `Ω[A⁄R]`. This file
supplies it, with its generator formula.

## The absence claim this file refutes

The "What is not done" section of
`StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic` records:

> Mathlib has `Ideal.Cotangent.equivOfEq`, for two *equal* ideals of one ring, and
> no transport along a ring isomorphism matching a pair of ideals; that
> lemma is still owed

and the "What is not done" section of
`StacksFrontier.AlgebraicGeometry.DiagonalChartPresentation.Basic` records the same thing in the
words "Mathlib has no transport of `Ideal.Cotangent` along a ring isomorphism matching a pair of
ideals at this pin, so that is a lemma to be written rather than cited."

**Both are false at this pin.** Mathlib has

* `Ideal.mapCotangent (I₁ : Ideal A) (I₂ : Ideal B) (f : A →ₐ[R] B) (h : I₁ ≤ I₂.comap f) :`
  `I₁.Cotangent →ₗ[R] I₂.Cotangent`
  (`Mathlib/RingTheory/Ideal/Cotangent.lean`), the transport along *any* algebra map carrying
  one ideal into the other — not merely an isomorphism;
* `Ideal.mapCotangent_toCotangent`, its generator formula, which holds by `rfl`: the transport
  sends `I₁.toCotangent x` to `I₂.toCotangent ⟨f x, _⟩`;
* `Ideal.mapCotangent_surjective_of_comap_eq` and `Ideal.mapCotangent_ker_of_surjective`, which
  are surjectivity and the kernel under `Function.Surjective (algebraMap A B)` together with
  `I.comap (algebraMap A B) = RingHom.ker (algebraMap A B) ⊔ J`.

So nothing had to be written: for a *bijective* `algebraMap` the kernel hypothesis collapses to
`⊥ ⊔ J = J` and the kernel of the transport to `⊥`, and `bijective_mapCotangent` below is six
lines of bookkeeping over those three cited lemmas. `Ideal.Cotangent.equivOfEq` was the wrong
search target; `Ideal.mapCotangent` is stated for a map of *different* rings from the start.

## Main definitions

* `Stacks.DiagonalCotangentTransport.cotangentEquiv`: the transport as a linear equivalence
  `J.Cotangent ≃ₗ[A] I.Cotangent`, for `algebraMap A B` bijective and `I.comap (algebraMap A B)`
  equal to `J`.

## Main results

* `Stacks.DiagonalCotangentTransport.bijective_mapCotangent`: `Ideal.mapCotangent` is bijective
  when `algebraMap A B` is bijective and the two ideals correspond.
* `Stacks.DiagonalCotangentTransport.cotangentEquiv_toCotangent`: its generator formula.
* `Stacks.DiagonalCotangentTransport.exists_addEquiv_kaehlerCotangentChart`: **the chart's
  `I ⧸ I²` is `Ω[Γ(X, U)⁄Γ(S, V)]`, with the generator formula of [Stacks, Tag 08S2].** The
  isomorphism carries `d b` to the class of the section `p₂^♯ b - p₁^♯ b` of the ambient chart.

## Why this is not a clause of [Stacks, Tag 08S2]

**No `stacks` attribute is attached, and the reason is not caution.** Everything here is a
statement about *rings of sections* and ideals inside them: no sheaf, no module pullback and no
`Stacks.Conormal.conormalSheaf` occurs. The two labelled assertions of [Stacks, Tag 08S2] are about
the comparison `Scheme.Hom.relativeDifferentials f ≅`
`Stacks.Conormal.conormalSheaf (pullback.diagonal f)`
and about its hom on sections, and the single statement separating
`StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine` from the statement is
`IsIso (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV)`. This file is one of the two
halves that statement factors into, and it is the *ring-level* half.

The other half — a generator formula for
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`, identifying the conormal
*sections* over the chart with the chart's `I ⧸ I²` compatibly with
`Stacks.Conormal.conormalQuotientMap` — is untouched here and remains open. With
it, `Stacks.LeibnizDerivation.existsUnique_affineConormalIsoKaehler_iff_isIso` proves the statement;
without it, the composite of that formula-free isomorphism with the equivalence below is an
*abstract* isomorphism `Γ(C_Δ, U) ≅ Ω[Γ(X, U)⁄Γ(S, V)]`, which says nothing about the particular
map `kaehlerToConormal`.

## Universe situation

A single universe `u`, as in the statements of the tag: `Ideal.Cotangent` of an ideal of a ring in
`Type u` is again in `Type u`, so the ring-level statements stay in one universe.

## Vocabulary

No existing declaration is restated here.

Nothing is Noetherian, finite, separated or quasi-compact; `f` is an arbitrary morphism of
schemes, and affineness of `U` and `V` enters only through
`Stacks.DiagonalChart.tensorIsoChart`.

## Transparency gotchas

`Ω[A⁄R]` is a `def` whose body is `(KaehlerDifferential.ideal R A).Cotangent`, not an `abbrev`,
so the two spellings unify at default transparency but are not syntactically equal. The
existence statement below is therefore phrased at the `Ω[A⁄R]` spelling and discharged by
`exact`, which elaborates at default transparency; `refine ⟨_, _⟩` against the
`(…).Cotangent` spelling of the witness reports a type mismatch between two displays of the
same type.

The membership proofs appearing in the generator formulas are taken as *arguments* rather than
constructed in the statement. Proof irrelevance then makes the formula usable against whichever
membership proof the caller happens to hold — which matters because
`Stacks.DiagonalConormal.one_tmul_sub_tmul_one_mem_ker` and
`KaehlerDifferential.one_smul_sub_smul_one_mem_ideal` are different terms of the same
proposition, and `Ideal.mapCotangent`'s own containment argument is a third.

`Ideal.mapCotangent_surjective_of_comap_eq` and `Ideal.mapCotangent_ker_of_surjective` state
their conclusions about `Ideal.mapCotangent J I (Algebra.ofId A B) h'` for their own `h'`, which
is not the `h` passed in below; the two are identified by proof irrelevance and no transport is
needed.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.DiagonalCotangentTransport

/-! ### The transport of `Ideal.Cotangent` along a bijective algebra map -/

section Ring

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **`Ideal.mapCotangent` is bijective when `algebraMap A B` is.** For a bijective
`algebraMap A B` and ideals `J` of `A` and `I` of `B` with `J` the comap of `I`, the transport
`J ⧸ J² ⟶ I ⧸ I²` is bijective.

Surjectivity is `Ideal.mapCotangent_surjective_of_comap_eq` and injectivity is
`Ideal.mapCotangent_ker_of_surjective`, both of which ask for the comap of `I` to be
`RingHom.ker (algebraMap A B) ⊔ J`; the kernel is `⊥` by injectivity, so that hypothesis is the
given one. -/
theorem bijective_mapCotangent (hbij : Function.Bijective (algebraMap A B))
    (J : Ideal A) (I : Ideal B) (hJI : Ideal.comap (algebraMap A B) I = J)
    (h : J ≤ Ideal.comap (algebraMap A B) I) :
    Function.Bijective (Ideal.mapCotangent J I (Algebra.ofId A B) h) := by
  have hker : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 hbij.1
  have heq : Ideal.comap (algebraMap A B) I = RingHom.ker (algebraMap A B) ⊔ J := by
    rw [hker, bot_sup_eq]
    exact hJI
  refine ⟨?_, Ideal.mapCotangent_surjective_of_comap_eq hbij.2 heq⟩
  rw [← LinearMap.ker_eq_bot, Ideal.mapCotangent_ker_of_surjective hbij.2 heq, hker, bot_inf_eq]
  simp

/-- **The transport of `Ideal.Cotangent` along a bijective algebra map**, as a linear
equivalence. -/
noncomputable def cotangentEquiv (hbij : Function.Bijective (algebraMap A B))
    (J : Ideal A) (I : Ideal B) (hJI : Ideal.comap (algebraMap A B) I = J)
    (h : J ≤ Ideal.comap (algebraMap A B) I) :
    J.Cotangent ≃ₗ[A] I.Cotangent :=
  LinearEquiv.ofBijective _ (bijective_mapCotangent hbij J I hJI h)

/-- **The generator formula for `cotangentEquiv`:** it carries the class of `x` to the class of
`algebraMap A B x`. This is `Ideal.mapCotangent_toCotangent`, which holds by `rfl`. -/
theorem cotangentEquiv_toCotangent (hbij : Function.Bijective (algebraMap A B))
    (J : Ideal A) (I : Ideal B) (hJI : Ideal.comap (algebraMap A B) I = J)
    (h : J ≤ Ideal.comap (algebraMap A B) I) (x : A) (hx : x ∈ J)
    (hy : algebraMap A B x ∈ I) :
    cotangentEquiv hbij J I hJI h (J.toCotangent ⟨x, hx⟩) =
      I.toCotangent ⟨algebraMap A B x, hy⟩ :=
  rfl

end Ring

/-! ### The chart's `I ⧸ I²` is `Ω[Γ(X, U)⁄Γ(S, V)]` -/

section Chart

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
  [Algebra Γ(S, V) Γ(X, U)]
  (halg : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)) = f.appLE V U hUV)
  (hV : IsAffineOpen V) (hU : IsAffineOpen U)

include hUV halg hV hU in
/-- **The conormal module of the ideal of the diagonal in the ambient chart is
`Ω[Γ(X, U)⁄Γ(S, V)]`, and the identification carries `d b` to the class of
`p₂^♯ b - p₁^♯ b`.**

This is `cotangentEquiv` across `Stacks.DiagonalChart.tensorIsoChart`, whose two ideals are
matched by `Stacks.DiagonalChart.kaehlerIdeal_eq_comap_ker_diagAppLE`. The generator formula is
`cotangentEquiv_toCotangent` applied to `1 ⊗ b - b ⊗ 1`, whose class on the left is `d b` by
`Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one` and whose image on the right is the
section `p₂^♯ b - p₁^♯ b` by `Stacks.DiagonalChart.tensorIsoChart_one_tmul_sub_tmul_one`.

The equivalence is stated additively because its two sides are modules over the two *different*
rings `Γ(X, U) ⊗[Γ(S, V)] Γ(X, U)` and `Γ(X ×_S X, ambientChart f U)`; `cotangentEquiv` is
linear over the first of them, and that is the form to use when linearity is needed. -/
theorem exists_addEquiv_kaehlerCotangentChart :
    ∃ g : Ω[Γ(X, U)⁄Γ(S, V)] ≃+
        (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).Cotangent,
      ∀ (b : Γ(X, U))
        (hy : ((pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
                (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U)).hom b -
              ((pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
                (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)).hom b ∈
            RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom),
        g (KaehlerDifferential.D Γ(S, V) Γ(X, U) b) =
          (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).toCotangent ⟨_, hy⟩ := by
  let _inst : Algebra ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U))
      Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) :=
    RingHom.toAlgebra (Stacks.DiagonalChart.tensorIsoChart f V U hUV halg hV hU).hom.hom
  have hbij : Function.Bijective
      (algebraMap ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U))
        Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U)) :=
    ConcreteCategory.bijective_of_isIso
      (Stacks.DiagonalChart.tensorIsoChart f V U hUV halg hV hU).hom
  have hJI : Ideal.comap
        (algebraMap ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U))
          Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U))
        (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom) =
      KaehlerDifferential.ideal Γ(S, V) Γ(X, U) :=
    (Stacks.DiagonalChart.kaehlerIdeal_eq_comap_ker_diagAppLE f V U hUV halg hV hU).symm
  refine ⟨(cotangentEquiv hbij _ _ hJI hJI.ge).toAddEquiv, fun b hy => ?_⟩
  have key := Stacks.DiagonalChart.tensorIsoChart_one_tmul_sub_tmul_one f V U hUV halg hV hU b
  refine Eq.trans (congrArg (cotangentEquiv hbij _ _ hJI hJI.ge)
    (Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one Γ(S, V) Γ(X, U) b).symm) ?_
  exact (cotangentEquiv_toCotangent hbij _ _ hJI hJI.ge _
    (Stacks.DiagonalConormal.one_tmul_sub_tmul_one_mem_ker Γ(S, V) Γ(X, U) b) (key ▸ hy)).trans
    (congrArg _ (Subtype.ext key))

end Chart

end Stacks.DiagonalCotangentTransport

end
