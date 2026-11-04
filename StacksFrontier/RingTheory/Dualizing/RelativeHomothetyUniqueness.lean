module

public import StacksFrontier.RingTheory.Dualizing.RelativeExistenceInputs
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothety

/-!
# The derived endomorphisms of a relative dualizing complex, from uniqueness

Let `R → A` be a flat ring map of finite presentation and let `K` be a relative dualizing complex
for `R → A` in the sense of [stacks 0E2C].  [stacks 0E2G] asserts that `A ⟶ RHom_A(K, K)` is an
isomorphism.  This file states that conclusion for **every** relative dualizing complex, over a
Noetherian base, with the two inputs the source's own proof uses named as hypotheses in their own
terms.  These statements are superseded and are not registered under the tag: [stacks 0E2G] in
full, over an arbitrary base and with nothing carried, is
`Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex` of
`StacksFrontier.RingTheory.Dualizing.RelativeHomothetyGeneral`.  The two inputs are the uniqueness of
relative dualizing complexes, which is [stacks 0E2D], and the library's standing open input for the
upper shriek formalism, through which [stacks 0E2E] identifies `ω_{A/R} = φ^!(R)` as a relative
dualizing complex.

## What this adds to `StacksFrontier.RingTheory.Dualizing.RelativeHomothety`

`Dualizing.PolynomialPresentation.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_flat`
is the same conclusion, and it carries three things: a choice of polynomial presentation `p` of
`A` over `R`, the projection-formula compatibility of [stacks 0E2A] at *that* presentation as the
two hypotheses `hProjFib` and `hProjSelf`, and the hypothesis `hdiag` of [stacks 0E2D] at the pair
`(K, φ^!(R))` — the invertibility of two tensor--Hom diagonals of [stacks 0BYN], which is a
statement about the derived base changes of `K` and of `φ^!(R)` along the left coprojection
`A → A ⊗[R] A` rather than about relative dualizing complexes.

Each of those three is replaced here:

* the presentation is produced internally by `Dualizing.nonempty_polynomialPresentation`, a map of
  finite presentation being in particular of finite type, so no choice of `p` is a hypothesis;
* `hProjFib` and `hProjSelf` become the single standing bundle `Dualizing.UpperShriekInputs`,
  quantified over every presentation and every target ring, which is the form in which the rest of
  the library carries this input — and `Dualizing.KFlatAlgebraActionEq` in the second statement,
  which is the one keystone that bundle reduces to;
* `hdiag` becomes `huniq`, which is the statement of [stacks 0E2D] itself.

The exchange of `hdiag` for `huniq` is not a weakening in the logical sense and is not claimed to
be one: `hdiag` is read at a single pair, while `huniq` is quantified over all pairs, and
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex` turns the former into the latter only at
that pair.  What it buys is that the carried hypothesis is a named tag of the source — the very
tag whose proof `hdiag` exists to complete — instead of a technical condition on the two
tensor--Hom diagonals of [stacks 0BYN] at the derived base changes along the left coprojection.
That makes the dependency of this tag on [stacks 0E2D] a theorem of the library rather than a
remark, which is the point of this file; and it is the dependency the source itself has.

How little that dependency is, is isolated in
`Dualizing.isIso_relativeHomothety_of_nonempty_iso_upperShriekFunctor_unit` below: given only an
isomorphism `K ≅ ω_{A/R}`, the conclusion of the tag at `K` costs **nothing** further — not the
projection-formula input, not even the hypothesis that `K` is a relative dualizing complex.  So
the whole residue of the tag over a Noetherian base is the production of that isomorphism, which
is [stacks 0E2D] applied to `K` and `ω_{A/R}`, and `hUS` is needed only to know that `ω_{A/R}` is
a relative dualizing complex so that [stacks 0E2D] applies to it — which is [stacks 0E2E].

The hypothesis `[IsNoetherianRing A]` is dropped as well: over a Noetherian `R` a map of finite
type has Noetherian target.

## Why the base is Noetherian here

The reference object is `ω_{A/R} = φ^!(R)`, which is available only over a Noetherian base.  The
passage to an arbitrary base — spreading out by [stacks 02JO], passing to the filtered colimit of
the finitely generated subalgebras by [stacks 0DHX] through the self-extensions of the stages, and
identifying `K` with the colimit object by [stacks 0E2D] — is carried out in
`StacksFrontier.RingTheory.Dualizing.RelativeHomothetyGeneral`.

## The dependency on [stacks 0E2D] is not an artefact of this library

[stacks 0E2G] is proved in the source *from* [stacks 0E2D], at both steps of its proof: the
reduction to a Noetherian base needs uniqueness to descend the complex, and over the Noetherian
base uniqueness is what identifies the given `K` with `φ^!(R)` before [stacks 0BZW] is applied.
So the asymmetry between the two hypotheses of
`Dualizing.isIso_derivedHomothety_of_isRelativeDualizingComplex` is real — at the canonical
`ω_{A/R}` the invertibility `hhom` is a theorem, by [stacks 0BZW] (1)(c), with nothing carried —
but it does not yield this tag on its own: transporting invertibility from `ω_{A/R}` to an
arbitrary `K` is transport along an isomorphism `K ≅ ω_{A/R}`, and producing one is exactly
[stacks 0E2D].  A transport not going through uniqueness would need `End_{D(A)}(K) = A` from the
defining condition of [stacks 0E2C] alone; the documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeEndomorphisms` records what that would take, and that
the defining condition computes morphisms *out of* the diagonal where the tag is about the
morphisms *into* it.

## Main results

* `Dualizing.isIso_relativeHomothety_of_nonempty_iso_upperShriekFunctor_unit` — the conclusion of
  the tag at any object isomorphic to `ω_{A/R} = φ^!(R)`, over a flat map of finite type of a
  Noetherian base, **carrying nothing**.  This is not the tag: it assumes an identification in
  place of the tag's hypothesis, and it is the component the two statements below use.
* `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_nonempty_iso` — the
  conclusion of [stacks 0E2G] for every relative dualizing complex of a flat map of finite
  presentation over a Noetherian base, carrying the uniqueness of [stacks 0E2D] and the standing
  bundle `Dualizing.UpperShriekInputs`.
* `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_kFlatAlgebraActionEq` — the
  same with the bundle replaced by the single keystone `Dualizing.KFlatAlgebraActionEq`.

## References

* [Stacks Project, Tag 0E2G](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
-/

@[expose] public section

open CategoryTheory

namespace Dualizing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

noncomputable section

/-- **The conclusion of [stacks 0E2G] at anything isomorphic to `ω_{A/R} = φ^!(R)`, carrying
nothing.**  Let `R → A` be flat of finite type with `R` Noetherian, presented by `p`, and let `K`
be an object of `D(A)` isomorphic to `φ^!(R)`.  Then `A ⟶ RHom_A(K, K)` is an isomorphism.

This is *not* the tag: it assumes an identification of `K` with the canonical object in place of
the tag's hypothesis that `K` is a relative dualizing complex, and it does not assert that
`φ^!(R)` is one.  It is recorded separately because it isolates how little the tag needs beyond
unconditional results over a Noetherian base.  Invertibility at `φ^!(R)` is [stacks 0BZW] (1)(c),
`Dualizing.PolynomialPresentation.isIso_relativeHomothety_relativeDualizingComplex`, whose
perfectness hypothesis is discharged from flatness by part (2) of that tag; the transport is
`Dualizing.isIso_relativeHomothety_iff_of_iso`.  Nothing else enters — in particular neither the
projection-formula compatibility of [stacks 0E2A] nor any hypothesis on the tensor--Hom diagonals
of [stacks 0BYN].

So over a Noetherian base the entire residue of [stacks 0E2G] is the production of the
isomorphism `K ≅ φ^!(R)`, which is [stacks 0E2D] at that pair. -/
theorem isIso_relativeHomothety_of_nonempty_iso_upperShriekFunctor_unit (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) (K : DerivedCategory (ModuleCat.{u} A))
    (hiso : Nonempty (K ≅ p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :
    IsIso (relativeHomothety A K) :=
  (isIso_relativeHomothety_iff_of_iso A hiso.some).2
    (PolynomialPresentation.isIso_relativeHomothety_relativeDualizingComplex R A p)

/-- **The conclusion of [stacks 0E2G] over a Noetherian base, from the uniqueness of relative
dualizing complexes.**  Superseded by
`Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex`, which carries nothing; kept
unregistered.  Let `R → A` be a flat ring map of finite presentation with `R` Noetherian, and let
`K` be a relative dualizing complex for `R → A`.  If any two relative dualizing complexes for
`R → A` are isomorphic — which is [stacks 0E2D], here the hypothesis `huniq` — then the canonical
map `A ⟶ RHom_A(K, K)` is an isomorphism.

The reference object is `ω_{A/R} = φ^!(R)` for a presentation produced internally.  That the
homothety is invertible there is [stacks 0BZW] (1)(c) and carries nothing, and that `ω_{A/R}` is a
relative dualizing complex in the sense of [stacks 0E2C] is [stacks 0E2E], which carries the
projection-formula compatibility of [stacks 0E2A] at the presentation square; `hUS` is the
library's standing bundle of that input, quantified over every presentation and every target ring.
Neither `huniq` nor `hUS` mentions the conclusion: the first says two relative dualizing complexes
are isomorphic and says nothing about derived endomorphisms, the second is a property of the
Tor-independent square of a presentation alone.

See this module's documentation for why the dependency on [stacks 0E2D] is the source's own and
for what dropping the Noetherian hypothesis would need. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_nonempty_iso
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing R] (hUS : UpperShriekInputs.{u})
    (huniq : ∀ K L : DerivedCategory (ModuleCat.{u} A),
      IsRelativeDualizingComplex R A K → IsRelativeDualizingComplex R A L → Nonempty (K ≅ L))
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K) :
    IsIso (relativeHomothety A K) := by
  classical
  obtain ⟨-, hProj⟩ := hUS
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hflat : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hfin : (algebraMap R A).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨p⟩ := nonempty_polynomialPresentation (algebraMap R A) hfin
  exact isIso_relativeHomothety_of_nonempty_iso_upperShriekFunctor_unit R A p K
    (huniq K _ hK (p.relativeDualizingComplex_isRelativeDualizingComplex_of_flat hflat
      (fun t => hProj R A p t.asIdeal.ResidueField) (hProj R A p A)))

/-- **The conclusion of [stacks 0E2G] over a Noetherian base, from uniqueness, over the one
keystone.**  Superseded by `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex`; kept
unregistered.  This is
`Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_nonempty_iso` with the bundle
`Dualizing.UpperShriekInputs` replaced by `Dualizing.KFlatAlgebraActionEq`, the
projection-formula compatibility of [stacks 0E2A] at an arbitrary Tor-independent square, which
supplies the bundle by `Dualizing.upperShriekInputs_of_kFlatAlgebraActionEq`.

So over a Noetherian base the tag costs exactly two named statements, neither of them about
derived endomorphisms: the keystone `hAct`, an equality of two natural transformations attached to
a Tor-independent square of rings, and the uniqueness `huniq` of [stacks 0E2D]. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_kFlatAlgebraActionEq
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing R] (hAct : KFlatAlgebraActionEq.{u})
    (huniq : ∀ K L : DerivedCategory (ModuleCat.{u} A),
      IsRelativeDualizingComplex R A K → IsRelativeDualizingComplex R A L → Nonempty (K ≅ L))
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K) :
    IsIso (relativeHomothety A K) :=
  isIso_relativeHomothety_of_isRelativeDualizingComplex_of_nonempty_iso R A
    (upperShriekInputs_of_kFlatAlgebraActionEq hAct) huniq K hK

end

end Dualizing

end
