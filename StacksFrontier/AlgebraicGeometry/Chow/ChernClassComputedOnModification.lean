module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyFunctoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a perfect object, computed on a modification

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be
locally of finite type over `S`, and let `E` be a perfect object of `D(𝒪_X)` whose Chern classes
are defined in the sense of Stacks 0F9E (1) — that is, some envelope `f : Y ⟶ X` has `Lf^*E`
isomorphic to a locally bounded complex `ℰ_Y^•` of finite locally free `𝒪_Y`-modules, which is
the datum `Stacks.Chow.EnvelopePresentation`.

**Stacks 0GUF** says that for `g : W ⟶ X` locally of finite type with `W` integral there is a
proper birational `b : W' ⟶ W` with `W'` integral, such that, writing `g' = g ∘ b`, the object
`L(g')^*E` is represented by a *bounded* complex of locally free modules of constant rank, and

  `res(c_p(E)) = c_p(ℰ^•)` in `A^p(W')`.

The geometric half of that statement — the existence of `W'` and of the factorization
`b ≫ g = a ≫ f` through the envelope — is
`AlgebraicGeometry.IsEnvelope.exists_properBirational_modification` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.BirationalModification`. This file
supplies the **characteristic class clause**, which that file explicitly leaves out.

The source compresses the clause into one sentence, "by construction its `p`th chern class gives
the restriction of `c_p(E)` by `W' → X`". Expanded, and using `g' = a ≫ f` for the lift
`a : W' ⟶ Y` produced with the modification, it is the chain

  `res_{g'}(c_p(E)) = res_a(res_f(c_p(E))) = res_a(c_p(ℰ_Y^•)) = c_p(a^*ℰ_Y^•)`,

whose three steps are, in order: the composition law for the restriction map on Chow cohomology,
`Stacks.Chow.chowCohomologyRestriction_comp`; the defining property of the Chern classes of `E`
relative to the presentation; and the base change compatibility of the characteristic class data,
`Stacks.Chow.PowerSumClassRule.IsBaseChangeCompatible`.

## Main results

* `Stacks.Chow.powerSumClass_eq_of_envelopePresentation_modification` — **Stacks 0GUF, the clause
  for the power sums.** For a family `c` restricting to `P_p(ℰ_Y^•)` along the envelope, the
  restriction of `c p` along `a ≫ f` is `P_p(a^*ℰ_Y^•)`.
* `Stacks.Chow.chernCharacter_eq_of_envelopePresentation_modification` — **Stacks 0GUF, the clause
  for the Chern character.** The same for `ch_p = P_p/p!`.
* `Stacks.Chow.rationalChowCohomologyRestriction_comp` — the composition law for the restriction
  map on rational Chow cohomology, the rational counterpart of
  `Stacks.Chow.chowCohomologyRestriction_comp`.
* `Stacks.Chow.chernCharacterComplexComponent_rationalChowCohomologyRestriction` — the base change
  clause for `ch_p` of a complex, the Chern character counterpart of
  `Stacks.Chow.powerSumClassComplex_chowCohomologyRestriction`.

## Implementation notes

**What stands in for `c_p(E)`, and why this does not assume its own conclusion.** This repository
does not construct the Chern classes of a perfect object: `Stacks.Chow.HasDefinedChernClasses` is
a `Prop`, `Stacks.Chow.EnvelopePresentation` is the datum witnessing it, and there is no
`c_p(E)`. What is proved about them is *uniqueness*, in the three Stacks 0GUD theorems of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness`, each of which takes a
family `c` of classes on `X` together with the hypothesis that its restriction along the envelope
of a presentation is the corresponding class of the presenting complex. That hypothesis is the
only expression this repository has for "`c` **is** the family of Chern classes of `E`", and it is
the hypothesis taken here, in exactly the shape
`Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded` takes it.

It is not the conclusion: the hypothesis is about the restriction along the envelope `f : Y ⟶ X`,
and the conclusion is about the restriction along the composite `a ≫ f : W' ⟶ X` to the
modification, a different morphism, with a different complex — the pullback `a^*ℰ_Y^•` — on the
right. The content is that the one determines the other, and what carries it is the composition
law together with the base change compatibility of the data.

**Why the power sums and not the total Chern class.** `P_p` of a complex is the alternating
**sum** of the `P_p` of its terms, so the restriction map passes through it for the plain reason
that it is a homomorphism of groups. The total Chern class of a complex is the alternating
**product** of Stacks 0ESZ, and restricting it needs the restriction map to be multiplicative for
the product of `A^*(X)^∧`; that is Stacks 0FE0, hence Stacks 0B6Y, and the docstring of
`Stacks.Chow.chowCohomologyRestriction` records that only the additive map is constructed here.
The total Chern class reading of 0GUF's clause is therefore **not** delivered, and the obstruction
is a missing theorem about the restriction map, not a missing hypothesis.

**Which window, and why no quasi-compactness is needed.** The classes are taken at the
bounded-window `Stacks.Chow.powerSumClassComplex` rather than at
`Stacks.Chow.powerSumClassComplexLocallyBounded`. This matches the source, whose conclusion is
about a complex that is *bounded* on `W'`; and it avoids the `CompactSpace` instance that the
locally bounded construction needs, which the source does not assume of the envelope. The same
window serves on both sides: the degreewise pullback of a complex vanishing outside a window
vanishes outside that window.

**What is still not delivered.** The refinement of 0GUF's conclusion that on an *integral* `W'`
the pulled back complex is bounded with terms of *constant rank* is separate, and this repository
has no result deriving constant rank from integrality; nothing here needs it, the window being
carried explicitly instead. Neither is the identification of `a^*ℰ_Y^•` with a representative of
`L(g')^*E`, which is the derived-category half of the source's construction; the nearest
available result is `Stacks.Chow.hasDefinedChernClasses_of_derivedPullback` of Stacks 0GUE.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

section Modification

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)
  {E : DerivedCategory X.Modules}

/-- **Stacks 0GUF, the characteristic class clause, for the power sums.** Let `E` be an object of
`D(𝒪_X)` and let `H` be an envelope presentation of it, Stacks 0F9E (1), with presenting complex
`ℰ_Y^• = H.P` vanishing outside the degrees `w, …, w + k`. Let `a : W' ⟶ Y` be the lift to the
envelope of a modification of a morphism `g : W ⟶ X`, as produced by
`AlgebraicGeometry.IsEnvelope.exists_properBirational_modification`, so that the morphism
`g' : W' ⟶ X` of the source is `a ≫ H.f`.

If a family `c` of Chow cohomology classes of `X` restricts along the envelope to the power sums
of the presenting complex — which is this repository's expression for `c` being the family of
power sum classes `P_p(E)` of `E`, and is the hypothesis of
`Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded` — then its restriction
along `g' = a ≫ H.f` is the power sum class of the pulled back complex `a^*ℰ_Y^•`:

  `res_{g'}(P_p(E)) = P_p(a^*ℰ_Y^•)`.

This is the source's chain
`res_{g'}(c_p(E)) = res_a(res_f(c_p(E))) = res_a(c_p(ℰ_Y^•)) = c_p(a^*ℰ_Y^•)`. See the
implementation notes of this file for what stands in for `c_p(E)`, why the power sums and not the
total Chern class, and what the statement does not deliver. -/
@[stacks 0GUF "the characteristic class clause res(c_p(E)) = c_p(E^bullet), in the power sum \
reading P_p of Tag 0ESZ, for the lift a : W' -> Y of the modification to the envelope, so that \
res is along the g' = a . f of the tag. CARRIED: the family P_p(E) itself, which this repository \
does not construct -- it is taken as a family restricting along the envelope to P_p of the \
presenting complex, the hypothesis of the Tag 0GUD uniqueness theorems and the only expression \
here for 'c is the family of Chern classes of E'; the base change compatibility of the power sum \
data, which Stacks.Chow.PowerSumClassRule does not record; and the identification of a^*E_Y^. \
with a representative of L(g')^*E. NOT DELIVERED: the total Chern class reading, which needs the \
multiplicativity of the restriction map, Tag 0FE0 hence Tag 0B6Y, not formalized here; and the \
refinement that on an integral W' the pulled back complex has terms of constant rank. The \
geometric half of the tag is Stacks 0GUF on \
AlgebraicGeometry.IsEnvelope.exists_properBirational_modification"]
theorem powerSumClass_eq_of_envelopePresentation_modification (H : EnvelopePresentation E)
    [LocallyOfFiniteType H.f] {V : Scheme.{u}} (a : V ⟶ H.Y) [LocallyOfFiniteType a]
    (W : PowerSumClassRule C G (H.f ≫ sX)) (Wa : PowerSumClassRule C G (a ≫ (H.f ≫ sX)))
    (hW : PowerSumClassRule.IsBaseChangeCompatible C G (H.f ≫ sX) a hgys W Wa)
    (w : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := H.Y.ringCatSheaf)
        (H.P.X (w + (i : ℤ))))
    {c : ∀ p : ℕ, chowCohomologyComponent C G sX (p : ℤ)}
    (hc : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      powerSumClassComplex C G (H.f ≫ sX) W H.P w k p)
    (p : ℕ) :
    chowCohomologyRestriction C G sX (a ≫ H.f) (p : ℤ) hgys (c p) =
      powerSumClassComplex C G (a ≫ (H.f ≫ sX)) Wa
        (((Scheme.Modules.pullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj H.P)
        w k p := by
  rw [← chowCohomologyRestriction_comp C G sX H.f a (p : ℤ) hgys (c p), hc p]
  exact powerSumClassComplex_chowCohomologyRestriction C G (H.f ≫ sX) a hgys hW H.P w k hflf p

/-- **The composition law for the restriction map on rational Chow cohomology.** The rational
restriction map is the integral one tensored with `𝐐`, so the law follows from
`Stacks.Chow.chowCohomologyRestriction_comp` on pure tensors.

It is stated here rather than alongside the integral laws in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyFunctoriality` only because
`Stacks.Chow.rationalChowCohomologyRestriction` is defined in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness`, which that module does
not import. -/
theorem rationalChowCohomologyRestriction_comp {Y V : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] (a : V ⟶ Y) [LocallyOfFiniteType a] (p : ℤ)
    (c : rationalChowCohomologyComponent C G sX p) :
    rationalChowCohomologyRestriction C G (f ≫ sX) a p hgys
        (rationalChowCohomologyRestriction C G sX f p hgys c) =
      rationalChowCohomologyRestriction C G sX (a ≫ f) p hgys c := by
  induction c using TensorProduct.inductionOn with
  | tmul q x =>
    rw [rationalChowCohomologyRestriction_tmul, rationalChowCohomologyRestriction_tmul,
      rationalChowCohomologyRestriction_tmul, chowCohomologyRestriction_comp]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    rfl

/-- **The base change clause for the Chern character of a complex.** The rational restriction map
carries the component `ch_p(ℰ^•) = P_p(ℰ^•)/p!` of Stacks 0ESZ to the corresponding component of
the pulled back complex. It follows from the clause for the power sums,
`Stacks.Chow.powerSumClassComplex_chowCohomologyRestriction`, together with the action of the
rational restriction map on a pure tensor: the factorial is a scalar and is untouched. -/
theorem chernCharacterComplexComponent_rationalChowCohomologyRestriction {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {V : Scheme.{u}} (g : V ⟶ Y)
    [LocallyOfFiniteType g] {W : PowerSumClassRule C G sY}
    {Wg : PowerSumClassRule C G (g ≫ sY)}
    (hW : PowerSumClassRule.IsBaseChangeCompatible C G sY g hgys W Wg)
    (P : CochainComplex Y.Modules ℤ) (w : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (w + (i : ℤ)))) (p : ℕ) :
    rationalChowCohomologyRestriction C G sY g (p : ℤ) hgys
        (chernCharacterComplexComponent C G sY W P w k p) =
      chernCharacterComplexComponent C G (g ≫ sY) Wg
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) w k p := by
  rw [chernCharacterComplexComponent, chernCharacterComplexComponent,
    rationalChowCohomologyRestriction_tmul,
    powerSumClassComplex_chowCohomologyRestriction C G sY g hgys hW P w k hflf p]

/-- **Stacks 0GUF, the characteristic class clause, for the Chern character.** The Chern
character reading of `res(c_p(E)) = c_p(ℰ^•)`: for a family `c` of rational Chow cohomology
classes of `X` restricting along the envelope of a presentation to the components
`ch_p(ℰ_Y^•) = P_p(ℰ_Y^•)/p!`, the restriction of `c p` along `g' = a ≫ H.f` is `ch_p(a^*ℰ_Y^•)`.

The hypothesis is the one of `Stacks.Chow.eq_of_restriction_eq_chernCharacterComplexLocallyBounded`,
the Stacks 0GUD uniqueness theorem for the Chern character, read at a bounded window; see the
implementation notes of this file. -/
@[stacks 0GUF "the characteristic class clause res(c_p(E)) = c_p(E^bullet), in the Chern \
character reading ch_p = P_p/p! of Tag 0ESZ, for the lift a : W' -> Y of the modification to the \
envelope, so that res is along the g' = a . f of the tag. CARRIED: the family ch_p(E) itself, \
which this repository does not construct -- it is taken as a family restricting along the \
envelope to ch_p of the presenting complex, the hypothesis of the Tag 0GUD uniqueness theorem; \
the base change compatibility of the power sum data; and the identification of a^*E_Y^. with a \
representative of L(g')^*E. NOT DELIVERED: the total Chern class reading, which needs the \
multiplicativity of the restriction map, Tag 0FE0 hence Tag 0B6Y"]
theorem chernCharacter_eq_of_envelopePresentation_modification (H : EnvelopePresentation E)
    [LocallyOfFiniteType H.f] {V : Scheme.{u}} (a : V ⟶ H.Y) [LocallyOfFiniteType a]
    (W : PowerSumClassRule C G (H.f ≫ sX)) (Wa : PowerSumClassRule C G (a ≫ (H.f ≫ sX)))
    (hW : PowerSumClassRule.IsBaseChangeCompatible C G (H.f ≫ sX) a hgys W Wa)
    (w : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := H.Y.ringCatSheaf)
        (H.P.X (w + (i : ℤ))))
    {c : ∀ p : ℕ, rationalChowCohomologyComponent C G sX (p : ℤ)}
    (hc : ∀ p : ℕ, rationalChowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      chernCharacterComplexComponent C G (H.f ≫ sX) W H.P w k p)
    (p : ℕ) :
    rationalChowCohomologyRestriction C G sX (a ≫ H.f) (p : ℤ) hgys (c p) =
      chernCharacterComplexComponent C G (a ≫ (H.f ≫ sX)) Wa
        (((Scheme.Modules.pullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj H.P)
        w k p := by
  rw [← chernCharacterComplexComponent_rationalChowCohomologyRestriction C G hgys (H.f ≫ sX) a
      hW H.P w k hflf p, ← hc p,
    rationalChowCohomologyRestriction_comp C G sX hgys H.f a (p : ℤ) (c p)]

end Modification

end Stacks.Chow

end
