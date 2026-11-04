module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the Chern classes of a perfect object of the derived category

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes
are defined in the sense of Stacks 0F9E (1), that is, one admitting an *envelope presentation*
`Stacks.Chow.EnvelopePresentation`: an envelope `f : Y ⟶ X` together with a locally bounded
complex `P` of finite locally free `𝒪_Y`-modules representing `Lf^*E`. **Stacks 0GUD** asserts
that there are unique classes

  `c_p(E) ∈ A^p(X)`,  `P_p(E) ∈ A^p(X)`,  `ch_p(E) ∈ A^p(X) ⊗ 𝐐`

whose restrictions along every such envelope are the corresponding classes of the presenting
complex. **This file proves the uniqueness half only**, and says so in the attributes: the
existence of the three families is *not* constructed here, and nothing below assumes it.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_injective_of_isEnvelope` — restriction
  `res : A^p(X) ⟶ A^p(Y)` of Chow cohomology along an envelope `Y ⟶ X` is injective.
* `Stacks.Chow.rationalChowCohomologyRestriction_injective_of_isEnvelope` — the same with
  rational coefficients.
* `Stacks.Chow.eq_of_restriction_eq_totalChernClassComplexLocallyBounded`,
  `Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded`,
  `Stacks.Chow.eq_of_restriction_eq_chernCharacterComplexLocallyBounded` — **Stacks 0GUD,
  uniqueness**, for the total Chern class, for the power sums and for the Chern character: two
  families of classes on `X` whose restrictions along one envelope presentation of `E` are the
  classes of its presenting complex agree.

## Main definitions

* `Stacks.Chow.rationalChowCohomologyRestriction` — the restriction map
  `A^p(X) ⊗ 𝐐 ⟶ A^p(Y) ⊗ 𝐐` of Stacks 0B7F with rational coefficients, which is what the
  statement about the Chern character is read through.

## Implementation notes

### Uniqueness here, existence elsewhere

The three statements are of the shape `property c → property d → c = d`. The existence halves are
proved in other files: the descent of a bivariant class along an envelope (Stacks 0GUC) is
`Stacks.Chow.existsUnique_bivariantRestriction_eq_of_isEnvelope` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence`, and the existence of the
total Chern class of a perfect object whose Chern classes are defined (Stacks 0GUD) is
`Stacks.Chow.existsUnique_forall_res_eq_complexChern` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern`, which also compares two
envelope presentations.

### Why the hypotheses are taken at a single presentation

The source states the defining property as a condition at *every* envelope presentation of `E`.
The statements below assume it at *one* presentation, which is a weaker hypothesis and hence a
stronger theorem: the uniqueness clause of the tag follows from each of them by instantiating the
condition at any single presentation whose source is quasi-compact. Quasi-compactness of the
source enters because the classes below are the *carried* ones, over a
`Stacks.Chow.ChowCohomologySeriesRing` and a `Stacks.Chow.PowerSumClassRule` at an arbitrary
Gysin system, and in that form a locally bounded complex has them in this repository only on a
quasi-compact scheme, as `Stacks.Chow.totalChernClassComplexLocallyBounded` and
`Stacks.Chow.powerSumClassComplexLocallyBounded`; so the condition of the tag is not expressible
at a presentation with non-quasi-compact source. With the classes *built* rather than carried, at
`Stacks.Chow.gysinSystemOfInvertible`, the truly local case is delivered — it is
`Stacks.Chow.complexChern` (ComplexChernClass.lean:196) and
`Stacks.Chow.complexPowerSumComponent` (DerivedChernClasses.lean:414), where Stacks 0ESZ is
registered.

### How uniqueness is proved

Restriction of bivariant classes along an envelope is injective with no hypothesis, by
`Stacks.Chow.bivariantRestrictionAddHom_injective_of_isEnvelope'`, the uniqueness half of
Stacks 0GUC. The restriction map of Stacks 0B7F on Chow cohomology is that map followed by the
transport of a bivariant class along the canonical identification `X ×_X Y ≅ Y`, and transport is
injective because the cap operations of a transported class are the original ones pushed forward
along isomorphisms of the base changes. So `res : A^p(X) ⟶ A^p(Y)` is injective, and two families
with the same restrictions agree degreewise.

With rational coefficients the same argument needs that `𝐐 ⊗_𝐙 (-)` preserves injectivity, which
is flatness of `𝐐` over `𝐙`: it is a localization of `𝐙`, so `Module.Flat ℤ ℚ` follows from
`IsLocalization.flat`.

### The redundant instance on the presentation

Each statement takes `[LocallyOfFiniteType H.f]` as an instance argument although it follows from
`H.envelope.isProper`, because the types of the later arguments mention the structure morphism
`H.f ≫ sX` of the source of the envelope over the base, which needs that instance to be formed.
Nothing is assumed by it: every consumer obtains it from the presentation itself.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-! ### Injectivity of the transport of a bivariant class -/

section Transport

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A B W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hv : v ≫ sW = sA)
  (u : B ⟶ W) [LocallyOfFiniteType u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)
  (p : ℤ)

/-- **Transport of a bivariant class along an isomorphism over the target is injective.** The cap
operations of a transported class are those of the original one pushed forward along the induced
isomorphisms of the base changes, and pushforward along an isomorphism is injective. -/
theorem bivariantTransportAddHom_injective (hgys : G.IsNaturalUnderBaseChangeIso) :
    Function.Injective (bivariantTransportAddHom C G sA sB sW v hv u hu θ hθ p hgys) := by
  intro c d hcd
  refine BivariantClass.ext C G sA sW v hv p ?_
  intro T g _ k α
  refine chowPushforwardOfIso_injective C (pullback.fst v g ≫ sA) (pullback.fst u g ≫ sB)
    (transportPullbackIso v u θ hθ g).hom
    (transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g) (k - p) ?_
  exact congrArg (fun e : BivariantClass C G sB sW u hu p => e.cap g k α) hcd

end Transport

/-! ### Injectivity of restriction on Chow cohomology along an envelope -/

section Envelope

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℤ)

/-- **Restriction of Chow cohomology along an envelope is injective.** This is the uniqueness
half of Stacks 0GUC, `Stacks.Chow.bivariantRestrictionAddHom_injective_of_isEnvelope'`, read on
the restriction map `res : A^p(X) ⟶ A^p(Y)` of Stacks 0B7F: that map is restriction of bivariant
classes along `g` followed by the transport along the canonical identification `X ×_X Y ≅ Y`, and
both are injective. No hypothesis beyond the isomorphism case of Stacks 02TA for the Gysin
system, which the restriction map carries already. -/
theorem chowCohomologyRestriction_injective_of_isEnvelope
    (hgys : G.IsNaturalUnderBaseChangeIso) (hgE : IsEnvelope g) :
    Function.Injective (chowCohomologyRestriction C G sX g p hgys) := by
  intro c d hcd
  refine bivariantRestrictionAddHom_injective_of_isEnvelope' C G sX sX (𝟙 X)
    (Category.id_comp sX) g p hgys hgE ?_
  refine bivariantTransportAddHom_injective C G (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (g ≫ sX)
    (pullback.snd (𝟙 X) g)
    (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) g) (𝟙 Y)
    (Category.id_comp (g ≫ sX)) (identityBaseChangeIso g) (Category.comp_id _) p hgys ?_
  exact hcd

/-- The restriction map `A^p(X) ⊗ 𝐐 ⟶ A^p(Y) ⊗ 𝐐` of Stacks 0B7F with rational coefficients:
the restriction map of Chow cohomology tensored with `𝐐`. -/
def rationalChowCohomologyRestriction (hgys : G.IsNaturalUnderBaseChangeIso) :
    rationalChowCohomologyComponent C G sX p →ₗ[ℤ]
      rationalChowCohomologyComponent C G (g ≫ sX) p :=
  LinearMap.lTensor ℚ (chowCohomologyRestriction C G sX g p hgys).toIntLinearMap

/-- The rational restriction map on a pure tensor is the restriction of its Chow cohomology
factor. -/
@[simp]
theorem rationalChowCohomologyRestriction_tmul (hgys : G.IsNaturalUnderBaseChangeIso) (q : ℚ)
    (c : chowCohomologyComponent C G sX p) :
    rationalChowCohomologyRestriction C G sX g p hgys (q ⊗ₜ[ℤ] c) =
      q ⊗ₜ[ℤ] chowCohomologyRestriction C G sX g p hgys c :=
  LinearMap.lTensor_tmul ℚ (chowCohomologyRestriction C G sX g p hgys).toIntLinearMap q c

/-- **Restriction of rational Chow cohomology along an envelope is injective.** The integral
statement is `Stacks.Chow.chowCohomologyRestriction_injective_of_isEnvelope`, and `𝐐` is flat
over `𝐙`, being a localization of it, so tensoring with `𝐐` preserves the injectivity. -/
theorem rationalChowCohomologyRestriction_injective_of_isEnvelope
    (hgys : G.IsNaturalUnderBaseChangeIso) (hgE : IsEnvelope g) :
    Function.Injective (rationalChowCohomologyRestriction C G sX g p hgys) := by
  have hflat : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (chowCohomologyRestriction_injective_of_isEnvelope C G sX g p hgys hgE)

end Envelope

/-! ### Uniqueness of the classes of an object of the derived category -/

section Uniqueness

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)
  {E : DerivedCategory X.Modules}

/-- **Stacks 0GUD, uniqueness for the total Chern class.** Let `E` be an object of `D(𝒪_X)` and
let `H` be an envelope presentation of it, Stacks 0F9E (1), whose source is quasi-compact. Two
families `c, d` of Chow cohomology classes of `X` whose restrictions along the envelope of `H`
are the coefficients of the total Chern class `c(P)` of the presenting complex are equal.

The existence of such a family is **not** proved: see the implementation notes of this file. The
hypothesis is taken at the single presentation `H` rather than at every presentation of `E`, so
this is stronger than the uniqueness clause of the tag. -/
@[stacks 0GUD "the uniqueness half for the total Chern class c(E), read on the coefficients of \
the series of Tag 0ESZ; the existence of the classes is not constructed here, and the hypothesis \
is taken at one envelope presentation rather than at all of them, which is stronger"]
theorem eq_of_restriction_eq_totalChernClassComplexLocallyBounded
    (H : EnvelopePresentation E) [LocallyOfFiniteType H.f] [CompactSpace H.Y]
    {R : ChowCohomologySeriesRing C G (H.f ≫ sX)} (D : TotalChernClassSeries C G (H.f ≫ sX) R)
    {c d : ∀ p : ℕ, chowCohomologyComponent C G sX (p : ℤ)}
    (hc : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      (totalChernClassComplexLocallyBounded C G (H.f ≫ sX) D H.P H.locallyBounded).1 p)
    (hd : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (d p) =
      (totalChernClassComplexLocallyBounded C G (H.f ≫ sX) D H.P H.locallyBounded).1 p) :
    c = d := by
  funext p
  exact chowCohomologyRestriction_injective_of_isEnvelope C G sX H.f (p : ℤ) hgys H.envelope
    ((hc p).trans (hd p).symm)

/-- **Stacks 0GUD, uniqueness for the power sums.** Let `E` be an object of `D(𝒪_X)` and let `H`
be an envelope presentation of it, Stacks 0F9E (1), whose source is quasi-compact. Two families
`c, d` of Chow cohomology classes of `X` whose restrictions along the envelope of `H` are the
classes `P_p(P)` of the presenting complex are equal.

The existence of such a family is **not** proved: see the implementation notes of this file. The
hypothesis is taken at the single presentation `H` rather than at every presentation of `E`, so
this is stronger than the uniqueness clause of the tag. -/
@[stacks 0GUD "the uniqueness half for the power sums P_p(E), the classes of Tag 0ESZ; the \
existence of the classes is not constructed here, and the hypothesis is taken at one envelope \
presentation rather than at all of them, which is stronger"]
theorem eq_of_restriction_eq_powerSumClassComplexLocallyBounded
    (H : EnvelopePresentation E) [LocallyOfFiniteType H.f] [CompactSpace H.Y]
    (W : PowerSumClassRule C G (H.f ≫ sX))
    {c d : ∀ p : ℕ, chowCohomologyComponent C G sX (p : ℤ)}
    (hc : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      powerSumClassComplexLocallyBounded C G (H.f ≫ sX) W H.P H.locallyBounded p)
    (hd : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (d p) =
      powerSumClassComplexLocallyBounded C G (H.f ≫ sX) W H.P H.locallyBounded p) :
    c = d := by
  funext p
  exact chowCohomologyRestriction_injective_of_isEnvelope C G sX H.f (p : ℤ) hgys H.envelope
    ((hc p).trans (hd p).symm)

/-- **Stacks 0GUD, uniqueness for the Chern character.** Let `E` be an object of `D(𝒪_X)` and let
`H` be an envelope presentation of it, Stacks 0F9E (1), whose source is quasi-compact. Two
families `c, d` of rational Chow cohomology classes of `X` whose restrictions along the envelope
of `H` are the components `ch_p(P) = P_p(P)/p!` of the Chern character of the presenting complex
are equal.

The existence of such a family is **not** proved: see the implementation notes of this file. The
hypothesis is taken at the single presentation `H` rather than at every presentation of `E`, so
this is stronger than the uniqueness clause of the tag. -/
@[stacks 0GUD "the uniqueness half for the Chern character ch(E), read componentwise as \
ch_p = P_p/p! with the classes P_p of Tag 0ESZ; the existence of the classes is not constructed \
here, and the hypothesis is taken at one envelope presentation rather than at all of them, which \
is stronger"]
theorem eq_of_restriction_eq_chernCharacterComplexLocallyBounded
    (H : EnvelopePresentation E) [LocallyOfFiniteType H.f] [CompactSpace H.Y]
    (W : PowerSumClassRule C G (H.f ≫ sX))
    {c d : ∀ p : ℕ, rationalChowCohomologyComponent C G sX (p : ℤ)}
    (hc : ∀ p : ℕ, rationalChowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
        powerSumClassComplexLocallyBounded C G (H.f ≫ sX) W H.P H.locallyBounded p)
    (hd : ∀ p : ℕ, rationalChowCohomologyRestriction C G sX H.f (p : ℤ) hgys (d p) =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
        powerSumClassComplexLocallyBounded C G (H.f ≫ sX) W H.P H.locallyBounded p) :
    c = d := by
  funext p
  exact rationalChowCohomologyRestriction_injective_of_isEnvelope C G sX H.f (p : ℤ) hgys
    H.envelope ((hc p).trans (hd p).symm)

end Uniqueness

end Stacks.Chow

end
