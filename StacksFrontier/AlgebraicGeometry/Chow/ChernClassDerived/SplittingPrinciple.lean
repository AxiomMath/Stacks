module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined
public import StacksCore.Tactic.StacksAttribute

/-!
# The splitting principle for the Chern classes of a perfect derived object

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes are
defined, Stacks 0F9E (1): there are an envelope `f : Y ⟶ X` and a locally bounded complex
`ℰ^•` of finite locally free `𝒪_Y`-modules representing `Lf^*E`. **Stacks 0FAD** observes that a
relation between the bivariant classes attached to `E` may then be proved after restricting
along `f`, where it becomes a relation between the classes of `ℰ^•`. The reduction is what is
proved here, in the form that justifies it: two Chow cohomology classes on `X` whose
restrictions along the envelope of a presentation of `E` agree are equal, because restriction
along an envelope is injective.

## Main results

* `Stacks.Chow.eq_of_chowCohomologyRestriction_eq_of_envelopePresentation` — **Stacks 0FAD**: a
  relation `c = d` between Chow cohomology classes on `X` may be checked after restriction along
  the envelope of a presentation of `E`.
* `Stacks.Chow.eq_of_forall_chowCohomologyRestriction_eq_of_hasDefinedChernClasses` — the same
  reduction with the presentation left to the reader's choice, as in the source: it suffices that
  the restrictions agree along every presentation, one of which exists.
* `Stacks.Chow.chowCohomologyRestriction_injective_of_isEnvelope` — the content of the two
  statements above: the restriction map `A^p(X) ⟶ A^p(Y)` of Stacks 0B7F along an envelope
  `f : Y ⟶ X` is injective.
* `Stacks.Chow.bivariantTransportAddHom_injective` — transport of a bivariant class along an
  isomorphism over the target is injective.

## Implementation notes

### Stacks 0GUD is not claimed

The source phrases the reduction as following from the uniqueness assertion of Stacks 0GUD: the
Chern classes of a perfect object are the unique bivariant classes restricting to those of a
representing complex. Stacks 0GUD is not in this repository — the Chern classes of a perfect
object are not constructed here, so there are no classes `c_p(E)`, `P_p(E)` and `ch_p(E)` to
relate — and nothing below claims that tag. What is proved is the principle those uniqueness
statements rest on, and which is what makes the reduction valid: restriction along the envelope
of a presentation is injective, so any relation between classes on `X` is implied by the
corresponding relation upstairs. The statements are therefore about arbitrary Chow cohomology
classes on `X`, with the existence of a presentation of `E` as the hypothesis the source uses;
once the Chern classes of `E` are constructed as restrictions of the classes of `ℰ^•`, the
reduction of the source is this statement applied to them.

Only the envelope of the presentation is used below. The complex `ℰ^•` and the isomorphism
`Lf^*E ≅ ℰ^•` are what turn the restricted relation into a relation between the Chern classes of
a complex of finite locally free modules, and that identification is precisely the part of the
source supplied by Stacks 0GUD, so it is absent here; the presentation is carried in the
statements because it is the hypothesis under which the source makes the reduction.

### Where the injectivity comes from

The restriction map `A^p(X) ⟶ A^p(Y)` of Stacks 0B7F is by construction the restriction map of
Stacks 0F9Z for the identity of `X`, followed by the transport of a bivariant class along the
canonical isomorphism `X ×_X Y ≅ Y`, so it is injective as soon as both factors are. The first
is the uniqueness half of Stacks 0GUC, available with no hypothesis as
`Stacks.Chow.bivariantRestrictionAddHom_injective_of_isEnvelope'`; the second is injective
because its cap operations are those of the original class pushed forward along an isomorphism
of the test fibre products.

In particular nothing is assumed here beyond the properness and complete decomposedness of the
envelope: the Stacks 02S2 descent datum that proper pushforward on Chow groups carries in this
repository is discharged inside the uniqueness statement; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent`. The isomorphism case of Stacks
02TA for the Gysin system, `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, is carried
because the restriction and transport maps themselves are only defined with it.

## References

* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-! ### Transport along an isomorphism is injective -/

/-- Transport of bivariant classes along an isomorphism `θ : A ≅ B` over `W` is injective: the
cap operations of the transported class are those of the original one, pushed forward along the
induced isomorphism of the base changes, and pushforward along an isomorphism is injective. -/
theorem bivariantTransportAddHom_injective (C : ChowSituation.{u}) (G : GysinSystem C)
    {A B W : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (v : A ⟶ W)
    [LocallyOfFiniteType v] (hv : v ≫ sW = sA) (u : B ⟶ W) [LocallyOfFiniteType u]
    (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v) (p : ℤ)
    (hgys : G.IsNaturalUnderBaseChangeIso) :
    Function.Injective (bivariantTransportAddHom C G sA sB sW v hv u hu θ hθ p hgys) := by
  intro c d hcd
  have hcd' : bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c =
      bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys d := hcd
  refine BivariantClass.ext C G sA sW v hv p ?_
  intro T g _ k α
  have h : bivariantTransportCap C G sA sB sW v hv u hu θ hθ p c g k α =
      bivariantTransportCap C G sA sB sW v hv u hu θ hθ p d g k α := by
    rw [← bivariantTransport_cap C G sA sB sW v hv u hu θ hθ p hgys c g k α,
      ← bivariantTransport_cap C G sA sB sW v hv u hu θ hθ p hgys d g k α, hcd']
  simp only [bivariantTransportCap_apply] at h
  exact chowPushforwardOfIso_injective C (pullback.fst v g ≫ sA) (pullback.fst u g ≫ sB)
    (transportPullbackIso v u θ hθ g).hom
    (transportPullbackIso_hom_comp_base C sA sB sW v hv u hu θ hθ g) (k - p) h

/-! ### Restriction on Chow cohomology along an envelope is injective -/

/-- Restriction `A^p(X) ⟶ A^p(Y)` of Chow cohomology classes along an envelope `f : Y ⟶ X` is
injective: it is the restriction map of Stacks 0F9Z for the identity of `X`, injective by the
uniqueness half of Stacks 0GUC, followed by a transport along `X ×_X Y ≅ Y`. -/
theorem chowCohomologyRestriction_injective_of_isEnvelope (C : ChowSituation.{u})
    (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [LocallyOfFiniteType f] (p : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso)
    (hf : IsEnvelope f) :
    Function.Injective (chowCohomologyRestriction C G sX f p hgys) := by
  intro c d hcd
  refine bivariantRestrictionAddHom_injective_of_isEnvelope' C G sX sX (𝟙 X)
    (Category.id_comp sX) f p hgys hf ?_
  refine bivariantTransportAddHom_injective C G (pullback.fst (𝟙 X) f ≫ sX) (f ≫ sX) (f ≫ sX)
    (pullback.snd (𝟙 X) f)
    (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) f) (𝟙 Y)
    (Category.id_comp (f ≫ sX)) (identityBaseChangeIso f) (by simp) p hgys ?_
  exact hcd

/-! ### The splitting principle -/

/-- **Stacks 0FAD.** A relation between Chow cohomology classes on `X` may be proved after
restricting along the envelope `f : Y ⟶ X` of a presentation of `E`: two classes of degree `p`
on `X` whose restrictions to `A^p(Y)` agree are equal. -/
@[stacks 0FAD "the splitting principle: a relation between bivariant classes on X may be \
checked after restriction along the envelope of a presentation, restriction along an envelope \
being injective"]
theorem eq_of_chowCohomologyRestriction_eq_of_envelopePresentation (C : ChowSituation.{u})
    (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {E : DerivedCategory X.Modules} (H : EnvelopePresentation E) (p : ℤ)
    (hgys : G.IsNaturalUnderBaseChangeIso) {c d : chowCohomologyComponent C G sX p} :
    letI : IsProper H.f := H.envelope.isProper
    letI : LocallyOfFiniteType H.f := IsProper.toLocallyOfFiniteType
    chowCohomologyRestriction C G sX H.f p hgys c =
        chowCohomologyRestriction C G sX H.f p hgys d →
      c = d := by
  have : IsProper H.f := H.envelope.isProper
  have : LocallyOfFiniteType H.f := IsProper.toLocallyOfFiniteType
  exact fun h => chowCohomologyRestriction_injective_of_isEnvelope C G sX H.f p hgys H.envelope h

/-- **Stacks 0FAD.** The same reduction with the envelope left to be chosen, as in the source: if
the Chern classes of `E` are defined, then two Chow cohomology classes of degree `p` on `X` whose
restrictions agree along the envelope of every presentation of `E` are equal. -/
@[stacks 0FAD "the splitting principle with the choice of envelope left open: the Chern classes \
of E being defined, a relation between bivariant classes on X follows from the relation after \
restriction along the envelope of every presentation"]
theorem eq_of_forall_chowCohomologyRestriction_eq_of_hasDefinedChernClasses
    (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E)
    (p : ℤ) (hgys : G.IsNaturalUnderBaseChangeIso) {c d : chowCohomologyComponent C G sX p}
    (h : ∀ H : EnvelopePresentation E,
      letI : IsProper H.f := H.envelope.isProper
      letI : LocallyOfFiniteType H.f := IsProper.toLocallyOfFiniteType
      chowCohomologyRestriction C G sX H.f p hgys c =
        chowCohomologyRestriction C G sX H.f p hgys d) :
    c = d := by
  obtain ⟨H⟩ := hE
  exact eq_of_chowCohomologyRestriction_eq_of_envelopePresentation C G sX H p hgys (h H)

end Stacks.Chow

end
