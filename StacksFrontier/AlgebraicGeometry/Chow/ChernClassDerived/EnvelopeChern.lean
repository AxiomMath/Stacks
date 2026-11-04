module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Criteria
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.SplittingPrinciple

/-!
# The Chern classes of a perfect object by descent along an envelope

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes are defined
(Stacks 0F9E (1)): some envelope `f : Y ⟶ X` has `Lf^*E` represented by a locally bounded complex
`𝓔^•` of finite locally free `𝒪_Y`-modules. Stacks 0GUD constructs the total Chern class
`c(E) ∈ ∏_{p ≥ 0} A^p(X)`: the unique class whose restriction to `Y` is `c(𝓔^•)`, independent of
the choice of `f` and `𝓔^•`.

The proof follows the source. The restriction of `c(𝓔^•)` along either projection
`Y ×_X Y ⟶ Y` is the total Chern class of the pulled back complex, and both pulled back complexes
represent the derived pullback of `E` to `Y ×_X Y`, so they have the same total Chern class by
Stacks 0ESZ; Stacks 0GUC then descends `c(𝓔^•)` to `X`. A second presentation along `f'` gives
the same class, because both restrict to the same class on the envelope `Y ×_X Y' ⟶ X`, along
which restriction is injective.

## Main definitions

* `Stacks.Chow.EnvelopePresentation.pullbackRepresentation` — for a presentation `(f, 𝓔^•)` of
  `E` and `h : Z ⟶ Y`, the termwise pullback `h^*𝓔^•` represents `L(h ≫ f)^*E`.
* `Stacks.Chow.EnvelopePresentation.pullbackRepresentationIso` — two presentations pulled back
  along morphisms with equal composites to `X` represent isomorphic objects.
* `Stacks.Chow.perfectChernClass` — the total Chern class `c(E)` of an object whose Chern classes
  are defined, Stacks 0F9E (2).

## Main results

* `Stacks.Chow.TotalChowClass.existsUnique_res_eq_of_isEnvelope` — descent of total Chow
  cohomology classes along an envelope.
* `Stacks.Chow.TotalChowClass.res_injective_of_isEnvelope` — restriction along an envelope is
  injective.
* `Stacks.Chow.res_perfectChernClass` — the restriction of `c(E)` along the envelope of every
  presentation of `E` is the total Chern class of the presenting complex.
* `Stacks.Chow.eq_perfectChernClass` — uniqueness, from a single presentation.
* `Stacks.Chow.existsUnique_forall_res_eq_complexChern` — Stacks 0GUD for the total Chern class.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Descent of total classes -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The two projections `Y ×_X Y ⟶ Y` followed by the structure morphism of `Y` agree, when that
structure morphism factors through `f : Y ⟶ X`. -/
theorem pullbackSnd_comp_eq_pullbackFst_comp (f : Y ⟶ X) (hs : f ≫ sX = sY) :
    pullback.snd f f ≫ sY = pullback.fst f f ≫ sY := by
  rw [← hs, pullback.condition_assoc]

/-- **Descent of total Chow cohomology classes along an envelope.** Let `f : Y ⟶ X` be an
envelope and let `c'` be a total class of `Y` whose restrictions along the two projections
`Y ×_X Y ⟶ Y` agree. Then there is a unique total class of `X` restricting to `c'` along `f`.
This is Stacks 0GUC for the identity of `X`, in every degree. -/
theorem existsUnique_res_eq_of_isEnvelope (f : Y ⟶ X) [LocallyOfFiniteType f]
    (envelope : IsEnvelope f) (hs : f ≫ sX = sY) (c' : TotalChowClass C sY)
    (hc' : res (pullback.fst f f) rfl c' =
      res (pullback.snd f f) (pullbackSnd_comp_eq_pullbackFst_comp f hs) c') :
    ∃! c : TotalChowClass C sX, res f hs c = c' := by
  subst hs
  have key : ∀ p : ℕ, ∃! c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ),
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f (p : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = c' p := by
    intro p
    refine existsUnique_chowCohomologyRestriction_eq_of_isEnvelope C sX (p : ℤ) envelope (c' p)
      fun t _ k α β hαβ ↦ ?_
    have hα := op_res_apply (pullback.fst f f) rfl c' t k p
      (chowGroupCongr C (Category.assoc _ _ _) k α) α (chowGroupCongr_heq C _ k α)
    have hβ := op_res_apply (pullback.snd f f) (pullbackSnd_comp_eq_pullbackFst_comp f rfl) c' t
      k p (chowGroupCongr C (Category.assoc _ _ _) k α) β
      ((chowGroupCongr_heq C _ k α).trans hαβ)
    rw [hc'] at hα
    exact hα.symm.trans hβ
  choose c hc huniq using key
  refine ⟨c, ext fun p ↦ (res_rfl_apply f c p).trans (hc p), fun d hd ↦ funext fun p ↦ ?_⟩
  exact huniq p (d p) ((res_rfl_apply f d p).symm.trans (congrFun hd p))

/-- **Restriction of total classes along an envelope is injective.** -/
theorem res_injective_of_isEnvelope (f : Y ⟶ X) [LocallyOfFiniteType f]
    (envelope : IsEnvelope f) (hs : f ≫ sX = sY) :
    Function.Injective (res (C := C) f hs) := by
  subst hs
  intro c d hcd
  funext p
  refine chowCohomologyRestriction_injective_of_isEnvelope C (gysinSystemOfInvertible C) sX f
    (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) envelope ?_
  rw [← res_rfl_apply, ← res_rfl_apply, hcd]

end TotalChowClass

/-! ### Pulling back an envelope presentation -/

section Presentation

variable {X : Scheme.{u}} {E : DerivedCategory X.Modules}

/-- **The pullback of a presentation.** For an envelope presentation `(f, 𝓔^•)` of `E` and a
morphism `h : Z ⟶ Y` to the source of the envelope, the termwise pullback `h^*𝓔^•` represents the
derived pullback `L(h ≫ f)^*E`: the complex `𝓔^•` is K-flat, so `h^*𝓔^•` computes
`Lh^*(Lf^*E)`, which is `L(h ≫ f)^*E`. -/
def EnvelopePresentation.pullbackRepresentation (H : EnvelopePresentation E) {Z : Scheme.{u}}
    (h : Z ⟶ H.Y) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (h ≫ H.f).toLRSHom.toShHom).obj E ≅
      DerivedCategory.Q.obj (pullbackComplex h H.P) :=
  ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical h.toLRSHom.toShHom
      H.f.toLRSHom.toShHom).app E).symm ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).mapIso
      H.representation.some ≪≫
    Cohomology.derivedPullbackIsoPullbackOfKFlat h.toLRSHom.toShHom H.P
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree H.P
        H.locallyBounded)

/-- Two morphisms with equal composites to `X` pull envelope presentations back to complexes
representing isomorphic objects. -/
def EnvelopePresentation.pullbackRepresentationIso (H H' : EnvelopePresentation E)
    {Z : Scheme.{u}} (h : Z ⟶ H.Y) (h' : Z ⟶ H'.Y) (e : h ≫ H.f = h' ≫ H'.f) :
    DerivedCategory.Q.obj (pullbackComplex h H.P) ≅
      DerivedCategory.Q.obj (pullbackComplex h' H'.P) :=
  (H.pullbackRepresentation h).symm ≪≫
    (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
      (congrArg (fun m : Z ⟶ X ↦ m.toLRSHom.toShHom) e))).app E ≪≫
    H'.pullbackRepresentation h'

end Presentation


/-! ### The total Chern class of an object whose Chern classes are defined -/

section PerfectChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E : DerivedCategory X.Modules}

/-- The envelope of a presentation is locally of finite type, being proper. -/
instance EnvelopePresentation.locallyOfFiniteType_f (H : EnvelopePresentation E) :
    LocallyOfFiniteType H.f :=
  have := H.envelope.isProper
  inferInstance

/-- **Stacks 0ESZ along two presentations.** Pulling back two envelope presentations of `E` along
morphisms `h : Z ⟶ Y`, `h' : Z ⟶ Y'` with `h ≫ f = h' ≫ f'` gives complexes with the same total
Chern class: both represent the derived pullback of `E` to `Z`. -/
theorem complexChern_pullbackComplex_eq (H H' : EnvelopePresentation E) {Z : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (h : Z ⟶ H.Y) (h' : Z ⟶ H'.Y)
    (e : h ≫ H.f = h' ≫ H'.f) :
    complexChern C sZ
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h H.P H.locallyBounded) =
      complexChern C sZ
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback h' H'.P
          H'.locallyBounded) :=
  complexChern_eq_of_iso C sZ _ _ (H.pullbackRepresentationIso H' h h' e)

/-- **The classes of two presentations agree after restriction** along morphisms with equal
composites to `X`. -/
theorem res_complexChern_eq_res_complexChern (H H' : EnvelopePresentation E) {Z : Scheme.{u}}
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] (h : Z ⟶ H.Y) [LocallyOfFiniteType h]
    (h' : Z ⟶ H'.Y) [LocallyOfFiniteType h'] (e : h ≫ H.f = h' ≫ H'.f)
    (hs : h ≫ (H.f ≫ sX) = sZ) (hs' : h' ≫ (H'.f ≫ sX) = sZ) :
    TotalChowClass.res h hs (complexChern C (H.f ≫ sX) H.locallyBounded) =
      TotalChowClass.res h' hs' (complexChern C (H'.f ≫ sX) H'.locallyBounded) := by
  rw [res_complexChern, res_complexChern]
  exact complexChern_pullbackComplex_eq C H H' sZ h h' e

/-- **Stacks 0GUD for one presentation.** For an envelope presentation `(f, 𝓔^•)` of `E` there is
a unique total class of `X` whose restriction along `f` is the total Chern class of `𝓔^•`. -/
theorem existsUnique_res_eq_complexChern (H : EnvelopePresentation E) :
    ∃! c : TotalChowClass C sX,
      TotalChowClass.res H.f rfl c = complexChern C (H.f ≫ sX) H.locallyBounded :=
  TotalChowClass.existsUnique_res_eq_of_isEnvelope H.f H.envelope rfl _
    (res_complexChern_eq_res_complexChern C sX H H (pullback.fst H.f H.f) (pullback.snd H.f H.f)
      pullback.condition rfl _)

/-- **The total Chern class `c(E)` of an object whose Chern classes are defined**, Stacks 0F9E
(2): the class of Stacks 0GUD, the unique total class of `X` whose restriction along the envelope
of a presentation of `E` is the total Chern class of the presenting complex. Its degree-`p`
component is `c_p(E)`. -/
@[stacks 0F9E "clause (2) for c(E): the class c(E) in prod_{p >= 0} A^p(X), carrying c_p(E) in \
degree p, for an object of D(O_X) whose Chern classes are defined in the sense of clause (1). \
Stacks.Chow.res_perfectChernClass pins it down at every envelope presentation, which is how \
Lemma 0GUD characterizes it. The two further classes clause (2) names are ch(E) \
(Stacks.Chow.perfectChernCharacter) and P_p(E) (Stacks.Chow.perfectPowerSumComponent)"]
def perfectChernClass (hE : HasDefinedChernClasses E) : TotalChowClass C sX :=
  (existsUnique_res_eq_complexChern C sX hE.some).exists.choose

/-- **The characterization of `c(E)`, at every presentation.** For every envelope presentation
`(f, 𝓔^•)` of `E`, the restriction of `c(E)` along `f` is the total Chern class of `𝓔^•`; so the
class does not depend on the choice of the envelope and of the complex. -/
theorem res_perfectChernClass (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E) :
    TotalChowClass.res H.f rfl (perfectChernClass C sX hE) =
      complexChern C (H.f ≫ sX) H.locallyBounded := by
  set H₀ := hE.some
  have hc₀ : TotalChowClass.res H₀.f rfl (perfectChernClass C sX hE) =
      complexChern C (H₀.f ≫ sX) H₀.locallyBounded :=
    (existsUnique_res_eq_complexChern C sX H₀).exists.choose_spec
  have hπ : IsEnvelope (pullback.snd H₀.f H.f) :=
    isEnvelope_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H₀.f H.f)
      H₀.envelope
  have e := (pullback.condition (f := H₀.f) (g := H.f)).symm
  refine TotalChowClass.res_injective_of_isEnvelope (pullback.snd H₀.f H.f) hπ rfl ?_
  have hs : pullback.fst H₀.f H.f ≫ (H₀.f ≫ sX) = pullback.snd H₀.f H.f ≫ (H.f ≫ sX) := by
    rw [← Category.assoc, ← e, Category.assoc]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr e _ hs,
    ← TotalChowClass.res_res H₀.f rfl _ hs, hc₀]
  exact res_complexChern_eq_res_complexChern C sX H₀ H _ _ e.symm _ _

/-- **Uniqueness of `c(E)`.** A total class of `X` whose restriction along the envelope of one
presentation of `E` is the total Chern class of the presenting complex is `c(E)`. -/
theorem eq_perfectChernClass (hE : HasDefinedChernClasses E) (H : EnvelopePresentation E)
    {c : TotalChowClass C sX}
    (hc : TotalChowClass.res H.f rfl c = complexChern C (H.f ≫ sX) H.locallyBounded) :
    c = perfectChernClass C sX hE :=
  TotalChowClass.res_injective_of_isEnvelope H.f H.envelope rfl
    (hc.trans (res_perfectChernClass C sX hE H).symm)

/-- **Stacks 0GUD, for the total Chern class.** If the Chern classes of `E` are defined, there is
a unique total class `c(E) ∈ ∏_{p ≥ 0} A^p(X)` whose restriction along the envelope `f : Y ⟶ X`
of every presentation of `E` by a locally bounded complex `𝓔^•` of finite locally free
`𝒪_Y`-modules is the total Chern class `c(𝓔^•)`.

This is the total-Chern-class third of Stacks 0GUD, at the hypotheses of the source, with `Y`
not assumed quasi-compact; it is untagged because Stacks 0GUD asserts the existence and
uniqueness of `c(E)`, `ch(E)` and `P_p(E)` together. -/
theorem existsUnique_forall_res_eq_complexChern (hE : HasDefinedChernClasses E) :
    ∃! c : TotalChowClass C sX, ∀ H : EnvelopePresentation E,
      TotalChowClass.res H.f rfl c = complexChern C (H.f ≫ sX) H.locallyBounded :=
  ⟨perfectChernClass C sX hE, res_perfectChernClass C sX hE,
    fun _ hc ↦ eq_perfectChernClass C sX hE hE.some (hc hE.some)⟩

end PerfectChern

end Stacks.Chow

end
