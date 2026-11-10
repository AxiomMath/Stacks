module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Modifications
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Properties

/-!
# Properties of a modification of a scheme at a closed point

Let `s` be a closed point of a scheme `S` whose open complement `S ∖ {s}` has quasi-compact
inclusion, and let `X ⟶ S` be a morphism of finite presentation which is an isomorphism over
`S ∖ {s}`.  Base change along `Spec 𝒪_{S, s} ⟶ S` is an equivalence onto the corresponding
category over `Spec 𝒪_{S, s}`, and `X ⟶ S` is separated, proper, finite or étale exactly when its
base change is.

## Main results

* `AlgebraicGeometry.GlueingNearPoint.isSeparated_iff_isSeparated_baseChange`,
  `AlgebraicGeometry.GlueingNearPoint.isProper_iff_isProper_baseChange`,
  `AlgebraicGeometry.GlueingNearPoint.isFinite_iff_isFinite_baseChange`,
  `AlgebraicGeometry.GlueingNearPoint.etale_iff_etale_baseChange`: [Stacks, Tag 0BFN].

## Implementation notes

One direction is stability of the four properties under base change.  For the other, the
morphism is regarded as a scheme of finite presentation over the neighbourhood `⊤` of
`(S ∖ {s}) ∪ {s}`, so that the descent theorem
`AlgebraicGeometry.GlueingNearPoint.exists_open_isSeparated` and its companions apply; the
neighbourhood they produce contains `S ∖ {s}` and `s`, hence is all of `S`.

## References

* [Stacks Project, Lemma 32.21.2 (0BFN)](https://stacks.math.columbia.edu/tag/0BFN)
* [Stacks Project, Lemma 32.21.1 (0B3X)](https://stacks.math.columbia.edu/tag/0B3X)
* [Stacks Project, Lemma 32.20.4 (0EY3)](https://stacks.math.columbia.edu/tag/0EY3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.GlueingNearPoint

variable {S : Scheme.{u}} {s : S}

/-- Base change along an isomorphism preserves and reflects any property stable under
isomorphism. -/
private lemma prop_pullback_snd_iff {X T : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (f : X ⟶ S) (g : T ⟶ S) [IsIso g] :
    P (pullback.snd f g) ↔ P f :=
  P.arrow_mk_iso_iff
    (Arrow.isoMk (asIso (pullback.fst f g)) (asIso g) (by simpa using pullback.condition))

/-- A modification of `S` at the closed point `s`, regarded as a scheme of finite presentation
over the open neighbourhood `⊤` of `(S ∖ {s}) ∪ {s}`. -/
private def awayModel (hs : IsClosed ({s} : Set S))
    (X : FinitePresentationAway (puncturedOpen hs)) :
    FinitePresentationNeighborhoodModel S (puncturedOpen hs) s where
  neighborhood := ⟨⊤, le_top, by simp⟩
  source := X.obj.left
  hom := X.obj.hom ≫ S.topIso.inv
  finitePresentation := by
    have h := X.property.1
    have : LocallyOfFinitePresentation X.obj.hom := h.1
    have : QuasiCompact X.obj.hom := h.2.1
    have : QuasiSeparated X.obj.hom := h.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma awayModel_ambient (hs : IsClosed ({s} : Set S))
    (X : FinitePresentationAway (puncturedOpen hs)) :
    (neighborhoodModelToAmbient S (puncturedOpen hs) s).obj (awayModel hs X) = X.obj := by
  have h : (X.obj.hom ≫ S.topIso.inv) ≫ (⊤ : S.Opens).ι = X.obj.hom := by
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  change Over.mk ((X.obj.hom ≫ S.topIso.inv) ≫ (⊤ : S.Opens).ι) = X.obj
  rw [h]
  rfl

/-- A property of the restriction of `Y ⟶ S` to an open subscheme containing the closed point `s`
and its complement is a property of `Y ⟶ S`. -/
private lemma prop_of_prop_restrict (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hs : IsClosed ({s} : Set S)) {V : S.Opens} (hUV : puncturedOpen hs ≤ V) (hsV : s ∈ V)
    {Y : Over S} (hY : P ((Over.pullback V.ι).obj Y).hom) : P Y.hom := by
  obtain rfl := eq_top_of_puncturedOpen_le hs hUV hsV
  have : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  exact (prop_pullback_snd_iff P Y.hom (⊤ : S.Opens).ι).mp hY

/-- The restriction of a modification to the complement of the closed point is an isomorphism,
hence has every property containing the isomorphisms. -/
private lemma prop_restrict_puncturedOpen (P : MorphismProperty Scheme.{u})
    (hs : IsClosed ({s} : Set S)) (X : FinitePresentationAway (puncturedOpen hs))
    (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsIso f → P f) :
    P ((Over.pullback (puncturedOpen hs).ι).obj
      ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj (awayModel hs X))).hom := by
  rw [awayModel_ambient]
  exact hP _ X.property.2

/-- A modification of `S` at the closed point `s` has a property `P` stable under base change and
containing the isomorphisms exactly when its base change along `Spec 𝒪_{S, s} ⟶ S` has it, as
soon as `P` descends from `S ∖ {s}` and `Spec 𝒪_{S, s}` to a neighbourhood of `(S ∖ {s}) ∪ {s}`. -/
private lemma prop_iff_prop_baseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsIso f → P f)
    (hs : IsClosed ({s} : Set S)) (X : FinitePresentationAway (puncturedOpen hs))
    (hex : P ((Over.pullback (puncturedOpen hs).ι).obj
        ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj (awayModel hs X))).hom →
      P ((Over.pullback (S.fromSpecStalk s)).obj
        ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj (awayModel hs X))).hom →
      ∃ V : S.Opens, puncturedOpen hs ≤ V ∧ V ≤ (awayModel hs X).neighborhood.V ∧ s ∈ V ∧
        P ((Over.pullback V.ι).obj
          ((neighborhoodModelToAmbient S (puncturedOpen hs) s).obj (awayModel hs X))).hom) :
    P X.obj.hom ↔ P ((finitePresentationAwayBaseChange S s hs).obj X).obj.hom := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback X.obj.hom (S.fromSpecStalk s)), fun hg ↦ ?_⟩
  obtain ⟨V, hUV, -, hsV, hPV⟩ :=
    hex (prop_restrict_puncturedOpen P hs X hP) (by rw [awayModel_ambient]; exact hg)
  have h := prop_of_prop_restrict P hs hUV hsV hPV
  rwa [awayModel_ambient] at h

/-- **Stacks Project, Tag 0BFN (separated case).** A morphism of finite presentation to `S` which
is an isomorphism over the complement of a closed point `s` is separated exactly when its base
change along `Spec 𝒪_{S, s} ⟶ S` is separated. -/
@[stacks 0BFN "separated"]
theorem isSeparated_iff_isSeparated_baseChange (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    (X : FinitePresentationAway (puncturedOpen hs)) :
    IsSeparated X.obj.hom ↔
      IsSeparated ((finitePresentationAwayBaseChange S s hs).obj X).obj.hom :=
  prop_iff_prop_baseChange (@IsSeparated) (fun f hf ↦ have : IsIso f := hf; inferInstance) hs X
    (exists_open_isSeparated S _ s (notMem_puncturedOpen hs)
      (isRetrocompact_of_quasiCompact_ι _ hqc) (awayModel hs X))

/-- **Stacks Project, Tag 0BFN (proper case).** A morphism of finite presentation to `S` which is
an isomorphism over the complement of a closed point `s` is proper exactly when its base change
along `Spec 𝒪_{S, s} ⟶ S` is proper. -/
@[stacks 0BFN "proper"]
theorem isProper_iff_isProper_baseChange (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    (X : FinitePresentationAway (puncturedOpen hs)) :
    IsProper X.obj.hom ↔
      IsProper ((finitePresentationAwayBaseChange S s hs).obj X).obj.hom :=
  prop_iff_prop_baseChange (@IsProper) (fun f hf ↦ have : IsIso f := hf; inferInstance) hs X
    (exists_open_isProper S _ s (notMem_puncturedOpen hs)
      (isRetrocompact_of_quasiCompact_ι _ hqc) (awayModel hs X))

/-- **Stacks Project, Tag 0BFN (finite case).** A morphism of finite presentation to `S` which is
an isomorphism over the complement of a closed point `s` is finite exactly when its base change
along `Spec 𝒪_{S, s} ⟶ S` is finite. -/
@[stacks 0BFN "finite"]
theorem isFinite_iff_isFinite_baseChange (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    (X : FinitePresentationAway (puncturedOpen hs)) :
    IsFinite X.obj.hom ↔
      IsFinite ((finitePresentationAwayBaseChange S s hs).obj X).obj.hom :=
  prop_iff_prop_baseChange (@IsFinite) (fun f hf ↦ have : IsIso f := hf; inferInstance) hs X
    (exists_open_isFinite S _ s (notMem_puncturedOpen hs)
      (isRetrocompact_of_quasiCompact_ι _ hqc) (awayModel hs X))

/-- **Stacks Project, Tag 0BFN (étale case).** A morphism of finite presentation to `S` which is
an isomorphism over the complement of a closed point `s` is étale exactly when its base change
along `Spec 𝒪_{S, s} ⟶ S` is étale. -/
@[stacks 0BFN "etale"]
theorem etale_iff_etale_baseChange (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι)
    (X : FinitePresentationAway (puncturedOpen hs)) :
    Etale X.obj.hom ↔
      Etale ((finitePresentationAwayBaseChange S s hs).obj X).obj.hom :=
  prop_iff_prop_baseChange (@Etale) (fun f hf ↦ have : IsIso f := hf; inferInstance) hs X
    (exists_open_etale S _ s (notMem_puncturedOpen hs)
      (isRetrocompact_of_quasiCompact_ι _ hqc) (awayModel hs X))

end AlgebraicGeometry.GlueingNearPoint
