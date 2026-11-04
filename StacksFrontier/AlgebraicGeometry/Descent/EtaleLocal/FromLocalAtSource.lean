module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Defs

/-!
# Étale locality on source and target from locality on the source

Tag 04R2 derives étale locality on the source and target from étale locality on the source,
étale locality on the target, and stability under postcomposition with open immersions. The
difficult half of that proof — the induction on the degree of the fibres of an étale morphism
of affines — exists solely to upgrade stability under postcomposition with an *open immersion*
to stability under postcomposition with an *étale* morphism.

This file records the remaining, purely formal half: once stability under postcomposition with
an étale morphism is available outright, étale locality on the source alone already gives
étale locality on the source and target, and locality on the target is not needed at all —
only étale base change, which is a hypothesis in its own right.

For smoothness this is the whole story. Postcomposition with an étale morphism preserves
smoothness because an étale morphism is smooth and smooth morphisms compose, so the geometric
input of Tag 04R2 is not required: smoothness is étale local on the source and target as soon
as it is étale local on the source.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.ofArrows_mem_etalePrecoverage_iff`: membership in the étale precoverage.
* `AlgebraicGeometry.respectsLeft_etale_of_isLocalAtSource`: **Stacks 04QV**, étale case.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource`: étale locality on the
  source together with étale postcomposition and étale base change gives étale locality on the
  source and target.
* `AlgebraicGeometry.Smooth.respectsRight_etale`: postcomposition with an étale morphism
  preserves smoothness.
* `AlgebraicGeometry.smooth_isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, smooth case,
  conditional on smoothness being étale local on the source.

## Implementation notes

Locality on the source is Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtSource` for
`AlgebraicGeometry.Scheme.etalePrecoverage`, and the conclusion is the structure of Tag 04QZ.

The étale precoverage consists of the jointly surjective families of étale morphisms, so a
single étale morphism is a covering only when it is surjective. Adjoining the identity of the
target produces a covering containing an arbitrary étale morphism, which is how stability under
étale precomposition is extracted from locality on the source.

Étale base change is taken as `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, which
is how Mathlib states it for smoothness; the proof uses it only along étale morphisms.

## References

* [Stacks Project, Tag 04QV](https://stacks.math.columbia.edu/tag/04QV)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- A family of morphisms of schemes is an étale covering exactly when it is jointly
surjective and each of its members is étale. -/
theorem ofArrows_mem_etalePrecoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} :
    Presieve.ofArrows X f ∈ Scheme.etalePrecoverage S ↔
      (∀ x, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, Etale (f i) :=
  Scheme.ofArrows_mem_precoverage_iff _

namespace EtalePrecoverage

/-- The two-member family consisting of a morphism `a : X' ⟶ X` and the identity of `X`,
as a family of schemes over `X`. -/
private def withId {X' X : Scheme.{u}} (_a : X' ⟶ X) : Bool → Scheme.{u}
  | true => X'
  | false => X

/-- The two-member family consisting of a morphism `a : X' ⟶ X` and the identity of `X`. -/
private def withIdMap {X' X : Scheme.{u}} (a : X' ⟶ X) : ∀ b, withId a b ⟶ X
  | true => a
  | false => 𝟙 X

/-- Adjoining the identity of `X` to a `Q`-morphism `a : X' ⟶ X` gives a covering of `X` for the
precoverage of `Q`, of which `a` is a member. It is a covering because the identity is
surjective. -/
private theorem withIdMap_mem {Q : MorphismProperty Scheme.{u}}
    (hid : ∀ X : Scheme.{u}, Q (𝟙 X)) {X' X : Scheme.{u}} (a : X' ⟶ X) (ha : Q a) :
    Presieve.ofArrows (withId a) (withIdMap a) ∈ Scheme.precoverage Q X :=
  (Scheme.ofArrows_mem_precoverage_iff Q).mpr
    ⟨fun x => ⟨false, show x ∈ Set.range (𝟙 X : X ⟶ X).base by simp⟩, by
      rintro (_ | _)
      · exact hid X
      · exact ha⟩

end EtalePrecoverage

/-- A property of morphisms of schemes which is local on the source for the precoverage of a
class `Q` containing the identities is preserved by precomposition with a `Q`-morphism. -/
private theorem respectsLeft_of_isLocalAtSource (P Q : MorphismProperty Scheme.{u})
    (hP : P.IsLocalAtSource (Scheme.precoverage Q)) (hid : ∀ X : Scheme.{u}, Q (𝟙 X))
    {X' X Y : Scheme.{u}} (a : X' ⟶ X) (ha : Q a) (f : X ⟶ Y) (hf : P f) : P (a ≫ f) :=
  have := hP
  MorphismProperty.IsLocalAtSource.comp (EtalePrecoverage.withIdMap_mem hid a ha) a ⟨true⟩ hf

/-- A property of morphisms of schemes that is étale local on the source is preserved by
precomposition with an étale morphism. -/
theorem respectsLeft_etale_of_isLocalAtSource (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] :
    P.RespectsLeft (@Etale : MorphismProperty Scheme.{u}) where
  precomp a ha _f hf :=
    respectsLeft_of_isLocalAtSource P @Etale ‹_› (fun _ => inferInstance) a ha _ hf

namespace IsEtaleLocalOnSourceAndTarget

/-- A property of morphisms of schemes that is étale local on the source, stable under base
change, and preserved by postcomposition with an étale morphism, is étale local on the source
and target.

This is the formal part of Tag 04R2. The geometric part of that lemma is the derivation of
postcomposition stability along étale morphisms from postcomposition stability along open
immersions, which is assumed here. -/
theorem of_isLocalAtSource (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsStableUnderBaseChange]
    [P.RespectsRight (@Etale : MorphismProperty Scheme.{u})] :
    IsEtaleLocalOnSourceAndTarget P where
  precomp := respectsLeft_etale_of_isLocalAtSource P
  pullbackSnd_of_etale f hf g _ := MorphismProperty.pullback_snd f g hf
  iff_forall_exists_etale_neighborhood {X Y} f := by
    classical
    refine ⟨fun hf x => ⟨X, Y, 𝟙 X, 𝟙 Y, f, x, inferInstance, inferInstance, by simp, by simp,
      hf⟩, fun h => ?_⟩
    choose U V a b k u ha hb hu hcomm hP using h
    refine MorphismProperty.IsLocalAtSource.of_forall_comp
      (ofArrows_mem_etalePrecoverage_iff.mpr ⟨fun x => ⟨x, u x, hu x⟩, ha⟩) ?_
    rintro W g ⟨x⟩
    rw [← hcomm x]
    exact MorphismProperty.RespectsRight.postcomp (Q := @Etale) (b x) (hb x) (k x) (hP x)

end IsEtaleLocalOnSourceAndTarget

/-- Postcomposition with an étale morphism preserves smoothness: an étale morphism is smooth,
and smooth morphisms compose. -/
theorem Smooth.respectsRight_etale :
    MorphismProperty.RespectsRight (@Smooth : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    let : Etale i := hi
    let : Smooth f := hf
    exact inferInstance

/-- Being a smooth morphism of schemes is étale local on the source and target, given that it
is étale local on the source.

The geometric content of Tag 04R2 is not needed for smoothness: postcomposition with an étale
morphism preserves smoothness outright, by `AlgebraicGeometry.Smooth.respectsRight_etale`. -/
-- Deliberately NOT tagged `@[stacks 04R3 "smooth"]`. Stacks 04R3 asserts
-- `IsEtaleLocalOnSourceAndTarget @Smooth` *unconditionally*, whereas this theorem carries
-- `[IsLocalAtSource @Smooth Scheme.etalePrecoverage]`. An instance argument is still a
-- hypothesis -- and a less visible one than an explicit binder -- so tagging this would
-- record a weaker statement as though the tag were proved. The tag belongs on whatever
-- discharges that instance.
theorem smooth_isEtaleLocalOnSourceAndTarget
    [MorphismProperty.IsLocalAtSource (@Smooth : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage] :
    IsEtaleLocalOnSourceAndTarget (@Smooth : MorphismProperty Scheme.{u}) :=
  let := Smooth.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

end AlgebraicGeometry

end
