module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable

/-!
# Closed immersions of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of formal
algebraic spaces over `S` is a *closed immersion* (Stacks 0ANP) when it is representable by
algebraic spaces and a closed immersion in the sense of Stacks 03XZ: every base change of `f`
along a scheme-valued point of `Y` is a closed immersion of schemes.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsClosedImmersion`: closed immersions of formal algebraic
  spaces over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_comp`: **Stacks 0GHW**, a composite of two
  closed immersions is a closed immersion.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_isPullback`: **Stacks 0GHX**, a base
  change of a closed immersion is a closed immersion.

## Implementation notes

The condition does not use the witnesses that the source and the target are formal algebraic
spaces, so it is stated for an arbitrary morphism of fppf sheaves, as the source's Tag 03XZ
condition is. Representability is the notion of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the sheaves carrying formal
algebraic spaces take values in `Type (u + 1)` rather than in `Type u`; the representability
witness is bundled with the property because it is what makes the base changes algebraic
spaces, so the definition is an existential over that witness rather than a conjunction.

## References

* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0GHW](https://stacks.math.columbia.edu/tag/0GHW)
* [Stacks Project, Tag 0GHX](https://stacks.math.columbia.edu/tag/0GHX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of formal algebraic spaces over `S` is a *closed immersion* when it is
representable by algebraic spaces and every base change of it along a scheme-valued point of its
target is a closed immersion of schemes. The condition makes sense, and is stated, for an
arbitrary morphism of fppf sheaves on the big fppf site of `S`. -/
@[stacks 0ANP]
abbrev IsClosedImmersion {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) g.hom) f.hom hrep

/-- Closed immersions of schemes, read as a property of the morphisms of the big fppf site of
`S`, are stable under base change. -/
@[ega "I 10.14.5" "(ii), special case"]
instance inverseImage_isClosedImmersion_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  refine ⟨?_⟩
  intro X Y Y' Z f g f' g' hp hg
  exact AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (hp.map (BigFppfOver.toScheme B S hS)) hg

/-- Closed immersions of schemes are stable under composition, read as a property of the
morphisms of the big fppf site of `S`. -/
@[ega "I 10.14.5" "(i), special case"]
private instance inverseImage_isClosedImmersion_isStableUnderComposition :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition := by
  let _ : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) := by
    refine ⟨?_⟩
    intro X Y Z f g hf hg
    let _ : AlgebraicGeometry.IsClosedImmersion f := hf
    let _ : AlgebraicGeometry.IsClosedImmersion g := hg
    exact AlgebraicGeometry.IsClosedImmersion.comp f g
  exact MorphismProperty.IsStableUnderComposition.inverseImage _

/-- A closed immersion of the big fppf site of `S` stays a closed immersion after every
represented base change of its universe-lifted Yoneda image. -/
private theorem relative_isClosedImmersion_uliftYoneda_map
    {V U : BigFppfOver B S hS} (t : V ⟶ U)
    (ht : MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) t) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      ((uliftYoneda.{u + 1}).map t) :=
  MorphismProperty.relative_map ht

/-- A morphism property respecting isomorphisms holds for the top of a pullback square exactly
when it holds for the first projection of the canonical pullback. -/
private theorem iff_fst_of_isPullback {C : Type*} [Category C] (R : MorphismProperty C)
    [R.RespectsIso] {P A B D : C} {p : P ⟶ A} {q : P ⟶ B} {ξ : A ⟶ D} {h : B ⟶ D}
    [HasPullback ξ h] (sq : IsPullback p q ξ h) : R p ↔ R (pullback.fst ξ h) := by
  rw [← sq.isoPullback_hom_fst]
  exact (R.cancel_left_of_respectsIso sq.isoPullback.hom _)

/-- A composite of two closed immersions of formal algebraic spaces over `S` is a closed
immersion. -/
@[stacks 0GHW, ega "I 4.2.5" "closed immersions"]
theorem isClosedImmersion_comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsClosedImmersion B S hS f) (hg : IsClosedImmersion B S hS g) :
    IsClosedImmersion B S hS (f ≫ g) := by
  obtain ⟨hfRep, hfProp⟩ := hf
  obtain ⟨hgRep, hgProp⟩ := hg
  refine ⟨Space.isRepresentableByAlgebraicSpacesULift_comp B S hS f.hom g.hom hfRep hgRep, ?_⟩
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let R := Q.relative (uliftYoneda.{u + 1})
  let _ : R.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  intro U ξ
  have hq : R (pullback.fst ξ g.hom) := by simpa [R, Q] using hgProp U ξ
  obtain ⟨hrel, hprop⟩ := hq
  obtain ⟨V, t, s, hpb⟩ := hrel (𝟙 ((uliftYoneda.{u + 1}).obj U))
  have ht : Q t := hprop (g := 𝟙 _) s t hpb
  let ξ' : (uliftYoneda.{u + 1}).obj V ⟶ Y.1 := s ≫ pullback.snd ξ g.hom
  have hfc : R (pullback.fst ξ' f.hom) := by simpa [R, Q, ξ'] using hfProp V ξ'
  have hRt : R ((uliftYoneda.{u + 1}).map t) := by
    simpa [R, Q] using relative_isClosedImmersion_uliftYoneda_map B S hS t ht
  have hcompC : R (pullback.fst ξ' f.hom ≫ (uliftYoneda.{u + 1}).map t) :=
    MorphismProperty.comp_mem _ _ _ hfc hRt
  let _ : IsIso s := hpb.isIso_fst_of_isIso
  have hV : IsPullback ((uliftYoneda.{u + 1}).map t) (s ≫ pullback.snd ξ g.hom) ξ g.hom := by
    apply (IsPullback.of_hasPullback ξ g.hom).of_iso'
      (asIso s) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa using hpb.w
    all_goals simp
  have hsquare : IsPullback
      (pullback.fst ξ' f.hom ≫ (uliftYoneda.{u + 1}).map t)
      (pullback.snd ξ' f.hom) ξ (f.hom ≫ g.hom) :=
    (IsPullback.of_hasPullback ξ' f.hom).paste_horiz hV
  exact (iff_fst_of_isPullback R hsquare).mp hcompC

/-- **Stacks 046F** in the value universe `Type (u + 1)`: in a cartesian square of presheaves
on the big fppf site of `S` whose right-hand column `a` is representable by algebraic spaces
and whose projections have a property `Q` invariant under isomorphism, the projections of the
left-hand column `a'` have `Q` as well. -/
private theorem hasPropertyULift_of_isPullback
    (Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))) [Q.RespectsIso]
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {k : F' ⟶ F} {a' : F' ⟶ G'} {a : F ⟶ G} {g : G' ⟶ G} (sq : IsPullback k a' a g)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a)
    (ha' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a')
    (hP : Space.HasPropertyULift.{u + 1} B S hS (fun _ _ f ↦ Q f.hom) a ha) :
    Space.HasPropertyULift.{u + 1} B S hS (fun _ _ f ↦ Q f.hom) a' ha' := by
  intro U ξ
  have hpaste : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ k) (ξ ≫ g) a :=
    ((IsPullback.of_hasPullback ξ a').flip.paste_horiz sq).flip
  have h₀ : Q (pullback.fst (ξ ≫ g) a) := hP U (ξ ≫ g)
  exact (iff_fst_of_isPullback Q hpaste).mpr h₀

/-- A base change of a closed immersion of formal algebraic spaces over `S` is a closed
immersion: in a cartesian square of fppf sheaves on the big fppf site of `S` whose right-hand
column `f` is a closed immersion, the left-hand column `snd` is a closed immersion. -/
@[stacks 0GHX]
theorem isClosedImmersion_of_isPullback {X Y Y' P : FppfSheaf B S hS}
    {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback fst snd f g)
    (hf : IsClosedImmersion B S hS f) : IsClosedImmersion B S hS snd := by
  obtain ⟨hrep, hprop⟩ := hf
  have hsq : IsPullback fst.hom snd.hom f.hom g.hom :=
    sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let R := Q.relative (uliftYoneda.{u + 1})
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hsq hrep,
    hasPropertyULift_of_isPullback B S hS R hsq hrep _ hprop⟩

end AlgebraicGeometry.FormalSpace

end
