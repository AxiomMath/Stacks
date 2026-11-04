module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperEtaleDescent

/-!
# Properness of morphisms of formal algebraic spaces is local on the target

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of fppf sheaves
over `S` is proper in the sense of **Stacks 0AM6** when every base change of it along a
scheme-valued point of `Y` is an algebraic space over `S` proper over that point. This file
proves that the condition may be checked after a surjective étale covering of each
scheme-valued point by one object of the site: both halves of it descend along such a covering,
being an algebraic space by **Stacks 0BGR** and properness by **Stacks 0422**.

This is for properness what
`AlgebraicGeometry.FormalSpace.isRepresentable_of_forall_surjective_etale_cover` is for
representability by algebraic spaces, and it is the form in which a covering of a scheme-valued
point of the target — by its affine opens, or by charts of the members of a covering as in
Definition 0AIM — is used.

## Main results

* `AlgebraicGeometry.FormalSpace.isProper_of_forall_surjective_etale_cover`: **properness is
  local on the target** along one surjective étale morphism of the site per point.
* `AlgebraicGeometry.FormalSpace.isProper_of_isRepresentable_of_forall_fppfFamily`: the same
  along a covering *family* of the site per point, for a morphism already known to be
  representable by algebraic spaces.

## Implementation notes

Both halves are checked at one scheme-valued point `ξ : U ⟶ Y` at a time. The base change of
`f` along `ξ` is a sheaf, and the morphism to it from its base change along the covering
`q : U' ⟶ U` is a base change of the universe-lifted Yoneda image of `q`, hence representable by
objects of the site, surjective and étale; so Stacks 0BGR applies to it and
`AlgebraicGeometry.Space.isProperULift_of_isPullback_uliftYoneda_map` applies to the cartesian
square it sits in. The hypothesis is stated for the base change along the composite
`U' ⟶ U ⟶ Y`, which is the shape a caller has, and is compared with the base change along `q`
of the base change along `ξ` by `CategoryTheory.Limits.pullbackRightPullbackFstIso`.

Nothing is asked of `X` or `Y` beyond the sheaf condition, and the conclusion is the full
properness of `f`, representability included.

The family form asks for representability instead of producing it. The reason is that the family
form of Stacks 0422 — `AlgebraicGeometry.Space.isProperULift_of_isPullback_uliftYoneda_family`
— descends properness along an arbitrary covering family of the site, whereas Stacks 0BGR
descends being an algebraic space only along a *single* morphism representable by objects of the
site; turning a family into one such morphism means forming the coproduct of its members inside
the site and knowing that the coproduct of the base changes is again an algebraic space, which
is Stacks 02WQ in the value universe `Type (u + 1)`,
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_coproduct`. That coproduct also needs a uniform
size bound on the atlases of the members, which is why the family form is the convenient one
whenever representability is already known; it is used that way in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ProperAffineLocal`.

## References

* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Properness of morphisms of formal algebraic spaces is local on the target.** A morphism
`f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` is proper in the sense of
**Stacks 0AM6** as soon as every scheme-valued point `ξ : U ⟶ Y` of its target admits a
morphism `q : U' ⟶ U` of the site, surjective and étale on underlying schemes, such that the
base change of `f` along `U' ⟶ U ⟶ Y` is an algebraic space over `S` proper over `U'`.

Being an algebraic space descends along `q` by **Stacks 0BGR** and properness by
**Stacks 0422**, both applied to the base change of the universe-lifted Yoneda image of `q`
along the projection of the base change of `f` along `ξ`. -/
@[stacks 0AM6 "local on the target"]
theorem isProper_of_forall_surjective_etale_cover {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      ∃ (U' : BigFppfOver B S hS) (q : U' ⟶ U),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        Space.IsAlgebraicSpaceULift.{u + 1} B S hS
          (pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom) ∧
        Space.IsProperULift.{u + 1} B S hS
          (pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom)) :
    IsProper B S hS f := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.surjectiveOnSite B S hS)
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.etaleOnSite B S hS)
  have key : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ f.hom) ∧
        Space.IsProperULift.{u + 1} B S hS (pullback.fst ξ f.hom) := by
    intro U ξ
    obtain ⟨U', q, hqs, hqe, halg', hproper'⟩ := h U ξ
    have hUL : Space.IsAlgebraicSpaceULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U) :=
      Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U
    have hU'L : Space.IsAlgebraicSpaceULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U') :=
      Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U'
    have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback ξ f.hom) :=
      Presheaf.isSheaf_pullback _ ξ f.hom hUL.isSheaf X.cond Y.cond
    -- the base change along `q` of the base change along `ξ`
    have halg2 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
        (pullback ((uliftYoneda.{u + 1}).map q) (pullback.fst ξ f.hom)) :=
      Space.isAlgebraicSpaceULift_of_iso B S hS
        (pullbackRightPullbackFstIso ξ f.hom ((uliftYoneda.{u + 1}).map q)).symm halg'
    -- being an algebraic space descends: Stacks 0BGR
    have halgU : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ f.hom) :=
      Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS hsheaf halg2
        (pullback.snd ((uliftYoneda.{u + 1}).map q) (pullback.fst ξ f.hom))
        (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
          (Space.relative_uliftYoneda_map B S hS _ q hqs))
        (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _)
          (Space.relative_uliftYoneda_map B S hS _ q hqe))
    refine ⟨halgU, ?_⟩
    -- properness descends: Stacks 0422
    have hp'proper : Space.IsProperULift.{u + 1} B S hS
        (pullback.fst ((uliftYoneda.{u + 1}).map q) (pullback.fst ξ f.hom)) := by
      have h1 := Space.isProperULift_precomp B S hS
        (pullbackRightPullbackFstIso ξ f.hom ((uliftYoneda.{u + 1}).map q))
        (pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom) halg2 halg' hU'L hproper'
      rwa [pullbackRightPullbackFstIso_hom_fst] at h1
    exact Space.isProperULift_of_isPullback_uliftYoneda_map B S hS q
      (IsPullback.of_hasPullback ((uliftYoneda.{u + 1}).map q) (pullback.fst ξ f.hom)).flip
      halgU hqs hqe hp'proper
  exact ⟨fun U ξ => (key U ξ).1, fun U ξ => (key U ξ).2⟩


/-- **Properness of a morphism representable by algebraic spaces is local on the target for a
covering family of the site.** Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf
site of `S` which is representable by algebraic spaces, and suppose every scheme-valued point
`ξ : U ⟶ Y` of its target admits a family `{qᵢ : Vᵢ ⟶ U}` of morphisms of the site whose Yoneda
images form an fppf covering family of `U`, such that the base change of `f` along each
`Vᵢ ⟶ U ⟶ Y` is proper as a morphism of algebraic spaces. Then `f` is proper in the sense of
**Stacks 0AM6**.

Unlike `AlgebraicGeometry.FormalSpace.isProper_of_forall_surjective_etale_cover` this takes a
*family* and not one morphism, so it needs no coproduct of the members inside the site; what it
asks instead is that `f` be representable by algebraic spaces, since being an algebraic space is
the half of properness which the family form of **Stacks 0422** does not descend. The base
change of `f` along `Vᵢ ⟶ U ⟶ Y` is compared with the base change along `qᵢ` of the base change
along `ξ` by `CategoryTheory.Limits.pullbackRightPullbackFstIso`. -/
@[stacks 0AM6 "local on the target for a covering family, given representability"]
theorem isProper_of_isRepresentable_of_forall_fppfFamily {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (h : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      ∃ (Idx : Type (u + 1)) (V : Idx → BigFppfOver B S hS) (q : ∀ i, V i ⟶ U),
        Space.IsFppfCovering B S hS (fun i => yoneda.obj (V i))
          (fun i => yoneda.map (q i)) ∧
        ∀ i, Space.IsProperULift.{u + 1} B S hS
          (pullback.fst ((uliftYoneda.{u + 1}).map (q i) ≫ ξ) f.hom)) :
    IsProper B S hS f := by
  refine ⟨hrep, fun U ξ => ?_⟩
  obtain ⟨Idx, V, q, hcov, hp'⟩ := h U ξ
  have hsqi : ∀ i, IsPullback
      ((pullbackRightPullbackFstIso ξ f.hom ((uliftYoneda.{u + 1}).map (q i))).inv ≫
        pullback.snd ((uliftYoneda.{u + 1}).map (q i)) (pullback.fst ξ f.hom))
      (pullback.fst ((uliftYoneda.{u + 1}).map (q i) ≫ ξ) f.hom)
      (pullback.fst ξ f.hom) ((uliftYoneda.{u + 1}).map (q i)) := by
    intro i
    refine ((IsPullback.of_hasPullback ((uliftYoneda.{u + 1}).map (q i))
      (pullback.fst ξ f.hom)).flip).of_iso
      (pullbackRightPullbackFstIso ξ f.hom ((uliftYoneda.{u + 1}).map (q i)))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
    simp
  exact Space.isProperULift_of_isPullback_uliftYoneda_family B S hS hsqi (hrep U ξ) hcov hp'

end AlgebraicGeometry.FormalSpace

end
