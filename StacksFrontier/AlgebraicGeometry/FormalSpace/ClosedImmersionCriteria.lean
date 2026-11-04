module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion

/-!
# Criteria for a morphism of formal algebraic spaces to be a closed immersion

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Stacks 0GHY lists five conditions equivalent to `f` being a
closed immersion:

1. `f` is a closed immersion;
2. for every scheme `T` and morphism `T ⟶ Y` the projection `X ×_Y T ⟶ T` is a closed
   immersion;
3. the same for every affine scheme `T`;
4. there is a covering `{Y_j ⟶ Y}` as in Stacks 0AIM with each `X ×_Y Y_j ⟶ Y_j` a closed
   immersion;
5. there is a morphism `Z ⟶ Y` of formal algebraic spaces which is representable by algebraic
   spaces, surjective, flat and locally of finite presentation, with `X ×_Y Z ⟶ Z` a closed
   immersion.

This file proves the equivalence of (1) and (2) and the necessity of (4).

## Main definitions

* `AlgebraicGeometry.FormalSpace.yonedaSheaf`: an object of the big fppf site of `S` read as
  an fppf sheaf on that site, which is the shape a scheme-valued point of a formal algebraic
  space takes in conditions (2) and (3).

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_iff_forall_scheme`: **Stacks 0GHY** for
  conditions (1) and (2), the equivalence of being a closed immersion with every base change
  along a scheme-valued point of the target being a closed immersion.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_pullback_snd`: condition (2) and, a
  fortiori, condition (3) are necessary.
* `AlgebraicGeometry.FormalSpace.exists_atlas_isClosedImmersion_pullback_snd`: condition (4)
  is necessary.

## Implementation notes

A scheme-valued point of an fppf sheaf `Y` is a morphism out of the universe-lifted Yoneda
presheaf of an object of the big fppf site of `S`. That presheaf is a sheaf, being the
underlying presheaf of `AlgebraicGeometry.FormalSpace.yonedaSheaf`, so such a point is the
same thing as a morphism of fppf sheaves and the projection it produces is a morphism of fppf
sheaves to which `AlgebraicGeometry.FormalSpace.IsClosedImmersion` applies directly; no
sheafification of a Yoneda presheaf is involved. Both conditions are therefore tested against
the same family of points, and the equivalence of (1) and (2) is the statement that the
defining condition on `f` may be read off from its base changes one point at a time: the base
change of `X ×_Y T ⟶ T` along the identity of `T` is `X ×_Y T ⟶ T` itself, and the base change
of `f` along the point `T ⟶ Y` is the same morphism, so the conditions match up through the
isomorphisms comparing the three fibre products. Necessity is Stacks 0GHX; sufficiency uses
only that a property stable under base change along the universe-lifted Yoneda embedding is
invariant under isomorphism.

Condition (4) is spelled out rather than abbreviated, since the covering of Stacks 0AIM is the
atlas appearing in the definition of a formal algebraic space and that definition does not
name it. Its necessity needs the hypothesis that the target is a formal algebraic space, which
is where the covering comes from; the base changes are closed immersions by Stacks 0GHX.

The implications not formalized here are the descent steps of Stacks 0GHY: (3) implies (2),
which is Zariski-locality of the condition on the target, and (4) or (5) implies (1), which is
descent of closed immersions along a surjective étale covering and along a surjective flat
morphism locally of finite presentation. Condition (5) itself is not stated, as the notions of
a surjective, flat, locally finitely presented morphism of formal algebraic spaces are not yet
available. Two features of the source are worth recording for whoever completes the list. The
printed form of condition (5) asks that `X ×_Y Z ⟶ X` be a closed immersion; that is a typo,
since the descent it is used for concerns the projection to `Z`, and the intended condition is
that `X ×_Y Z ⟶ Z` be a closed immersion. The printed list also ends with an editorial note
asking for more conditions, so the source's list is open-ended; the equivalence to be
formalized is the one among conditions (1)–(5).

## References

* [Stacks Project, Tag 0GHX](https://stacks.math.columbia.edu/tag/0GHX)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object `T` of the big fppf site of `S`, read as an fppf sheaf on that site: its
underlying presheaf is the universe-lifted Yoneda presheaf of `T`, which is a sheaf because
the topology of the big fppf site of `S` is subcanonical. A morphism of fppf sheaves out of it
is the same thing as a scheme-valued point of the target at `T`. -/
def yonedaSheaf (T : BigFppfOver B S hS) : FppfSheaf B S hS :=
  ⟨(uliftYoneda.{u + 1}).obj T,
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T).isSheaf⟩

/-- Stacks 0GHY, condition (1) implies condition (2): a base change of a closed immersion of
fppf sheaves on the big fppf site of `S` along a scheme-valued point of its target is a closed
immersion. Restricting the objects `T` to the affine ones gives condition (3). -/
theorem isClosedImmersion_pullback_snd {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) (T : BigFppfOver B S hS)
    (g : yonedaSheaf B S hS T ⟶ Y) :
    IsClosedImmersion B S hS (pullback.snd f g) :=
  isClosedImmersion_of_isPullback B S hS (IsPullback.of_hasPullback f g) hf

/-- Stacks 0GHY, condition (2) implies condition (1): a morphism of fppf sheaves on the big
fppf site of `S` all of whose base changes along scheme-valued points of its target are closed
immersions is a closed immersion. -/
theorem isClosedImmersion_of_forall_scheme {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ Y),
      IsClosedImmersion B S hS (pullback.snd f g)) :
    IsClosedImmersion B S hS f := by
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let R := Q.relative (uliftYoneda.{u + 1})
  have key : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.1),
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ f.hom) ∧
        R (pullback.fst ξ f.hom) := by
    intro U ξ
    let g : yonedaSheaf B S hS U ⟶ Y := ⟨ξ⟩
    obtain ⟨hrep, hprop⟩ := h U g
    have hsq : IsPullback (pullback.fst f g).hom (pullback.snd f g).hom f.hom ξ :=
      (IsPullback.of_hasPullback f g).map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    have hid : IsPullback (pullback.snd f g).hom (𝟙 ((pullback f g).1))
        (𝟙 ((yonedaSheaf B S hS U).1)) (pullback.snd f g).hom := IsPullback.of_id_snd
    refine ⟨Space.isAlgebraicSpaceULift_of_iso B S hS
      (hid.isoPullback.symm ≪≫ hsq.flip.isoPullback)
      (hrep U (𝟙 ((yonedaSheaf B S hS U).1))), ?_⟩
    have h₀ : R (pullback.fst (𝟙 ((yonedaSheaf B S hS U).1)) (pullback.snd f g).hom) :=
      hprop U (𝟙 ((yonedaSheaf B S hS U).1))
    have h₁ : R ((pullback.snd f g).hom) := by
      rw [← hid.isoPullback_hom_fst]
      exact (R.cancel_left_of_respectsIso hid.isoPullback.hom _).mpr h₀
    rw [← hsq.flip.isoPullback_hom_fst] at h₁
    exact (R.cancel_left_of_respectsIso hsq.flip.isoPullback.hom _).mp h₁
  exact ⟨fun U ξ => (key U ξ).1, fun U ξ => (key U ξ).2⟩

/-- **Stacks 0GHY**, the equivalence of conditions (1) and (2): a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` is a closed immersion if and only if for every scheme `T`
over the big fppf site of `S` and every morphism `T ⟶ Y` the projection `X ×_Y T ⟶ T` is a
closed immersion. As with the definition of a closed immersion, no hypothesis that `X` and `Y`
are formal algebraic spaces is needed. -/
@[stacks 0GHY "conditions (1) and (2)"]
theorem isClosedImmersion_iff_forall_scheme {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsClosedImmersion B S hS f ↔
      ∀ (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ Y),
        IsClosedImmersion B S hS (pullback.snd f g) :=
  ⟨fun hf => isClosedImmersion_pullback_snd B S hS f hf,
    isClosedImmersion_of_forall_scheme B S hS f⟩

/-- Stacks 0GHY, condition (1) implies condition (4): if `f : X ⟶ Y` is a closed immersion and
`Y` is a formal algebraic space over `S`, then the atlas of `Y` furnished by Stacks 0AIM is a
covering `{Y_j ⟶ Y}` by affine formal algebraic spaces, representable by algebraic spaces and
étale, with surjective induced map from the coproduct, along which every base change of `f` is
a closed immersion. -/
theorem exists_atlas_isClosedImmersion_pullback_snd {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : IsClosedImmersion B S hS f) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (g : ∀ i, Yi i ⟶ Y),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Yi i)) ∧
      (∀ i, ∃ hgi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g i).hom hgi) ∧
      Sheaf.IsLocallySurjective (Sigma.desc g) ∧
      ∀ i, IsClosedImmersion B S hS (pullback.snd f (g i)) := by
  obtain ⟨-, I, Yi, g, haffine, hetale, hsurjective⟩ := hY
  exact ⟨I, Yi, g, haffine, hetale, hsurjective, fun i =>
    isClosedImmersion_of_isPullback B S hS (IsPullback.of_hasPullback f (g i)) hf⟩

end AlgebraicGeometry.FormalSpace

end
