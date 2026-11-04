module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering

/-!
# One surjective flat morphism of finite presentation is an fppf covering

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of algebraic spaces
over `S` which is surjective (**Stacks 03ME**), flat (**Stacks 03ML**) and locally of finite
presentation (**Stacks 03XP**) is, all by itself, an fppf covering family of `Y` in the sense of
**Stacks 03Y8**: a one-member family whose single member is flat and locally of finite
presentation and whose image exhausts the points of the target.

Presented as a covering family of the fppf precoverage of **Stacks 03YH** on the algebraic spaces
over `S`, that is what lets a property of morphisms of algebraic spaces which is local on the base
for the fppf topology be tested on a single base change — the form in which fppf descent is
consumed.

## Main results

* `AlgebraicGeometry.Space.isFppfCovering_singleton`: **Stacks 03Y8** for the one-member family
  of a surjective flat morphism locally of finite presentation.
* `AlgebraicGeometry.Space.ofArrows_singleton_mem_fppf_precoverage`: that family as a covering of
  `AlgebraicGeometry.Space.Topology.fppf.precoverage`.
* `AlgebraicGeometry.Space.prop_iff_pullbackSnd_of_fppf`: a property local on the base for the
  fppf topology may be tested on the base change along such a morphism.
* `AlgebraicGeometry.Space.prop_of_isPullback_of_fppf`: the descent direction of that test, read
  on an arbitrary cartesian square rather than on the canonical pullback.

## Implementation notes

Surjectivity of a morphism of algebraic spaces is by definition surjectivity of the induced map
on points (`AlgebraicGeometry.Space.IsSurjective`), and joint surjectivity of a one-member family
is `Set.iUnion_const` followed by `Function.Surjective.range_eq`; so no comparison of point sets
occurs here and, unlike `AlgebraicGeometry.Space.isFppfCovering_atlas`, the source need not be
representable by a scheme. The target's and the source's algebraicity are the bundling data of
`AlgebraicGeometry.AlgebraicSpaces`.

The index type of the family is `PUnit` in the universe the precoverage quantifies over, which is
independent of the universe of the site; `AlgebraicGeometry.Space.Topology.precoverage` takes that
universe as a parameter, so it is written out at every use.

`prop_of_isPullback_of_fppf` is stated for an arbitrary cartesian square because that is the shape
a 2-fibre product of categories fibred in groupoids produces after being read on representing
presheaves; it is the canonical-pullback statement composed with
`CategoryTheory.IsPullback.isoPullback`, whose cancellation is available because
`CategoryTheory.MorphismProperty.IsLocalAtTarget` extends
`CategoryTheory.MorphismProperty.RespectsIso`.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03Y8 for a single morphism.** A surjective flat morphism of algebraic spaces over
`S` which is locally of finite presentation is an fppf covering family of its target, indexed by
a one-element type.

The two algebraicity clauses are the bundling data of the two objects, flatness and local finite
presentation are the hypotheses, and joint surjectivity of a one-member family is surjectivity of
its single map on points, which is what `AlgebraicGeometry.Space.IsSurjective` says. -/
theorem isFppfCovering_singleton {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    IsFppfCovering B S hS (fun _ : PUnit.{v + 1} => X.obj) (fun _ => f.hom) := by
  refine ⟨Y.property, fun _ => X.property, fun _ => hflat, fun _ => hlfp, ?_⟩
  simp only [Set.iUnion_const]
  exact hsurj.range_eq

/-- The one-member presieve of a surjective flat morphism of algebraic spaces over `S` locally of
finite presentation is a covering family of the fppf precoverage of **Stacks 03YH**. -/
theorem ofArrows_singleton_mem_fppf_precoverage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    Presieve.ofArrows (fun _ : PUnit.{v + 1} => X) (fun _ => f) ∈
      (Topology.fppf.precoverage.{u, v} B S hS).coverings Y :=
  ⟨PUnit.{v + 1}, fun _ => X, fun _ => f, rfl, Y.property, fun _ => X.property,
    isFppfCovering_singleton.{u, v} B S hS f hsurj hflat hlfp⟩

/-- **A property of morphisms of algebraic spaces over `S` local on the base for the fppf
topology may be tested on the base change along one surjective flat morphism locally of finite
presentation.** This is the form in which fppf descent of such a property is consumed: the
hypotheses on `f` are exactly those of **Stacks 03Y8** for a one-member family. -/
theorem prop_iff_pullbackSnd_of_fppf
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    P g ↔ P (pullback.snd g f) := by
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (ofArrows_singleton_mem_fppf_precoverage.{u, v} B S hS f hsurj hflat hlfp) (f := g)).trans
    ⟨fun h => h f (Presieve.ofArrows.mk PUnit.unit), ?_⟩
  intro h U k hpb hk
  cases hk
  exact h

/-- **The descent direction of `AlgebraicGeometry.Space.prop_iff_pullbackSnd_of_fppf`, read on an
arbitrary cartesian square.** If the square is cartesian and its bottom edge `f` is surjective,
flat and locally of finite presentation, then `P` holds of `g` as soon as it holds of the
projection `snd` to `X`.

Stated this way because a consumer producing the square as a 2-fibre product does not produce the
canonical pullback; the comparison is `CategoryTheory.IsPullback.isoPullback`, cancelled using the
`CategoryTheory.MorphismProperty.RespectsIso` that
`CategoryTheory.MorphismProperty.IsLocalAtTarget` extends. -/
theorem prop_of_isPullback_of_fppf
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {W X Y Z : AlgebraicSpaces B S hS} {g : Z ⟶ Y} {f : X ⟶ Y}
    {fst : W ⟶ Z} {snd : W ⟶ X} (hsq : IsPullback fst snd g f)
    (hsurj : IsSurjective B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hsnd : P snd) : P g := by
  have : HasPullback g f := hsq.hasPullback
  refine (prop_iff_pullbackSnd_of_fppf.{u, v} B S hS P g f hsurj hflat hlfp).2 ?_
  have hcancel : P (hsq.isoPullback.inv ≫ snd) :=
    (P.cancel_left_of_respectsIso hsq.isoPullback.inv snd).2 hsnd
  rw [hsq.isoPullback_inv_snd] at hcancel
  exact hcancel

end AlgebraicGeometry.Space

end
