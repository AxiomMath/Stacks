module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalOnSourceAndTarget

/-!
# The étale-smooth diagram criterion for morphisms of algebraic spaces (Stacks 0CG1)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target in the sense of **Stacks 0CFZ**, and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Stacks 0CG1 compares `P f` with seven conditions; this module proves
the two of them that the statements of Stacks 0CIF are phrased through, namely its conditions
(c) and (d):

```
U ---h---> V
|          |
a          b
v          v
X ---f---> Y
```

with `b` smooth and the induced `U ⟶ X ×_Y V` étale — condition (d) asks `P h` of *every* such
diagram, condition (c) of *one* with `a` surjective.

## Main results

* `AlgebraicGeometry.Space.prop_of_etale_smooth_surjective_diagram`: **Stacks 0CG1**,
  (c) ⇒ (a).
* `AlgebraicGeometry.Space.prop_of_etale_smooth_surjective_square`: the same, with the diagram
  given by its two vertical morphisms and the comparison taken to be the canonical one.
* `AlgebraicGeometry.Space.prop_etale_smooth_diagram_of_prop`: **Stacks 0CG1**, (a) ⇒ (d).

## Implementation notes

Both directions come from the three fields of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget` alone; neither needs Stacks 0CG0,
whose content is the comparison of Definition 0CFZ with étale locality on the source and smooth
locality on the target. In particular neither carries an fppf
`CategoryTheory.MorphismProperty.IsLocalAtTarget` hypothesis.

The diagram is given by the comparison morphism `e : U ⟶ X ×_Y V` rather than by the pair
`(a, h)`, which is the shape the locality field of Stacks 0CFZ is stated in; a consumer holding
`a` and `h` together with the commuting square supplies
`CategoryTheory.Limits.pullback.lift`, whose composites with the two projections are `a` and `h`.
The fibre product is `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of **Stacks 02X2**, with
its first projection to `X` and its second to `V`.

Surjectivity of `a` is surjectivity of the induced map on points, i.e.
`AlgebraicGeometry.Space.IsSurjective` of **Stacks 03ME**, written out as surjectivity of
`AlgebraicGeometry.Space.pointsMap` so that the point produced is exactly what the locality field
consumes.

Of the other conditions of Stacks 0CG1, (b) is the locality field of Stacks 0CFZ itself, and
(e), (f) and (g) are the conditions of Stacks 0CG0.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CG1, (c) ⇒ (a).** Let `P` be étale-smooth local on the source-and-target. If there
is one diagram over `f : X ⟶ Y` with smooth right-hand vertical morphism `b : V ⟶ Y`, étale
comparison `e : U ⟶ X ×_Y V`, left-hand vertical morphism `e ≫ pr_X` surjective on points, and
with `P` of the top horizontal morphism `e ≫ pr_V`, then `f` has `P`.

Every point of `X` is the image of a point of `U`, so the given diagram is the étale-smooth
neighbourhood that the locality field of Stacks 0CFZ asks for at each point. -/
theorem prop_of_etale_smooth_surjective_diagram
    {P : MorphismProperty (AlgebraicSpaces B S hS)}
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {X Y U V : AlgebraicSpaces B S hS} (f : X ⟶ Y) (b : V ⟶ Y)
    (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
    (hb : IsSmooth B S hS b.hom) (he : IsEtale B S hS e.hom)
    (hsurj : Function.Surjective (pointsMap B S hS U.1
      (e ≫ (ObjectProperty.homMk (pullback.fst f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom))
    (hPh : P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
      AlgebraicSpaces.fiberProduct B S hS f b ⟶ V))) :
    P f := by
  refine (hP.iff_forall_exists_etale_smooth_neighborhood f).2 (fun x => ?_)
  obtain ⟨uu, hu⟩ := hsurj x
  exact ⟨V, U, b, e, uu, hb, he, hu, hPh⟩

/-- **Stacks 0CG1, (c) ⇒ (a), with the diagram given by its two vertical morphisms.** Let `P` be
étale-smooth local on the source-and-target, and let

```
U ---h---> V
|          |
α          β
v          v
F ---φ---> G
```

be a commuting square of algebraic spaces over `S` in which `β` is smooth, `α` is surjective on
points, the induced comparison `U ⟶ F ×_G V` is étale, and `h` has `P`. Then `φ` has `P`.

This is `AlgebraicGeometry.Space.prop_of_etale_smooth_surjective_diagram` with the comparison
`CategoryTheory.Limits.pullback.lift` of the given square in place of an abstract morphism to the
fibre product; it is the form a diagram of Stacks 0CIF produces after the two vertical
1-morphisms are read as morphisms of representing algebraic spaces. -/
theorem prop_of_etale_smooth_surjective_square
    {P : MorphismProperty (AlgebraicSpaces B S hS)}
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {F G U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (φ : F ⟶ G) (β : V ⟶ G) (α : U ⟶ F) (h : U ⟶ V)
    (hcomm : α ≫ φ = h ≫ β)
    (hβ : IsSmooth B S hS β)
    (hα : Function.Surjective (pointsMap B S hS U α))
    (he : IsEtale B S hS (pullback.lift α h hcomm))
    (hPh : P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)) :
    P (ObjectProperty.homMk φ : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) := by
  refine prop_of_etale_smooth_surjective_diagram B S hS hP
    (ObjectProperty.homMk φ : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
    (ObjectProperty.homMk β : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
    (ObjectProperty.homMk (pullback.lift α h hcomm) :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶
        AlgebraicSpaces.fiberProduct B S hS
          (ObjectProperty.homMk φ : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
          (ObjectProperty.homMk β : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩))
    hβ he ?_ ?_
  · change Function.Surjective (pointsMap B S hS U (pullback.lift α h hcomm ≫ pullback.fst φ β))
    rwa [pullback.lift_fst]
  · change P (ObjectProperty.homMk (pullback.lift α h hcomm ≫ pullback.snd φ β) :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)
    rwa [pullback.lift_snd]

/-- **Stacks 0CG1, (a) ⇒ (d).** Let `P` be étale-smooth local on the source-and-target. If
`f : X ⟶ Y` has `P`, then so does the top horizontal morphism of *every* diagram over `f` with
smooth right-hand vertical morphism and étale comparison to the fibre product.

The base change `X ×_Y V ⟶ V` has `P` because `P` is stable under smooth base change, and the
top horizontal morphism is that base change precomposed with the étale comparison. No
surjectivity is needed. -/
theorem prop_etale_smooth_diagram_of_prop
    {P : MorphismProperty (AlgebraicSpaces B S hS)}
    (hP : IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {X Y U V : AlgebraicSpaces B S hS} (f : X ⟶ Y) (b : V ⟶ Y)
    (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
    (hb : IsSmooth B S hS b.hom) (he : IsEtale B S hS e.hom) (hf : P f) :
    P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
      AlgebraicSpaces.fiberProduct B S hS f b ⟶ V)) :=
  hP.precomp_of_etale e _ he (hP.pullbackSnd_of_smooth f hf b hb)

end AlgebraicGeometry.Space

end
