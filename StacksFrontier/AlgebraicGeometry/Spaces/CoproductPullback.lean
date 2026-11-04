module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# Pulling back a coproduct of fppf sheaves at an arbitrary index type

`StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive` shows that a coproduct of sheaves of
types is a van Kampen colimit at any index type. This file records what that says on the big
fppf site over a scheme `S`, where it is the step that splits a representable sheaf along a
coproduct of subfunctors.

Mathlib supplies only `CategoryTheory.FinitaryExtensive` for a category of sheaves, which is
why `AlgebraicGeometry.Space.isOpenImmersion_coproductInj` has to complement a chosen summand
with the sheafified join of the others in order to reduce to the binary case. The results here
need no such reduction.

## Main results

* `AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback`: if `G` is the coproduct
  of a family `Fᵢ` of fppf sheaves over `S` and each `Aᵢ` sits in a pullback square over
  `t : A ⟶ G` and `ι i : Fᵢ i ⟶ G`, then `A` is the coproduct of the `Aᵢ`.
* `AlgebraicGeometry.Space.isColimitCofanMkPullback` is the same statement for the chosen
  pullbacks `Fᵢ ×_G A`.

## Implementation notes

The index type carries `Small.{u} I`. That is the same condition as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf`, and for the same reason: it is what
makes an `I`-indexed coproduct of `Type u`-valued sheaves land in `Type u` again, and it is
simultaneously what `AlgebraicGeometry.Scheme.{u}` needs for a coproduct to exist, so it is
the right condition on both sides of the comparison between sheaf and scheme coproducts. It
cannot be read off the colimit hypothesis: a cofan of initial objects with initial vertex is a
colimit cofan for an index type of any size.

The square form is stated first and the chosen-pullback form derived from it, because a caller
holding a `CategoryTheory.MorphismProperty.presheaf` hypothesis gets its pullback squares from
`CategoryTheory.Functor.relativelyRepresentable.isPullback` rather than from
`CategoryTheory.Limits.pullback`, and converting between the two is pointless work.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

variable {I : Type v} [Small.{u} I]
  {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}

/-- **A family of pullback squares over a coproduct of fppf sheaves exhibits the source as a
coproduct.** If `G` is the coproduct of the family `Fᵢ`, if `t : A ⟶ G` is an arbitrary
morphism of fppf sheaves over `S`, and if each `Aᵢ` sits in a pullback square over `t` and
`ι i`, then `A` is the coproduct of the `Aᵢ`. There is no restriction on the size of the index
type beyond `Small.{u} I`, and in particular no finiteness hypothesis. -/
theorem nonempty_isColimit_cofanMk_of_isPullback (ι : ∀ i, Fᵢ i ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι))
    {A : Sheaf (BigFppfOver.topology B S hS) (Type u)} (t : A ⟶ G)
    {Aᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)} (p : ∀ i, Aᵢ i ⟶ A)
    (q : ∀ i, Aᵢ i ⟶ Fᵢ i) (hpb : ∀ i, IsPullback (p i) (q i) t (ι i)) :
    Nonempty (IsColimit (Cofan.mk A p)) :=
  let := BigFppfOver.hasSheafify_type B S hS
  Sheaf.nonempty_isColimit_cofanMk_of_isPullback _ ι hcoprod t p q hpb

/-- **Pulling back a coproduct of fppf sheaves decomposes the source as a coproduct.** The
chosen-pullback form of `AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback`. -/
noncomputable def isColimitCofanMkPullback (ι : ∀ i, Fᵢ i ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι))
    {A : Sheaf (BigFppfOver.topology B S hS) (Type u)} (t : A ⟶ G)
    [∀ i, HasPullback (ι i) t] :
    IsColimit (Cofan.mk A fun i ↦ pullback.snd (ι i) t) :=
  (nonempty_isColimit_cofanMk_of_isPullback B S hS ι hcoprod t _
    (fun i ↦ pullback.fst (ι i) t) fun i ↦ (IsPullback.of_hasPullback (ι i) t).flip).some

end Space

end AlgebraicGeometry

end
