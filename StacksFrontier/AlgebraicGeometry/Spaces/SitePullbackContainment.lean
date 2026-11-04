module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize

/-!
# A big fppf site contains the fibre products of the schemes it contains

The underlying category of a big fppf site over `S` is the schemes whose size is below a
cardinal which is a strong prelimit, so it is closed under the two operations which bound the
size of a fibre product: the product in the slice over `S`, by
`AlgebraicGeometry.BigFppfSite.contains_prod_left`, and the source of a monomorphism, by
`AlgebraicGeometry.BigFppfSite.contains_of_mono`.  A fibre product in the slice over `S` is a
subobject of the product of its two factors, so it is contained whenever they are.

This is what lets the schemes built in the course of a groupoid argument — the arrow scheme of a
restriction, the scheme of composable pairs of a subgroupoid — be tested in the site without
their containment being carried as a hypothesis.

## Main results

* `AlgebraicGeometry.BigFppfSite.mono_pullbackToProd`: the comparison of a fibre product in the
  slice over `S` with the product of its factors is a monomorphism.
* `AlgebraicGeometry.BigFppfSite.contains_pullback_left`: a big fppf site over `S` contains the
  scheme underlying a fibre product of two objects of `Over S` whose underlying schemes it
  contains.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSite

variable {S : Scheme.{u}}

/-- The comparison of a fibre product in the slice over `S` with the product of its two
factors.  It is a monomorphism, because a generalized point of a fibre product is determined by
its two projections. -/
noncomputable def pullbackToProd {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ⟶ (X ⨯ Y : Over S) :=
  prod.lift (pullback.fst f g) (pullback.snd f g)

instance mono_pullbackToProd {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Mono (pullbackToProd f g) where
  right_cancellation {_T} a b h := by
    refine pullback.hom_ext ?_ ?_
    · have h₁ := congrArg (fun k => k ≫ prod.fst) h
      simpa only [Category.assoc, pullbackToProd, prod.lift_fst] using h₁
    · have h₂ := congrArg (fun k => k ≫ prod.snd) h
      simpa only [Category.assoc, pullbackToProd, prod.lift_snd] using h₂

/-- **A big fppf site over `S` contains the fibre products of the schemes it contains.** -/
theorem contains_pullback_left (B : BigFppfSite.{u}) {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : B.Contains X.left) (hY : B.Contains Y.left) :
    B.Contains (pullback f g).left :=
  B.contains_of_mono (pullbackToProd f g).left
    (B.contains_prod_left X Y hX hY)

end AlgebraicGeometry.BigFppfSite

end
