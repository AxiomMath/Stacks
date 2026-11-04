module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData

/-!
# The fibre products of a family of the big fppf category as chosen pullbacks

`CategoryTheory.Pseudofunctor.DescentData'` presents a descent datum by transition isomorphisms
over *chosen* binary and threefold fibre products, and
`CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence` identifies that presentation
with the choice-free `CategoryTheory.Pseudofunctor.DescentData`.  To read a descent datum for
quasi-coherent modules relative to a family of *representable* algebraic spaces on the underlying
family of schemes, the fibre products of the family have to be presented in that form, and the
choice has to be the one the representability comparison sees: the fibre product taken in the big
fppf category over `S` and then carried to schemes, not an unrelated fibre product of schemes.

This file makes that choice.  The big fppf category over `S` has fibre products and
`AlgebraicGeometry.BigFppfOver.toScheme` preserves them, both by Stacks 021U, so
`CategoryTheory.Limits.ChosenPullback.ofHasPullback`,
`CategoryTheory.Limits.ChosenPullback₃.ofHasPullbacks` and the two `map` constructions of
`StacksFrontier/CategoryTheory/Sites/Descent/RestrictedBaseDescentData.lean` supply everything; what
is added is the instantiation and the `CategoryTheory.IsPullback` witness the `map` constructions
ask for.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.siteFibreProduct` and
  `AlgebraicGeometry.BigFppfOver.siteFibreProduct₃`: the fibre products of the big fppf category
  over `S`, as chosen pullbacks.
* `AlgebraicGeometry.BigFppfOver.schemeFibreProduct` and
  `AlgebraicGeometry.BigFppfOver.schemeFibreProduct₃`: **the fibre products of a family of the
  big fppf category over `S`, read on the underlying schemes.**  These are the chosen pullbacks
  a transported `CategoryTheory.Pseudofunctor.DescentData'` is indexed by.

## Main results

* `AlgebraicGeometry.BigFppfOver.isPullback_map_siteFibreProduct`: the image of the chosen fibre
  product on the underlying schemes is a fibre product there.

## Implementation notes

The object and the projections of `AlgebraicGeometry.BigFppfOver.schemeFibreProduct` are, by
construction, the images of those of `AlgebraicGeometry.BigFppfOver.siteFibreProduct`.  That is
the point: a morphism into the chosen pullback of schemes which a transport has to produce is
then the image of a morphism of the site, so the comparison with the fibre product of the
representable algebraic spaces is an equality of spellings rather than a further isomorphism.

No `stacks` attribute is registered.  Stacks 021U is tagged where the fibre products of the big
fppf category over `S` and their preservation are proved; what is added here is their packaging
as chosen pullbacks, which is a step in the proof of Stacks 04W8.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 021U.**  The fibre product of two morphisms of the big fppf category over `S`, as a
chosen pullback. -/
public noncomputable abbrev siteFibreProduct {X Y T : BigFppfOver B S hS} (f : X ⟶ T)
    (g : Y ⟶ T) : ChosenPullback f g :=
  ChosenPullback.ofHasPullback f g

/-- **Stacks 021U.**  The threefold wide fibre product of three morphisms of the big fppf
category over `S` with common target, as a threefold wide chosen pullback of the three binary
ones. -/
public noncomputable abbrev siteFibreProduct₃ {X Y Z T : BigFppfOver B S hS} (f : X ⟶ T)
    (g : Y ⟶ T) (h : Z ⟶ T) :
    ChosenPullback₃ (siteFibreProduct B S hS f g) (siteFibreProduct B S hS g h)
      (siteFibreProduct B S hS f h) :=
  ChosenPullback₃.ofHasPullbacks _ _ _

/-- **Stacks 021U.**  The chosen fibre product of the big fppf category over `S`, read on the
underlying schemes, is a fibre product of schemes:
`AlgebraicGeometry.BigFppfOver.toScheme` preserves fibre products. -/
public theorem isPullback_map_siteFibreProduct {X Y T : BigFppfOver B S hS} (f : X ⟶ T)
    (g : Y ⟶ T) :
    IsPullback ((toScheme B S hS).map (siteFibreProduct B S hS f g).p₁)
      ((toScheme B S hS).map (siteFibreProduct B S hS f g).p₂) ((toScheme B S hS).map f)
      ((toScheme B S hS).map g) :=
  (siteFibreProduct B S hS f g).isPullback.map (toScheme B S hS)

/-- **The fibre product of two morphisms of the big fppf category over `S`, read on the
underlying schemes.**  This is the chosen pullback a descent datum transported from a family of
representable algebraic spaces is indexed by: its object is the scheme underlying the fibre
product of the site, and its projections are the underlying morphisms of the projections. -/
public noncomputable abbrev schemeFibreProduct {X Y T : BigFppfOver B S hS} (f : X ⟶ T)
    (g : Y ⟶ T) :
    ChosenPullback ((toScheme B S hS).map f) ((toScheme B S hS).map g) :=
  (siteFibreProduct B S hS f g).map (toScheme B S hS)
    (isPullback_map_siteFibreProduct B S hS f g)

/-- **The threefold wide fibre product of three morphisms of the big fppf category over `S`, read
on the underlying schemes.**  This is the threefold wide chosen pullback the cocycle condition of
a transported descent datum is read over. -/
public noncomputable abbrev schemeFibreProduct₃ {X Y Z T : BigFppfOver B S hS} (f : X ⟶ T)
    (g : Y ⟶ T) (h : Z ⟶ T) :
    ChosenPullback₃ (schemeFibreProduct B S hS f g) (schemeFibreProduct B S hS g h)
      (schemeFibreProduct B S hS f h) :=
  (siteFibreProduct₃ B S hS f g h).map (toScheme B S hS)
    (isPullback_map_siteFibreProduct B S hS f g)
    (isPullback_map_siteFibreProduct B S hS g h)
    (isPullback_map_siteFibreProduct B S hS f h)
    ((siteFibreProduct₃ B S hS f g h).isPullback₂.map (toScheme B S hS))

end AlgebraicGeometry.BigFppfOver

end
