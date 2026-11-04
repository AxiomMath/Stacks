module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# An open of an object of the big h category over `S` is again one

The class of schemes a `AlgebraicGeometry.BigHSite` admits is cut out by a cardinality bound, and
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` says the bound is inherited by an open
subscheme. So an open of an object of the big h category over `S` is again an object of it, over
the same base, and its inclusion is a morphism of the site. This is the analogue for the big h
site of `AlgebraicGeometry.BigFppfOver.opensObj` and `AlgebraicGeometry.BigEtaleOver.opensObj`.

## Main definitions

* `AlgebraicGeometry.BigHOver.opensObj`: **an open of an object of the big h category over `S`,
  as an object of that category.**
* `AlgebraicGeometry.BigHOver.opensι`: its inclusion, as a morphism of the site.
* `AlgebraicGeometry.BigHOver.opensHom`: the inclusion of one open into a larger one.

## Main results

* `AlgebraicGeometry.BigHOver.contains_opens`: the scheme class of a big h site is closed under
  passing to an open subscheme.
* `AlgebraicGeometry.BigHOver.toScheme_obj_opensObj`, `..._map_opensι` and `..._map_opensHom`: the
  underlying scheme and morphisms of schemes are the open subscheme and its inclusions, by
  definition.
* `AlgebraicGeometry.BigHOver.opensRange_toScheme_map_opensι`: the image of the inclusion is the
  open itself.

## Implementation notes

The three `toScheme` computations are `rfl`: `AlgebraicGeometry.BigHOver.toScheme` is the
composite of the forgetful functor to the scheme class with the inclusion of that class, and both
act on an object of the slice by projection. They are stated as `@[simp]` lemmas since these
projections are not unfolded by `simp`.

## References

* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.BigHOver

/-- **The scheme class of a big h site is closed under passing to an open subscheme.** The class
is cut out by a cardinality bound, and the bound is inherited along a monomorphism which is
locally of finite presentation, by Stacks 000R. -/
public theorem contains_opens (B : BigHSite.{u}) {Z : Scheme.{u}} (hZ : B.Contains Z)
    (W : Z.Opens) : B.Contains (W : Scheme.{u}) :=
  Scheme.size_lt_of_isOpenImmersion W.ι hZ

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open of an object of the big h category over `S`, as an object of that category.** Its
structure morphism to `S` is the inclusion of the open followed by the structure morphism of the
ambient object. -/
@[implicit_reducible]
public def opensObj {X : BigHOver B S hS} (W : ((toScheme B S hS).obj X).Opens) :
    BigHOver B S hS :=
  Over.mk
    ((ObjectProperty.homMk W.ι :
      B.obj (W : Scheme.{u}) (contains_opens B ((forget B S hS).obj X).2 W) ⟶
        (forget B S hS).obj X) ≫ X.hom)

/-- The structure morphism of `opensObj B S hS W` is the inclusion of `W` followed by the structure
morphism of `X`. -/
@[simp]
public theorem opensObj_hom_hom {X : BigHOver B S hS}
    (W : ((toScheme B S hS).obj X).Opens) :
    (opensObj B S hS W).hom.hom = W.ι ≫ X.hom.hom := rfl

/-- The underlying scheme of `opensObj B S hS W` is the open subscheme `W`. -/
@[simp]
public theorem toScheme_obj_opensObj {X : BigHOver B S hS}
    (W : ((toScheme B S hS).obj X).Opens) :
    (toScheme B S hS).obj (opensObj B S hS W) = (W : Scheme.{u}) := rfl

/-- **The inclusion of an open of an object of the big h category over `S`**, as a morphism of
that category. -/
@[implicit_reducible]
public def opensι {X : BigHOver B S hS} (W : ((toScheme B S hS).obj X).Opens) :
    opensObj B S hS W ⟶ X :=
  Over.homMk (ObjectProperty.homMk W.ι) (by simp [opensObj])

/-- The underlying morphism of schemes of `opensι B S hS W` is the inclusion `W.ι`. -/
@[simp]
public theorem toScheme_map_opensι {X : BigHOver B S hS}
    (W : ((toScheme B S hS).obj X).Opens) :
    (toScheme B S hS).map (opensι B S hS W) = W.ι := rfl

/-- The inclusion of an open of an object of the big h category over `S` is an open immersion of
schemes. -/
public instance isOpenImmersion_toScheme_map_opensι {X : BigHOver B S hS}
    (W : ((toScheme B S hS).obj X).Opens) :
    IsOpenImmersion ((toScheme B S hS).map (opensι B S hS W)) :=
  inferInstanceAs (IsOpenImmersion W.ι)

/-- **The image of the inclusion of an open is that open.** -/
@[simp]
public theorem opensRange_toScheme_map_opensι {X : BigHOver B S hS}
    (W : ((toScheme B S hS).obj X).Opens) :
    ((toScheme B S hS).map (opensι B S hS W)).opensRange = W :=
  W.opensRange_ι

/-- **The inclusion of one open of an object of the big h category over `S` into a larger one**,
as a morphism of that category. -/
@[implicit_reducible]
public noncomputable def opensHom {X : BigHOver B S hS}
    {W W' : ((toScheme B S hS).obj X).Opens} (h : W ≤ W') :
    opensObj B S hS W ⟶ opensObj B S hS W' :=
  Over.homMk
    (ObjectProperty.homMk
      (X := B.obj (W : Scheme.{u}) (contains_opens B ((forget B S hS).obj X).2 W))
      (Y := B.obj (W' : Scheme.{u}) (contains_opens B ((forget B S hS).obj X).2 W'))
      (((toScheme B S hS).obj X).homOfLE h))
    (by
      apply ObjectProperty.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom, opensObj_hom_hom, opensObj_hom_hom,
        ← Category.assoc]
      exact congrArg (fun k => k ≫ X.hom.hom)
        (Scheme.homOfLE_ι (X := (toScheme B S hS).obj X) h))

/-- The underlying morphism of schemes of `opensHom B S hS h` is the inclusion
`Scheme.homOfLE h` of `W` into `W'`. -/
@[simp]
public theorem toScheme_map_opensHom {X : BigHOver B S hS}
    {W W' : ((toScheme B S hS).obj X).Opens} (h : W ≤ W') :
    (toScheme B S hS).map (opensHom B S hS h) = ((toScheme B S hS).obj X).homOfLE h := rfl

/-- The inclusion of a smaller open into a larger one composed with the inclusion of the larger
one is the inclusion of the smaller one, as morphisms of the site. -/
@[simp]
public theorem opensHom_opensι {X : BigHOver B S hS}
    {W W' : ((toScheme B S hS).obj X).Opens} (h : W ≤ W') :
    opensHom B S hS h ≫ opensι B S hS W' = opensι B S hS W := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  rw [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom]
  exact Scheme.homOfLE_ι (X := (toScheme B S hS).obj X) h

end AlgebraicGeometry.BigHOver

end
