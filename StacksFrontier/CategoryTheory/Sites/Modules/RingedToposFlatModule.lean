module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Modules flat over the base of a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi and let `F` be a sheaf of
`O`-modules. Then `F` is *flat over `(Sh(D), O')`* when it is flat as an `f⁻¹O'`-module, the
`f⁻¹O'`-module structure being restriction of scalars along the inverse-image form
`f⁻¹O' ⟶ O` of the structure map of `f`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.IsFlatOver`: flatness of a sheaf of `O`-modules over the
  target ringed topos of a morphism of ringed topoi.

## Implementation notes

This is flatness relative to a second ringed topos, and is not the absolute flatness of a
sheaf of modules over its own structure sheaf; the latter is
`AlgebraicGeometry.SheafOfModules.IsFlat`, in terms of which this predicate is stated. The two
agree for the identity morphism of a ringed topos only up to the identification of `O` with
`id⁻¹O`, so neither is a special case of the other on the nose.

The inverse-image form of the structure map is taken at the level of sheaves of commutative
rings and pushed to sheaves of rings by `CategoryTheory.sheafCompose` with
`forget₂ CommRingCat RingCat`, because restriction of scalars for sheaves of modules is indexed
by morphisms of sheaves of rings.

Three nearby notions are not this one.

* `AlgebraicGeometry.IsFlatOver`, Stacks 08KT part (2), is the same notion for a morphism of
  ringed *spaces*, where it is tested stalkwise rather than by exactness of a tensor functor.
* `AlgebraicGeometry.SheafOfModules.IsFlatMap`, Stacks 03ER part (4), is flatness of a morphism
  of sheaves of rings, so applied to `f⁻¹O' ⟶ O` it is flatness of `f` itself and quantifies
  over no module.
* `Deformation.ToposThickening.IsFlatOverBase` is the variant on a thickened topos, where the
  module lives over the direct image `i_*O` and the scalars are restricted along
  `i_*f⁻¹O_ℬ ⟶ i_*O`.

## References

* [Stacks Project, Tag 08M5](https://stacks.math.columbia.edu/tag/08M5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

/-- A sheaf `F` of `O`-modules on `X = (Sh(C), O)` is **flat over** the ringed topos
`Y = (Sh(D), O')` along a morphism of ringed topoi `f : X ⟶ Y` when `F`, regarded as a sheaf of
`f⁻¹O'`-modules by restriction of scalars along the inverse-image form `f⁻¹O' ⟶ O` of the
structure map of `f`, is flat. -/
@[stacks 08M5 "the definition: a sheaf of modules flat over the target ringed topos"]
noncomputable abbrev IsFlatOver
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
    (f : RingedToposHom X Y)
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  AlgebraicGeometry.SheafOfModules.IsFlat
    ((_root_.SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage)).obj F)

end AlgebraicGeometry.RingedToposHom
