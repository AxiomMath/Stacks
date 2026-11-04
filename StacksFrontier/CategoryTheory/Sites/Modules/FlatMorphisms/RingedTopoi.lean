module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat morphisms of ringed topoi

A morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is *flat* when the
inverse-image form `f⁻¹O_D ⟶ O_C` of its structure map is a flat morphism of sheaves of rings,
that is, when `O_C` is flat as an `f⁻¹O_D`-module. Flatness of a morphism of ringed sites is
the same condition on the structure map of the associated morphism of ringed topoi.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.IsFlat` is flatness of a morphism of ringed topoi.

## Implementation notes

The structure map is taken in its inverse-image form, which is the form the source uses.
Flatness of a morphism of sheaves of rings is `AlgebraicGeometry.SheafOfModules.IsFlatMapULift`:
the rings of sections are first lifted into a universe containing the site, where the tensor
product of sheaves of modules is available, so that flatness imposes no sheafification or
local-bijectivity hypotheses on the caller and the universe of the sections stays independent
of the universes of the underlying site.

Flatness of a morphism of ringed *sites* is the already available
`AlgebraicGeometry.RingedSite.Hom.IsFlat`, which is this condition on the inverse-image form
of that morphism's structure map.

## References

* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

/-- A morphism of ringed topoi is flat when its inverse-image structure map is flat. -/
@[stacks 04JB "flat morphisms of ringed topoi",
  sga "4 Vbis 2.4.3.1" "non-fibered case",
  sga "4 V 1.8" "left flat"]
abbrev IsFlat {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (f : RingedToposHom X Y) : Prop :=
  SheafOfModules.IsFlatMapULift f.fSharpInverseImage

end AlgebraicGeometry.RingedToposHom

add_to_stacks 04JB "flat morphisms of ringed sites" AlgebraicGeometry.RingedSite.Hom.IsFlat

end
