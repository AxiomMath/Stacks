module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle

/-!
# An affine-space bundle over an irreducible base is irreducible

Let `f : X ⟶ Y` be an affine-space bundle of rank `r` in the sense of
`Stacks.Chow.IsAffineSpaceBundle`, so that every point of `Y` has an open neighbourhood `U` over
which `f` is the projection `𝔸^r_U ⟶ U`. This file shows that `X` is irreducible as soon as `Y`
is.

The argument is local on the target and goes through Mathlib's notion of a geometrically
irreducible morphism. Both `AlgebraicGeometry.GeometricallyIrreducible` — in its unfolded form
`AlgebraicGeometry.geometrically (IrreducibleSpace ·)`, which is where the Zariski-local instance
lives — and openness of the underlying map are local on the target, and both hold for the
projection of affine space over an arbitrary base; so
`Stacks.Chow.morphismProperty_of_isAffineSpaceBundle` transfers them to `f`, and
`AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace` concludes. The point of passing
through openness is that irreducibility of `X` needs more than irreducibility of the fibres: the
generic fibre has to be dense, which is what the open map gives.

## Main results

* `Stacks.Chow.irreducibleSpace_of_isAffineSpaceBundle`: **an affine-space bundle of rank `r`
  over an irreducible scheme has irreducible total space.**
* `Stacks.LineBundle.Situation.irreducibleSpace_totalSpace`: **the total space of a line bundle
  over an irreducible scheme is irreducible**, which is the rank-one case applied to
  `Stacks.LineBundle.Situation.isAffineSpaceBundle_totalSpaceToBase`.
* `Stacks.LineBundle.irreducibleSpace_lineBundleSpace`: the same at the `lineBundleProj` spelling
  of [Stacks, Tag 01M2] used by the construction of [Stacks, Tag 0F97].

## Implementation notes

Only the weak `IrreducibleSpace` conclusion is drawn here, because that is all an affine-space
bundle hypothesis alone gives: reducedness of `X` needs reducedness of `Y` as a further
hypothesis, and with it `Stacks.Chow.isReduced_of_isAffineSpaceBundle` and
`Stacks.Chow.isIntegral_of_isAffineSpaceBundle` upgrade these statements to
`AlgebraicGeometry.IsReduced` and `AlgebraicGeometry.IsIntegral`.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)

/-- **An affine-space bundle is a geometrically irreducible morphism.** Geometric irreducibility
is Zariski-local on the target in its unfolded form `geometrically (IrreducibleSpace ·)`, and
affine `r`-space over a base is geometrically irreducible over it. -/
theorem geometricallyIrreducible_of_isAffineSpaceBundle (h : IsAffineSpaceBundle f r) :
    GeometricallyIrreducible f := by
  rw [geometricallyIrreducible_iff]
  refine morphismProperty_of_isAffineSpaceBundle
    (AlgebraicGeometry.geometrically (fun Z : Scheme.{u} => IrreducibleSpace Z)) f r
    (fun T => ?_) h
  exact (geometricallyIrreducible_iff _).mp inferInstance

/-- **The underlying map of an affine-space bundle is open.** Openness of the underlying map is
Zariski-local on the target, and the projection of affine space over a base is open. -/
theorem isOpenMap_of_isAffineSpaceBundle (h : IsAffineSpaceBundle f r) : IsOpenMap f.base :=
  morphismProperty_of_isAffineSpaceBundle
    (AlgebraicGeometry.topologically @IsOpenMap) f r
    (fun T => AffineSpace.isOpenMap_over T) h

/-- **An affine-space bundle of rank `r` over an irreducible scheme has irreducible total
space.** -/
theorem irreducibleSpace_of_isAffineSpaceBundle (h : IsAffineSpaceBundle f r)
    [IrreducibleSpace Y] : IrreducibleSpace X :=
  have := geometricallyIrreducible_of_isAffineSpaceBundle f r h
  GeometricallyIrreducible.irreducibleSpace f (isOpenMap_of_isAffineSpaceBundle f r h)

end Stacks.Chow

namespace Stacks.LineBundle

/-- **The total space of a line bundle over an irreducible scheme is irreducible.** The total
space is an affine-space bundle of rank one over the scheme the bundle lives on, by
`Stacks.LineBundle.Situation.isAffineSpaceBundle_totalSpaceToBase`. -/
theorem Situation.irreducibleSpace_totalSpace (D : Situation.{u}) [IrreducibleSpace D.X] :
    IrreducibleSpace D.totalSpace :=
  Stacks.Chow.irreducibleSpace_of_isAffineSpaceBundle D.totalSpaceToBase 1
    D.isAffineSpaceBundle_totalSpaceToBase

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The total space of the line bundle of an invertible module on an irreducible scheme is
irreducible**, at the `lineBundleProj` spelling of [Stacks, Tag 01M2] that the construction of
[Stacks, Tag 0F97] uses. -/
theorem irreducibleSpace_lineBundleSpace [IrreducibleSpace Y] :
    IrreducibleSpace (lineBundleSpace Y M) :=
  Stacks.Chow.irreducibleSpace_of_isAffineSpaceBundle (lineBundleProj Y M) 1
    (isAffineSpaceBundle_lineBundleProj Y M)

end Stacks.LineBundle

end
