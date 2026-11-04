module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable

/-!
# The direct-image map of a morphism over `X`, at one étale chart

`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` identifies the sections of the
direct-image algebra `Y.hom_* 𝒪_Y` over an étale chart `V` of `X` with the global regular
functions on the scheme `Y ×_X V`, for `Y` over `X` with representable structure morphism.  This
file reads the map `AlgebraicGeometry.Space.pushforwardRingMap` which a morphism `f : Y ⟶ Z` of
`CategoryTheory.Over X` induces on direct images through that identification, at one chart, and
records the one thing about it that the development can presently prove: it is a morphism of
`Γ(V)`-algebras.

## Main results

* `AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app`: **the chart
  value of the direct-image map is a map of `Γ(V)`-algebras.**  Transported by
  `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at the source and the target, the
  component at `V` of `AlgebraicGeometry.Space.pushforwardRingMap f` is a ring map
  `Γ(Z ×_X V) ⟶ Γ(Y ×_X V)` commuting with pullback of regular functions along the two cartesian
  projections to `V`.

## Implementation notes

**What this is and what it is not.**  The statement below says that the chart value of
`AlgebraicGeometry.Space.pushforwardRingMap f` is a `Γ(V)`-algebra map.  It does **not** say that
it is the map which the base-changed morphism of schemes `Y ×_X V ⟶ Z ×_X V` induces on regular
functions; that identification is
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`, which needs the
chart-level composition law of base change and is therefore proved after this file.  The
distinction is the content Stacks 081V's faithfulness clause turns on: it needs the equal
direct-image maps to force the restricted morphisms equal, and for that the chart value has to be
*recognised as coming from `f`*, not merely known to respect the base.

Of the naturality square that identification is, this file supplies the triangle over the base.
The square itself is read off the four factors of
`AlgebraicGeometry.Space.pushforwardRingMap`: the two composition-carrying ones by
`AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentableComp`, which reads
the comparison `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso` of iterated direct
images and `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` on the sections over a
chart; the first factor, the direct image along `Z.hom` of the structure map of `f.left`, by
naturality of `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` in its sheaf
argument; and the fourth by eliminating the equation `CategoryTheory.Over.w` that its transport
is built from.

**Why the proof is two rewrites.**  Both edges of the triangle are instances of
`AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`, Stacks 03G8 part (2) at
one chart, one at `Z.hom` and one at `Y.hom`; what joins them is
`AlgebraicGeometry.Space.fSharp_comp_pushforwardRingMap`, the statement that the structure-algebra
map of `Z` followed by the direct-image map of `f` is the structure-algebra map of `Y`, read at
the chart by `AlgebraicGeometry.Space.commRingSheafHom_app_congr`.  Nothing about the four
factors of `AlgebraicGeometry.Space.pushforwardRingMap` is unfolded, which is why the chart value
comes out constrained but not identified.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart value of the direct-image map of a morphism over `X` is a map of
`Γ(V)`-algebras.**  Let `f : Y ⟶ Z` be a morphism of algebraic spaces over `X` whose two
structure morphisms are representable, and let `V` be an étale scheme chart of `X`.  Read through
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at `Z` and at `Y`, the component at `V`
of `AlgebraicGeometry.Space.pushforwardRingMap f` is a ring map
`Γ(Z ×_X V) ⟶ Γ(Y ×_X V)` which carries the pullback of regular functions along the cartesian
projection `Z ×_X V ⟶ V` to the pullback along `Y ×_X V ⟶ V`.

Both triangles are
`AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`, Stacks 03G8 part (2) at
a single chart, and what joins them is
`AlgebraicGeometry.Space.fSharp_comp_pushforwardRingMap`.

This does **not** identify the map with the one induced by the base-changed morphism
`Y ×_X V ⟶ Z ×_X V`; that is
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward`. -/
theorem cartesianProjectionAppTop_comp_pushforwardRingMap_app
    {X : AlgebraicSpaces B S hS} {Y Z : Over X} (f : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (hZ.snd V.1.hom)).appTop ≫
        (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv ≫
        (pushforwardRingMap B S hS f).hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Y hY V).hom =
      ((BigFppfOver.toScheme B S hS).map (hY.snd V.1.hom)).appTop := by
  have key : (smallEtaleRingedToposHom B S hS Z.hom).fSharp.hom.app (op V) ≫
      (pushforwardRingMap B S hS f).hom.app (op V) =
      (smallEtaleRingedToposHom B S hS Y.hom).fSharp.hom.app (op V) :=
    commRingSheafHom_app_congr (fSharp_comp_pushforwardRingMap B S hS f) (op V)
  rw [← fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z hZ V,
    ← fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Y hY V]
  exact (cancelRetractionLeft ((smallEtaleRingedToposHom B S hS Z.hom).fSharp.hom.app (op V))
        (pushforwardAlgebraSectionsIso B S hS Z hZ V).hom_inv_id
        ((pushforwardRingMap B S hS f).hom.app (op V) ≫
          (pushforwardAlgebraSectionsIso B S hS Y hY V).hom)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ (pushforwardAlgebraSectionsIso B S hS Y hY V).hom) key))

end AlgebraicGeometry.Space

end
