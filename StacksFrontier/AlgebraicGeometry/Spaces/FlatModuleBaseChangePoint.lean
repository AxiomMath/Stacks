module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Stacks 05VW at a point of the point space

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module.  Part (1) of Stacks 05VW says that if `F` is flat over `Y` at a
point of `X`, then the inverse image `(g')^*F` is flat over `Y'` at every point of `X'` above
it.  `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChange.lean` proves that at a
*geometric* point, as `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`.  This
file reads it at a point of the point space `|X|` of Stacks 03BU, where flatness at a point is
membership of the relative flat locus `AlgebraicGeometry.Space.flatLocus` of Stacks 0DLR.

That reading is what the consumers of Stacks 05VW in this tree ask for, and several of them
carry it as a hypothesis.

## Main results

* `AlgebraicGeometry.Space.mem_flatLocus_modulePullback_of_mem_flatLocus`: **Stacks 05VW,
  part (1), at a point of the point space.**
* `AlgebraicGeometry.Space.isFlatOverAtPoint_baseChange`: **Stacks 05VW** in full, at a point
  of the point space for a cartesian square of algebraic spaces: parts (1) and (2) and the final
  assertion, for a quasi-coherent module and nothing more.

## Implementation notes

The relative flat locus of Stacks 0DLR is the *some-chart* condition: a point lies in it when
some commuting square of étale scheme charts through it witnesses flatness of the restricted
module at a point of the source chart.  For a quasi-coherent module that condition is Stacks 05VU
flatness of the geometric stalk at a geometric point above the given point, by
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleLocusOpen.lean`.  The proof of part (1) is that
chart-free reading on both sides of the square together with the geometric-point form of
part (1).  So nothing about charts enters, and in particular the statement does not depend on
which chart the some-chart locus of Stacks 0DLR picks.

Quasi-coherence of the inverse image, which the reading on the side of `X'` needs, is
Stacks 03GA,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.

The cartesian square is taken on the underlying presheaves, as the consumers take it, and is
transported to the category of algebraic spaces — where
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback` asks for it — by
faithfulness of the inclusion.

## References

* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **Stacks 05VW, part (1), at a point of the point space.**  In a cartesian square of
algebraic spaces

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

let `F` be a quasi-coherent `𝒪_X`-module and let `x'` be a point of `|X'|`.  If `F` is flat over
`Y` at the image of `x'` in `|X|`, then the inverse image `(g')^*F` is flat over `Y'` at `x'`,
flatness at a point being membership of the relative flat locus of Stacks 0DLR.

A geometric point of `X'` above `x'` exists by Stacks 04XE, flatness at a point is flatness of
the geometric stalk there by
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`, and the implication
between the two geometric-stalk conditions is part (1) of Stacks 05VW,
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`.  The inverse image is
quasi-coherent by Stacks 03GA. -/
@[stacks 05VW "part (1) read at a point of the point space of Stacks 03BU, flatness at a point \
being membership of the relative flat locus of Stacks 0DLR"]
theorem mem_flatLocus_modulePullback_of_mem_flatLocus {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x' : points B S hS X'.1)
    (hx : pointsMap B S hS X'.1 g'.hom x' ∈ flatLocus B S hS X.2 f.hom F) :
    x' ∈ flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) := by
  have hcat : IsPullback g' f' f g := IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F
      inferInstance
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X'.1 x'
  subst hxbar
  refine (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f' _ xbar).2
    (isFlatOverAtGeometricPoint_modulePullback B S hS hcat F xbar ?_)
  exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F
    (geometricPointMap g'.hom xbar)).1 hx

/-- **Stacks 05VW, part (2), at a point of the point space.**  In a cartesian square of
algebraic spaces

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

let `F` be a quasi-coherent `𝒪_X`-module, let `x'` be a point of `|X'|` and suppose that `g` is
flat at the image of `x'` in `|Y'|`.  If the inverse image `(g')^*F` is flat over `Y'` at `x'`,
then `F` is flat over `Y` at the image of `x'` in `|X|`, flatness at a point being membership of
the relative flat locus of Stacks 0DLR.

The proof is that of part (1) read in the opposite direction: a geometric point of `X'` above
`x'` exists by Stacks 04XE, flatness at a point is flatness of the geometric stalk there by
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`, and the implication
between the two geometric-stalk conditions is part (2) of Stacks 05VW,
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback`.  The inverse image is
quasi-coherent by Stacks 03GA. -/
@[stacks 05VW "part (2) read at a point of the point space of Stacks 03BU, flatness at a point \
being membership of the relative flat locus of Stacks 0DLR"]
theorem mem_flatLocus_of_mem_flatLocus_modulePullback {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x' : points B S hS X'.1)
    (hg : IsFlatAt B S hS g.hom (pointsMap B S hS X'.1 f'.hom x'))
    (hx : x' ∈ flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)) :
    pointsMap B S hS X'.1 g'.hom x' ∈ flatLocus B S hS X.2 f.hom F := by
  have hcat : IsPullback g' f' f g := IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F
      inferInstance
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X'.1 x'
  subst hxbar
  refine (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F
    (geometricPointMap g'.hom xbar)).2
    (isFlatOverAtGeometricPoint_of_modulePullback B S hS hcat F xbar hg ?_)
  exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f' _ xbar).1 hx

/-- **Stacks 05VW.**  Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S`, let `F` be a quasi-coherent `𝒪_X`-module
and write `F' = (g')^*F`.  For every point `x'` of `|X'|` with image `x` in `|X|`:

1. if `F` is flat over `Y` at `x`, then `F'` is flat over `Y'` at `x'`;
2. if `g` is flat at the image `f'(x')` of `x'` in `|Y'|` and `F'` is flat over `Y'` at `x'`,
   then `F` is flat over `Y` at `x`;

and in particular, if `F` is flat over `Y`, then `F'` is flat over `Y'`.

Flatness of a module over the target at a point of the point space is
`AlgebraicGeometry.Space.IsFlatOverAtPoint` of Stacks 05VV, flatness over the target is
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV, and flatness of `g` at a point is
`AlgebraicGeometry.Space.IsFlatAt` of Stacks 03ML part (2).

At a point, a geometric point of `X'` above `x'` exists by Stacks 0488 part (1), flatness at a
point is flatness of the geometric stalk there by Stacks 05VU,
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`, and the two parts are
then `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback` and
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback`.  The final assertion is
`AlgebraicGeometry.Space.isFlatOver_modulePullback`, the quasi-coherence of `F'` it asks for
being Stacks 03GA,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, so that
nothing beyond quasi-coherence of `F` is assumed. -/
@[stacks 05VW "parts (1) and (2) at a point of |X'|, flatness at a point being Stacks 05VV (1), \
and the final assertion, for a quasi-coherent module"]
theorem isFlatOverAtPoint_baseChange {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] :
    (∀ x' : points B S hS X'.1,
        IsFlatOverAtPoint B S hS X.2 f.hom F (pointsMap B S hS X'.1 g'.hom x') →
          IsFlatOverAtPoint B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) x') ∧
      (∀ x' : points B S hS X'.1, IsFlatAt B S hS g.hom (pointsMap B S hS X'.1 f'.hom x') →
        IsFlatOverAtPoint B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) x' →
          IsFlatOverAtPoint B S hS X.2 f.hom F (pointsMap B S hS X'.1 g'.hom x')) ∧
      (IsFlatOver B S hS X.2 f.hom F →
        IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)) := by
  have : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F inferInstance
  refine ⟨fun x' hx => ?_, fun x' hg hx => ?_, isFlatOver_modulePullback B S hS hpb F⟩
  · obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X'.1 x'
    exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f' _ xbar).2
      (isFlatOverAtGeometricPoint_modulePullback B S hS hpb F xbar
        ((mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F
          (geometricPointMap g'.hom xbar)).1 hx))
  · obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X'.1 x'
    exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F
        (geometricPointMap g'.hom xbar)).2
      (isFlatOverAtGeometricPoint_of_modulePullback B S hS hpb F xbar hg
        ((mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f' _ xbar).1 hx))

end AlgebraicGeometry.Space

end
