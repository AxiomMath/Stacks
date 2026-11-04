module

public import Mathlib.Tactic.TFAE
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.LocallyNoetherianFibres
public import StacksCore.Tactic.StacksAttribute

/-!
# Normal morphisms are the flat morphisms with geometrically normal fibres

Normality of a morphism of schemes is defined pointwise: at each point of the source the morphism
is flat and the fibre through that point is geometrically normal at it. This file identifies that
condition with the two global properties it is assembled from, namely flatness of the morphism and
geometric normality of each of its fibres as a scheme over the residue field of its base point.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isNormal_of_flat_of_isGeometricallyNormal_fiber`: a flat morphism
  all of whose fibres are geometrically normal schemes is a normal morphism.
* `AlgebraicGeometry.Scheme.Hom.isNormal_iff`: a morphism is normal exactly when it is flat and
  each of its fibres is a geometrically normal scheme.
* `AlgebraicGeometry.Scheme.Hom.isNormal_tfae`: the equivalence of Tag 0391, stated for a morphism
  all of whose fibres are locally Noetherian.

## Implementation notes

Flatness of a morphism of schemes, Mathlib's `AlgebraicGeometry.Flat`, is an affine-local property
rather than a pointwise one, so the passage between it and the stalkwise flatness entering the
definition of a normal morphism is `AlgebraicGeometry.Flat.iff_flat_stalkMap`. Geometric normality
of a fibre is pointwise by definition, so the fibre halves differ only in which points of the
fibre are named: the definition of a normal morphism tests the point `f.asFiber x` coming from a
point `x` of the source, and every point of a fibre arises this way, which is the content of
`AlgebraicGeometry.Scheme.Hom.IsNormal.isGeometricallyNormal_fiber`.

The source states the equivalence under its standing hypothesis that all fibres of the morphism
are locally Noetherian, and `AlgebraicGeometry.Scheme.Hom.isNormal_tfae` reproduces it there,
using the property `AlgebraicGeometry.locallyNoetherianFibers` of Tag 0392. That hypothesis is
what makes the pointwise notion of Tag 0390 the intended one; neither implication consumes it,
so the equivalence itself is recorded unconditionally as
`AlgebraicGeometry.Scheme.Hom.isNormal_iff`.

## References

* [Stacks Project, Tag 0391](https://stacks.math.columbia.edu/tag/0391)
* [Stacks Project, Tag 0390](https://stacks.math.columbia.edu/tag/0390)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat morphism whose fibres are geometrically normal schemes over the residue fields of
their base points is a normal morphism. -/
@[ega "IV 6.8.4" "6.8.4(ii)"]
public theorem isNormal_of_flat_of_isGeometricallyNormal_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Flat f) (hfib : ∀ s : Y, IsGeometricallyNormal (f.fiberToSpecResidueField s)) :
    IsNormal f := fun x =>
  ⟨show IsFlatAt f.toLRSHom.toShHom x from (Flat.iff_flat_stalkMap f).1 hf x,
    hfib (f x) (f.asFiber x)⟩

/-- A morphism of schemes is normal exactly when it is flat and each of its fibres is a
geometrically normal scheme over the residue field of its base point. -/
@[stacks 0391 "stated without the source's standing hypothesis that all fibres are locally \
Noetherian, which neither implication uses", sga "6 XII 1.6"]
public theorem isNormal_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsNormal f ↔ Flat f ∧ ∀ s : Y, IsGeometricallyNormal (f.fiberToSpecResidueField s) :=
  ⟨fun hf => ⟨IsNormal.flat hf, IsNormal.isGeometricallyNormal_fiber hf⟩,
    fun hf => isNormal_of_flat_of_isGeometricallyNormal_fiber f hf.1 hf.2⟩

/-- **Stacks Project, Tag 0391.** For a morphism of schemes all of whose fibres are locally
Noetherian, being normal is equivalent to being flat with geometrically normal fibres. -/
@[stacks 0391]
public theorem isNormal_tfae {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hfib : locallyNoetherianFibers f) :
    List.TFAE
      [IsNormal f, Flat f ∧ ∀ s : Y, IsGeometricallyNormal (f.fiberToSpecResidueField s)] := by
  tfae_have 1 ↔ 2 := isNormal_iff f
  tfae_finish

end AlgebraicGeometry.Scheme.Hom

end
