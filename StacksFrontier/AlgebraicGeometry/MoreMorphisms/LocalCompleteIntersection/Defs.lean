module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local complete intersection morphisms

A morphism of schemes `f : X ⟶ S` is *Koszul at* a point `x` of `X` when it is of finite type at
`x` and, on some open neighbourhood `U` of `x`, the restriction `f|_U` factors as a
Koszul-regular immersion `U ⟶ P` followed by a smooth morphism `P ⟶ S`. It is a *Koszul
morphism*, or a *local complete intersection morphism*, when it is Koszul at every point of its
source.

## Main definitions

* `AlgebraicGeometry.KoszulAt`: part (1) of Stacks 069F, the condition at a point.
* `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism`: part (2) of Stacks 069F, the condition
  at every point.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersection_iff` and
  `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.koszulAt`: the pointwise criterion, in its
  introduction and elimination forms.
* `AlgebraicGeometry.KoszulAt.finiteTypeAt`: a morphism Koszul at a point is of finite type
  there.

## Implementation notes

Finite type at a point is `AlgebraicGeometry.finiteTypeAt`, which is part (1) of Stacks 01T1,
and Koszul-regularity of the immersion is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion`, which is part (2) of
Stacks 063J. The open neighbourhood enters as the open subscheme `U.toScheme`, so the
factorization is recorded as the equality `U.ι ≫ f = i ≫ π` of morphisms out of it. The
immersion hypothesis `IsImmersion i` is an explicit existential witness rather than an instance
argument, because it has to be in scope before Koszul-regularity of `i` can be written down.

`RingHom.IsLocalCompleteIntersection` is the ring-map notion of Stacks 07D0, phrased by a finite
polynomial presentation with Koszul-regular kernel. It is a different, affine formulation; the
comparison between the two is not made here, and nothing below depends on it.

## References

* [The Stacks Project, Definition 37.62.1 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Definition 37.15.1 (01T1)](https://stacks.math.columbia.edu/tag/01T1)
* [The Stacks Project, Definition 31.21.4 (063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- **Stacks 069F, part (1).** A morphism of schemes `f : X ⟶ S` is *Koszul at* `x : X` if it is
of finite type at `x` and there are an open neighbourhood `U` of `x`, a scheme `P` smooth over
`S` and a Koszul-regular immersion `i : U ⟶ P` through which the restriction of `f` to `U`
factors. -/
@[stacks 069F "part (1): Koszul at a point", sga "6 VIII 1.1" "at a point"]
def KoszulAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  finiteTypeAt f x ∧
    ∃ (U : X.Opens) (_ : x ∈ U) (P : Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ S)
      (hi : IsImmersion i),
      let : IsImmersion i := hi
      IsKoszulRegularImmersion i ∧ Smooth π ∧ U.ι ≫ f = i ≫ π

/-- **Stacks 069F, part (2).** A *local complete intersection morphism*, also called a *Koszul
morphism*, is a morphism of schemes that is Koszul at every point of its source. -/
@[stacks 069F "part (2): local complete intersection morphism", sga "6 VIII 1.1"]
def IsLocalCompleteIntersectionMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, KoszulAt f x

/-- A morphism of schemes is a local complete intersection morphism exactly when it is Koszul at
every point of its source; this is Stacks 069F, part (2), unfolded. -/
theorem isLocalCompleteIntersection_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    IsLocalCompleteIntersectionMorphism f ↔ ∀ x : X, KoszulAt f x :=
  Iff.rfl

/-- A morphism that is a local complete intersection morphism is Koszul at each of its points;
this is Stacks 069F, part (2), in its elimination form. -/
theorem IsLocalCompleteIntersectionMorphism.koszulAt {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsLocalCompleteIntersectionMorphism f) (x : X) : KoszulAt f x :=
  hf x

/-- Being Koszul at a point implies finite type at that point, since the latter is part of the
definition in Stacks 069F, part (1). -/
theorem KoszulAt.finiteTypeAt {X S : Scheme.{u}} {f : X ⟶ S} {x : X} (hx : KoszulAt f x) :
    AlgebraicGeometry.finiteTypeAt f x :=
  hx.1

end AlgebraicGeometry

end
