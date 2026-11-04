module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Scheme

/-!
# Local characterizations of seminormal and absolutely weakly normal schemes

Seminormality and absolute weak normality of a scheme can each be checked on every affine open,
on an affine open covering, or on an arbitrary open covering. Both properties are inherited by
open subschemes.

Both are the property of locally satisfying a ring property which is local in the sense of
`CommRing.PropertyIsLocal`, so the four equivalent criteria and the restriction to open
subschemes are the general statements about such properties, specialized.

## Main results

* `AlgebraicGeometry.isSeminormal_tfae`: the four equivalent criteria for seminormality.
* `AlgebraicGeometry.isSeminormal_open`: open subschemes of seminormal schemes are seminormal.
* `AlgebraicGeometry.isAbsolutelyWeaklyNormal_tfae`: the analogous four criteria for absolute
  weak normality.
* `AlgebraicGeometry.isAbsolutelyWeaklyNormal_open`: absolute weak normality is inherited by
  open subschemes.

## Implementation notes

Affine opens are bundled as `AlgebraicGeometry.Scheme.affineOpens`, and covers are expressed as
suprema of open subobjects. The first and third declarations state the two instances of the
enumerated equivalence; the other two state the corresponding assertions about open subschemes.

## References

* [Stacks Project, Tag 0EUP](https://stacks.math.columbia.edu/tag/0EUP)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme is seminormal if and only if the section ring of every affine open is seminormal,
if and only if this holds on an affine open covering, if and only if the scheme has an open
covering by seminormal open subschemes. -/
@[stacks 0EUP "seminormal equivalent conditions"]
public theorem isSeminormal_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsSeminormal X,
      ∀ U : X.affineOpens, IsSeminormalRing Γ(X, U.val),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsSeminormalRing Γ(X, (U i).val),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsSeminormal (U i).toScheme] := by
  tfae_have 1 ↔ 2 := isLocally_iff_forall_affineOpens isSeminormalRing_propertyIsLocal X
  tfae_have 1 ↔ 3 := isLocally_iff_exists_affineOpenCover _ X
  tfae_have 1 ↔ 4 := isLocally_iff_exists_openCover isSeminormalRing_propertyIsLocal X
  tfae_finish

/-- Every open subscheme of a seminormal scheme is seminormal. -/
@[stacks 0EUP "seminormal open subschemes"]
public theorem isSeminormal_open {X : Scheme.{u}} (hX : IsSeminormal X)
    (U : X.Opens) : IsSeminormal U.toScheme :=
  isLocally_open isSeminormalRing_propertyIsLocal X hX U

/-- A scheme is absolutely weakly normal if and only if the section ring of every affine open is
absolutely weakly normal, if and only if this holds on an affine open covering, if and only if
the scheme has an open covering by absolutely weakly normal open subschemes. -/
@[stacks 0EUP "absolutely weakly normal equivalent conditions"]
public theorem isAbsolutelyWeaklyNormal_tfae (X : Scheme.{u}) :
    List.TFAE [
      IsAbsolutelyWeaklyNormal X,
      ∀ U : X.affineOpens, IsAbsolutelyWeaklyNormalRing Γ(X, U.val),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).val) = ⊤ ∧ ∀ i, IsAbsolutelyWeaklyNormalRing Γ(X, (U i).val),
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsAbsolutelyWeaklyNormal (U i).toScheme] := by
  tfae_have 1 ↔ 2 :=
    isLocally_iff_forall_affineOpens isAbsolutelyWeaklyNormalRing_propertyIsLocal X
  tfae_have 1 ↔ 3 := isLocally_iff_exists_affineOpenCover _ X
  tfae_have 1 ↔ 4 :=
    isLocally_iff_exists_openCover isAbsolutelyWeaklyNormalRing_propertyIsLocal X
  tfae_finish

/-- Every open subscheme of an absolutely weakly normal scheme is absolutely weakly normal. -/
@[stacks 0EUP "absolutely weakly normal open subschemes"]
public theorem isAbsolutelyWeaklyNormal_open {X : Scheme.{u}}
    (hX : IsAbsolutelyWeaklyNormal X) (U : X.Opens) :
    IsAbsolutelyWeaklyNormal U.toScheme :=
  isLocally_open isAbsolutelyWeaklyNormalRing_propertyIsLocal X hX U

end AlgebraicGeometry

end
