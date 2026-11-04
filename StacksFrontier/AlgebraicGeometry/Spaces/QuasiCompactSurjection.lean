module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# Quasi-compactness ascends along a surjection of algebraic spaces

Tag 040W has two parts. The first is the slogan that the image of a quasi-compact algebraic
space under a surjective morphism is quasi-compact: if `f : X ⟶ Y` is surjective and `X` is
quasi-compact in the sense of Tag 03E3, then so is `Y`. The second is the relative form: in a
commuting triangle `p = f ≫ q` with `f` surjective, quasi-compactness of `p` in the sense of
Tag 03HE forces quasi-compactness of `q`.

## Main results

* `AlgebraicGeometry.Space.IsQuasiCompactSpace.of_isSurjective` is part (1).
* `AlgebraicGeometry.Space.IsQuasiCompact.of_isSurjective_comp` is part (2).

## Implementation notes

Surjectivity is Tag 03ME, `AlgebraicGeometry.Space.IsSurjective`, surjectivity of the induced
map on point sets. Part (1) is the topological statement `Function.Surjective.compactSpace`
transported across Tag 03E4, `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points`,
which needs both `X` and `Y` algebraic. Part (2) applies part (1) to the comparison map
`T ×_Z X ⟶ T ×_Z Y`, a base change of `f` and hence surjective by Tag 03MH; both fibre products
are algebraic spaces by Tag 02X2, `AlgebraicGeometry.isAlgebraicSpace_pullback`.

## References

* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 04Z9](https://stacks.math.columbia.edu/tag/04Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 040W, part (1).** The image of a quasi-compact algebraic space under a
surjective morphism of algebraic spaces over `S` is quasi-compact: if `f : X ⟶ Y` is
surjective on points and `X` is quasi-compact, then `Y` is quasi-compact. -/
@[stacks 040W "part (1): quasi-compactness of the target"]
theorem IsQuasiCompactSpace.of_isSurjective {f : X ⟶ Y}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsSurjective B S hS f) (h : IsQuasiCompactSpace B S hS X) :
    IsQuasiCompactSpace B S hS Y :=
  isQuasiCompactSpace_of_compactSpace_points B S hS hY
    (@Function.Surjective.compactSpace _ _ _ _ _ (continuous_pointsMap B S hS f)
      (compactSpace_points_of_isQuasiCompactSpace B S hS hX h) hf)

/-- **Stacks 040W, part (2).** In a commuting triangle `f ≫ q = p` of morphisms of algebraic
spaces over `S` whose horizontal arrow `f` is surjective, quasi-compactness of `p` implies
quasi-compactness of `q`. -/
@[stacks 040W "part (2): quasi-compactness of a morphism", ega "IV 1.1.3"]
theorem IsQuasiCompact.of_isSurjective_comp {f : X ⟶ Y} {p : X ⟶ Z} {q : Y ⟶ Z}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hcomm : f ≫ q = p)
    (hf : IsSurjective B S hS f) (hp : IsQuasiCompact B S hS p) :
    IsQuasiCompact B S hS q := by
  subst hcomm
  intro T hT hTqc g
  have hleft := (IsPullback.of_right' (IsPullback.of_hasPullback g (f ≫ q))
    (IsPullback.of_hasPullback g q)).flip
  exact IsQuasiCompactSpace.of_isSurjective B S hS
    (isAlgebraicSpace_pullback B S hS g (f ≫ q) hT hX hZ)
    (isAlgebraicSpace_pullback B S hS g q hT hY hZ)
    (surjective_pointsMap_of_isPullback B S hS hleft hf) (hp T hT hTqc g)

end AlgebraicGeometry.Space

end
