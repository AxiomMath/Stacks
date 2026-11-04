module

public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProperCheckSquare

/-!
# Chow's square over a quasi-compact quasi-separated base

Let `S` be a quasi-compact quasi-separated scheme and let `f : X ⟶ S` be separated and of finite
type. Then there is a commutative square

```
X' ---i---> ℙⁿ_S
|            |
π            |
v            v
X ----f----> S
```

with `π` proper and surjective and `i` an immersion, and for such a square `f` is proper if and
only if `i` is a closed immersion.

## Main results

* `AlgebraicGeometry.exists_projectiveSpace_square_isProper_iff_isClosedImmersion`: for a
  separated morphism of finite type to a quasi-compact quasi-separated scheme there is a square
  as above with `π` proper and surjective and `i` an immersion, and for that square `f` is
  proper if and only if `i` is a closed immersion.

## References

* [Stacks Project, Tag 05LZ](https://stacks.math.columbia.edu/tag/05LZ)
* [Stacks Project, Tag 0205](https://stacks.math.columbia.edu/tag/0205)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Let `S` be quasi-compact and quasi-separated and let `f : X ⟶ S` be separated and of finite
type. Then there are an `n`, a scheme `X'`, a proper surjective morphism `π : X' ⟶ X` and an
immersion `i : X' ⟶ ℙⁿ_S` with `π ≫ f = i ≫ (ℙⁿ_S ↘ S)`. Moreover `f` is proper if and only if
`i` is a closed immersion. -/
@[stacks 05LZ]
theorem exists_projectiveSpace_square_isProper_iff_isClosedImmersion {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S),
      IsProper π ∧ Surjective π ∧ IsImmersion i ∧ π ≫ f = i ≫ (ProjectiveSpace n S ↘ S) ∧
        (IsProper f ↔ IsClosedImmersion i) := by
  obtain ⟨n, X', π, i, hπ, hsurj, hi, w⟩ :=
    hasChowModification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨n, X', π, i, hπ, hsurj, hi, w, isProper_iff_isClosedImmersion_projectiveSpace f π i w⟩

end AlgebraicGeometry

end
