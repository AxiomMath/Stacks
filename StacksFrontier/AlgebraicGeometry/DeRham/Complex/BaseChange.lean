module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change and étale localization for differential forms

A commutative square of schemes

```
X' → X
↓    ↓
S' → S
```

induces the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on sheaves of relative differential
`n`-forms. **If the square is cartesian, or if its two horizontal arrows are étale, that map is
an isomorphism in every degree.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback`: the map is an
  isomorphism in every degree for a cartesian square.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale`: the map is an
  isomorphism in every degree when the two horizontal arrows are étale.

## References

* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)

/-- In a cartesian square of schemes, the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on relative
differential forms is an isomorphism in every degree. -/
@[stacks 0FL5]
theorem isIso_relativeDifferentialFormsMap_of_isPullback (H : IsPullback f p' p g) (n : ℤ) :
    IsIso (relativeDifferentialFormsMap f p p' g H.w n) :=
  isIso_relativeDifferentialFormsMap f p p' g H.w
    (isIso_relativeDifferentialsMap_of_isPullback f p' p g H) n

/-- In a commutative square of schemes whose two horizontal arrows `f : X' ⟶ X` and `g : S' ⟶ S`
are étale, the canonical map `f^*Ω^n_{X/S} ⟶ Ω^n_{X'/S'}` on relative differential forms is an
isomorphism in every degree. -/
@[stacks 0FLV "isomorphism on each exterior power"]
theorem isIso_relativeDifferentialFormsMap_of_etale (hcomm : f ≫ p = p' ≫ g)
    [Etale f] [Etale g] (n : ℤ) :
    IsIso (relativeDifferentialFormsMap f p p' g hcomm n) :=
  isIso_relativeDifferentialFormsMap f p p' g hcomm
    (isIso_relativeDifferentialsMap_of_etale f p p' g hcomm) n

end AlgebraicGeometry.Scheme.Hom

end
