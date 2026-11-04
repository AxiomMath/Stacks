module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# A cartesian square restricted to a compatible pair of opens of its two bases

The reduction of conclusion (c) of [Stacks, Tag 0EX3] to the affine case
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens`) quantifies over an affine
open `V` of `Y'` and an affine open `W` of `Y''` lying over it. Everything the proof then does —
the Leray comparison along the affine `h'`, the projection formula, conclusion (b) — is about a
cartesian square with affine base, and the square in hand is the original one restricted to that
pair of opens:

```
f''⁻¹(W) --h'|--> f'⁻¹(V)
   |f'' ∣ W          |f' ∣ V
   W -----h|----->   V
```

This file supplies that square, and the inequality of opens its horizontal restriction needs. The
restricted `h` is a morphism of affine schemes, hence affine, which is the hypothesis
`[IsAffineHom h]` that the projection formula and the Leray comparison of this directory carry —
so over a compatible pair of affine opens those hypotheses are discharged rather than assumed,
and neither `Y'` nor `Y''` needs one.

## Main results

Both in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `preimage_le_preimage_of_isPullback`: `f''⁻¹(W) ≤ (h')⁻¹(f'⁻¹(V))` for a commuting square and
  `W ≤ h⁻¹(V)`.
* `isPullback_resLE_of_isPullback`: **the restricted square is cartesian.**

## Implementation notes

*The square is Mathlib's, with the fourth open computed.*
`AlgebraicGeometry.Scheme.Hom.isPullback_resLE` restricts a cartesian square to opens chosen on
three of its four corners, the fourth being forced as the intersection of the two preimages. Here
the two preimages are `(h')⁻¹(f'⁻¹(V))` and `f''⁻¹(W)`, and the commutativity of the square makes
the first contain the second, so the intersection is `f''⁻¹(W)` and the restricted vertical
morphisms are the plain `AlgebraicGeometry.morphismRestrict` of `f'` and `f''` — which is the
spelling the rest of the directory, and
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase`, are stated at.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
  {h : Y'' ⟶ Y'}

/-- **The preimage in `X''` of an open of `Y''` lying over an open of `Y'` lies over the preimage
in `X'`.** For a commuting square `h' ≫ f' = f'' ≫ h` and `W ≤ h⁻¹(V)`, the open `f''⁻¹(W)` of
`X''` is contained in `(h')⁻¹(f'⁻¹(V))`: both preimages are taken along the two equal composites
`h' ≫ f'` and `f'' ≫ h`. -/
theorem preimage_le_preimage_of_isPullback (hsq : IsPullback h' f'' f' h) {V : Y'.Opens}
    {W : Y''.Opens} (hWV : W ≤ h ⁻¹ᵁ V) : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, hsq.w, Scheme.Hom.comp_preimage]
  exact f''.preimage_mono hWV

/-- **A cartesian square restricted to a compatible pair of opens of its two bases is
cartesian.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an open `V` of `Y'` and an open `W` of `Y''` with `W ≤ h⁻¹(V)`, the square
```
f''⁻¹(W) --h'|--> f'⁻¹(V)
   |f'' ∣ W          |f' ∣ V
   W -----h|----->   V
```
is cartesian. Neither open carries a hypothesis; when both are affine the restricted `h` is a
morphism of affine schemes, so `AlgebraicGeometry.isAffineHom_of_isAffine` discharges the
affineness hypothesis of the projection formula and of the Leray comparison. -/
theorem isPullback_resLE_of_isPullback (hsq : IsPullback h' f'' f' h) {V : Y'.Opens}
    {W : Y''.Opens} (hWV : W ≤ h ⁻¹ᵁ V) :
    IsPullback
      (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
      (f'' ∣_ W) (f' ∣_ V) (h.resLE V W hWV) := by
  have hUY : (f'' ⁻¹ᵁ W : X''.Opens) = h' ⁻¹ᵁ (f' ⁻¹ᵁ V) ⊓ f'' ⁻¹ᵁ W :=
    (inf_eq_right.2 (preimage_le_preimage_of_isPullback hsq hWV)).symm
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    Scheme.Hom.isPullback_resLE hsq hWV (le_refl (f' ⁻¹ᵁ V)) hUY

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
