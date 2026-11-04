module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEmertonGerbe

/-!
# Lifting smooth affines along a first order thickening of algebraic stacks (Stacks 0CKI)

Let `𝒳 ⊂ 𝒳'` be a first order thickening of algebraic stacks, `W` an affine scheme and
`x : W → 𝒳` smooth. Emerton's proposition (Stacks 0CKI) gives a cartesian square
```
  W ──→ W'
  │      │ x'
  ↓      ↓
  𝒳 ──→ 𝒳'
```
with `x'` smooth and `W'` affine.

The proof follows the source. The category of smooth lifts `𝒞 ⟶ W_{spaces,étale}` of Stacks 0CJP
is a gerbe (Stacks 0CJU, 0CJX) whose band is a quasi-coherent `𝒪_W`-module (Stacks 0CKG (2),
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_band_isQuasicoherent`). Its cohomology on the
affine `W` therefore vanishes in positive degrees, so `𝒞` has an object over `W` (Stacks 0CK0).
That object is the square above, and `W'` is affine because `W ⟶ W'` is a thickening (Stacks 05ZR,
06AD). All of this is
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_lift_of_band_isQuasicoherent`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_smooth_affine_lift_of_isFirstOrderThickening`:
  Stacks 0CKI.

## References

* [Stacks Project, Tag 0CKI](https://stacks.math.columbia.edu/tag/0CKI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0CKI (Emerton).** Let `ι : 𝒳 ⟶ 𝒳'` be a first order thickening of algebraic stacks,
let `W` be affine and let `x : W ⟶ 𝒳` be smooth. Then there are an affine `W'`, a morphism
`i : W ⟶ W'` and a smooth `x' : W' ⟶ 𝒳'` such that the square `x ≫ ι ≅ i ≫ x'` is
2-cartesian, i.e. `W = 𝒳 ×_{𝒳'} W'`.

Here `W` and `W'` are algebraic spaces that are affine, that is, representable by affine schemes,
viewed as algebraic stacks through `algebraicSpaceStackFunctor`. -/
@[stacks 0CKI]
theorem exists_smooth_affine_lift_of_isFirstOrderThickening {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {ι : 𝒳 ⟶ 𝒳'} (hι₁ : IsFirstOrderThickening B S hS ι) (W : AlgebraicSpaces B S hS)
    (hW : Space.IsAffineSpace B S hS W.obj) (x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳)
    (hx : IsSmooth B S hS x) :
    ∃ (W' : AlgebraicSpaces B S hS) (i : W ⟶ W')
      (x' : (algebraicSpaceStackFunctor B S hS).obj W' ⟶ 𝒳')
      (α : x ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'),
      IsSmooth B S hS x' ∧
        Nonempty (IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj W, x,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x')) ∧
        Space.IsAffineSpace B S hS W'.obj :=
  EtaleSmoothLift.exists_lift_of_band_isQuasicoherent
    (hι := isThickening_of_isFirstOrderThickening hι₁) (hx := hx) hW
    (EtaleSmoothLift.exists_band_isQuasicoherent hι₁)

end AlgebraicGeometry.Stack.AlgebraicStacks
