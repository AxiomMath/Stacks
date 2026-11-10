module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureDiagramNormalization
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureFunctionFieldDiagram
public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds

/-!
# A first failure of étale base change is seen over an algebraically closed function field

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer invertible on `S`. If `BC(f, n, q)`
holds and `BC(f, n, q + 1)` does not (the conditions of [Stacks, Tag 0F02]), then there are
cartesian squares

```
X  ←--  X'  ←-h-  Y
|f      |         |
S  ←--  S'  ←---  Spec K(S')
```

with `S'` affine, integral and normal with algebraically closed function field `K(S')`, and a
divisor `d` of `n` with `R^{q+1} h_*(ℤ/dℤ)` nonzero. This is [Stacks, Tag 0F1D].

## Main results

* `Stacks.EtaleCohomology.FirstFailureFunctionField.functionFieldFailure_of_not_baseChangeHolds`
  — [Stacks, Tag 0F1D].

## Implementation notes

The proof is the source's. [Stacks, Tag 0F08]
(`Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_firstFailure`) gives the
diagram over an algebraically closed extension `K` of `K(S')`, and
`Stacks.EtaleCohomology.FirstFailureFunctionField.functionFieldFailure_of_normalFailureDiagram`
descends it from `K` to `K(S')` by [Stacks, Tag 0F0B] (2) and the relative Leray spectral
sequence. The input [Stacks, Tag 0F09] of Tag 0F0B is
`Stacks.EtaleCohomology.smoothLimitBaseChange_holds`.

Degrees are shifted by one as in `BaseChangeHigher/FirstFailureDiagram.lean`: the source's
`q ≥ 1` with `BC(f, n, q - 1)` true and `BC(f, n, q)` false is degree `q + 1` here, with `q : ℕ`.
`n` invertible on `S` means that `n` is a unit in `Γ(S, 𝒪_S)`.

## References

* [Stacks Project, Tag 0F1D](https://stacks.math.columbia.edu/tag/0F1D)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.FirstFailureFunctionField

open FirstFailureDiagram

/-- **Stacks Project, Tag 0F1D.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `n`
is invertible on `S`, `BC(f, n, q)` holds and `BC(f, n, q + 1)` does not. Then there are
cartesian squares

```
X  ←--  X'  ←-h-  Y
|f      |         |
S  ←--  S'  ←---  Spec K
```

where `S'` is affine, integral and normal with algebraically closed function field `K = K(S')`,
the bottom right arrow is the canonical morphism from the spectrum of the function field, and
there is an integer `d ∣ n` with `R^{q+1} h_*(ℤ/dℤ)` nonzero
(`Stacks.EtaleCohomology.FirstFailureFunctionField.FunctionFieldFailure`). -/
@[stacks 0F1D]
public theorem functionFieldFailure_of_not_baseChangeHolds {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) : FunctionFieldFailure f n (q + 1) :=
  functionFieldFailure_of_normalFailureDiagram f n (q + 1) hn smoothLimitBaseChange_holds
    (normalFailureDiagram_of_firstFailure f n q hprev hfail)

end Stacks.EtaleCohomology.FirstFailureFunctionField

end
