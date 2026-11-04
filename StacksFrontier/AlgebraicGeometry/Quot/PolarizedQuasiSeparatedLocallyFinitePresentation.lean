module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.AlgebraicOfArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.StronglyFormallyEffective
public import StacksFrontier.Deformation.Artin.Versality.OpennessOfVersality

/-!
# `𝒫olarized → Spec(ℤ)` is quasi-separated and locally of finite presentation (Stacks 0DPU)

**Stacks 0DPU**: the morphism `𝒫olarized → Spec(ℤ)` is quasi-separated and locally of finite
presentation. Both properties belong to 1-morphisms of algebraic stacks:

* quasi-separatedness is Stacks 04YW, `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`;
* local finite presentation is Stacks 06Q2,
  `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`.

The statement is made at `AlgebraicGeometry.polarizedAlgebraicStack B hZ`, the stack
`AlgebraicGeometry.polarizedStackUnconditional` of polarized proper schemes over `Spec(ℤ)` taken
as an algebraic stack, which it is by Quot, Theorem 0D4X.

## Main results

* `AlgebraicGeometry.PolarizedAlgebraicity.isSquareZeroEffective_polarized`: square-zero towers
  of `𝒫olarized` are effective.
* `AlgebraicGeometry.PolarizedAlgebraicity.isAlgebraicStack_polarized`: `𝒫olarized` is an
  algebraic stack (Quot, Theorem 0D4X).
* `AlgebraicGeometry.polarizedAlgebraicStack`: `𝒫olarized` over `Spec(ℤ)` as an algebraic stack.
* `AlgebraicGeometry.isQuasiSeparated_and_isLocallyOfFinitePresentation_polarizedAlgebraicStack`:
  Stacks 0DPU.

## References

* [Stacks Project, Tag 0DPU](https://stacks.math.columbia.edu/tag/0DPU)
* [Stacks Project, Tag 0DPT](https://stacks.math.columbia.edu/tag/0DPT)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D4V](https://stacks.math.columbia.edu/tag/0D4V)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedAlgebraicity

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- **Square-zero towers of `𝒫olarized` are effective**, in the sense of hypothesis (4) of
Stacks 0CXU. -/
theorem isSquareZeroEffective_polarized :
    Deformation.Artin.IsSquareZeroEffective B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).isFiberedInGroupoids :=
  fun Λ _ chart _ R cR hcR hsurj hsq =>
    isStronglyFormallyEffective_polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ)
      Λ chart R cR hcR hsurj (fun f x hx => ⟨2, by
        have hx' : x * x ∈ RingHom.ker (R.map f).hom.toRingHom ^ 2 := by
          rw [sq]
          exact Ideal.mul_mem_mul hx hx
        rw [hsq f] at hx'
        simpa [pow_two] using hx'⟩)

/-- **`𝒫olarized` is an algebraic stack** (Quot, Theorem 0D4X). -/
theorem isAlgebraicStack_polarized :
    Stack.IsAlgebraicStack.{u, u + 1, u, u + 1} B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val :=
  isAlgebraicStack_polarized_of_isOpenVersality B hZ (fun U hU y hy u hu hv =>
    Deformation.Artin.isOpenVersality_of_isSquareZeroEffective B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ))
      (hasRepresentableDiagonal_polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ))
      (satisfiesRSStar_polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ))
      (isLimitPreservingPolarizedUnconditional B hZ (isTerminal_obj_specULiftZ B hZ))
      (isSquareZeroEffective_polarized B hZ) U hU y hy u hu hv)

end AlgebraicGeometry.PolarizedAlgebraicity

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- **`𝒫olarized` as an algebraic stack.** The stack of polarized proper schemes over `Spec(ℤ)`
as an object of the 2-category of algebraic stacks. -/
abbrev polarizedAlgebraicStack : Stack.AlgebraicStacks.{u, u + 1} B _ hZ :=
  PolarizedAlgebraicity.polarizedAlgebraicStackOf B hZ (isTerminal_obj_specULiftZ B hZ)
    (PolarizedAlgebraicity.isAlgebraicStack_polarized B hZ)

/-- The morphism `𝒫olarized → Spec(ℤ)` is quasi-separated (Stacks 04YW) and locally of finite
presentation (Stacks 06Q2). -/
@[stacks 0DPU "the morphism Polarized → Spec(Z) is quasi-separated and locally of finite \
presentation"]
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_polarizedAlgebraicStack :
    Stack.AlgebraicStacks.IsQuasiSeparated B _ hZ
        (Stack.structureMorphism B _ hZ (polarizedAlgebraicStack B hZ)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B _ hZ
        (Stack.structureMorphism B _ hZ (polarizedAlgebraicStack B hZ)) :=
  PolarizedAlgebraicity.isQuasiSeparated_and_isLocallyOfFinitePresentation_polarizedAlgebraicStackOf
    B hZ (isTerminal_obj_specULiftZ B hZ) _

end AlgebraicGeometry

end
