module

public import StacksFrontier.RingTheory.CompleteIntersection.BaseChange
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.LocalRing.ResidueField.FiberBaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt

/-!
# Base change of the complete-intersection condition on a fibre

Let `R → A` be of finite type, let `R → R'` be arbitrary and let `A'` be the base change, so
`A' = R' ⊗_R A`.  Let `q'` be a prime of `A'` lying over the prime `q` of `A` and over the prime
`p'` of `R'`, and let `p` be the prime of `R` below both.  This file proves that the fibre
`κ(p') ⊗_{R'} A'_{q'}` is a complete intersection over `κ(p')` exactly when the fibre
`κ(p) ⊗_R A_q` is one over `κ(p)`.

This is the ring-level content of Stacks Lemma 02V3: the fibres of the base change are the base
changes of the fibres, so the assertion is Stacks Lemma 00SI applied to the field extension
`κ(p) ⊆ κ(p')` and the finite type `κ(p)`-algebra `κ(p) ⊗_R A`.

## Main results

* `Stacks.SyntomicBaseChange.isCompleteIntersection_fiber_baseChange_iff`: the base-change
  statement above.

## Implementation notes

The fibre comparison is `Ideal.Fiber.isPushout_baseChange`: the square of fibres
`κ(p) → κ(p')`, `κ(p) ⊗_R A → κ(p') ⊗_{R'} A'` is a pushout square, which is what turns the base
change `R → R'` into the field extension that Lemma 00SI wants.  Its algebra structure
`Ideal.Fiber.baseChangeAlgebra` and scalar tower `Ideal.Fiber.isScalarTower_baseChange` depend on
the chosen pushout square, so they are introduced with `let` and `have` in the proof below.

Both localizations are supplied to Lemma 00SI in the abstract form `IsLocalization.AtPrime`:
`κ(p) ⊗_R A_q` is a localization of the fibre `κ(p) ⊗_R A` at the prime cut out by `q`
(`Ideal.Fiber.isLocalization_atPrime`), so no isomorphism of rings has to be pushed through the
complete-intersection condition.

## References

* [Stacks 02V3](https://stacks.math.columbia.edu/tag/02V3), Lemma 29.30.12.
* [Stacks 00SI](https://stacks.math.columbia.edu/tag/00SI), Lemma 10.135.10.
-/

@[expose] public section

open scoped TensorProduct

open Algebra.TensorProduct (includeRight)

universe u

namespace Stacks.SyntomicBaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 02V3 at the level of rings.**  Let `R → A` be of finite type, let `R → R'` be
arbitrary and let `A' = R' ⊗_R A` be the base change, presented as a pushout square.  Let `q'` be
a prime of `A'`, let `q` be the prime of `A` below it, and let `p'`, `p` be the primes of `R'`,
`R` below `q'`, `q`.  Then the fibre `κ(p') ⊗_{R'} A'_{q'}` is a complete intersection over
`κ(p')` if and only if the fibre `κ(p) ⊗_R A_q` is a complete intersection over `κ(p)`.

This is Lemma 00SI applied to the field extension `κ(p) ⊆ κ(p')` and the finite type
`κ(p)`-algebra `κ(p) ⊗_R A`, whose base change along it is `κ(p') ⊗_{R'} A'` by
`Ideal.Fiber.isPushout_baseChange`. -/
theorem isCompleteIntersection_fiber_baseChange_iff
    {R R' A A' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
    [Algebra R R'] [Algebra R A] [Algebra R A'] [Algebra R' A'] [Algebra A A']
    [IsScalarTower R R' A'] [IsScalarTower R A A'] [Algebra.IsPushout R R' A A']
    [Algebra.FiniteType R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]
    (q' : Ideal A') [q'.IsPrime] [q'.LiesOver q] [q'.LiesOver p'] :
    IsCompleteIntersection p'.ResidueField (p'.Fiber (Localization.AtPrime q')) ↔
      IsCompleteIntersection p.ResidueField (p.Fiber (Localization.AtPrime q)) := by
  let := Ideal.residueFieldAlgebra p p'
  have := Ideal.isScalarTower_residueField p p'
  let := Ideal.Fiber.baseChangeAlgebra R R' A A' p p'
  have := Ideal.Fiber.isScalarTower_baseChange R R' A A' p p'
  have := Ideal.Fiber.isPushout_baseChange R R' A A' p p'
  -- the primes of the two fibres cut out by `q` and `q'`
  obtain ⟨Q', hQ', hQ'q'⟩ :=
    Ideal.Fiber.exists_comap_includeRight_eq q' p' (Ideal.over_def q' p').symm
  have := hQ'
  set Q : Ideal (p.Fiber A) := Q'.comap (algebraMap (p.Fiber A) (p'.Fiber A')) with hQdef
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have : Q'.LiesOver Q := ⟨rfl⟩
  have hmem (b : A') : (includeRight b : p'.Fiber A') ∈ Q' ↔ b ∈ q' := by
    rw [← hQ'q']; rfl
  have hQq : Q.comap (includeRight : A →ₐ[R] p.Fiber A) = q := by
    have hq : q = q'.comap (algebraMap A A') := Ideal.over_def q' q
    ext a
    rw [Ideal.mem_comap, hQdef, Ideal.mem_comap,
      Ideal.Fiber.algebraMap_baseChange_includeRight R R' A A' p p', hmem, hq,
      Ideal.mem_comap]
  -- the two fibres at a prime, as abstract localizations
  have := Ideal.Fiber.isLocalization_atPrime p Q q hQq (Localization.AtPrime q)
  have := Ideal.Fiber.isLocalization_atPrime p' Q' q' hQ'q' (Localization.AtPrime q')
  let := (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
    (IsScalarTower.toAlgHom R A (Localization.AtPrime q))).toRingHom.toAlgebra
  let := (Algebra.TensorProduct.map (AlgHom.id p'.ResidueField p'.ResidueField)
    (IsScalarTower.toAlgHom R' A' (Localization.AtPrime q'))).toRingHom.toAlgebra
  have : IsScalarTower p.ResidueField (p.Fiber A) (p.Fiber (Localization.AtPrime q)) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower p'.ResidueField (p'.Fiber A') (p'.Fiber (Localization.AtPrime q')) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  exact Algebra.IsPushout.isCompleteIntersection_localization_atPrime_iff p.ResidueField
    p'.ResidueField (p.Fiber A) (p'.Fiber A') Q Q'
    (p.Fiber (Localization.AtPrime q)) (p'.Fiber (Localization.AtPrime q'))

end Stacks.SyntomicBaseChange
