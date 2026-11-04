module

public import StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts
public import StacksCore.CategoryTheory.Monoidal.Rigid.Retract
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionInduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Karoubian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesFiniteBiproducts
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesMonoidal
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidalPreadditive
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiRigid

/-!
# Every Chow motive has a left dual (Stacks 0FGJ)

The proof of Stacks 0FGJ: a motive `(X, p, m)` is a retract of `h(X) ⊗ 𝟏(m)`, the Tate motive
`𝟏(m)` is invertible, so by Stacks 0FFS and 0FFU (`M_k` is Karoubian, Stacks 0FGB) it suffices
that every `h(X)` has a left dual; decomposing `X` into its parts of constant dimension
(Stacks 0FFT for the direct sum `h(X ⨿ Y) ≅ h(X) ⊕ h(Y)`), it suffices that `h(X)` has a left dual
for `X` of constant dimension `d`, which is Stacks 0FGI.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.retractHTensorTate`: a motive `M = (X, p, m)` is a retract
  of `h(X) ⊗ 𝟏(m)`.
* `Stacks.WeilCohomology.ChowMotiveCat.nonempty_hasRightDual_h_of`: the reduction to schemes of
  constant dimension.
* `Stacks.WeilCohomology.ChowMotiveCat.rightRigidCategory`, **Stacks 0FGJ**: `M_k` is rigid.
* `Stacks.WeilCohomology.ChowMotiveCat.nonempty_hasRightDual`: every motive has a left dual.

## References

* [Stacks Project, Tag 0FGJ](https://stacks.math.columbia.edu/tag/0FGJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.GradedCategory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k]

/-- A motive `M = (X, p, m)` is a retract of `h(X) ⊗ 𝟏(m)`, both maps being `p`. -/
def retractHTensorTate (M : ChowMotiveCat k) :
    Retract M ((h k).obj (op M.scheme) ⊗ tate k M.twist) :=
  TwistedKaroubi.retractTensorUnitTwist M

/-- **Reduction to equidimensional schemes.** If `h(X)` has a left dual for every smooth
projective `X` of constant relative dimension, then it has one for every smooth projective `X`:
duals are carried along isomorphisms and retracts (Stacks 0FFU, `M_k` being Karoubian, Stacks
0FGB), and from `h(X)`, `h(Y)` to `h(X ⨿ Y) ≅ h(X) ⊕ h(Y)` (Stacks 0FFT). -/
theorem nonempty_hasRightDual_h_of
    (hdim : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ),
      AlgebraicGeometry.RelativeDimension X.obj.hom d →
      Nonempty (HasRightDual ((h k).obj (op X))))
    (X : (SmoothProjectiveScheme k).FullSubcategory) : Nonempty (HasRightDual ((h k).obj (op X)))
        := by
  refine SmoothProjectiveScheme.induction_relativeDimension
    (fun X => Nonempty (HasRightDual ((h k).obj (op X)))) ?_ ?_ hdim X
  · rintro X Y e ⟨hX⟩
    exact nonempty_hasRightDual_of_retract (Retract.ofIso ((h k).mapIso e.op))
  · rintro X Y c hc ⟨hX⟩ ⟨hY⟩
    let : HasBinaryBiproduct ((h k).obj (op X)) ((h k).obj (op Y)) := hasBinaryBiproduct_h X Y
    let : HasRightDual ((h k).obj (op X) ⊞ (h k).obj (op Y)) := hasRightDualBiprod
    exact nonempty_hasRightDual_of_retract (Retract.ofIso (hCoprodIsoBiprod hc))

/-- The motive `h(X)` of every smooth projective scheme over `k` has a left dual. -/
theorem nonempty_hasRightDual_h (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Nonempty (HasRightDual ((h k).obj (op X))) :=
  nonempty_hasRightDual_h_of
    (fun X _ hX => ⟨HasRightDual.mk _ (exact := motiveExactPairing X hX)⟩) X

/-- **Stacks 0FGJ.** Every object of the category `M_k` of Chow motives has a left dual:
`M_k` is (right) rigid, in Mathlib's naming. -/
@[stacks 0FGJ]
noncomputable instance rightRigidCategory : RightRigidCategory (ChowMotiveCat k) :=
  TwistedKaroubi.rightRigidCategoryOfHasRightDualOfObj fun X =>
    (nonempty_hasRightDual_h (k := k) X.as).some

/-- **Stacks 0FGJ**, objectwise: every Chow motive `M` has a left dual (Stacks' "`Mᘁ` is a left
dual of `M`" is Mathlib's `ExactPairing M Mᘁ`). -/
@[stacks 0FGJ]
theorem nonempty_hasRightDual (M : ChowMotiveCat k) : Nonempty (HasRightDual M) :=
  ⟨inferInstance⟩

end Stacks.WeilCohomology.ChowMotiveCat
