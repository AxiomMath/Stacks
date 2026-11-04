module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiIdempotentComplete
public import StacksCore.CategoryTheory.Monoidal.Rigid.Retract
public import Mathlib.CategoryTheory.Retract

/-!
# Duals in the twisted Karoubi envelope

Let `C` be a graded monoidal category. In its twisted Karoubi envelope every triple
`M = (X, p, m)` is a retract of `(X, 𝟙, 0) ⊗ (𝟙_ C, 𝟙, m)`: it is cut out of `(X, 𝟙, m)` by `p`,
and tensoring with the twisted unit `(𝟙_ C, 𝟙, m)` adds `m` to the twist. The twisted unit is
invertible, hence has a left dual; so as soon as `(X, 𝟙, 0)` has a left dual, so does
`(X, 𝟙, 0) ⊗ (𝟙_ C, 𝟙, m)` (Stacks 0FFS), and therefore so does its retract `M` (Stacks 0FFU,
the twisted Karoubi envelope being idempotent complete).

Applied to the graded category of correspondences, `(X, 𝟙, 0)` is the motive `h(X)` and
`(𝟙_ C, 𝟙, m)` the Tate motive `𝟏(m)`; this is the formal part of the proof of Stacks 0FGJ.

As everywhere in this library, Stacks' "`Y` is a left dual of `X`" (Categories, Definition 0FFP)
is Mathlib's `ExactPairing X Y`, which Mathlib phrases as `HasRightDual X`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.retractUntwist`: `(X, p, m)` is a retract of
  `(X, 𝟙, m)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.retractTensorUnitTwist`: `(X, p, m)` is a retract
  of `(X, 𝟙, 0) ⊗ (𝟙_ C, 𝟙, m)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.rightRigidCategoryOfHasRightDualOfObj`: if every
  `(X, 𝟙, 0)` has a left dual, every object has one.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.nonempty_hasRightDual_of_ofObj`: a triple
  `(X, p, m)` has a left dual as soon as `(X, 𝟙, 0)` has one.

## References

* [Stacks Project, Tag 0FGJ](https://stacks.math.columbia.edu/tag/0FGJ)
* [Stacks Project, Tag 0FFS](https://stacks.math.columbia.edu/tag/0FFS)
* [Stacks Project, Tag 0FFU](https://stacks.math.columbia.edu/tag/0FFU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- A triple `(X, p, m)` is a retract of `(X, 𝟙, m)`, both maps being `p`. -/
def retractUntwist (M : TwistedKaroubi R C) :
    Retract M ({ ofObj (R := R) M.X with twist := M.twist } : TwistedKaroubi R C) where
  i := Hom.mk M.p ⟨grade_cast M.p_mem (sub_self M.twist).symm, M.idem, Category.comp_id _⟩
  r := Hom.mk M.p ⟨grade_cast M.p_mem (sub_self M.twist).symm, Category.id_comp _, M.idem⟩
  retract := hom_ext M.idem

variable [MonoidalCategory C] [IsGradedMonoidal R C]

/-- A triple `(X, p, m)` is a retract of `(X, 𝟙, 0) ⊗ (𝟙_ C, 𝟙, m)`. -/
def retractTensorUnitTwist (M : TwistedKaroubi R C) :
    Retract M (ofObj (R := R) M.X ⊗ ({ ofObj (R := R) (𝟙_ C) with twist := M.twist } :
      TwistedKaroubi R C)) :=
  (retractUntwist M).trans (Retract.ofIso
    ((tensorUnitTwistIso (ofObj (R := R) M.X) M.twist ≪≫
      twistCongrIso (ofObj (R := R) M.X) (zero_add M.twist)).symm))

/-- A triple `(X, p, m)` of the twisted Karoubi envelope has a left dual as soon as `(X, 𝟙, 0)`
has one: `(X, 𝟙, 0) ⊗ (𝟙_ C, 𝟙, m)` then has a left dual (Stacks 0FFS, the twisted unit being
invertible), and `(X, p, m)` is a retract of it (Stacks 0FFU). -/
theorem nonempty_hasRightDual_of_ofObj (M : TwistedKaroubi R C)
    (hX : HasRightDual (ofObj (R := R) M.X)) : Nonempty (HasRightDual M) := by
  let : HasRightDual ({ ofObj (R := R) (𝟙_ C) with twist := M.twist } : TwistedKaroubi R C) :=
    { rightDual := { ofObj (R := R) (𝟙_ C) with twist := -M.twist }
      exact := unitTwistExactPairing M.twist (-M.twist) (add_neg_cancel M.twist) }
  let : HasRightDual (ofObj (R := R) M.X ⊗
      ({ ofObj (R := R) (𝟙_ C) with twist := M.twist } : TwistedKaroubi R C)) :=
    hasRightDualTensor
  exact nonempty_hasRightDual_of_retract (retractTensorUnitTwist M)

/-- If every `(X, 𝟙, 0)` has a left dual, every object of the twisted Karoubi envelope has a left
dual: it is right rigid in Mathlib's naming. -/
@[instance_reducible]
noncomputable def rightRigidCategoryOfHasRightDualOfObj
    (h : ∀ X : C, HasRightDual (ofObj (R := R) X)) : RightRigidCategory (TwistedKaroubi R C) where
  rightDual M := (nonempty_hasRightDual_of_ofObj M (h M.X)).some

end CategoryTheory.GradedCategory.TwistedKaroubi
