module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule

/-!
# The ungraded realization of a unital homomorphism of sheaves of graded algebras

Let `A` and `B` be sheaves of `ℤ`-graded algebras over a sheaf of rings `R` on a site
([Stacks, Tag 0FQW]) and let `φ : A ⟶ B` be a unital homomorphism. Over each object `U` of the
site the homogeneous sections of `A` assemble into a ring
`Stacks.GradedAlgebra.Total`, and `φ` assembles degreewise into a ring homomorphism between
those rings. This file builds that ring homomorphism and records the two facts transported
along it: surjectivity, and commutativity of the target.

## Main definitions

* `SheafOfModules.GradedAlgebra.UnitalHom.totalAddHom` — the degreewise assembly of `φ` as an
  additive map of the rings of homogeneous sections.
* `SheafOfModules.GradedAlgebra.UnitalHom.totalRingHom` — the same map as a ring homomorphism.

## Main results

* `SheafOfModules.GradedAlgebra.UnitalHom.surjective_totalRingHom` — a homomorphism surjective
  on the sections of every homogeneous piece is surjective on the rings of homogeneous sections.
* `SheafOfModules.GradedAlgebra.UnitalHom.isCommutative_of_surjective` — the target of a
  degreewise surjective homomorphism out of a commutative sheaf of graded algebras is again
  commutative.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace SheafOfModules.GradedAlgebra.UnitalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A B : GradedAlgebra.{w, w} R} (φ : UnitalHom A B)

/-- **The ungraded realization of a unital homomorphism, as an additive map.** On a homogeneous
section of degree `n` it is the degree-`n` component of `φ`. -/
noncomputable def totalAddHom (U : Cᵒᵖ) :
    A.toPresheafGradedAlgebra.Total U →+ B.toPresheafGradedAlgebra.Total U :=
  DirectSum.toAddMonoid fun n =>
    AddMonoidHom.mk' (fun x => B.toPresheafGradedAlgebra.incl n ((φ.app n).val.app U x))
      fun x y => by
        rw [map_add, Stacks.GradedAlgebra.incl_add]

/-- On the inclusion of a degree-`n` section `x`, `totalAddHom φ U` is the inclusion of the
degree-`n` component of `φ` applied to `x`. -/
@[simp]
theorem totalAddHom_incl (U : Cᵒᵖ) (n : ℤ) (x : (A.piece n).val.obj U) :
    totalAddHom φ U (A.toPresheafGradedAlgebra.incl n x)
      = B.toPresheafGradedAlgebra.incl n ((φ.app n).val.app U x) := by
  unfold totalAddHom
  exact DirectSum.toAddMonoid_of _ n _

/-- `totalAddHom φ U` sends `1` to `1`. -/
theorem totalAddHom_one (U : Cᵒᵖ) : totalAddHom φ U 1 = 1 := by
  rw [Stacks.GradedAlgebra.one_eq_incl, totalAddHom_incl]
  exact (congrArg (B.toPresheafGradedAlgebra.incl 0) (φ.map_one U)).trans
    (B.toPresheafGradedAlgebra.one_eq_incl U).symm

/-- `totalAddHom φ U` is multiplicative. -/
theorem totalAddHom_mul (U : Cᵒᵖ) (a b : A.toPresheafGradedAlgebra.Total U) :
    totalAddHom φ U (a * b) = totalAddHom φ U a * totalAddHom φ U b := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => simp
  | incl i x =>
    induction b using Stacks.GradedAlgebra.incl_induction with
    | zero => simp
    | incl j y =>
      rw [Stacks.GradedAlgebra.incl_mul_incl, totalAddHom_incl, totalAddHom_incl,
        totalAddHom_incl, Stacks.GradedAlgebra.incl_mul_incl]
      exact congrArg (B.toPresheafGradedAlgebra.incl (i + j)) (φ.map_mul i j U x y)
    | add b b' hb hb' => rw [mul_add, map_add, map_add, hb, hb', mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, map_add, ha, ha', add_mul]

/-- **The ungraded realization of a unital homomorphism of sheaves of graded algebras**: the
degreewise assembly of `φ` on the rings of homogeneous sections over an object of the site. -/
noncomputable def totalRingHom (U : Cᵒᵖ) :
    A.toPresheafGradedAlgebra.Total U →+* B.toPresheafGradedAlgebra.Total U where
  toFun := totalAddHom φ U
  map_one' := totalAddHom_one φ U
  map_mul' := totalAddHom_mul φ U
  map_zero' := map_zero (totalAddHom φ U)
  map_add' := map_add (totalAddHom φ U)

/-- The underlying function of `totalRingHom φ U` is `totalAddHom φ U`. -/
@[simp]
theorem totalRingHom_apply (U : Cᵒᵖ) (a : A.toPresheafGradedAlgebra.Total U) :
    totalRingHom φ U a = totalAddHom φ U a := rfl

/-- **A homomorphism surjective in every degree is surjective on the rings of homogeneous
sections.** -/
theorem surjective_totalRingHom (U : Cᵒᵖ)
    (h : ∀ n : ℤ, Function.Surjective ((φ.app n).val.app U)) :
    Function.Surjective (totalRingHom φ U) := by
  intro b
  induction b using Stacks.GradedAlgebra.incl_induction with
  | zero => exact ⟨0, map_zero _⟩
  | incl n y =>
    obtain ⟨x, rfl⟩ := h n y
    exact ⟨A.toPresheafGradedAlgebra.incl n x, totalAddHom_incl φ U n x⟩
  | add b b' hb hb' =>
    obtain ⟨a, rfl⟩ := hb
    obtain ⟨a', rfl⟩ := hb'
    exact ⟨a + a', map_add _ a a'⟩

/-- A heterogeneous equality of sections of `A` in equal degrees `i = j` is preserved by
applying the corresponding components of `φ`. -/
theorem heq_app (U : Cᵒᵖ) {i j : ℤ} (e : i = j) {x : (A.piece i).val.obj U}
    {y : (A.piece j).val.obj U} (h : HEq x y) :
    HEq ((φ.app i).val.app U x) ((φ.app j).val.app U y) := by
  subst e
  rw [eq_of_heq h]

/-- **Commutativity passes to the target of a degreewise surjective unital homomorphism.** If `A`
is commutative and `φ` is surjective on sections in every degree and over every object, then `B`
is commutative. -/
theorem isCommutative_of_surjective [A.IsCommutative]
    (h : ∀ (n : ℤ) (U : Cᵒᵖ), Function.Surjective ((φ.app n).val.app U)) :
    B.IsCommutative := by
  refine ⟨fun i j U x y => ?_⟩
  obtain ⟨x', rfl⟩ := h i U x
  obtain ⟨y', rfl⟩ := h j U y
  change HEq ((B.mul i j).app U _ _) ((B.mul j i).app U _ _)
  rw [← φ.map_mul, ← φ.map_mul]
  exact heq_app φ U (add_comm i j)
    (Stacks.GradedAlgebra.IsCommutative.mul_comm (A := A.toPresheafGradedAlgebra) i j U x' y')

end SheafOfModules.GradedAlgebra.UnitalHom

end
