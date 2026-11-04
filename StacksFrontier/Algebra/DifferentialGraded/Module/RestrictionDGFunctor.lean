module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# Restriction of scalars as a differential graded functor

A homomorphism `φ : A → B` of differential graded algebras induces a differential graded functor
from the differential graded category of right differential graded `B`-modules to that of right
differential graded `A`-modules. On objects it restricts the algebra action; on homogeneous
morphisms it does nothing, since a `B`-linear map is in particular `A`-linear through `φ` and
neither the grading nor the differential changes.

## Main definitions

* `DifferentialGradedModule.restrictScalarsDGFunctor`: the differential graded restriction
  functor, together with its action on objects and on every degree of the Hom module.

## Implementation notes

The construction is a subtype of `DGCategory.DGFunctor`, recording that the functor sends `N` to
`restrictScalars φ N` and leaves the underlying linear map of every homogeneous morphism
unchanged.

## References

* [Stacks Project, Tag 09LD](https://stacks.math.columbia.edu/tag/09LD)
-/

@[expose] public section

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Restriction along a homomorphism of differential graded algebras, as a differential graded
functor between the differential graded categories of right modules. -/
@[stacks 09LD]
noncomputable def restrictScalarsDGFunctor (φ : A.Hom B) :
    { F : DGCategory.DGFunctor (dgCategory B) (dgCategory A) //
      (∀ N : DifferentialGradedModule B, F.obj N = restrictScalars φ N) ∧
      (∀ (L M : DifferentialGradedModule B) (n : ℤ) (f : (dgCategory B).Hom L M n),
        HEq (F.map f).1 f.1) } :=
  ⟨{ obj := fun N => restrictScalars φ N
     map := fun {L M n} f => ⟨f.1, by
       rw [mem_homogeneousMapSubmodule]
       exact ⟨f.2.1, fun a x => f.2.2 (φ.toAlgebraHom a) x⟩⟩
     map_add := by intros; apply Subtype.ext; rfl
     map_smul := by intros; apply Subtype.ext; rfl
     map_d := by intros; apply Subtype.ext; simp only [dgCategory_d_val]; rfl
     map_comp := by intros; apply Subtype.ext; simp only [dgCategory_comp_val]
     map_id := by intros; apply Subtype.ext; simp only [dgCategory_id_val] },
   ⟨fun _ => rfl, fun _ _ _ _ => HEq.rfl⟩⟩

end DifferentialGradedModule
