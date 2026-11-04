module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryClosedMaps
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory

/-! # Homotopy classes of homomorphisms into a shift

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `M` and `N` be
differential graded `A`-modules. By Tag 09LC the homomorphisms `M ⟶ N[k]` are exactly the
degree-`k` homogeneous right `A`-linear maps `M → N` killed by the Hom differential, and two of
them are homotopic exactly when their difference is a boundary for that differential. This file
packages the two statements into the dictionary they are used through: a homomorphism into a
shift *is* a closed homogeneous map (`homogeneousMapOfHomShift`), every morphism of the homotopy
category out of `M` into the image of `N[k]` is represented by one, and two of them have the
same homotopy class exactly when their difference is a boundary.

## Main definitions

* `DifferentialGradedModule.homogeneousMapOfHomShift`: a homomorphism `M ⟶ N[k]`, read as a
  degree-`k` homogeneous map `M → N`.

## Main results

* `DifferentialGradedModule.homogeneousMapDifferential_homogeneousMapOfHomShift`: that map is
  closed for the Hom differential.
* `DifferentialGradedModule.exists_hom_shift_toHomotopyCategory_map_eq`: every morphism of
  `K(A, d)` from `M` to `N[k]` is the class of a homomorphism `M ⟶ N[k]`.
* `DifferentialGradedModule.toHomotopyCategory_map_eq_iff_exists_homogeneousMapDifferential`: two
  homomorphisms into a shift have the same class in `K(A, d)` exactly when the difference of the
  corresponding homogeneous maps is a boundary for the Hom differential.

## Implementation notes

The homogeneous map and the homomorphism are related by an equation between their underlying
linear maps rather than by `homogeneousMapOfHomShift`, so that the results apply to a
homomorphism produced in any other way — in particular to the homomorphism obtained from a closed
homogeneous map by `homogeneousMapDifferential_eq_zero_iff_exists_hom_shift`, whose only
specification is such an equation.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and the
modules all live in a single universe `u`, following the Stacks Tag 09JJ formalization.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
  {M N : DifferentialGradedModule A}

/-- A homomorphism of differential graded modules `M ⟶ N[k]`, read as a degree-`k` homogeneous
right `A`-linear map `M → N`. -/
def homogeneousMapOfHomShift {k : ℤ} (F : M ⟶ N.shift k) : HomogeneousMap A M N k :=
  ⟨F.toFun, ⟨fun i x hx => F.map_grading i x hx, fun a x => F.map_smul x a⟩⟩

/-- The homogeneous map read off a homomorphism into a shift has that homomorphism's underlying
linear map. -/
@[simp] theorem homogeneousMapOfHomShift_val {k : ℤ} (F : M ⟶ N.shift k) :
    (homogeneousMapOfHomShift A F).1 = F.toFun :=
  rfl

/-- The homogeneous map underlying a homomorphism into a shift is closed for the Hom
differential. -/
theorem homogeneousMapDifferential_homogeneousMapOfHomShift {k : ℤ} (F : M ⟶ N.shift k) :
    homogeneousMapDifferential A (homogeneousMapOfHomShift A F) = 0 :=
  (homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A M N k _).mpr ⟨F, rfl⟩

/-- Every morphism of the homotopy category from `M` to the image of `N[k]` is the homotopy class
of a homomorphism `M ⟶ N[k]`. -/
theorem exists_hom_shift_toHomotopyCategory_map_eq {k : ℤ}
    (ψ : (toHomotopyCategory A).obj M ⟶ (toHomotopyCategory A).obj (N.shift k)) :
    ∃ F : M ⟶ N.shift k, (toHomotopyCategory A).map F = ψ :=
  (toHomotopyCategory A).map_surjective ψ

/-- Two homomorphisms of differential graded modules are homotopic exactly when their difference
is null-homotopic. -/
theorem homotopic_iff_homotopic_sub_zero (f g : M ⟶ N) :
    Homotopic f g ↔ Homotopic (f - g) 0 := by
  have key (h : M.M →ₗ[MulOpposite A.A] N.M) (x : M.M) :
      (f.toFun x - g.toFun x = N.d (h x) + h (M.d x)) ↔
        ((f - g).toFun x - (0 : M ⟶ N).toFun x = N.d (h x) + h (M.d x)) := by
    rw [Hom.hom_sub_toFun, Hom.hom_zero_toFun, LinearMap.sub_apply, LinearMap.zero_apply,
      sub_zero]
  constructor
  · rintro ⟨H⟩
    refine ⟨{ toLinearMap := H.toLinearMap, map_grading := H.map_grading, homotopy_eq := ?_ }⟩
    exact fun x => (key H.toLinearMap x).mp (H.homotopy_eq x)
  · rintro ⟨H⟩
    refine ⟨{ toLinearMap := H.toLinearMap, map_grading := H.map_grading, homotopy_eq := ?_ }⟩
    exact fun x => (key H.toLinearMap x).mpr (H.homotopy_eq x)

/-- Two homomorphisms into a shift have the same class in the homotopy category exactly when the
difference of the corresponding homogeneous maps is a boundary for the Hom differential. -/
theorem toHomotopyCategory_map_eq_iff_exists_homogeneousMapDifferential {k : ℤ}
    {f g : HomogeneousMap A M N k} {F G : M ⟶ N.shift k}
    (hF : F.toFun = f.1) (hG : G.toFun = g.1) :
    (toHomotopyCategory A).map F = (toHomotopyCategory A).map G ↔
      ∃ c : HomogeneousMap A M N (k - 1),
        (homogeneousMapDifferential A c).1 = (f.1 : M.M →ₗ[R] N.M) - g.1 := by
  refine (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) F G).trans ?_
  refine (homotopic_iff_homotopic_sub_zero A F G).trans ?_
  refine (homotopic_zero_iff_exists_homogeneousMapDifferential A (f - g) (F - G)
    (by rw [Hom.hom_sub_toFun, hF, hG]; rfl)).trans ?_
  exact exists_congr fun c => by rw [Submodule.coe_sub]

end DifferentialGradedModule

end
