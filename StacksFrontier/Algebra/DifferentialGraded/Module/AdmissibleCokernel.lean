module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.Subquotient

/-!
# Admissible monomorphisms and their cokernels

An admissible monomorphism `f : K ⟶ L` of right differential graded modules is, by definition,
split by a map of graded modules. That splitting descends to a graded splitting of the
projection `L ⟶ L/f(K)`: the map `ȳ ↦ y - f(π y)` is well defined on the quotient and is a
section of the projection in graded modules. Consequently every admissible monomorphism is the
first arrow of an admissible short exact sequence, with the cokernel as its third term.

## Main definitions

* `DifferentialGradedModule.Hom.cokernelGradedSection`: the graded section of the cokernel
  projection determined by a retraction of an admissible monomorphism.

## Main results

* `DifferentialGradedModule.Hom.isAdmissibleShortExact_cokernelπ`: an admissible monomorphism
  and the projection onto its cokernel form an admissible short exact sequence.
* `DifferentialGradedModule.exists_isAdmissibleShortExact`: every admissible monomorphism
  extends to an admissible short exact sequence.

## Implementation notes

The retraction is extracted from the existential `IsAdmissibleMono` by choice, so the section
depends on that choice; the short exact sequence produced by `exists_isAdmissibleShortExact` does
not. The quotient is the cokernel of `Subquotient`.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
  {K L : DifferentialGradedModule.{u, v, w} A}

/-- The graded section `ȳ ↦ y - f(π y)` of the projection onto the cokernel of an admissible
monomorphism `f`, built from a chosen graded retraction `π` of `f`. -/
noncomputable def Hom.cokernelGradedSection (f : Hom K L) (hf : IsAdmissibleMono f) :
    GradedHom f.cokernelObj L := by
  classical
  refine
    { toFun := ((f.range).restrictScalars R).liftQ
        (LinearMap.id - f.toFun ∘ₗ hf.choose.toFun) ?_
      map_smul := ?_
      map_grading := ?_ }
  · intro y hy
    rw [Hom.range_restrictScalars, LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    change f.toFun x - f.toFun (hf.choose.toFun (f.toFun x)) = 0
    rw [hf.choose_spec x, sub_self]
  · intro x a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective ((f.range).restrictScalars R) x
    change ((f.range).restrictScalars R).liftQ _ _
        (Submodule.Quotient.mk (p := (f.range).restrictScalars R) (MulOpposite.op a • y)) =
      MulOpposite.op a • ((f.range).restrictScalars R).liftQ _ _
        (Submodule.Quotient.mk (p := (f.range).restrictScalars R) y)
    rw [Submodule.liftQ_apply, Submodule.liftQ_apply]
    change MulOpposite.op a • y - f.toFun (hf.choose.toFun (MulOpposite.op a • y)) =
      MulOpposite.op a • (y - f.toFun (hf.choose.toFun y))
    rw [hf.choose.map_smul, f.map_smul, smul_sub]
  · intro n x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change ((f.range).restrictScalars R).liftQ _ _
      (Submodule.Quotient.mk (p := (f.range).restrictScalars R) y) ∈ L.grading n
    rw [Submodule.liftQ_apply]
    change y - f.toFun (hf.choose.toFun y) ∈ L.grading n
    exact (L.grading n).sub_mem hy
      (f.map_grading n _ (hf.choose.map_grading n y hy))

/-- The graded map `cokernelGradedSection` is a section of the projection onto the cokernel. -/
theorem Hom.cokernelπ_cokernelGradedSection (f : Hom K L) (hf : IsAdmissibleMono f)
    (x : f.cokernelObj.M) :
    f.cokernelπ.toFun ((f.cokernelGradedSection hf).toFun x) = x := by
  classical
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective ((f.range).restrictScalars R) x
  change Submodule.Quotient.mk (p := f.range)
      (((f.range).restrictScalars R).liftQ _ _
        (Submodule.Quotient.mk (p := (f.range).restrictScalars R) y)) =
    Submodule.Quotient.mk (p := (f.range).restrictScalars R) y
  rw [Submodule.liftQ_apply]
  change Submodule.Quotient.mk (p := f.range) (y - f.toFun (hf.choose.toFun y)) =
    Submodule.Quotient.mk (p := f.range) y
  rw [Submodule.Quotient.eq]
  refine ⟨-(hf.choose.toFun y), ?_⟩
  rw [map_neg]
  abel

/-- An admissible monomorphism, together with the projection onto its cokernel, is an
admissible short exact sequence. -/
theorem Hom.isAdmissibleShortExact_cokernelπ (f : Hom K L) (hf : IsAdmissibleMono f) :
    IsAdmissibleShortExact f f.cokernelπ where
  injective := hf.injective
  surjective := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective ((f.range).restrictScalars R) x
    exact ⟨y, rfl⟩
  exact := by
    change LinearMap.range f.toFun = LinearMap.ker (((f.range).restrictScalars R).mkQ)
    rw [Submodule.ker_mkQ, Hom.range_restrictScalars]
  admissibleMono := hf
  admissibleEpi := ⟨f.cokernelGradedSection hf, f.cokernelπ_cokernelGradedSection hf⟩

/-- Every admissible monomorphism of differential graded modules is the first arrow of an
admissible short exact sequence. -/
theorem exists_isAdmissibleShortExact (f : Hom K L) (hf : IsAdmissibleMono f) :
    ∃ (M : DifferentialGradedModule.{u, v, w} A) (g : L ⟶ M), IsAdmissibleShortExact f g :=
  ⟨f.cokernelObj, f.cokernelπ, f.isAdmissibleShortExact_cokernelπ hf⟩

end DifferentialGradedModule
