module

public import StacksFrontier.Algebra.Homology.PseudoCoherent

/-!
# Finite free modules are pseudo-coherent

A finite free module over a ring `R` is a pseudo-coherent object of `D(R)`: the complex
concentrated in degree `0` with that value is a bounded complex of finite free modules
representing it.

## Main results

* `StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free`: a finite free module is
  pseudo-coherent, Stacks 064Q (4).
-/

open CategoryTheory CategoryTheory.Limits

@[expose] public section

namespace StacksDraft.PseudoCoherence

universe v u

variable {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]

/-- **A finite free module is pseudo-coherent.** The complex concentrated in degree `0` with
value `M` is a bounded complex of finite free `R`-modules representing `M` in `D(R)`. -/
public theorem isModulePseudoCoherent_of_finite_free (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] : IsModulePseudoCoherent (R := R) M := by
  classical
  let E := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R M)
  refine ⟨E, ⟨⟨0, inferInstance⟩, ?_⟩,
    ⟨((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app (ModuleCat.of R M)).symm⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of R M)).toLinearEquiv
    exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
      Module.Free.of_equiv e.symm⟩
  · have hz : IsZero (E.X i) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R M) i hi
    have : Subsingleton (E.X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, inferInstance⟩

/-- **A finite free module object of `ModuleCat R` is pseudo-coherent.** -/
public theorem isModulePseudoCoherent_of_isFiniteFree {M : ModuleCat.{v} R}
    (hM : IsFiniteFree M) : IsModulePseudoCoherent (R := R) M :=
  have := hM.1
  have := hM.2
  isModulePseudoCoherent_of_finite_free (R := R) M

end StacksDraft.PseudoCoherence

end
