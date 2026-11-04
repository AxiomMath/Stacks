module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemFrobeniusUnit
public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemZariski
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidZariskiDescent

/-!
# Condition (1) of Stacks 0EX9 for Stacks Tag 0EXE

The category fibred in groupoids of Stacks Tag 0EXE, whose fibre over an object `U` of the big h
category over `S` is the groupoid of finite locally free `colim_F 𝒪_U`-modules, is a stack in
groupoids for the Zariski topology. This is condition (1) of Stacks 0EX9 for it; the source's
proof is the one line "by definition we have glueing for the Zariski topology".

`AlgebraicGeometry.isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_isStackFor`
reduced it to Zariski descent for *all* sheaves of `colim_F 𝒪_U`-modules. The pseudofunctor of
those is the pseudofunctor of modules of the Frobenius system of sheaves of rings
(`AlgebraicGeometry.frobeniusColimitModulePseudofunctor_eq`), which has the restriction property
(`AlgebraicGeometry.frobeniusRingSheafSystem_unitBijective`), and the pseudofunctor of modules of
any such system is a stack for every Zariski family
(`AlgebraicGeometry.BigHOver.RingSheafSystem.isStackFor_of_mem_zariskiPrecoverage`).

## Main results

* `AlgebraicGeometry.isStackFor_frobeniusColimitModulePseudofunctor_of_mem_zariskiPrecoverage`:
  sheaves of `colim_F 𝒪`-modules form a stack for every Zariski family of the big h site.
* `AlgebraicGeometry.frobeniusVectorBundleGroupoidFibration_isZariskiStackInGroupoids`:
  **condition (1) of Stacks 0EX9 for Stacks Tag 0EXE**, with no hypothesis.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe t u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **Sheaves of `colim_F 𝒪_U`-modules form a stack for every Zariski family of the big h
category over `S`.** -/
theorem isStackFor_frobeniusColimitModulePseudofunctor_of_mem_zariskiPrecoverage
    {ι : Type t} {U : BigHOver B S hS} {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ U)
    (hf : Presieve.ofArrows X f ∈ (BigHOver.zariskiPrecoverage B S hS).coverings U) :
    (frobeniusColimitModulePseudofunctor B S hS p hpS).IsStackFor (Presieve.ofArrows X f) := by
  rw [frobeniusColimitModulePseudofunctor_eq]
  exact BigHOver.RingSheafSystem.isStackFor_of_mem_zariskiPrecoverage
    (frobeniusRingSheafSystem_unitBijective B S hS p hpS) f hf

/-- **Condition (1) of Stacks 0EX9 for Stacks Tag 0EXE**: the category fibred in groupoids of
finite locally free `colim_F 𝒪_U`-modules over the big h site of a scheme `S` in
characteristic `p` is a stack in groupoids for the Zariski topology. No hypothesis. -/
theorem frobeniusVectorBundleGroupoidFibration_isZariskiStackInGroupoids :
    BigHOver.IsZariskiStackInGroupoids B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) :=
  isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_isStackFor B S hS p hpS
    fun f hf => isStackFor_frobeniusColimitModulePseudofunctor_of_mem_zariskiPrecoverage
      B S hS p hpS f hf

end AlgebraicGeometry

end
