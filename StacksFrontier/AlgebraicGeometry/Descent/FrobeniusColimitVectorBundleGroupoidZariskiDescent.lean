module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiLocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidZariski

/-!
# Condition (1) of Stacks 0EX9 for Stacks Tag 0EXE, reduced to Zariski descent for modules

`AlgebraicGeometry.isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_families`
reduced condition (1) of Stacks 0EX9 for Stacks Tag 0EXE to two inputs per Zariski family of the
big h category over `S`: that finite local freeness is detected along the family (`hP`), and that
the pseudofunctor of *all* Frobenius-colimit modules is a stack for the family (`hR`).

`AlgebraicGeometry.isFiniteLocallyFree_of_bigHFrobeniusColimitPullback` proves the first. This
file substitutes it, so that condition (1) rests on `hR` alone.

## Main results

* `isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_isStackFor` (in
  `AlgebraicGeometry`): **condition (1) of Stacks 0EX9 for Stacks Tag 0EXE holds as soon as the
  pseudofunctor of all sheaves of `colim_F 𝒪_U`-modules is a stack for every Zariski family of the
  big h category over `S`.** No hypothesis about finite local freeness remains.

## Implementation notes

The remaining hypothesis is the stack condition for
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at a single Zariski family, which is
Zariski descent for sheaves of modules over the Frobenius-colimit sheaf of rings. Its separated
half is `AlgebraicGeometry.faithful_toDescentData_frobeniusColimitModulePseudofunctor`; its
effective half is the gluing of such sheaves along the family, which the development does not
have.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- **Condition (1) of Stacks 0EX9 for the category fibred in groupoids of Stacks Tag 0EXE,
reduced to Zariski descent for Frobenius-colimit modules.**

This is
`AlgebraicGeometry.isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_families`
with its finite-local-freeness hypothesis discharged by
`AlgebraicGeometry.isFiniteLocallyFree_of_bigHFrobeniusColimitPullback`. The one hypothesis left
is the stack condition for the pseudofunctor of all sheaves of `colim_F 𝒪_U`-modules at a single
Zariski family of the site. -/
theorem isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_isStackFor
    (hR : ∀ {ι : Type (u + 1)} {U : BigHOver B S hS} {X : ι → BigHOver B S hS}
      (f : ∀ i, X i ⟶ U), Presieve.ofArrows X f ∈
        (BigHOver.zariskiPrecoverage B S hS).coverings U →
      (frobeniusColimitModulePseudofunctor B S hS p hpS).IsStackFor
        (Presieve.ofArrows X f)) :
    BigHOver.IsZariskiStackInGroupoids B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) :=
  isZariskiStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_families B S hS p hpS
    (fun f hf M h =>
      isFiniteLocallyFree_of_bigHFrobeniusColimitPullback p B S hS hpS f hf M h) hR

end AlgebraicGeometry

end
