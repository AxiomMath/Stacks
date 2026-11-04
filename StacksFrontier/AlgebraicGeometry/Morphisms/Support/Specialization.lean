module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen

/-!
# The support of a quasi-coherent module is stable under specialization

The support of a quasi-coherent sheaf of modules on a scheme is stable under specialization: if a
point lies in the support, so does every point it specializes to.

## Main results

* `AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_supp`: the support of a
  quasi-coherent sheaf of modules is stable under specialization.

## Implementation notes

Stability is expressed by Mathlib's `StableUnderSpecialization`, which is the Stacks
specialization relation on the underlying topological space. The argument is affine-local: around
the specialization choose an affine open containing it, where
`AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp` converts membership in the
support into membership in the support of the module of sections, and `Module.mem_support_mono`
gives the monotonicity in the prime.

## References

* [Stacks Project, Tag 05AC](https://stacks.math.columbia.edu/tag/05AC)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The support of a quasi-coherent sheaf of modules on a scheme is stable under
specialization. -/
@[stacks 05AC]
public lemma stableUnderSpecialization_supp (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] : StableUnderSpecialization (SheafOfModules.supp F) := by
  intro x y hxy hx
  obtain ⟨W, hW, hyW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := y) (by trivial)
  have hxW : x ∈ W := hxy.mem_open W.isOpen hyW
  have hpq : hW.primeIdealOf ⟨x, hxW⟩ ≤ hW.primeIdealOf ⟨y, hyW⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr <|
      hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp (by
        simpa [hW.fromSpec_primeIdealOf] using hxy)
  exact (mem_support_sections_iff_mem_supp F ⟨W, hW⟩ y hyW).1
    (Module.mem_support_mono hpq ((mem_support_sections_iff_mem_supp F ⟨W, hW⟩ x hxW).2 hx))

end AlgebraicGeometry.Scheme.Modules

end
