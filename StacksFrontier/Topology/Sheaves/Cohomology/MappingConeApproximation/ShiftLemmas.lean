module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence and shifts

Shifting a complex of `𝒪_X`-modules by `n` shifts the degree from which it is pseudo-coherent by
`-n`, both for a complex and for an object of the derived category. This is what turns the first
of the three implications of [Stacks, Tag 08CD] into the other two, by rotating the triangle.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_shift` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_shift`.

## Implementation notes

For a complex, the approximation of `E⟦n⟧` over an open `U` is the shift of the approximation of
`E`, composed with the compatibility of restriction with the shift
(`CategoryTheory.Functor.commShiftIso`); the source stays strictly perfect by
`Stacks.Cohomology.PerfectComplexTriangles.isStrictlyPerfect_shift`. That the two conditions on
  cohomology move by `-n` is the
shift sequence of the cohomology functors,
`CategoryTheory.Functor.ShiftSequence.shiftIso`, read through
`CategoryTheory.NatIso.isIso_map_iff` and
`StacksDraft.PseudoCoherence.epi_map_iff_of_natIso`.

For an object of the derived category the statement follows from the one for complexes, the
shifted representative being supplied by the shift compatibility of the localisation functor.

## References

* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- **Shifting a complex by `n` lowers the degree it is pseudo-coherent from by `n`.** -/
@[sga "6 I 2.5" "a), bounded clause"]
public theorem isPseudoCoherentComplexFrom_shift
    {E : CochainComplex (OXMod.{u, u} X) ℤ} {m : ℤ}
    (hE : IsPseudoCoherentComplexFrom E m) (n : ℤ) :
    IsPseudoCoherentComplexFrom (E⟦n⟧) (m - n) := by
  intro x
  obtain ⟨U, hxU, P, hP, α, hα, hα₀⟩ := hE x
  refine ⟨U, hxU, P⟦n⟧, Stacks.Cohomology.PerfectComplexTriangles.isStrictlyPerfect_shift hP n,
    (α⟦n⟧') ≫ (((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso n).inv.app E, ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have : IsIso (HomologicalComplex.homologyMap (α⟦n⟧') j) :=
      (NatIso.isIso_map_iff
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso
          n j (n + j) rfl) α).mpr (hα (n + j) (by omega))
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have : Epi (HomologicalComplex.homologyMap (α⟦n⟧') (m - n)) :=
      (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso
          n (m - n) m (by omega)) α).mpr hα₀
    exact epi_comp _ _

/-- **Shifting an object of the derived category by `n` lowers the degree it is pseudo-coherent
from by `n`.** -/
public theorem isPseudoCoherentFrom_shift [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {E : DerivedCategory (OXMod.{u, u} X)} {m : ℤ}
    (hE : IsPseudoCoherentFrom E m) (n : ℤ) :
    IsPseudoCoherentFrom (E⟦n⟧) (m - n) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  exact ⟨P⟦n⟧, isPseudoCoherentComplexFrom_shift hP n,
    ⟨(DerivedCategory.Q.commShiftIso n).app P ≪≫ (shiftFunctor _ n).mapIso e⟩⟩

end AlgebraicGeometry.RingedSpace

end
