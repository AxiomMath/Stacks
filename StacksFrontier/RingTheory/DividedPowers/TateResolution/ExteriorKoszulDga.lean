module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulCompatibility
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.HomDifferential
public import StacksFrontier.RingTheory.Koszul.Cone

/-! # The Koszul algebra as a differential graded divided power algebra

The exterior algebra of a module, graded by its exterior powers and contracted by a functional,
is the Koszul differential graded algebra of that functional. This file records it in the
vocabulary of the Tate resolution files: contraction is a differential graded algebra structure
in the sense of
`DividedPowers.TateResolution.IsDifferentialGradedAlgebra`, and the whole package — the grading,
its strict graded commutativity and the divided powers of
`DividedPowers.TateResolution.exteriorDividedPowerStructure` — is bundled as a
`DividedPowers.TateResolution.GradedDPAlgebra`, which is the shape in which the Tate tower maps
into a target.

The four fields of `IsDifferentialGradedAlgebra` are all available already: contraction lowers the
exterior degree by one (`Koszul.contraction_mem`), squares to zero
(`CliffordAlgebra.contractLeft_contractLeft`), obeys the signed Leibniz rule
(`DividedPowers.TateResolution.contractLeft_mul_of_mem`), and kills the zeroth exterior power
(`Stacks.MappingCone.NatIndexed.contraction_eq_zero_of_mem_exteriorPower_zero`). So this file
only assembles them.

## Main definitions

* `DividedPowers.TateResolution.koszulGradedDPAlgebra` — the exterior algebra of a module as a
  graded divided power algebra.

## Main results

* `DividedPowers.TateResolution.isDifferentialGradedAlgebra_contraction` — contraction by a
  functional is a differential on the exterior-power grading.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

open scoped ExteriorAlgebra

section Dga

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- **Contraction by a functional is a differential on the exterior-power grading.** This is the
Koszul differential graded algebra of the functional, written in the vocabulary the Tate
resolution files use. -/
@[ega "III 1.1.1" "partial"]
public theorem isDifferentialGradedAlgebra_contraction (φ : Module.Dual R E) :
    IsDifferentialGradedAlgebra (exteriorGrade R E) (Koszul.contraction φ) where
  d_grade_zero := fun hx =>
    Stacks.MappingCone.NatIndexed.contraction_eq_zero_of_mem_exteriorPower_zero φ hx
  d_mem := fun {n _} hx => Koszul.contraction_mem φ n hx
  d_sq_zero := fun x => CliffordAlgebra.contractLeft_contractLeft φ x
  leibniz := fun {i _ _ y} hx _ => contractLeft_mul_of_mem φ i hx y

end Dga

section Bundle

variable (R : Type u) [CommRing R] (r : ℕ)

/-- **The Koszul algebra of a finite sequence, as a graded divided power algebra.** The carrier is
the exterior algebra of `Rʳ`, the grading is by exterior powers, and the divided powers are those
of `DividedPowers.TateResolution.exteriorDividedPowerStructure`, which exist by Tag 09PH.

The differential is *not* part of the bundle: one and the same algebra carries the Koszul
differential of every sequence, and Tag 0GZ4 uses two of them at once. The differential is
supplied separately by
`DividedPowers.TateResolution.isDifferentialGradedAlgebra_contraction` and
`DividedPowers.TateResolution.isCompatibleWithDifferential_exteriorDividedPowerStructure`. -/
public noncomputable def koszulGradedDPAlgebra : GradedDPAlgebra.{u, u} R where
  carrier := ExteriorAlgebra R (Fin r → R)
  ring := inferInstance
  algebra := inferInstance
  grade := exteriorGrade R (Fin r → R)
  graded := inferInstance
  strict := inferInstance
  gamma := exteriorDividedPowerStructure R r

/-- The carrier of the bundled Koszul algebra is the exterior algebra of `Rʳ`. -/
public theorem koszulGradedDPAlgebra_carrier :
    (koszulGradedDPAlgebra R r).carrier = ExteriorAlgebra R (Fin r → R) := rfl

/-- The grading of the bundled Koszul algebra is by exterior powers. -/
public theorem koszulGradedDPAlgebra_grade :
    (koszulGradedDPAlgebra R r).grade = exteriorGrade R (Fin r → R) := rfl

/-- The divided powers of the bundled Koszul algebra are those of Tag 09PH. -/
public theorem koszulGradedDPAlgebra_gamma :
    (koszulGradedDPAlgebra R r).gamma = exteriorDividedPowerStructure R r := rfl

end Bundle

end DividedPowers.TateResolution

end
