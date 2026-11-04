module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal étaleness of a transformation splits into smoothness and unramifiedness

A transformation of set-valued functors on the big fppf site over a scheme is formally étale
exactly when it is both formally smooth and formally unramified: the unique-lifting condition
against affine square-zero closed immersions is the conjunction of existence of a lift and
uniqueness of a lift.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.formallyEtale_iff_formallySmooth_and_formallyUnramified`:
  **Stacks 04G4**.

## Implementation notes

The three predicates of Tag 049S quantify over exactly the same lifting problems, so the
equivalence is the pointwise statement that `∃!` is `∃` together with uniqueness, distributed
over those quantifiers.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04G4](https://stacks.math.columbia.edu/tag/04G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}

/-- **Stacks 04G4.** A transformation of set-valued functors on the big fppf site is
formally étale if and only if it is both formally smooth and formally unramified. -/
@[stacks 04G4, ega "IV 17.1.1" "étale ⟺ smooth+unram"]
public theorem formallyEtale_iff_formallySmooth_and_formallyUnramified (a : F ⟶ G) :
    FormallyEtale a ↔ (FormallySmooth a ∧ FormallyUnramified a) :=
  ⟨fun ha => ⟨fun T T' hT hT' i hi x y hxy => (ha T T' hT hT' i hi x y hxy).exists,
      fun T T' hT hT' i hi x y hxy _ _ hz₁ hz₂ => (ha T T' hT hT' i hi x y hxy).unique hz₁ hz₂⟩,
    fun ⟨hs, hu⟩ T T' hT hT' i hi x y hxy =>
      existsUnique_of_exists_of_unique (hs T T' hT hT' i hi x y hxy) (hu T T' hT hT' i hi x y hxy)⟩

end AlgebraicGeometry.Space

end
