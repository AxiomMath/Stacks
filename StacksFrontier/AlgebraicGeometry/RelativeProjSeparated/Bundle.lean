module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Qcoh
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme

/-!
# Sections of a projective bundle are closed immersions

`Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase` and
`isClosedImmersion_section` are statements about an arbitrary `RelativeProjData`. This file reads
them off for the projective bundle `P(E) = Proj(Sym E)` of a module, in the two forms this
repository has it: **unconditionally over an affine base**, and over an arbitrary scheme on the
quasi-coherence hypothesis `Stacks.SymGraded.IsQuasicoherentPieces` that the general projective
bundle still carries.

## Main results

* `Stacks.SymGraded.isSeparated_qcohProjectiveBundleToBase` and
  `Stacks.SymGraded.isClosedImmersion_section_qcohProjectiveBundle`: over an affine base, with no
  hypothesis beyond the ones the bundle itself needs.
* `Stacks.SymGraded.isSeparated_schemeProjectiveBundleToBase` and
  `Stacks.SymGraded.isClosedImmersion_section_schemeProjectiveBundle`: over an arbitrary scheme.

## Implementation notes

Nothing here is specific to the symmetric algebra. The projective bundle is a `RelativeProjData`
for the graded algebra `Sym(E)`, and separatedness of the structure morphism of a relative
homogeneous spectrum holds for every quasi-coherent, commutative, nonnegatively graded algebra;
so these are four instantiations and carry no proofs of their own.

In particular **no generation in degree one is used**. The sections-to-quotients correspondence of
Tag 0B3V does need it; being a closed immersion does not.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)

## Not done here

**No tag of 0B3V is claimed, and in particular not its "closed immersion" assertion.** That
assertion is about the projective bundle of a quasi-coherent module on an *arbitrary* scheme.
`isClosedImmersion_section_schemeProjectiveBundle` carries the extra hypothesis
`Stacks.SymGraded.IsQuasicoherentPieces E`, which the tag's statement does not, and
`isClosedImmersion_section_qcohProjectiveBundle` is restricted to an affine base, which is
strictly weaker than the tag's statement. Discharging `IsQuasicoherentPieces` for a
quasi-coherent module — equivalently, the third assertion of Tag 01CG over an affine base, as
named in the `Not done here` section of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict` — is the only thing
between `isClosedImmersion_section_schemeProjectiveBundle` and that assertion of the tag.

Nothing here addresses the bijection between sections and invertible quotients, the conormal
sheaf of a section, or any base-change compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjSeparated

namespace Stacks.SymGraded

universe u

/-! ### An affine base -/

section Affine

variable {R : CommRingCat.{u}} (E : (Spec R).Modules)

/-- **The projective bundle of a module on an affine scheme is separated over its base.** -/
public theorem isSeparated_qcohProjectiveBundleToBase :
    IsSeparated (qcohProjectiveBundleToBase E) :=
  isSeparated_toBase _ (qcohProjectiveBundle E)

/-- **Every section of the projective bundle of a module on an affine scheme is a closed
immersion.** -/
public theorem isClosedImmersion_section_qcohProjectiveBundle
    (σ : Spec R ⟶ (qcohProjectiveBundle E).scheme)
    (hσ : σ ≫ (qcohProjectiveBundle E).toBase = 𝟙 (Spec R)) :
    IsClosedImmersion σ :=
  isClosedImmersion_section (qcohProjectiveBundle E) σ hσ

end Affine

/-! ### An arbitrary base -/

section Scheme

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **The projective bundle of a module on an arbitrary scheme is separated over its base**,
given quasi-coherence of the homogeneous pieces of its symmetric algebra. -/
public theorem isSeparated_schemeProjectiveBundleToBase :
    IsSeparated (schemeProjectiveBundleToBase E hqc) :=
  isSeparated_toBase _ (schemeProjectiveBundle E hqc)

/-- **Every section of the projective bundle of a module on an arbitrary scheme is a closed
immersion**, given quasi-coherence of the homogeneous pieces of its symmetric algebra.

This is the whole geometric content of the "closed immersion" assertion of Tag 0B3V; see the
`Not done here` section of this file for why the tag is not attached. -/
public theorem isClosedImmersion_section_schemeProjectiveBundle
    (σ : X ⟶ (schemeProjectiveBundle E hqc).scheme)
    (hσ : σ ≫ (schemeProjectiveBundle E hqc).toBase = 𝟙 X) :
    IsClosedImmersion σ :=
  isClosedImmersion_section (schemeProjectiveBundle E hqc) σ hσ

end Scheme

end Stacks.SymGraded

end
