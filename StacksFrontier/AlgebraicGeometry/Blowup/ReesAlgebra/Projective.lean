module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjBridge
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymSurjective
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.GeneratedInDegreeOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup in a finite-type ideal sheaf is projective

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals of finite type, and let
`b : X' ⟶ X` be the blowup of `X` in `ℐ`, that is, the relative `Proj` of the Rees algebra
`⨁_{d ≥ 0} ℐ^d`. Then `b` is a projective morphism (Stacks 02NS, part (1)).

## Main results

* `AlgebraicGeometry.isGeneratedInDegreeOne_reesSheafGradedAlgebra`: the Rees algebra is
  generated in degree one, in the adjoin form.
* `AlgebraicGeometry.isProjective_blowUpToBase`: the blowup morphism is projective.

## Implementation notes

The surjection `Sym_{𝒪_X}(ℐ) ↠ ⨁_{d ≥ 0} ℐ^d` of graded `𝒪_X`-algebras induces, by Tag 07ZK (2), a
closed immersion `X' ↪ 𝐏(ℐ)` over `X`, whence the condition of Definition 01W8. For an arbitrary
quasi-coherent graded algebra generated in degree one by a degree-one piece of finite type this is
`AlgebraicGeometry.isProjective_relativeProj_toBase` (Tag 0B3U), which is applied to the Rees
algebra with three inputs:

* `Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp` identifies
  `AlgebraicGeometry.blowUpToBase` over the base with the relative `Proj` of the
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` of the Rees algebra, and
  projectivity transports along it by `AlgebraicGeometry.IsProjective.comp_iso`;
* `AlgebraicGeometry.ReesAlgebraData.isGeneratedInDegreeOne` at `Stacks.Blowup.reesAlgebraData`,
  turned into an equality of subalgebras by
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.adjoin_grading_one_eq_top`,
  gives generation in degree one;
* `Stacks.Blowup.isFiniteType_reesSheafGradedAlgebra_piece` at `n = 1` says that the degree-one
  piece, which is `ℐ`, is of finite type.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 0B3U](https://stacks.math.columbia.edu/tag/0B3U)
* [Stacks Project, Tag 07ZK](https://stacks.math.columbia.edu/tag/07ZK)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The Rees algebra of a quasi-coherent ideal sheaf is generated in degree one**, in the
adjoin form: over every affine open of the base the graded ring of homogeneous sections is
generated, as an algebra over its degree-zero part, by its degree-one part. -/
public theorem isGeneratedInDegreeOne_reesSheafGradedAlgebra :
    Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne
      (Stacks.Blowup.reesSheafGradedAlgebra I) := fun V hV =>
  (Stacks.Blowup.reesSheafGradedAlgebra I).adjoin_grading_one_eq_top V
    (Stacks.SymGraded.isGeneratedInDegreeOneAt_toSheafGradedAlgebra _ _ _ _ V
      (ReesAlgebraData.isGeneratedInDegreeOne I (Stacks.Blowup.reesAlgebraData I) ⟨V, hV⟩))

/-- The blowup of a scheme in a quasi-coherent sheaf of ideals of finite type is a projective
morphism. -/
@[stacks 02NS "part (1): `b : X' ⟶ X` is a projective morphism", ega "IV 19.4.1"]
public theorem isProjective_blowUpToBase (hI : I.IsFiniteType) :
    IsProjective (blowUpToBase I) := by
  obtain ⟨e, he⟩ := Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp I
  have hfin : ((Stacks.Blowup.reesSheafGradedAlgebra I).piece 1).IsFiniteType := by
    simpa using Stacks.Blowup.isFiniteType_reesSheafGradedAlgebra_piece I hI 1
  have h : IsProjective (e.hom ≫ blowUpToBase I) := by
    rw [he]
    exact isProjective_relativeProj_toBase (Stacks.Blowup.reesSheafGradedAlgebra I)
      (isGeneratedInDegreeOne_reesSheafGradedAlgebra I) hfin
  simpa using IsProjective.comp_iso e.symm h

end AlgebraicGeometry

end
