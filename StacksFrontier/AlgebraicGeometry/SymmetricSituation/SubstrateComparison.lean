module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation

/-!
# The two projective-bundle substrates of a quasi-coherent module have the same section rings

The projective bundle of a quasi-coherent `𝒪_X`-module `E` is built twice in this repository, from
the same sheaf of graded algebras `Sym(E)`: once as
`Stacks.SymGraded.schemeSheafGradedAlgebra`, a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, and once as
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent`, a `Stacks.RelativeProj.Situation`.
**This file identifies their graded rings of local sections over an open, for an arbitrary
quasi-coherent `E`.**

It is the general comparison of
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison` read at the symmetric
algebra: both substrates are built from
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` together with
commutativity, concentration in nonnegative degrees and quasi-coherence of the pieces, so the two
objects are `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra` and
`Stacks.AlgebraicGeometry.RelativeProjBridge.situationOfGradedAlgebra` of one and the same datum.
The comparison is therefore the identity map, and the only content is that the two `CommRing`
instances agree.

## Main definitions

* `Stacks.SymGraded.symmetricSectionRingEquiv`: **the two graded rings of local sections of
  `Sym(E)` over an open are the same ring.**
* `Stacks.SymGraded.symmetricSectionGradedHom` and `Stacks.SymGraded.symmetricSectionGradedInv`:
  that isomorphism and its inverse as homomorphisms of graded rings.

## Main results

* `Stacks.SymGraded.schemeSheafGradedAlgebra_eq_toSheafGradedAlgebra` and
  `Stacks.SymGraded.symmetricSituationOfQuasicoherent_eq_situationOfGradedAlgebra`: both
  substrates are the generic constructions on
  `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E`. Both hold by
  `rfl`, the three remaining fields of either being proofs of propositions.
* `Stacks.SymGraded.symmetricSectionRingEquiv_of`: the comparison is the identity on a homogeneous
  section.
* `Stacks.SymGraded.symmetricSectionRingEquiv_strHom` and
  `Stacks.SymGraded.symmetricSectionRingEquiv_resRingHom`: it carries the structure map to the
  canonical map from the structure sheaf, and it is natural in the open.

## Not done here

The algebra of the comparison of the two presentations of the projective bundle is settled by
this file; what remains for `AlgebraicGeometry.ProjectiveBundlePresentationsAgree` is the
glueing, the two presentations being glued by two different frameworks. See the `Not done here`
section of
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E)

/-! ### Both substrates are the generic constructions on `Sym(E)` -/

omit [E.IsQuasicoherent] in
/-- The `SheafGradedAlgebra` of `Sym(E)` is the generic conversion applied to it. This is its
definition. -/
theorem schemeSheafGradedAlgebra_eq_toSheafGradedAlgebra :
    schemeSheafGradedAlgebra E hqc =
      toSheafGradedAlgebra (Scheme.Modules.symmetricAlgebra X E)
        (isCommutative_symmetricAlgebra E)
        (vanishesInNegativeDegrees_symmetricAlgebra E) hqc := rfl

/-- **The projective bundle situation of `E` is the generic situation of `Sym(E)`.** The base
scheme and the graded algebra agree on the nose, and the remaining three fields of a
`Stacks.RelativeProj.Situation` are proofs of propositions. -/
theorem symmetricSituationOfQuasicoherent_eq_situationOfGradedAlgebra :
    RelativeProj.symmetricSituationOfQuasicoherent X E =
      situationOfGradedAlgebra (Scheme.Modules.symmetricAlgebra X E)
        (isCommutative_symmetricAlgebra E)
        (vanishesInNegativeDegrees_symmetricAlgebra E) hqc := rfl

/-- The graded-ring structure on the homogeneous sections of `Sym(E)` over an open, indexed by
`X.Opens`. `Stacks.RelativeProj.Situation.sectionRingGradedRing` is indexed by `s.base.Opens`,
and `(symmetricSituationOfQuasicoherent X E).base` is a chain of plain `def`s which instance
search does not unfold; the body here is that instance verbatim. -/
instance symmetricSituationGCommRing (U : X.Opens) :
    DirectSum.GCommRing
      ((RelativeProj.symmetricSituationOfQuasicoherent X E).sectionPieces U) :=
  RelativeProj.Situation.sectionRingGradedRing
    (RelativeProj.symmetricSituationOfQuasicoherent X E) U

/-! ### The comparison -/

/-- **The graded ring of homogeneous local sections of `Sym(E)` over an open is the same ring for
either substrate**, for an arbitrary quasi-coherent `E`. -/
def symmetricSectionRingEquiv (U : X.Opens) :
    (schemeSheafGradedAlgebra E hqc).sectionRing U ≃+*
      (RelativeProj.symmetricSituationOfQuasicoherent X E).sectionRing U :=
  situationSectionRingEquiv (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U

/-- The comparison leaves a homogeneous section where it is. -/
theorem symmetricSectionRingEquiv_of (U : X.Opens) (k : ℕ)
    (y : (schemeSheafGradedAlgebra E hqc).sectionPieces U k) :
    symmetricSectionRingEquiv E hqc U (DirectSum.of _ k y) =
      DirectSum.of
        ((RelativeProj.symmetricSituationOfQuasicoherent X E).sectionPieces U) k y :=
  situationSectionRingEquiv_of (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U k y

/-- **The comparison as a homomorphism of graded rings.** -/
def symmetricSectionGradedHom (U : X.Opens) :
    (schemeSheafGradedAlgebra E hqc).grading U →+*ᵍ
      (RelativeProj.symmetricSituationOfQuasicoherent X E).sectionRingGrading U :=
  situationSectionGradedHom (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U

/-- **The inverse comparison as a homomorphism of graded rings.** -/
def symmetricSectionGradedInv (U : X.Opens) :
    (RelativeProj.symmetricSituationOfQuasicoherent X E).sectionRingGrading U →+*ᵍ
      (schemeSheafGradedAlgebra E hqc).grading U :=
  situationSectionGradedInv (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U

/-- The comparison `symmetricSectionGradedHom` composed after its inverse
`symmetricSectionGradedInv` is the identity. -/
theorem symmetricSectionGradedHom_comp_inv (U : X.Opens) :
    (symmetricSectionGradedHom E hqc U).comp (symmetricSectionGradedInv E hqc U) =
      GradedRingHom.id
        ((RelativeProj.symmetricSituationOfQuasicoherent X E).sectionRingGrading U) :=
  situationSectionGradedHom_comp_inv (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U

/-- The inverse comparison `symmetricSectionGradedInv` composed after `symmetricSectionGradedHom`
is the identity. -/
theorem symmetricSectionGradedInv_comp_hom (U : X.Opens) :
    (symmetricSectionGradedInv E hqc U).comp (symmetricSectionGradedHom E hqc U) =
      GradedRingHom.id ((schemeSheafGradedAlgebra E hqc).grading U) :=
  situationSectionGradedInv_comp_hom (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U

/-! ### The structure map, and naturality in the open -/

/-- **The comparison carries the structure map to the canonical map from the structure sheaf.** -/
theorem symmetricSectionRingEquiv_strHom (U : X.Opens) (r : Γ(X, U)) :
    symmetricSectionRingEquiv E hqc U ((schemeSheafGradedAlgebra E hqc).strHom U r) =
      (RelativeProj.symmetricSituationOfQuasicoherent X E).sectionRingBaseMap U r :=
  situationSectionRingEquiv_strHom (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc U r

/-- **The comparison is natural in the open.** -/
theorem symmetricSectionRingEquiv_resRingHom {U V : X.Opens} (h : U ≤ V)
    (x : (schemeSheafGradedAlgebra E hqc).sectionRing V) :
    symmetricSectionRingEquiv E hqc U ((schemeSheafGradedAlgebra E hqc).resRingHom h x) =
      (RelativeProj.symmetricSituationOfQuasicoherent X E).sectionRingRestrict U V h
        (symmetricSectionRingEquiv E hqc V x) :=
  situationSectionRingEquiv_resRingHom (Scheme.Modules.symmetricAlgebra X E)
    (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc h x

end Stacks.SymGraded

end
