module

public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.GlueAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.SymSectionRing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists

/-!
# The two twisting sheaves `𝒪(1)` of a projective bundle agree

For a quasi-coherent module `F` on a scheme `X` the projective bundle
`𝐏(F) = Stacks.RelativeProj.projectiveBundle X F` is the relative `Proj` of the situation
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent X F`, and as such carries the twisting
sheaves `Stacks.RelativeProj.Situation.twistSheaf _ n` glued from the charts of that situation.
It also carries `Stacks.RelativeProj.tautologicalDatumTwist F`, the degree-one twist of
[Stacks, Tag 01NR] on the `SheafGradedAlgebra` presentation of `𝐏(F)`, read on `𝐏(F)` along the
comparison `Stacks.RelativeProj.bundlePresentationIso F` of the two presentations. This file
identifies the two, in every degree.

## Main definitions

* `Stacks.RelativeProj.presentationTwistIsoTwistSheaf`: the relative twist of the
  `SheafGradedAlgebra` presentation, read on `𝐏(F)`, is the twisting sheaf of the situation.
* `Stacks.RelativeProj.twistSheafOneIsoTautologicalDatumTwist`: the degree-one case,
  `𝒪_{𝐏(F)}(1) ≅ Stacks.RelativeProj.tautologicalDatumTwist F`.

## Implementation notes

This is `Stacks.AlgebraicGeometry.ProjThetaCompare.twistSheafAlgebraComparisonIso` for the
comparison `(bundlePresentationIso F).inv`, whose chart formula
`Stacks.ProjectiveBundle.relativeProjChart_presentationIso_inv` is the chart datum the
comparison asks for, with the graded comparison `Stacks.SymGraded.situationGradedHom` of the two
spellings of the graded ring of sections over an affine open. That comparison has a two-sided
inverse, so each chart twist comparison is invertible.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal
open Stacks.SymGraded Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.ProjTwistComparison

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` for the graded comparison of the two
spellings of the graded ring of sections of `Sym(F)` over an affine open: it has a right
inverse. -/
theorem irrelevant_le_map_situationGradedHom (W : X.affineOpens) :
    (HomogeneousIdeal.irrelevant ((symSituation F).sectionRingGrading W.1)) ≤
      (HomogeneousIdeal.irrelevant ((situationSheafGradedAlgebra F
          (isQuasicoherentPieces_of_isQuasicoherent F)).grading W.1)).map
        (situationGradedHom F (isQuasicoherentPieces_of_isQuasicoherent F) W.1) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _
    (Stacks.ProjectiveBundle.presentation_hmn F (isQuasicoherentPieces_of_isQuasicoherent F)
      (⟨W.1, show IsAffineOpen W.1 from W.2⟩ : X.AffineZariskiSite))

/-- **The relative twist of the `SheafGradedAlgebra` presentation of `𝐏(F)`, read on `𝐏(F)`, is
the twisting sheaf of the situation `Sym(F)`**, in every degree. -/
def presentationTwistIsoTwistSheaf (n : ℤ) :
    (Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist
          (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)) n) ≅
      Situation.twistSheaf (symmetricSituationOfQuasicoherent X F) n :=
  Stacks.AlgebraicGeometry.ProjThetaCompare.twistSheafAlgebraComparisonIso
    (s := symSituation F)
    (situationSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)) n
    (bundlePresentationIso F).inv
    (fun W => situationGradedHom F (isQuasicoherentPieces_of_isQuasicoherent F) W.1)
    (fun W => irrelevant_le_map_situationGradedHom F W)
    (fun W => Stacks.ProjectiveBundle.relativeProjChart_presentationIso_inv F
      (isQuasicoherentPieces_of_isQuasicoherent F)
      (⟨W.1, show IsAffineOpen W.1 from W.2⟩ : X.AffineZariskiSite))
    (fun {W W'} h => (situationGradedHom_res F (isQuasicoherentPieces_of_isQuasicoherent F)
      W'.1 W.1 h).symm)
    (fun W => isIso_twistMap_of_comp_eq_id _ _ n
      (Stacks.ProjectiveBundle.presentationInv F (isQuasicoherentPieces_of_isQuasicoherent F)
        (⟨W.1, show IsAffineOpen W.1 from W.2⟩ : X.AffineZariskiSite))
      (Stacks.ProjectiveBundle.presentation_hmn F (isQuasicoherentPieces_of_isQuasicoherent F)
        (⟨W.1, show IsAffineOpen W.1 from W.2⟩ : X.AffineZariskiSite))
      (Stacks.ProjectiveBundle.presentation_hnm F (isQuasicoherentPieces_of_isQuasicoherent F)
        (⟨W.1, show IsAffineOpen W.1 from W.2⟩ : X.AffineZariskiSite)))

/-- **`𝒪_{𝐏(F)}(1)` is the tautological twist**: the degree-one twisting sheaf of the situation
`Sym(F)` is `Stacks.RelativeProj.tautologicalDatumTwist F`. -/
def twistSheafOneIsoTautologicalDatumTwist :
    Situation.twistSheaf (symmetricSituationOfQuasicoherent X F) 1 ≅ tautologicalDatumTwist F :=
  (presentationTwistIsoTwistSheaf F 1).symm

end Stacks.RelativeProj

end
