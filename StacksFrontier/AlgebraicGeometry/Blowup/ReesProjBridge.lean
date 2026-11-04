module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.Modules.ClosedSubschemeQuotient
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Dictionary
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.QuasiCompact

/-!
# The blowup is the relative `Proj` of the Rees algebra, on the `SheafGradedAlgebra` substrate

The Rees algebra `⨁_{n ≥ 0} Iⁿ` of a quasi-coherent ideal sheaf is built in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebraSheaf.lean` as a
`SheafOfModules.GradedAlgebra`, and `Stacks.Blowup.reesSituation` reads it as a
`Stacks.RelativeProj.Situation`, whose relative `Proj` is identified with
`AlgebraicGeometry.blowUp` over the base by
`Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase`.

Results about closed subschemes of a relative `Proj` — Tags 0801, 0802 and 0803 — are stated
instead for a `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` and the
relative `Proj` assembled from it as a colimit over the small affine Zariski site of the base.
**This file puts the Rees algebra on that substrate and identifies its relative `Proj` with the
blowup, over the base.**

## Main definitions

* `Stacks.Blowup.reesSheafGradedAlgebra`: the Rees algebra of a quasi-coherent ideal sheaf as
  sheaf-level graded algebra data in the sense of Situation 01NN.

## Main results

* `Stacks.Blowup.exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp`: **the relative `Proj` of
  `Stacks.Blowup.reesSheafGradedAlgebra` is the blowup of the base in the centre, by an
  isomorphism over the base.**

## Implementation notes

The two relative `Proj`s are glued by different frameworks — a colimit over the small affine
Zariski site on the `SheafGradedAlgebra` side, and the cover by *all* affine opens on the
`Stacks.RelativeProj.Data` side — and the comparison of those two glueings, from a graded ring
isomorphism of the sections over each affine open, is
`Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj`. The graded ring isomorphism
itself is `Stacks.AlgebraicGeometry.RelativeProjBridge.situationSectionGradedHom`, which is
carried by the identity map: both section rings are `⨁_{k ≥ 0} Γ(𝒜ₖ, U)` and only the two
`CommRing` instances differ. So this file supplies no new mathematics; it composes the chart
comparison with the glueing comparison and with the blowup comparison.

`Stacks.Blowup.reesSituation` and
`Stacks.AlgebraicGeometry.RelativeProjBridge.situationOfGradedAlgebra` of the Rees graded algebra
are the same term: the two data fields are the same and the three remaining fields are `Prop`s.
`Stacks.Blowup.reesSituation_eq_situationOfGradedAlgebra` records that, and is `rfl`.

Negative-degree vanishing is asked for on local sections by
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.VanishesInNegativeDegrees`, while
`Stacks.Blowup.reesPiece_negative_isZero` gives it as a zero object; the passage evaluates the
piece at the open and uses that a zero module is a subsingleton.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)

## Not done here

No `@[stacks]` attribute is attached. The existence of the relative homogeneous spectrum is
Tag 01NQ and is tagged where it is built; the identification of the blowup with the relative
`Proj` of the Rees algebra is Tag 01OG, already claimed by
`Stacks.Blowup.exists_reesAlgebraData` and by the construction of the blowup itself, and this is
that identification moved to the other substrate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The Rees algebra as sheaf-level graded algebra data -/

/-- Homogeneous multiplication in the Rees algebra is commutative. -/
public theorem reesIsCommutative : IsCommutative (reesGradedAlgebra I) :=
  (reesAlgebraData I).mul_comm

/-- **The Rees algebra vanishes in negative degrees, on local sections.** The piece is a zero
object there, so its module of sections over any open is a subsingleton. -/
public theorem reesVanishesInNegativeDegrees :
    VanishesInNegativeDegrees (reesGradedAlgebra I) := by
  intro n hn U x
  let E := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj U
  exact (ModuleCat.subsingleton_of_isZero
    (E.map_isZero (reesPiece_negative_isZero I n hn))).elim _ _

/-- Every homogeneous piece of the Rees algebra is quasi-coherent. -/
public theorem reesIsQuasicoherent (n : ℤ) :
    (((reesGradedAlgebra I).piece n : X.Modules)).IsQuasicoherent :=
  (reesAlgebraData I).isQuasicoherent n

/-- **The Rees algebra `⨁_{n ≥ 0} Iⁿ` as sheaf-level graded algebra data**, in the sense of
Situation 01NN. This is the substrate on which the results about closed subschemes of a relative
`Proj` — Tags 0801, 0802 and 0803 — are stated. -/
public def reesSheafGradedAlgebra : SheafGradedAlgebra X :=
  toSheafGradedAlgebra (reesGradedAlgebra I) (reesIsCommutative I)
    (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I)

/-- The relative `Proj` situation of the Rees algebra is the situation attached to its graded
algebra: the two data fields agree and the three remaining fields are `Prop`s. -/
public theorem reesSituation_eq_situationOfGradedAlgebra :
    reesSituation I = situationOfGradedAlgebra (reesGradedAlgebra I) (reesIsCommutative I)
      (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) := rfl

/-! ### The two glueings of the relative `Proj` of the Rees algebra agree -/

/-- The graded-ring structure on the homogeneous sections of the Rees algebra over an open,
indexed by `X.Opens`. This is
`Stacks.RelativeProj.Situation.sectionRingGradedRing` verbatim; the restatement is needed
because `Stacks.Blowup.reesSituation` is a plain definition, which instance search does not
unfold, so the instance is not found at the index `U : X.Opens`. -/
public instance gcommRingReesSituation (U : X.Opens) :
    DirectSum.GCommRing ((reesSituation I).sectionPieces U) :=
  Stacks.RelativeProj.Situation.sectionRingGradedRing (reesSituation I) U

/-- The internal grading of the Rees algebra's section ring over an open, indexed by `X.Opens`.
This is `Stacks.RelativeProj.Situation.sectionRingGradingGradedRing` verbatim, restated for the
same reason as the instance above. -/
public instance gradedRingReesSituation (U : X.Opens) :
    GradedRing ((reesSituation I).sectionRingGrading U) :=
  Stacks.RelativeProj.Situation.sectionRingGradingGradedRing (reesSituation I) U

/-- The graded-ring comparison of the two substrates' sections over an affine open of the base. -/
public def reesChartHom (U : X.AffineZariskiSite) :
    ((reesSheafGradedAlgebra I).toGradedAlgebra).grading U →+*ᵍ
      (reesSituation I).sectionRingGrading
        (Stacks.AlgebraicGeometry.ProjPresentation.siteAffineOpen U).1 :=
  situationSectionGradedHom (reesGradedAlgebra I) (reesIsCommutative I)
    (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens

/-- The inverse graded-ring comparison. -/
public def reesChartInv (U : X.AffineZariskiSite) :
    (reesSituation I).sectionRingGrading
        (Stacks.AlgebraicGeometry.ProjPresentation.siteAffineOpen U).1 →+*ᵍ
      ((reesSheafGradedAlgebra I).toGradedAlgebra).grading U :=
  situationSectionGradedInv (reesGradedAlgebra I) (reesIsCommutative I)
    (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens

/-- **The comparison carries the degree-zero identification of the `SheafGradedAlgebra` to that
of the situation.** Both send a section of the structure sheaf to its multiple of the unit
section, read in degree zero. -/
public theorem strZero_comp_reesChartHom (U : X.AffineZariskiSite) :
    ((reesSheafGradedAlgebra I).toGradedAlgebra).strZero U ≫
        CommRingCat.ofHom (reesChartHom I U).gradedZeroRingHom =
      (Stacks.RelativeProj.Situation.chartData (reesSituation I)).base
        (Stacks.AlgebraicGeometry.ProjPresentation.siteAffineOpen U) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  refine Eq.trans (congrArg (situationSectionRingEquiv (reesGradedAlgebra I)
    (reesIsCommutative I) (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens)
    (((reesSheafGradedAlgebra I).toGradedAlgebra).coe_strZero_apply U r)) ?_
  refine Eq.trans (situationSectionRingEquiv_strHom (reesGradedAlgebra I) (reesIsCommutative I)
    (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens r) ?_
  exact (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
    (Stacks.RelativeProj.Situation.sectionRingBaseMap_mem_zero
      (reesSituation I) U.toOpens r)).symm

/-- **The relative `Proj` of the Rees algebra on the `SheafGradedAlgebra` substrate is the
relative `Proj` of `Stacks.Blowup.reesSituation`, by an isomorphism over the base.** The two
schemes are glued by different frameworks, and
`Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj` compares the glueings from
the graded-ring comparison of the sections over each affine open of the base. -/
public theorem exists_iso_relativeProj_reesSituation :
    ∃ e : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (reesSheafGradedAlgebra I)).scheme ≅
        Stacks.RelativeProj.Situation.relativeProj (reesSituation I),
      e.hom ≫ Stacks.RelativeProj.Situation.relativeProjToBase (reesSituation I) =
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (reesSheafGradedAlgebra I)).toBase :=
  Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj
    (Stacks.RelativeProj.Situation.chartData (reesSituation I))
    ((reesSheafGradedAlgebra I).toGradedAlgebra)
    (reesChartHom I) (reesChartInv I)
    (fun U => situationSectionGradedInv_comp_hom (reesGradedAlgebra I) (reesIsCommutative I)
      (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens)
    (fun U => situationSectionGradedHom_comp_inv (reesGradedAlgebra I) (reesIsCommutative I)
      (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.toOpens)
    (fun _ _ h => GradedRingHom.ext fun x =>
      situationSectionRingEquiv_resRingHom (reesGradedAlgebra I) (reesIsCommutative I)
        (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) h x)
    (strZero_comp_reesChartHom I)

/-! ### The relative `Proj` of the Rees algebra is the blowup -/

/-- **The relative `Proj` of the Rees algebra of a quasi-coherent ideal sheaf, on the
`SheafGradedAlgebra` substrate, is the blowup of the base in that ideal sheaf, by an isomorphism
over the base.**

This is the identification the results about closed subschemes of a relative `Proj` — Tags 0801,
0802 and 0803 — have to be instantiated along in order to speak about the blowup: they are
stated for a `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra` and the relative
`Proj` assembled from it, and this says that relative `Proj` is `AlgebraicGeometry.blowUp`.

It is `Stacks.Blowup.exists_iso_relativeProj_reesSituation`, the comparison of the two
glueings, composed with `Stacks.Blowup.reesSituationBlowUpIso`, the comparison of the
situation's relative `Proj` with the blowup. Both are isomorphisms over the base, so the
composite is too. -/
public theorem exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp :
    ∃ e : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (reesSheafGradedAlgebra I)).scheme ≅ AlgebraicGeometry.blowUp I,
      e.hom ≫ AlgebraicGeometry.blowUpToBase I =
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (reesSheafGradedAlgebra I)).toBase := by
  obtain ⟨e, he⟩ := exists_iso_relativeProj_reesSituation I
  refine ⟨e ≪≫ reesSituationBlowUpIso I, ?_⟩
  rwa [Iso.trans_hom, Category.assoc, reesSituationBlowUpIso_hom_blowUpToBase I]

/-! ### Two inputs of Tag 0803 at the Rees algebra -/

/-- **A power of a finite-type ideal sheaf is of finite type.** Over an affine open the ideal of
`I ^ n` is the `n`-th power of the ideal of `I`, and a power of a finitely generated ideal is
finitely generated. -/
public theorem isFiniteType_pow (hI : I.IsFiniteType) (n : ℕ) : (I ^ n).IsFiniteType := fun U => by
  rw [Scheme.IdealSheafData.ideal_pow]
  exact (hI U).pow

/-- **The homogeneous pieces of the Rees algebra of a finite-type ideal sheaf are of finite
type.** The degree-`n` piece is the ideal sheaf `I ^ n` read as a submodule of the structure
sheaf, which is of finite type because `I ^ n` is. This is the hypothesis `hA` of
[Stacks, Tag 0803] at the Rees algebra. -/
public theorem isFiniteType_reesSheafGradedAlgebra_piece (hI : I.IsFiniteType) (n : ℕ) :
    SheafOfModules.IsFiniteType.{u, u, u} ((reesSheafGradedAlgebra I).piece (n : ℤ)) :=
  SheafOfModules.IsFiniteType.of_iso
    (Stacks.FiniteTypeIdealSheaf.isFiniteType_unitSubmodule (I ^ n) (isFiniteType_pow I hI n))
    (Stacks.ClosedSubscheme.unitSubmoduleIsoKernel (I ^ n))

/-- **The structure morphism of the relative `Proj` of the Rees algebra is quasi-compact**, for a
centre of finite type. This is the instance argument `[QuasiCompact (relativeProj A).toBase]` of
[Stacks, Tag 0803] at the Rees algebra: the comparison with the blowup is an isomorphism over the
base, and `Stacks.Blowup.quasiCompact_blowUpToBase` gives it for the blowup. -/
public theorem quasiCompact_relativeProj_reesSheafGradedAlgebra_toBase (hI : I.IsFiniteType) :
    QuasiCompact (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (reesSheafGradedAlgebra I)).toBase := by
  obtain ⟨e, he⟩ := exists_iso_relativeProj_reesSheafGradedAlgebra_blowUp I
  have hb : QuasiCompact (AlgebraicGeometry.blowUpToBase I) := quasiCompact_blowUpToBase hI
  rw [← he]
  infer_instance

end Stacks.Blowup

end
