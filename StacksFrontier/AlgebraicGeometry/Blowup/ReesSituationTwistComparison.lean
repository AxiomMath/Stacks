module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistChartComparison

/-!
# The twisting sheaves of the two Rees algebras of a blowup agree

`StacksFrontier/AlgebraicGeometry/Blowup/ReesSituationComparison.lean` identifies the relative
projective spectrum of a Rees model `m` of a quasi-coherent ideal sheaf `J` with
`AlgebraicGeometry.blowUp J`, as schemes over the base:
`Stacks.Blowup.ReesModel.relativeProjIso`.  This file carries the twisting sheaves across that
identification: for every `n : ℤ`,

`c^* 𝒪_{X'}(n) ≅ 𝒪_{Proj(s)}(n)`, where `c = m.relativeProjIso.hom`.

The comparison itself is the chartwise transport of
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjTwistChartComparison.lean`,
`Stacks.RelativeProj.Situation.twistChartComparisonIso`, which asks for exactly four things about
the morphism of relative projective spectra, and all four are properties of an isomorphism of
gluing data:

* over each affine open `W` of the base, a homomorphism of the graded rings of local sections —
  `Stacks.RelativeProj.Data.Iso.inv`, which covers the irrelevant ideal by
  `Stacks.RelativeProj.Data.Iso.irrelevant_le_inv`;
* the factorization of the chart of the model followed by `c` through the chart of the chosen Rees
  algebra, which is `Stacks.Blowup.ReesModel.relativeProjChart_relativeProjIso_hom` read at the
  `AlgebraicGeometry.Proj.map` spelling;
* the compatibility of those homomorphisms with the restriction maps,
  `Stacks.RelativeProj.Data.Iso.restrict_comp_inv`;
* invertibility of the twist comparison of each of them, which holds because each has a two-sided
  inverse — `Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id`.

## Main results

* `Stacks.Blowup.ReesModel.twistSheafReesIso` and `Stacks.Blowup.reesSituationBlowUpTwistIso`:
  **the transport of the twisting sheaf across the comparison of the two presentations of the
  blowup**, in every degree.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open Stacks.RelativeProj Stacks.RelativeProj.Situation Stacks.ProjTwistComparison

universe u

namespace Stacks.RelativeProj.Situation

/-- **The restriction map of the gluing datum of charts is the restriction of graded section
rings.** The comparison of two gluing data is stated at the restriction map of the datum, the
lemmas about graded rings of sections at `Stacks.RelativeProj.Situation.gradedSectionRestriction`;
this identity passes between the two. -/
public theorem chartData_restrict (t : Situation.{u}) {W W' : t.base.affineOpens} (h : W ≤ W') :
    (chartData t).restrict h = gradedSectionRestriction t W.1 W'.1 h :=
  rfl

end Stacks.RelativeProj.Situation

namespace Stacks.Blowup.ReesModel

variable {s : Situation.{u}} {J : s.base.IdealSheafData} (m : ReesModel s J) (n : ℤ)

/-- The comparison of the two relative `Proj`s, read on the chart over an affine open `W` of the
base, with the comparison morphism of the charts at the `AlgebraicGeometry.Proj.map` spelling the
generic twist lemmas are stated at.  This is
`Stacks.Blowup.ReesModel.relativeProjChart_relativeProjIso_hom` with the chart isomorphism
`Stacks.RelativeProj.Data.Iso.projIso` unfolded; the two spellings are the same term. -/
public theorem relativeProjChart_comp_projMap_inv (W : s.base.affineOpens) :
    relativeProjChart s W ≫ m.relativeProjIso.hom
      = AlgebraicGeometry.Proj.map (m.dataIso.inv W) (m.dataIso.irrelevant_le_inv W)
        ≫ relativeProjChart (AlgebraicGeometry.reesSituation J) W :=
  m.relativeProjChart_relativeProjIso_hom W

/-- **The comparison of the two algebras of local sections commutes with the restriction maps**,
written at `Stacks.RelativeProj.Situation.gradedSectionRestriction` on both sides.  This is
`Stacks.RelativeProj.Data.Iso.restrict_comp_inv` read through
`Stacks.RelativeProj.Situation.chartData_restrict`. -/
public theorem gradedSectionRestriction_comp_inv {W W' : s.base.affineOpens} (h : W' ≤ W) :
    (gradedSectionRestriction s W'.1 W.1 h).comp (m.dataIso.inv W)
      = (m.dataIso.inv W').comp
          (gradedSectionRestriction (AlgebraicGeometry.reesSituation J) W'.1 W.1 h) := by
  rw [← chartData_restrict s h, ← chartData_restrict (AlgebraicGeometry.reesSituation J) h]
  exact m.dataIso.restrict_comp_inv h

/-- **The twist comparison attached to the chart of the comparison isomorphism is invertible.**
The graded ring homomorphism it is attached to has a two-sided inverse, so this is
`Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id`. -/
public theorem isIso_twistMap_dataIso_inv (W : s.base.affineOpens) :
    IsIso (twistMap (m.dataIso.inv W) (m.dataIso.irrelevant_le_inv W) n) :=
  isIso_twistMap_of_comp_eq_id _ _ n (m.dataIso.hom W) (m.dataIso.inv_comp_hom W)
    (m.dataIso.hom_comp_inv W)

/-- **The twisting sheaf of the blowup, transported to the relative projective spectrum of a Rees
model**: `c^* 𝒪_{X'}(n) ≅ 𝒪_{Proj(s)}(n)` for `c = m.relativeProjIso.hom`, in every degree.

This is `Stacks.RelativeProj.Situation.twistChartComparisonIso` for the comparison of the two
gluing data, with the identity on affine opens of the base. -/
public def twistSheafReesIso :
    (Scheme.Modules.pullback m.relativeProjIso.hom).obj
        (twistSheaf (AlgebraicGeometry.reesSituation J) n)
      ≅ twistSheaf s n :=
  twistChartComparisonIso m.relativeProjIso.hom (fun W => W) (fun h => h)
    (fun W => m.dataIso.inv W) (fun W => m.dataIso.irrelevant_le_inv W)
    (fun W => m.relativeProjChart_comp_projMap_inv W) n
    (fun h => m.gradedSectionRestriction_comp_inv h) (fun W => m.isIso_twistMap_dataIso_inv n W)

end Stacks.Blowup.ReesModel

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ)

/-- **The twisting sheaf of the blowup, transported to the relative `Proj` of the explicitly
built Rees algebra.**  The blowup of `X` in `I` is presented twice — as
`AlgebraicGeometry.blowUp I`, the relative `Proj` of the `Classical.choice`-chosen Rees algebra,
and as the relative `Proj` of `Stacks.Blowup.reesSituation I`, whose graded algebra one can
compute with — and `Stacks.Blowup.reesSituationBlowUpIso` identifies the two over the base.  This
carries `𝒪_{X'}(n)` across that identification, in every degree. -/
public def reesSituationBlowUpTwistIso :
    (Scheme.Modules.pullback (reesSituationBlowUpIso I).hom).obj
        (AlgebraicGeometry.blowUpTwist I n)
      ≅ Situation.twistSheaf (Stacks.Blowup.reesSituation I) n :=
  (reesSituationModel I).twistSheafReesIso n

end Stacks.Blowup

end
