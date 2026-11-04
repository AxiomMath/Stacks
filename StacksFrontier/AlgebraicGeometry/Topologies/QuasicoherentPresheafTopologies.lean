module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf

/-!
# The six topologies of Tag 03DT reduce to the fpqc one

Tag 03DT asserts the sheaf condition for the pullback-sections presheaf of Tag 03DS with
respect to `τ`-coverings of an arbitrary scheme over `S`, for each of the six topologies
`τ ∈ {Zariski, étale, smooth, syntomic, fppf, fpqc}`.  The source proves it only for `τ = fpqc`
and deduces the other five from the fact that every `τ`-covering is an fpqc covering, which is
Tags 0216, 0220, 0226, 021N and 022C.  This file carries out that deduction.

The point is not the mathematics — it is monotonicity — but the bookkeeping: the presheaf of
Tag 03DS lives on `CategoryTheory.Over S`, so the comparison needed is between the
*localisations* `τ.over S` and `fpqc.over S` rather than between the topologies on all schemes,
and the localisation of a Grothendieck topology at an object is not known to Mathlib to be
monotone.  `CategoryTheory.GrothendieckTopology.over_mono` supplies that -- it is already in
the library, at `StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean:136` -- and then
`CategoryTheory.Presieve.isSheaf_of_le` does the rest.

The consequence is a statement about the fpqc form of Tag 03DT — the form
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'` proves, and the one every associated
module on a site in the tree is built from, through
`Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_isContinuous`: this file shows that form
is not a weakening of Tag 03DT but carries all six of its topologies.

## Main results

* `Stacks.Sites.isSheaf_over_quasiCoherentPresheaf_of_fpqc`: the sheaf condition for the
  presheaf of Tag 03DS and the localisation at `S` of any topology coarser than the fpqc
  topology follows from the fpqc one.
* `Stacks.Sites.isSheaf_zariskiTopology_over_quasiCoherentPresheaf_of_fpqc`,
  `Stacks.Sites.isSheaf_etaleTopology_over_quasiCoherentPresheaf_of_fpqc`,
  `Stacks.Sites.isSheaf_smoothTopology_over_quasiCoherentPresheaf_of_fpqc`,
  `Stacks.Sites.isSheaf_syntomicTopology_over_quasiCoherentPresheaf_of_fpqc` and
  `Stacks.Sites.isSheaf_fppfTopology_over_quasiCoherentPresheaf_of_fpqc`: the five instances of
  it, one for each topology of Tag 03DT other than the fpqc one.
* `Stacks.Sites.isSheaf_addCommGrpCat_over_quasiCoherentPresheaf_of_fpqc`: the same transport
  for the abelian-group-valued sheaf condition, which is the form Tag 03DT is stated in.

## Implementation notes

`CategoryTheory.GrothendieckTopology.mem_over_iff` reduces membership in `J.over X` to
membership of the corresponding sieve of the base in `J`, and that correspondence
(`CategoryTheory.Sieve.overEquiv`) does not involve the topology at all; so monotonicity of the
localisation is monotonicity of `J` evaluated at one sieve.

There is no named `smoothTopology` or `syntomicTopology` on all of `Scheme.{u}` — the two
abbreviations of that name in
`StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings` are topologies on the
size-bounded `B.Schemes` of a big fppf site — so the smooth and syntomic statements are phrased
with `(AlgebraicGeometry.Scheme.precoverage _).toGrothendieck`, which is what
`AlgebraicGeometry.Scheme.smoothPrecoverage_le_fpqcPrecoverage` and its syntomic counterpart
compare to the fpqc precoverage.

The syntomic comparison itself is
`AlgebraicGeometry.Scheme.syntomicPrecoverage_le_fpqcPrecoverage` of
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies`, imported here.

No tag is claimed.  Every statement below is conditional on the fpqc case of Tag 03DT, which is
not proved in this repository; `StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore`
records what reaching it would take.

## References

* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v u

namespace Stacks.Sites

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

/-- **The five coarser topologies of Tag 03DT follow from the fpqc one.**  If the presheaf of
Tag 03DS satisfies the sheaf condition for the localisation at `S` of the fpqc topology, then it
satisfies it for the localisation at `S` of every topology coarser than the fpqc topology. -/
public theorem isSheaf_over_quasiCoherentPresheaf_of_fpqc
    {J : GrothendieckTopology Scheme.{u}} (hJ : J ≤ Scheme.fpqcTopology.{u})
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presieve.IsSheaf (J.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  Presieve.isSheaf_of_le _ (GrothendieckTopology.over_mono hJ S) h

/-- The Zariski case of Tag 03DT, from the fpqc case. -/
public theorem isSheaf_zariskiTopology_over_quasiCoherentPresheaf_of_fpqc
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presieve.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  isSheaf_over_quasiCoherentPresheaf_of_fpqc S F Scheme.zariskiTopology_le_fpqcTopology h

/-- The étale case of Tag 03DT, from the fpqc case. -/
public theorem isSheaf_etaleTopology_over_quasiCoherentPresheaf_of_fpqc
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presieve.IsSheaf (Scheme.etaleTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  isSheaf_over_quasiCoherentPresheaf_of_fpqc S F etaleTopology_le_fpqcTopology h

/-- The smooth case of Tag 03DT, from the fpqc case. -/
public theorem isSheaf_smoothTopology_over_quasiCoherentPresheaf_of_fpqc
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presieve.IsSheaf
      ((Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})).toGrothendieck.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  isSheaf_over_quasiCoherentPresheaf_of_fpqc S F
    (Precoverage.toGrothendieck_mono Scheme.smoothPrecoverage_le_fpqcPrecoverage) h

/-- The syntomic case of Tag 03DT, from the fpqc case. -/
public theorem isSheaf_syntomicTopology_over_quasiCoherentPresheaf_of_fpqc
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presieve.IsSheaf
      ((Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u})).toGrothendieck.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  isSheaf_over_quasiCoherentPresheaf_of_fpqc S F
    (Precoverage.toGrothendieck_mono Scheme.syntomicPrecoverage_le_fpqcPrecoverage) h

/-- The fppf case of Tag 03DT, from the fpqc case. -/
public theorem isSheaf_fppfTopology_over_quasiCoherentPresheaf_of_fpqc
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presieve.IsSheaf (Scheme.fppfTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
  isSheaf_over_quasiCoherentPresheaf_of_fpqc S F Scheme.fppfTopology_le_fpqcTopology h

/-- **The abelian form of the transport.**  Tag 03DT is a statement about the abelian presheaf
of Tag 03DS, and the fpqc sheaf condition in the underlying types gives the sheaf condition for
abelian groups for every topology coarser than the fpqc topology. -/
public theorem isSheaf_addCommGrpCat_over_quasiCoherentPresheaf_of_fpqc
    {J : GrothendieckTopology Scheme.{u}} (hJ : J ≤ Scheme.fpqcTopology.{u})
    (h : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presheaf.IsSheaf (J.over S) (quasiCoherentPresheafFunctor S F) :=
  isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_over_quasiCoherentPresheaf_of_fpqc S F hJ h)

end Stacks.Sites

end
