module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedFibreTwoChartVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpensAcyclicityTransport
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheavesAndRestriction

/-!
# Finiteness of the cohomological dimension from the affine opens

Let `X` be a quasi-compact quasi-separated scheme. If every affine open `V` of `X` has
finite cohomological dimension `cd(V) < ∞` ([Stacks, Tag 0F0Q]), then `cd(X) < ∞`.

This is the reduction step of the proof of [Stacks, Tag 0F10], part (2): the induction
principle of [Stacks, Tag 08DR] reduces to the affine case, and the induction step is the
Mayer--Vietoris sequence of [Stacks, Tag 0A50]. If `U`, `V` and `U ∩ V` have cohomology of
torsion sheaves vanishing above `d_U`, `d_V` and `d_{U ∩ V}`, then `U ∪ V` has it vanishing
above `max(d_U, d_V, d_{U ∩ V}) + 1`, by the window
`H^{n}(U ∩ V) ⟶ H^{n + 1}(U ∪ V) ⟶ H^{n + 1}(U) ⊕ H^{n + 1}(V)`.

## Main results

* `AlgebraicGeometry.Scheme.exists_bound_opensCohomology_of_isAffineOpen`: on every
  quasi-compact open `W` of a quasi-separated scheme whose affine opens have finite
  cohomological dimension, there is a uniform bound above which the cohomology over `W` of
  every torsion abelian sheaf vanishes.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_lt_top_of_isAffineOpen`: **the
  reduction**, `cd(X) < ∞` once `cd(V) < ∞` for every affine open `V`.

## Implementation notes

The induction runs over the objects `(opensToSite X).obj W` of the one-universe model
`Stacks.EtaleCohomology.MayerVietoris.topology X` of the small étale site, where the
Mayer--Vietoris sequence is available for arbitrary pairs of opens. The affine opens enter
through
`Stacks.EtaleCohomology.OpensAcyclicity.subsingleton_opensCohomology_of_subsingleton_H_smallEtale`,
which turns vanishing of the étale cohomology of the restriction to the open subscheme into
vanishing of cohomology over the object, and the conclusion leaves the model through
`Stacks.EtaleCohomology.MayerVietoris.cohomologyTopIsoH` and the dense subsite transport
`DenseSubsiteSheaf.subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite` (in the
namespace `Stacks.Cohomology`).

## References

* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)
open Stacks.EtaleCohomology.OpensAcyclicity
  (subsingleton_opensCohomology_of_subsingleton_H_smallEtale)
open Stacks.Cohomology.DenseSubsiteSheaf
  (subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite)

universe u

namespace AlgebraicGeometry.Scheme

/-- The property of an open `W` of `X` driving the induction: a uniform bound above which the
cohomology over `W` of every torsion abelian sheaf on `X_étale` vanishes. -/
abbrev HasOpensCohomologyBound (X : Scheme.{u}) (W : X.Opens) : Prop :=
  ∃ d : ℕ, ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F → ∀ n : ℕ, d < n →
      Subsingleton ((opensCohomology
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict X).obj F) n).obj (op W))

/-- The restriction of a torsion abelian sheaf to an open subscheme is torsion. -/
theorem torsionSheafProperty_smallEtaleOpensRestrict (X : Scheme.{u}) (W : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty W.toScheme.smallEtaleTopology
      ((Stacks.EtaleCohomology.OpensAcyclicity.smallEtaleOpensRestrict X W).obj F) :=
  Stacks.Torsion.torsionSheafProperty_sheafPushforwardContinuous _ F hF

/-- An affine open of finite cohomological dimension has a uniform cohomology bound. -/
theorem hasOpensCohomologyBound_of_isAffineOpen (X : Scheme.{u}) (V : X.Opens)
    (hV : IsAffineOpen V)
    (hcd : haveI : IsAffine V.toScheme := hV; etaleCohomologicalDimension V.toScheme < ⊤) :
    HasOpensCohomologyBound X V := by
  have : IsAffine V.toScheme := hV
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hcd.ne
  refine ⟨d, fun F hF n hn => subsingleton_opensCohomology_of_subsingleton_H_smallEtale X V F n ?_⟩
  exact isEtaleCohomologyBound_etaleCohomologicalDimension V.toScheme _
    (torsionSheafProperty_smallEtaleOpensRestrict X V F hF) n (by rw [← hd]; exact_mod_cast hn)

/-- **The Mayer--Vietoris step.** Bounds over `U`, `V` and `U ⊓ V` give a bound over
`U ⊔ V`. -/
theorem hasOpensCohomologyBound_sup (X : Scheme.{u}) (U V : X.Opens)
    (hU : HasOpensCohomologyBound X U) (hV : HasOpensCohomologyBound X V)
    (hUV : HasOpensCohomologyBound X (U ⊓ V)) :
    HasOpensCohomologyBound X (U ⊔ V) := by
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  obtain ⟨c, hc⟩ := hUV
  refine ⟨max (max a b) c + 1, fun F hF n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_of_subsingleton _ U V
    m (m + 1) rfl (hc F hF m (by omega)) (ha F hF _ (by omega)) (hb F hF _ (by omega))

/-- **Uniform vanishing over the quasi-compact opens.** On a quasi-separated scheme all of
whose affine opens have finite cohomological dimension, every quasi-compact open `W` carries a
uniform bound above which the cohomology over `W` of every torsion abelian sheaf vanishes. This
is the induction principle of [Stacks, Tag 08DR] with the Mayer--Vietoris step. -/
theorem exists_bound_opensCohomology_of_isAffineOpen (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (h : ∀ V : X.Opens, ∀ hV : IsAffineOpen V,
      haveI : IsAffine V.toScheme := hV; etaleCohomologicalDimension V.toScheme < ⊤)
    (W : X.Opens) (hW : IsCompact (W : Set X)) :
    HasOpensCohomologyBound X W :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (HasOpensCohomologyBound X)
    (fun V hV => hasOpensCohomologyBound_of_isAffineOpen X V hV (h V hV))
    (fun U V _ _ => hasOpensCohomologyBound_sup X U V) W hW

/-- **Finite cohomological dimension from the affine opens** (the reduction step of
[Stacks, Tag 0F10], part (2)). A quasi-compact quasi-separated scheme all of whose affine opens
have finite cohomological dimension has finite cohomological dimension. -/
theorem etaleCohomologicalDimension_lt_top_of_isAffineOpen (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (h : ∀ V : X.Opens, ∀ hV : IsAffineOpen V,
      haveI : IsAffine V.toScheme := hV; etaleCohomologicalDimension V.toScheme < ⊤) :
    etaleCohomologicalDimension X < ⊤ := by
  obtain ⟨d, hd⟩ := exists_bound_opensCohomology_of_isAffineOpen X h ⊤
    (by simpa using isCompact_univ (X := X))
  refine (etaleCohomologicalDimension_le X d fun F hF n hn => ?_).trans_lt (ENat.natCast_lt_top d)
  have := hd F hF n (by exact_mod_cast hn)
  let G := (Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict X).obj F
  exact subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite
    (Stacks.EtaleCohomology.MayerVietoris.topology X) X.smallEtaleTopology
    (AsSmall.down : Stacks.EtaleCohomology.MayerVietoris.Site X ⥤ X.Etale)
    (Stacks.EtaleCohomology.MayerVietoris.selfIsTerminal X)
    (Stacks.EtaleCohomology.MayerVietoris.isTerminalAsSmallDownSelf X) F n
    (AddCommGrpCat.subsingleton_of_isZero
      (Limits.IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton
        (G := G.H' n ((Stacks.EtaleCohomology.MayerVietoris.opensToSite X).obj ⊤)))
        (Stacks.EtaleCohomology.MayerVietoris.cohomologyTopIsoH X G n).symm))

end AlgebraicGeometry.Scheme

end
