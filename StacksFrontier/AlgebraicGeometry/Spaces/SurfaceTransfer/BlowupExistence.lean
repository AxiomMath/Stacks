module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupLocallyFiniteIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction

/-!
# Blowing up a locally Noetherian algebraic space

Let `S` be a scheme and let `X` be an algebraic space over `S` which is locally Noetherian, in
the sense that its étale scheme charts are locally Noetherian schemes. This file constructs the
blowing up of `X` in an arbitrary closed subspace `Z`.

The blowup of Stacks 085Q, `AlgebraicGeometry.Space.blowUpAlong'`, is glued from the relative
`Proj` of the Rees algebra of `ℐ_Z` on the presenting scheme `U`, on the relation scheme `R` and on
`R ×_U R` of an étale presentation, and it carries the set-theoretic side conditions that these
three relative `Proj`s be objects of the big fppf site. On a locally Noetherian scheme every
sheaf of ideals is of finite type, so the blowup of the scheme is proper over it, in particular of
finite type and quasi-compact; a scheme of finite type and quasi-compact over an object of the
site is an object of the site. Hence all three side conditions hold, and the universal property
of Stacks 085U then exhibits `blowUpAlong'` as the blowing up of `X` in `Z`.

## Main results

* `AlgebraicGeometry.Space.contains_relativeProj_reesSituation_of_isLocallyNoetherian`: the
  relative `Proj` of the Rees algebra of a sheaf of ideals on a locally Noetherian scheme of the
  site is a scheme of the site.
* `AlgebraicGeometry.Space.exists_isBlowupAlong_of_isLocallyNoetherian`: a locally Noetherian
  algebraic space has a blowing up in every closed subspace, and that blowing up inherits
  condition (2) of Stacks 0BB1 from the space.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The relative `Proj` of a Rees algebra on a locally Noetherian scheme of the site is a scheme
of the site.** Every sheaf of ideals of a locally Noetherian scheme is of finite type, so the
blowup is proper over the base, and a scheme of finite type and quasi-compact over an object of
the site is an object of the site. -/
theorem contains_relativeProj_reesSituation_of_isLocallyNoetherian (V : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData) :
    B.Contains (Stacks.Blowup.reesSituation I).relativeProj := by
  have hfg : ∀ U : ((BigFppfOver.toScheme B S hS).obj V).affineOpens, (I.ideal U).FG := by
    intro U
    have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, U.1) :=
      IsLocallyNoetherian.component_noetherian U
    exact IsNoetherian.noetherian _
  have : AlgebraicGeometry.IsProper (AlgebraicGeometry.blowUpToBase I) :=
    isProper_blowUpToBase_of_fg I hfg
  have hp : AlgebraicGeometry.IsProper (Stacks.Blowup.reesSituation I).relativeProjToBase := by
    rw [← Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase]
    exact MorphismProperty.comp_mem _ _ _ inferInstance ‹_›
  let ν : (Stacks.Blowup.reesSituation I).relativeProj ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    (Stacks.Blowup.reesSituation I).relativeProjToBase
  have : AlgebraicGeometry.IsProper ν := hp
  exact contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := V) ν

/-- An étale scheme chart of a locally Noetherian algebraic space is a locally Noetherian
scheme. -/
theorem isLocallyNoetherian_of_etale_chart {X : AlgebraicSpaces B S hS}
    (hX : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (A : SmallEtale B S hS X.obj) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A.1.left) :=
  (exists_atlas_iff_forall_etale B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T)
    X.property).mp hX A.1.left A.1.hom A.2

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The three side conditions of the construction of Stacks 085Q hold on a locally Noetherian
algebraic space, for any closed subspace and any presentation. -/
theorem contains_reesSituations_of_isLocallyNoetherian {X : AlgebraicSpaces B S hS}
    (hX : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj ∧
      B.Contains (reesRelationSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj ∧
      B.Contains (reesDoubleSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj := by
  have key (A : SmallEtale B S hS X.obj) :=
    have := isLocallyNoetherian_of_etale_chart hX A
    contains_relativeProj_reesSituation_of_isLocallyNoetherian A.1.left
  exact ⟨key (presentationChart P) _, key (presentationRelationChart P) _,
    key (presentationDoubleChart P) _⟩

/-- **A locally Noetherian algebraic space has a blowing up in every closed subspace**, and the
blowing up satisfies condition (2) of Stacks 0BB1 when the space does. It is the construction of
Stacks 085Q, whose side conditions hold by
`AlgebraicGeometry.Space.contains_reesSituations_of_isLocallyNoetherian`. -/
theorem exists_isBlowupAlong_of_isLocallyNoetherian {X : AlgebraicSpaces B S hS}
    (hX : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z : ClosedSubspaces B S hS X.obj) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsBlowupAlong B S hS Z b ∧
      (HasLocallyFiniteIrreducibleComponents B S hS X.obj →
        HasLocallyFiniteIrreducibleComponents B S hS X'.obj) := by
  let P := presentationOfIsAlgebraicSpace B S hS X.obj X.property
  obtain ⟨hcU, hcR, hcRR⟩ := contains_reesSituations_of_isLocallyNoetherian hX Z P
  have hb := isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR
  exact ⟨_, _, hb,
    hasLocallyFiniteIrreducibleComponents_of_isBlowupAlong_of_presentation B S hS Z P
      hcU hcR hcRR hb⟩

end AlgebraicGeometry.Space

end
