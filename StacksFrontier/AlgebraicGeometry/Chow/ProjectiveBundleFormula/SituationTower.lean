module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback

/-!
# The projective bundle of the relative-`Proj` situation model is a locally projective tower

The projective bundle `𝐏(ℰ) = Proj_X(Sym ℰ)` of a quasi-coherent module is constructed twice in
this library: as `Stacks.RelativeProj.projectiveBundle` (the relative `Proj` of the situation
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent`, with the twisting sheaves
`Stacks.RelativeProj.Situation.twistSheaf`), and as `Stacks.Chow.bundle` (the relative `Proj` of
`Stacks.SymGraded.schemeSheafGradedAlgebra`, with the twist
`Stacks.ProjectiveBundleSplitting.tautologicalTwist`), on which the projective space bundle formula
of Stacks 02TW / 02TX is proved. The two are compared over the base by
`Stacks.ProjectiveBundle.presentationIso`.

This file carries the structure the projective space bundle formula runs on — a projective tower
locally on the base (`Stacks.Chow.IsLocallyProjectiveTower`) — from the second presentation to the
first, **together with the twist**: for `ℰ` finite locally free of rank `n + 1`,
`(projectiveBundleToBase X ℰ, 𝒪(1))` is a projective tower of fibre dimension `n` locally on `X`,
with `𝒪(1)` the twisting sheaf of the situation model.

## The route

Being a locally projective tower is local on the base, so no global comparison of the two twists
is needed: over the chart of an affine open `U` of `X`, both twists are the absolute twist
`𝒪(1)` of `Proj Γ(U, Sym ℰ)` — the situation twist by its chart identification
`Stacks.RelativeProj.Situation.twistSheafChartIso`, the tautological twist by the chart
identification of its twist datum of Tag 01NR — and the two graded rings of sections are identified
by the graded isomorphism the presentation comparison is built from, along which the twist
comparison of Tag 01MY is an isomorphism
(`Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id`).

## Main results

* `Stacks.Chow.isLocallyProjectiveTower_of_isPullback_cover`: being a locally projective tower can
  be checked on the pullbacks to an open cover of the base.
* `Stacks.ProjectiveBundle.presentationChartTwistIso`: the chart-local comparison of the two
  twists.
* `Stacks.ProjectiveBundle.isLocallyProjectiveTower_projectiveBundle`: **the situation model of
  the projective bundle of a module of rank `n + 1`, with its `𝒪(1)`, is a projective tower of
  fibre dimension `n` locally on the base.**

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Being a locally projective tower can be checked on an open cover of the base**, given as a
family of cartesian squares over open immersions: if every point of `Y` lies in the image of an
open immersion `ι : V ⟶ Y` over which `π` pulls back to a locally projective tower `q` with the
pulled-back module, then `π` is a locally projective tower. -/
theorem isLocallyProjectiveTower_of_isPullback_cover {n : ℕ} {P Y : Scheme.{u}} {π : P ⟶ Y}
    {L : P.Modules}
    (h : ∀ y : Y, ∃ (V Q : Scheme.{u}) (ι : V ⟶ Y) (_ : IsOpenImmersion ι)
      (_ : y ∈ Set.range ι.base) (q : Q ⟶ V) (c : Q ⟶ P) (_ : IsPullback c q π ι),
      IsLocallyProjectiveTower n q ((Scheme.Modules.pullback c).obj L)) :
    IsLocallyProjectiveTower n π L := by
  intro y
  obtain ⟨V, Q, ι, hι, ⟨v, rfl⟩, q, c, hsq, htw⟩ := h y
  obtain ⟨W', hvW', hW'⟩ := htw v
  refine ⟨ι ''ᵁ W', ⟨v, hvW', rfl⟩, ?_⟩
  have hright : IsPullback ((q ⁻¹ᵁ W').ι ≫ c) (q ∣_ W') π (W'.ι ≫ ι) :=
    (isPullback_morphismRestrict q W').flip.paste_horiz hsq
  have hW := (isPullback_morphismRestrict π (ι ''ᵁ W')).flip
  have hg : (ι.isoImage W').inv ≫ W'.ι ≫ ι = (ι ''ᵁ W').ι := ι.isoImage_inv_ι W'
  let g' := hright.lift (π ⁻¹ᵁ (ι ''ᵁ W')).ι ((π ∣_ (ι ''ᵁ W')) ≫ (ι.isoImage W').inv)
    (by rw [Category.assoc, hg]; exact hW.w)
  have hg'₁ : g' ≫ (q ⁻¹ᵁ W').ι ≫ c = (π ⁻¹ᵁ (ι ''ᵁ W')).ι := hright.lift_fst _ _ _
  have hg'₂ : g' ≫ (q ∣_ W') = (π ∣_ (ι ''ᵁ W')) ≫ (ι.isoImage W').inv := hright.lift_snd _ _ _
  have hleft : IsPullback g' (π ∣_ (ι ''ᵁ W')) (q ∣_ W') (ι.isoImage W').inv := by
    refine IsPullback.of_right ?_ hg'₂ hright
    rw [hg'₁, hg]
    exact hW
  refine hW'.of_isPullback hleft ?_
  exact (Scheme.Modules.pullbackCongr hg'₁.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp g' ((q ⁻¹ᵁ W').ι ≫ c)).app L).symm ≪≫
    (Scheme.Modules.pullback g').mapIso
      (((Scheme.Modules.pullbackComp (q ⁻¹ᵁ W').ι c).app L).symm)

end Stacks.Chow

namespace Stacks.ProjectiveBundle

open Stacks.SymGraded Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.AlgebraicGeometry.RelativeProjGlue (relativeProj relativeProjToBase chart)
open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- **The degree-one twist of a twist datum, pulled back along a morphism factoring through a
chart by `Proj` of an invertible graded ring homomorphism, is the absolute twist.** Generic in
the graded algebra, the twist datum and the graded ring. -/
def pullbackTwistOfChartFactor {S : Scheme.{u}}
    {A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra S}
    (D : Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData A) (U : S.Opens)
    (hU : IsAffineOpen U) {R : Type u} {σ : Type u} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒮 : ℕ → σ} [GradedRing 𝒮] (φ : A.grading U →+*ᵍ 𝒮)
    (hφ : HomogeneousIdeal.irrelevant 𝒮 ≤ (HomogeneousIdeal.irrelevant (A.grading U)).map φ)
    [hiso : IsIso (Stacks.ProjTwistComparison.twistMap φ hφ 1)]
    {f : AlgebraicGeometry.Proj 𝒮 ⟶ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).scheme}
    (hf : f = AlgebraicGeometry.Proj.map φ hφ ≫
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart U hU) :
    (Scheme.Modules.pullback f).obj (D.algebra.piece 1) ≅ twistingSheaf 𝒮 1 :=
  letI := D.chartData.chart_isOpenImmersion U hU
  Scheme.Modules.pullbackIsoOfRestrictIso _ (D.chartData.chartIso U hU 1) _ hf ≪≫
    asIso (Stacks.ProjTwistComparison.twistMap φ hφ 1)

/-- The chart identification of the twisting sheaf of a situation, in inverse-image form. -/
def situationChartTwistIso (s : Stacks.RelativeProj.Situation.{u}) (W : s.base.affineOpens)
    (n : ℤ) :
    (Scheme.Modules.pullback (Stacks.RelativeProj.Situation.relativeProjChart s W)).obj
        (Stacks.RelativeProj.Situation.twistSheaf s n) ≅
      twistingSheaf (s.sectionRingGrading W.1) n :=
  Stacks.RelativeProj.Situation.twistSheafPullbackChartIso s n W (𝟙 _) (Category.id_comp _).symm ≪≫
    (Scheme.Modules.pullbackId _).app _

/-- The twist comparison along the comparison of the two graded rings of sections is an
isomorphism. -/
instance isIso_twistMap_situationGradedHom (U : X.AffineZariskiSite) :
    IsIso (Stacks.ProjTwistComparison.twistMap (situationGradedHom E hqc U.toOpens)
      (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc U)) 1) :=
  Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id _ _ 1
    (presentationInv E hqc U) (presentation_hmn E hqc U) (presentation_hnm E hqc U)

/-- **The two twists `𝒪(1)` of the projective bundle agree on each chart.** Over the chart of an
affine open `U` of the base of the situation model `Stacks.RelativeProj.projectiveBundle X E`,
the pullback of its twisting sheaf `𝒪(1)` is the pullback of the tautological twist of
`Stacks.Chow.bundle` along the chart followed by the inverse comparison of presentations: both are
the absolute twist `𝒪(1)` of `Proj Γ(U, Sym E)`, read through the graded isomorphism of the two
rings of sections. -/
def presentationChartTwistIso (U : X.AffineZariskiSite) :
    (Scheme.Modules.pullback (Stacks.RelativeProj.Situation.relativeProjChart (symSituation E)
        (siteAffineOpen U) ≫ (presentationIso E hqc).inv)).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
    (Scheme.Modules.pullback (Stacks.RelativeProj.Situation.relativeProjChart (symSituation E)
        (siteAffineOpen U))).obj
      (Stacks.RelativeProj.Situation.twistSheaf (symSituation E) 1) :=
  pullbackTwistOfChartFactor (projectiveBundleTwistData E hqc) U.toOpens U.2
      (situationGradedHom E hqc U.toOpens)
      (Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (presentation_hmn E hqc U))
      (hiso := isIso_twistMap_situationGradedHom E hqc U)
      (relativeProjChart_presentationIso_inv E hqc U) ≪≫
    (situationChartTwistIso (symSituation E) (siteAffineOpen U) 1).symm

/-- **The situation model of the projective bundle of a module of rank `n + 1`, with its twisting
sheaf `𝒪(1)`, is a projective tower of fibre dimension `n` locally on the base.** Over the chart
of each affine open of the base it is, by the comparison of presentations
`Stacks.ProjectiveBundle.presentationIso` and the chart comparison of the twists
`Stacks.ProjectiveBundle.presentationChartTwistIso`, the restriction of `Stacks.Chow.bundle` with
`Stacks.Chow.bundleTwist`, which is one (`Stacks.Chow.isLocallyProjectiveTower_bundle`). -/
theorem isLocallyProjectiveTower_projectiveBundle (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    Stacks.Chow.IsLocallyProjectiveTower n (Stacks.RelativeProj.projectiveBundleToBase X E)
      (Stacks.RelativeProj.Situation.twistSheaf
        (Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E) 1) := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  have hqc := Stacks.Chow.bundlePieces E
  have htb := Stacks.Chow.isLocallyProjectiveTower_bundle E n
  refine Stacks.Chow.isLocallyProjectiveTower_of_isPullback_cover fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let Uz : X.AffineZariskiSite := ⟨U, hU⟩
  have hsq := Stacks.RelativeProj.Situation.relativeProjChart_isPullback (symSituation E)
    (siteAffineOpen Uz)
  refine ⟨U.toScheme, _, U.ι, inferInstance, by simpa using hxU, _, _, hsq, ?_⟩
  have hbase : (presentationIso E hqc).inv ≫
      relativeProjToBase (situationSheafGradedAlgebra E hqc).toGradedAlgebra =
        Stacks.RelativeProj.projectiveBundleToBase X E := by
    rw [← presentationIso_hom_toBase E hqc, Iso.inv_hom_id_assoc]
  have hsq' : IsPullback
      (Stacks.RelativeProj.Situation.relativeProjChart (symSituation E) (siteAffineOpen Uz) ≫
        (presentationIso E hqc).inv)
      (Stacks.RelativeProj.Situation.projInclusionToOpen (symSituation E) Uz.toOpens Uz.2)
      (Stacks.Chow.bundleProj E) U.ι :=
    hsq.of_iso (Iso.refl _) (presentationIso E hqc).symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; exact hbase.symm)
      (by simp; rfl)
  exact htb.of_isPullback hsq' (presentationChartTwistIso E hqc Uz).symm

end Stacks.ProjectiveBundle

end
