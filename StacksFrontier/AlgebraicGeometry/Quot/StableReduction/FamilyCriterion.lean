module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.EtaleGenus
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.FieldExtensionFibre
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.FirstDirectImageRank
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres

/-!
# A fibrewise criterion for a morphism of schemes to be a stable family of genus `g`

Let `p : Y ⟶ S` be a proper, flat morphism of finite presentation of schemes which is
at-worst-nodal of relative dimension one, with `S` reduced and locally Noetherian. If for every
point `s ∈ S` the fibre `Y_s` over `κ(s)` has `H⁰(Y_s, 𝒪) = κ(s)`, genus `g ≥ 2`, no rational
tails and no rational bridges, then `p` is a stable family of curves of genus `g` (Stacks 0E75,
0E78).

## Main definitions

* `AlgebraicGeometry.IsStableFibreOfGenus`: the fibre condition at a point of the base.

## Main results

* `AlgebraicGeometry.isStableFamilyOfSchemesOfGenus_of_forall_isStableFibreOfGenus`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The fibre of `p : Y ⟶ S` over `s ∈ S` is a stable curve of genus `g` over `κ(s)`: its global
functions are `κ(s)`, its genus is `g`, it has genus at least two and neither a rational tail nor
a rational bridge. -/
abbrev IsStableFibreOfGenus (g : ℕ) {Y S : Scheme.{u}} (p : Y ⟶ S) (s : S) : Prop :=
  IsIso ((Scheme.ΓSpecIso (S.residueField s)).inv ≫ (p.fiberToSpecResidueField s).appTop) ∧
    HasGenusTwoNoRationalTailNoRationalBridge (S.residueField s) (p.fiberToSpecResidueField s) ∧
    genus (p.fiberToSpecResidueField s) = g

/-- **A fibrewise criterion for stable families of genus `g`.** A proper flat morphism of finite
presentation `p : Y ⟶ S`, at-worst-nodal of relative dimension one, onto a reduced locally
Noetherian scheme `S` of the site, all of whose fibres are stable curves of genus `g`, is a stable
family of curves of genus `g`. -/
theorem isStableFamilyOfSchemesOfGenus_of_forall_isStableFibreOfGenus (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) {Y S : Scheme.{u}} (p : Y ⟶ S) (hS : B.Contains S)
    [IsReduced S] [IsLocallyNoetherian S] [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (hnodal : IsAtWorstNodalOfRelativeDimensionOne p) (g : ℕ)
    (hfib : ∀ s : S, IsStableFibreOfGenus g p s) :
    IsStableFamilyOfSchemesOfGenus B hZ g p hS := by
  -- the fibres are geometrically connected (Stacks 0FD1 at a fibre)
  have hgc : GeometricallyConnected p :=
    ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun s =>
      have := (hfib s).1
      have : IsIso (p.fiberToSpecResidueField s).appTop :=
        IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (S.residueField s)).inv _
      (Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_isIso_appTop p s
        inferInstance).geometrically_connectedSpace⟩
  -- (a) the fibres have dimension one
  have hdim : ∀ y, topologicalKrullDimAt (p.fiber (p y)) (p.asFiber y) ≤ 1 := fun y => by
    rw [hnodal.1.2 y]
    rfl
  have hY := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS
  refine ⟨‹Flat p›, ‹IsProper p›, ‹LocallyOfFinitePresentation p›, hdim, ?_⟩
  refine ⟨⟨⟨?_, ?_⟩, fun pt => ?_⟩, ?_⟩
  · -- (b) nodality on every étale chart
    exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
      (integerSiteMap B hZ hY hS p)).2 hnodal
  · -- (c) universally bijective global functions (Stacks 0E0L)
    open Stacks.AlgebraicGeometry.NodalFamilyCohomology in
    exact CurveFamily.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfFiberDimensionLE B hZ
      (integerSiteMap B hZ hY hS p) _ _ _ _ fun hsq =>
        (isIso_c_and_isIso_c_of_isPullback_of_isAtWorstNodal p hnodal).2 hsq
  · -- (d) the fibre conditions at a field-valued point
    obtain ⟨V, v, q, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ _ pt
    have hsq' := AlgebraicSpaces.isPullback_hom B integerBase hZ hsq
    refine ⟨V, v, q.hom, hsq', ?_⟩
    obtain ⟨q', hq'⟩ : ∃ q' : V ⟶ integerSiteObject B hZ hY, yoneda.map q' = q.hom :=
      ⟨Yoneda.fullyFaithful.preimage q.hom, Yoneda.fullyFaithful.map_preimage _⟩
    rw [← hq'] at hsq'
    have hw : q' ≫ integerSiteMap B hZ hY hS p = v ≫ pt.value :=
      yoneda.map_injective ((yoneda.map_comp _ _).trans
        (hsq'.w.trans (yoneda.map_comp _ _).symm))
    have hS' := (IsPullback.of_map yoneda hw hsq').map (BigFppfOver.toScheme B integerBase hZ)
    exact hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback p hnodal
      (fun s => ⟨(hfib s).1, (hfib s).2.1⟩) pt.carrier _ hS'
  · -- (e) the genus: `R¹p_*𝒪_Y` is locally free of rank `g`
    open Stacks.AlgebraicGeometry.NodalFamilyCohomology in
    exact CurveFamily.hasGenus_curveFamilyOfFiberDimensionLE B hZ
      (integerSiteMap B hZ hY hS p) _ _ _ _ g
      (isFiniteLocallyFreeOfRank_rightDerived_one_of_forall_genus p hnodal g fun s => (hfib s).2.2)

end AlgebraicGeometry

end
