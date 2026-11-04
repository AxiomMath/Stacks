module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementClauses
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.NoetherianDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionStep
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackChartPostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# Shrinking the source to a quasi-compact open neighbourhood of a proper support

Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` a morphism locally of finite type and
quasi-separated, and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules, flat over `Y`, whose
support is contained in a closed subset `Z` of `|X|` proper over `Y`.  The first sentence of the
proof of Stacks 08JR is: "We may replace `X` by a quasi-compact open neighbourhood of the union of
the supports of the `𝒢^i`.  Hence we may assume `X` is Noetherian."  This file provides that
reduction.

* `Z` is compact, so it lies in a quasi-compact open subspace `j : X' ⟶ X`, and
  `(X ∖ Z, X' ⟶ X)` is an elementary distinguished square.
* `X'` is Noetherian, and `j ≫ f` is locally of finite type, quasi-compact and quasi-separated.
* An object `E ∈ D^-_{Coh}(𝒪_X)` restricts to an object of `D^-_{Coh}(𝒪_{X'})`, which is then
  pseudo-coherent (Stacks 08IK).
* For an object `M` of `D(𝒪_X)` supported on `Z`, restriction to `X'` is bijective on
  `Ext^i(E, M) ⟶ Ext^i(E|_{X'}, M|_{X'})` (Stacks 08GG through the Mayer–Vietoris sequence of the
  square, `AlgebraicGeometry.Space.bijective_map_edsEtale_of_isZero_target`).

## Main results

* `AlgebraicGeometry.Space.exists_isElementaryDistinguishedSquare_of_flatProperSupportComplex`.
* `AlgebraicGeometry.Space.isNoetherian_edsEtale_of_isQuasiCompactSpace`.
* `AlgebraicGeometry.Space.isPseudoCoherent_edsEtaleRestrict_of_isCoherent_homology`.
* `AlgebraicGeometry.Space.bijective_edsEtaleRestrict_shiftedHom_of_cohomologySupportedOn`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The quasi-compact open neighbourhood -/

section Neighbourhood

variable {X Y : AlgebraicSpaces B S hS}

/-- **A quasi-compact open neighbourhood of the support of `𝒢^•`.**  The closed set `Z` proper
over `Y` containing the supports of the terms of `𝒢^•` is compact (`Y` is quasi-compact), hence
lies in a quasi-compact open subspace `V`; with the open complement of `Z` it forms an elementary
distinguished square, whose closed complement is `Z`. -/
theorem exists_isElementaryDistinguishedSquare_of_flatProperSupportComplex
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    ∃ (Z : Set (points B S hS X.1)) (hZ : IsClosed Z) (V : Subfunctor X.1)
      (_hsq : IsElementaryDistinguishedSquare B S hS X.2
        (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι),
      IsProperOver B S hS X.2 Y.2 f.hom hf Z hZ ∧
      (∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z) ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
      edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ) = Z ∧
      Z ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  obtain ⟨Z, hZcl, hZp, hGZ⟩ := hG.properSupport
  have hZc : IsCompact Z := isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf Z hZcl hZp
  obtain ⟨V, hV, hVqc, hZV⟩ := exists_isQuasiCompactSpace_openSubspace_of_isCompact B S hS X.2 Z hZc
  refine ⟨Z, hZcl, V,
    isElementaryDistinguishedSquare_openSubspaceOfPoints B S hS X.2 Z hZcl V hV hZV, hZp, hGZ,
    hVqc, ?_, hZV⟩
  rw [edsComplementPoints, range_pointsMap_ι_openSubspaceOfPoints, compl_compl]

end Neighbourhood

/-! ### Coherence along an étale morphism -/

/-- **Coherence is preserved by restriction along an étale morphism into a locally Noetherian
algebraic space**: quasi-coherence and finite type are (Stacks 03DO), and on a locally Noetherian
algebraic space a module is coherent if and only if it is quasi-coherent of finite type
(Stacks 07UB). -/
theorem isCoherent_etaleModulePullback_of_hasEtaleLocalProperty {X Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) :
    IsCoherent B S hS Y.1 Y.2 ((etaleModulePullback.{u, u} B S hS g hg).obj M) := by
  have := Fact.mk hY
  have hft := isFiniteType_etaleModulePullback B S hS g hg M
    (SheafOfModules.isFiniteType_of_presheaf_isFiniteType M hM.toIsCoherentOnSite.isFiniteType)
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS Y.1 Y.2 _).2
    ⟨isQuasicoherentOnSite_etaleModulePullback B S hS g hg M hM.toIsQuasicoherentOnSite,
      Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ hft)⟩

/-! ### Flatness along an étale morphism -/

/-- **Flatness over the base is preserved by restriction along an étale morphism of the source.**
If `M` on `X` is flat over `Y` along `f`, then `j^*M` on `X'` is flat over `Y` along `j ≫ f`, for
`j : X' ⟶ X` étale: a chart diagram of `j ≫ f` is a chart diagram of `f` once its chart of `X'` is
postcomposed with `j` (`AlgebraicGeometry.Space.ChartDiagram.postcompSource`), and the restriction
of `j^*M` to a chart of `X'` is the restriction of `M` to the postcomposed chart
(`AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_postcomp`). -/
theorem isFlatOver_etaleModulePullback_comp {X X' Y : AlgebraicSpaces B S hS} (j : X' ⟶ X)
    (hj : IsEtale B S hS j.hom) (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : IsFlatOver B S hS X.2 f.hom M) :
    IsFlatOver B S hS X'.2 (j ≫ f).hom ((etaleModulePullback.{u, u} B S hS j hj).obj M) := by
  intro d
  have h := hM (ChartDiagram.postcompSource B S hS j f hj (j ≫ f) rfl d)
  change AlgebraicGeometry.IsFlatOver _ (restrictToChart B S hS X'.2 _ d.U)
  rw [restrictToChart_etaleModulePullback_postcomp B S hS j hj M d.U]
  exact h

/-! ### The restricted morphism and the restricted space -/

section Square

variable {X Y : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor X.1} {fV : V ⟶ X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo fV)

/-- The composite of the étale morphism of an elementary distinguished square with a morphism
locally of finite type is locally of finite type (Stacks 06LT, 03XG). -/
theorem isLocallyOfFiniteType_edsEtaleHom_comp (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsLocallyOfFiniteType B S hS (edsEtaleHom B S hS hsq ≫ f).hom :=
  isLocallyOfFiniteType_comp' B S hS (edsEtaleHom B S hS hsq).hom f.hom X.2 Y.2
    (isLocallyOfFiniteType_of_isEtale' B S hS _ (isEtale_edsEtaleHom B S hS hsq)) hf

/-- If the étale morphism of an elementary distinguished square is a monomorphism (the inclusion
of an open subspace), its composite with a quasi-separated morphism is quasi-separated
(Stacks 042N, 03KK, 04ZH). -/
theorem isQuasiSeparated_edsEtaleHom_comp [Mono fV] (f : X ⟶ Y)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom :=
  isQuasiSeparated_comp B S hS hsq.isAlgebraicSpace X.2 (edsEtaleHom B S hS hsq).hom f.hom
    (isQuasiSeparated_of_mono B S hS (edsEtaleHom B S hS hsq).hom (inferInstanceAs (Mono fV)))
    hfqs

/-- **The quasi-compact open neighbourhood is Noetherian.**  It is quasi-compact by hypothesis;
it is quasi-separated, being quasi-separated over the quasi-separated `Y` (Stacks 04ZH); and it is
locally Noetherian, being locally of finite type over the locally Noetherian `Y` (Stacks 04ZK). -/
theorem isNoetherian_edsEtale_of_isQuasiCompactSpace [Mono fV]
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
    (hVqc : IsQuasiCompactSpace B S hS V) :
    IsNoetherian B S hS hTop (edsEtale B S hS hsq).1 :=
  ⟨hVqc,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hTop hsq.isAlgebraicSpace hY.2.1
      (isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hsq.isAlgebraicSpace Y.2 _
      (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf) hY.2.2⟩

/-- **Properness over the base of the inverse image of the closed complement.**  Let `T` be the
closed complement of the open subspace of the square and suppose `T` is proper over `Y` along `f`.
If the étale morphism `j : X' ⟶ X` of the square is a monomorphism, then `j⁻¹(T)` is proper over
`Y` along `j ≫ f`.  The inverse image `Q = j⁻¹(T_red)` of the reduced closed subspace is
isomorphic to `T_red` by the defining property of the square, so `Q ⟶ X' ⟶ X ⟶ Y` is proper; the
reduced closed subspace of `X'` on `j⁻¹(T)` factors through `Q`. -/
theorem isProperOver_preimage_edsComplementPoints [Mono fV] (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hT : IsProperOver B S hS X.2 Y.2 f.hom hf (edsComplementPoints B S hS Uo)
      hsq.isClosedComplement) :
    IsProperOver B S hS (edsEtale B S hS hsq).2 Y.2 (edsEtaleHom B S hS hsq ≫ f).hom
      (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
      (pointsMap B S hS V fV ⁻¹' edsComplementPoints B S hS Uo)
      (isClosed_preimage_pointsMap B S hS hsq.isAlgebraicSpace X.2 fV
        hsq.isClosedComplement) := by
  set D := reducedClosedSubspace B S hS X.1 X.2 _ hsq.isClosedComplement with hD
  have hDcl : IsClosedSubspace B S hS D :=
    isClosedSubspace_reducedClosedSubspace' B S hS X.2 _ hsq.isClosedComplement
  set Q := D.preimage fV with hQ
  have hsqQ : D.fromPreimage fV ≫ D.ι = Q.ι ≫ fV := (Subfunctor.isPullback_preimage fV D).w
  have hQalg : IsAlgebraicSpace B S hS Q.toFunctor :=
    isAlgebraicSpace_of_isPullback hDcl.1 hsq.isAlgebraicSpace X.2.isSheaf
      X.2.diagonal_representable (Subfunctor.isPullback_preimage fV D)
  have hiso : IsIso (D.fromPreimage fV) := hsq.isIsoOverComplement
  have hQproper : IsProper B S hS (Q.ι ≫ (edsEtaleHom B S hS hsq ≫ f).hom) := by
    change IsProper B S hS (Q.ι ≫ fV ≫ f.hom)
    rw [← Category.assoc, ← hsqQ, Category.assoc]
    exact isProper_comp B S hS hQalg hDcl.1 Y.2 _ _ (isProper_of_isIso B S hS _) hT
  have hcl' := isClosed_preimage_pointsMap B S hS hsq.isAlgebraicSpace X.2 fV
    hsq.isClosedComplement
  have hRalg : IsAlgebraicSpace B S hS
      (reducedClosedSubspace B S hS V hsq.isAlgebraicSpace _ hcl').toFunctor :=
    isAlgebraicSpace_reducedClosedSubspace B S hS V hsq.isAlgebraicSpace _ hcl'
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS X.2 hRalg D hDcl
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS V hsq.isAlgebraicSpace _ hcl')
    ((reducedClosedSubspace B S hS V hsq.isAlgebraicSpace _ hcl').ι ≫ fV)).2 (by
      rintro _ ⟨r, rfl⟩
      rw [hD, range_pointsMap_ι_reducedClosedSubspace, pointsMap_comp]
      have hr := Set.mem_range_self (f := pointsMap B S hS _
        (reducedClosedSubspace B S hS V hsq.isAlgebraicSpace _ hcl').ι) r
      rwa [range_pointsMap_ι_reducedClosedSubspace] at hr)
  refine isProperOver_of_isProper_ι_comp B S hS (edsEtale B S hS hsq).2 Y.2 _ _ _ hcl' Q hQalg
    hQproper (g ≫ inv (D.fromPreimage fV) (I := hiso)) ?_
  have : Mono (edsEtaleHom B S hS hsq).hom := inferInstanceAs (Mono fV)
  apply (cancel_mono (edsEtaleHom B S hS hsq).hom).1
  change (g ≫ inv (D.fromPreimage fV) (I := hiso)) ≫ Q.ι ≫ fV = _ ≫ fV
  rw [← hsqQ]
  change g ≫ inv (D.fromPreimage fV) (I := hiso) ≫ D.fromPreimage fV ≫ D.ι = _
  rw [IsIso.inv_hom_id_assoc, hg]
  rfl

/-- **The hypotheses of Stacks 0DKJ survive the restriction to the neighbourhood.**  If `𝒢^•`
satisfies them for `f` with support in the closed complement `T` of the square, then its
restriction to `X'` satisfies them for `j ≫ f`: it is bounded, its terms are coherent
(`X'` being locally Noetherian) and flat over `Y`, and its support lies in `j⁻¹(T)`, which is
proper over `Y`. -/
theorem flatProperSupportComplex_edsEtaleRestrict [Mono fV] (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hN : HasEtaleLocalProperty B S hS (edsEtale B S hS hsq).1
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G)
    (hGT : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆
      edsComplementPoints B S hS Uo)
    (hT : IsProperOver B S hS X.2 Y.2 f.hom hf (edsComplementPoints B S hS Uo)
      hsq.isClosedComplement) :
    FlatProperSupportComplex B S hS (edsEtaleHom B S hS hsq ≫ f)
      (isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf)
      (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) where
  bounded := by
    obtain ⟨a, b, h⟩ := hG.bounded
    have : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    exact ⟨a, b, fun q hq => (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).map_isZero (h q hq)⟩
  isCoherent q := isCoherent_etaleModulePullback_of_hasEtaleLocalProperty B S hS _
    (isEtale_edsEtaleHom B S hS hsq) hN _ (hG.isCoherent q)
  isFlatOver q := isFlatOver_etaleModulePullback_comp B S hS _ (isEtale_edsEtaleHom B S hS hsq) f
    _ (hG.isFlatOver q)
  properSupport := ⟨_, _, isProperOver_preimage_edsComplementPoints B S hS hsq f hf hT, fun q => by
    change supportOfSheaf B S hS (edsEtale B S hS hsq).1 ((SheafOfModules.toSheaf _).obj
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj (G.X q))) ⊆ _
    rw [supportOfSheaf_toSheaf_etaleModulePullback]
    exact Set.preimage_mono (hGT q)⟩

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- Restriction of modules along the étale morphism of the square, on derived categories. -/
abbrev edsEtaleRestrict :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) :=
  (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory

/-- The cohomology sheaves of the restriction of `E` are the restrictions of the cohomology
sheaves of `E`. -/
def edsEtaleRestrictHomologyIso (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj ((edsEtaleRestrict B S hS hsq).obj E) ≅
      (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj ((DerivedCategory.homologyFunctor _ q).obj E) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)) q).app E

/-- **Restriction preserves boundedness above.** -/
theorem isBoundedAbove_edsEtaleRestrict (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.IsBoundedAbove E) :
    DerivedCategoryB.IsBoundedAbove ((edsEtaleRestrict B S hS hsq).obj E) := by
  obtain ⟨b, hb⟩ := hE
  exact ⟨b, fun q hq => ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).map_isZero (hb q hq)).of_iso
      (edsEtaleRestrictHomologyIso B S hS hsq E q)⟩

/-- **Restriction along the open neighbourhood of a support is bijective on `Ext` into an object
supported there.**  If `M ∈ D(𝒪_X)` has its cohomology supported on the closed complement of the
open subspace of the square, then for every `E` and every `i` the map
`Ext^i(E, M) ⟶ Ext^i(E|_{X'}, M|_{X'})`, `e ↦ e|_{X'}` composed with the commutation of the
restriction with the shift, is bijective (Stacks 08GG, through the Mayer–Vietoris sequence). -/
theorem bijective_edsEtaleRestrict_shiftedHom_of_cohomologySupportedOn
    (E M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hM : CohomologySupportedOn B S hS X.1 X.2 (edsComplementPoints B S hS Uo) M) (i : ℤ) :
    Function.Bijective (fun e : E ⟶ M⟦i⟧ =>
      (edsEtaleRestrict B S hS hsq).map e ≫
        ((edsEtaleRestrict B S hS hsq).commShiftIso i).hom.app M) := by
  have hMi := cohomologySupportedOn_shift B S hS X _ M hM i
  obtain ⟨hU, hP⟩ := isZero_edsOpen_and_edsInter_of_cohomologySupportedOn B S hS hsq _ hMi
  exact ((Iso.homToEquiv (((edsEtaleRestrict B S hS hsq).commShiftIso i).app M)).bijective).comp
    (bijective_map_edsEtale_of_isZero_target B S hS hsq E (M⟦i⟧) hU hP)

/-- **Restriction to the Noetherian neighbourhood of an object of `D^-_{Coh}(𝒪_X)` is
pseudo-coherent** (Stacks 08IK on the Noetherian `X'`): its cohomology sheaves are the
restrictions of those of `E`, coherent by
`AlgebraicGeometry.Space.isCoherent_etaleModulePullback_of_hasEtaleLocalProperty`, and it is
bounded above. -/
theorem isPseudoCoherent_edsEtaleRestrict_of_isCoherent_homology
    (hTop : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hTop (edsEtale B S hS hsq).1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hEcoh : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ q).obj E))
    (hEb : DerivedCategoryB.IsBoundedAbove E) :
    (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPseudoCoherent
      ((edsEtaleRestrict B S hS hsq).obj E) :=
  isPseudoCoherent_of_isCoherent_homology_of_isNoetherian B S hS (edsEtale B S hS hsq) hTop hN _
    (fun q => isCoherent_of_iso B S hS (edsEtale B S hS hsq).2
      (edsEtaleRestrictHomologyIso B S hS hsq E q).symm
      (isCoherent_etaleModulePullback_of_hasEtaleLocalProperty B S hS _
        (isEtale_edsEtaleHom B S hS hsq) hN.2.2 _ (hEcoh q)))
    (isBoundedAbove_edsEtaleRestrict B S hS hsq E hEb)

end Square

end AlgebraicGeometry.Space

end
