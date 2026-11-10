module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatLocalBaseCanonicalExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatStalksCompleted
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableImageExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartIdealSheaf
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.IsoTransport
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine

/-!
# The algebraization situation of an affine chart

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals, `U ⊆ X` an open whose
complement lies in the support of `ℐ`, and `V ⊆ X` an affine open. With `A = Γ(X, V)` the triple
`(A, ℐ(V), 𝔞)`, for `𝔞` the ideal of the complement of `U` in `Spec A ≅ V`, is an algebraization
situation in the sense of Stacks 0EHC whose open complement is `U ∩ V`. A coherent `ℐ`-adic system
`(F_n)` on `U` restricts to a coherent adic system on that open complement, and its module of
sections there is the module `Γ(V, j_*F_n)` of sections over `V` of the direct image along
`j : U → X`.

This file sets up that dictionary and uses it to apply the algebraization results of Stacks 0EJU
on every affine open of a scheme proper over a complete Noetherian local ring, which is steps 1 and
2 of the proof of Stacks 0EJV.

## Main definitions

* `Stacks.Algebraization.chartSituation` — the algebraization situation of an affine open.
* `Stacks.Algebraization.chartMap` — the open immersion from its open complement to `U`.
* `Stacks.Algebraization.chartSystem` — the restriction of a coherent adic system on `U`.
* `Stacks.Algebraization.baseToStalk` — the ring map `R → 𝒪_{Y,y}` of a scheme over `Spec R`.

## Main results

* `Stacks.Algebraization.chartSectionsSystemIso` — the sections of the chart system are the
  sections over `V` of the direct images `j_*F_n`.
* `Stacks.Algebraization.hasFiniteLowDegreeCohomology_chartSystem` — hypothesis (3) of 0EJU on
  the chart, from the coherence of `j_*F_1` and `R¹j_*F_1`.
* `Stacks.Algebraization.flatCompletedStalks_chartSystem` — hypothesis (2) of 0EJU on the chart,
  from the flatness of `F_n` over `R/𝔪ⁿ`.
* `Stacks.Algebraization.isStableAdicSystem_sections_of_flat` — the conditions of the
  Mittag-Leffler criterion 0EHH for the system `Γ(V, j_*F_n)`.

## References

* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u}) (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **The three conditions of Stacks 0EHH in the situation of Stacks 0EJU.** Under the
hypotheses of Stacks 0EJU the inverse system `H⁰(U, F_n)` is Mittag-Leffler, the limit topology
on its limit is the `I`-adic topology, and its terms are finite `A`-modules. -/
theorem isStableAdicSystem_globalSectionsSystem_of_flatLocalBase (B : FlatLocalBase S F)
    (h3 : HasFiniteLowDegreeCohomology S F) :
    Stacks.Coherent.IsStableAdicSystem (globalSectionsSystem S F) S.I :=
  ⟨isMittagLeffler_globalSectionsSystem_of_flatLocalBase S F B h3.2,
    exists_projection_ker_le_adicPower S F
      (limitTopology_eq_adicModuleTopology_of_flatLocalBase S F B h3.1),
    finite_globalSections_of_finite_idealPowerSections S F h3.1
      (finite_idealPowerSections_of_flatLocalBase S F B h3.1)⟩

/-! ### The algebraization situation of an affine chart -/

section Chart

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
  (V : X.affineOpens)

omit [IsLocallyNoetherian X] in
/-- A point of `Spec Γ(X, V)` maps into `V` under `Spec Γ(X, V) ⟶ X`. -/
private theorem fromSpec_mem_affineOpen (p : Spec Γ(X, V)) :
    V.2.fromSpec p ∈ (V : X.Opens) := by
  have h : V.2.fromSpec p ∈ Set.range V.2.fromSpec := ⟨p, rfl⟩
  rwa [V.2.range_fromSpec] at h

/-- The ideal of `Γ(X, V)` cutting out the complement of `U` in `Spec Γ(X, V) ≅ V`. -/
def chartComplementIdeal : Ideal Γ(X, V) :=
  PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum Γ(X, V) | p ∉ V.2.fromSpec ⁻¹ᵁ U}

omit [IsLocallyNoetherian X] in
/-- If the complement of `U` lies in the support of `I`, then `I(V)` is contained in the ideal of
the complement of `U` in `Spec Γ(X, V)`. -/
theorem le_chartComplementIdeal (hU : ((U : Set X))ᶜ ⊆ I.support) :
    I.ideal V ≤ chartComplementIdeal U V := by
  intro s hs
  rw [chartComplementIdeal, PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  have hpV := fromSpec_mem_affineOpen V p
  have hsupp : V.2.fromSpec p ∈ I.support := hU hp
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hpV, Scheme.mem_zeroLocus_iff] at hsupp
  by_contra hps
  have hmem : p ∈ (PrimeSpectrum.basicOpen s : (Spec Γ(X, V)).Opens) := hps
  rw [← V.2.fromSpec_preimage_basicOpen] at hmem
  exact hsupp s hs hmem

/-- **The algebraization situation of an affine chart.** For an affine open `V` of `X`, the ring
`A = Γ(X, V)`, the ideal `I(V)` and the ideal of the complement of `U` in `V`. -/
abbrev chartSituation (hU : ((U : Set X))ᶜ ⊆ I.support) : AlgebraizationSituation.{u} where
  A := Γ(X, V)
  noetherianA := IsLocallyNoetherian.component_noetherian V
  I := I.ideal V
  a := chartComplementIdeal U V
  I_le_a := le_chartComplementIdeal I U V hU

variable (hU : ((U : Set X))ᶜ ⊆ I.support)

/-- The open complement of the chart situation is the preimage of `U` in `Spec Γ(X, V)`. -/
theorem chartSituation_U : (chartSituation I U V hU).U = V.2.fromSpec ⁻¹ᵁ U := by
  apply Opens.ext
  change (PrimeSpectrum.zeroLocus (chartComplementIdeal U V : Set Γ(X, V)))ᶜ = _
  rw [chartComplementIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hcl : IsClosed {p : PrimeSpectrum Γ(X, V) | p ∉ V.2.fromSpec ⁻¹ᵁ U} :=
    (V.2.fromSpec ⁻¹ᵁ U).isOpen.isClosed_compl
  rw [hcl.closure_eq]
  ext p
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
  rfl

/-- The chart `Spec Γ(X, V) ⟶ X`, typed with the source of the chart situation. -/
abbrev chartFromSpec : (chartSituation I U V hU).X ⟶ X := V.2.fromSpec

/-- The chart `Spec Γ(X, V) ⟶ X` is an open immersion. -/
instance : IsOpenImmersion (chartFromSpec I U V hU) := V.2.isOpenImmersion_fromSpec

/-- The open complement of the chart situation maps into `U` under `Spec Γ(X, V) ⟶ X`. -/
theorem range_chartSituation_U_fromSpec :
    Set.range ((chartSituation I U V hU).U.ι ≫ chartFromSpec I U V hU) ⊆ Set.range U.ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hy : (y.1 : (chartSituation I U V hU).X) ∈ chartFromSpec I U V hU ⁻¹ᵁ U :=
    chartSituation_U I U V hU ▸ y.2
  exact hy

/-- **The chart map** `U' ⟶ U` from the open complement of the chart situation, the restriction of
`Spec Γ(X, V) ≅ V ⊆ X` to the preimage of `U`. -/
def chartMap : (chartSituation I U V hU).U.toScheme ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι ((chartSituation I U V hU).U.ι ≫ chartFromSpec I U V hU)
    (range_chartSituation_U_fromSpec I U V hU)

/-- The chart map followed by the inclusion of `U` is the inclusion of the open complement
followed by `Spec Γ(X, V) ⟶ X`. -/
@[reassoc (attr := simp)]
theorem chartMap_ι :
    chartMap I U V hU ≫ U.ι = (chartSituation I U V hU).U.ι ≫ chartFromSpec I U V hU :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chart map is an open immersion. -/
instance : IsOpenImmersion (chartMap I U V hU) := by
  have : IsOpenImmersion (chartMap I U V hU ≫ U.ι) := by
    rw [chartMap_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ U.ι

omit [IsLocallyNoetherian X] in
/-- The ideal sheaf `I` on `X`, pulled back to `Spec Γ(X, V)`, is the one generated by `I(V)`. -/
theorem comap_fromSpec_eq_ofIdealTop :
    I.comap V.2.fromSpec =
      Scheme.IdealSheafData.ofIdealTop ((I.ideal V).map (Scheme.ΓSpecIso Γ(X, V)).inv.hom) := by
  have h := baseIdealSheaf_isoSpec I V
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap] at h
  rw [← V.2.isoSpec_inv_ι, Scheme.IdealSheafData.comap_comp, ← h,
    ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rfl

/-- The ideal sheaf `I` restricted to `U` and pulled back along the chart map is the ideal sheaf
of the chart situation on its open complement. -/
theorem comap_chartMap :
    (I.comap U.ι).comap (chartMap I U V hU) = idealOnOpen (chartSituation I U V hU) := by
  rw [← Scheme.IdealSheafData.comap_comp, chartMap_ι, Scheme.IdealSheafData.comap_comp]
  change (I.comap V.2.fromSpec).comap _ = _
  rw [comap_fromSpec_eq_ofIdealTop]
  rfl

/-- **A coherent adic system on `U`, read on the chart situation of `V`.** -/
def chartSystem (F : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι)) :
    Stacks.Coherent.CoherentAdicSystems (idealOnOpen (chartSituation I U V hU)) :=
  ⟨F.obj ⋙ Scheme.Modules.restrictFunctor (chartMap I U V hU), by
    rw [← comap_chartMap I U V hU]
    exact Stacks.Coherent.isCoherentAdicSystem_restrict (I.comap U.ι) (chartMap I U V hU) F⟩

/-- The image of the chart map is `U ∩ V`, as an open of `U`. -/
theorem chartMap_image_top :
    chartMap I U V hU ''ᵁ ⊤ = U.ι ⁻¹ᵁ (V : X.Opens) := by
  apply Opens.ext
  ext x
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
  change x ∈ Set.range (chartMap I U V hU) ↔ U.ι x ∈ (V : X.Opens)
  constructor
  · rintro ⟨y, rfl⟩
    change (chartMap I U V hU ≫ U.ι) y ∈ (V : X.Opens)
    rw [chartMap_ι]
    exact fromSpec_mem_affineOpen V ((chartSituation I U V hU).U.ι y)
  · intro hx
    have h : U.ι x ∈ Set.range V.2.fromSpec := by rwa [V.2.range_fromSpec]
    obtain ⟨p, hp⟩ := h
    have hpU : p ∈ (chartSituation I U V hU).U := by
      rw [chartSituation_U]
      change V.2.fromSpec p ∈ U
      rw [hp]
      exact x.2
    refine ⟨⟨p, hpU⟩, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    change (chartMap I U V hU ≫ U.ι) ⟨p, hpU⟩ = U.ι x
    rw [chartMap_ι]
    exact hp

omit [IsLocallyNoetherian X] in
/-- For an affine open `W`, the map `Γ(X, W) ⟶ Γ(Spec Γ(X, W), ⊤)` induced by
`Spec Γ(X, W) ⟶ X` is the inverse of the canonical isomorphism. -/
theorem fromSpec_appLE_top {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec.appLE W ⊤ hW.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, W)).inv := by
  simp only [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  simp

/-- The ring map `Γ(X, V) ⟶ Γ(U, U ∩ V)` through the chart agrees with the restriction. -/
theorem chartMap_ringHom_compat :
    (Scheme.ΓSpecIso (.of Γ(X, V))).inv ≫ (chartSituation I U V hU).U.ι.appTop ≫
        ((chartMap I U V hU).appIso ⊤).inv ≫
        U.toScheme.presheaf.map (eqToHom (chartMap_image_top I U V hU).symm).op =
      U.ι.app (V : X.Opens) := by
  have hcongr : ∀ {A B : Scheme.{u}} {f g : A ⟶ B} (_ : f = g) (W : B.Opens) (W' : A.Opens)
      (e : W' ≤ f ⁻¹ᵁ W) (e' : W' ≤ g ⁻¹ᵁ W), f.appLE W W' e = g.appLE W W' e' := by
    intro A B f g h W W' e e'
    subst h
    rfl
  have key : U.ι.appLE (V : X.Opens) (chartMap I U V hU ''ᵁ ⊤)
        (chartMap_image_top I U V hU).le ≫ ((chartMap I U V hU).appIso ⊤).hom =
      (Scheme.ΓSpecIso (.of Γ(X, V))).inv ≫ (chartSituation I U V hU).U.ι.appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE,
      hcongr (chartMap_ι I U V hU) _ _ _ (by
        intro x _
        exact fromSpec_mem_affineOpen V ((chartSituation I U V hU).U.ι x)),
      ← Scheme.Hom.appLE_comp_appLE (chartSituation I U V hU).U.ι (chartFromSpec I U V hU)
        (V : X.Opens) ⊤ ⊤ V.2.fromSpec_preimage_self.ge le_rfl]
    have h2 : (chartFromSpec I U V hU).appLE (V : X.Opens) ⊤ V.2.fromSpec_preimage_self.ge =
        (Scheme.ΓSpecIso (.of Γ(X, V))).inv := fromSpec_appLE_top V.2
    rw [h2]
    rfl
  rw [← Category.assoc, ← key]
  simp only [Scheme.Hom.appLE, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
  rw [show (homOfLE (chartMap_image_top I U V hU).le).op ≫
      (eqToHom (chartMap_image_top I U V hU).symm).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Restriction from the image of the chart map to `U ∩ V` is semilinear with respect to the
ring map `Γ(X, V) ⟶ Γ(U, U ∩ V)` and the scalar map of the chart situation. -/
theorem chartSections_map_smul (M : U.toScheme.Modules) (x : Γ(M, chartMap I U V hU ''ᵁ ⊤))
    (a : Γ(X, V)) :
    M.presheaf.map (eqToHom (chartMap_image_top I U V hU).symm).op
        (((chartMap I U V hU).appIso ⊤).inv (scalarMap (chartSituation I U V hU) a) • x) =
      U.ι.app (V : X.Opens) a •
        M.presheaf.map (eqToHom (chartMap_image_top I U V hU).symm).op x := by
  rw [Scheme.Modules.map_smul (i := eqToHom (chartMap_image_top I U V hU).symm)]
  congr 1
  exact congr($(chartMap_ringHom_compat I U V hU) a)

/-- **The sections of the chart system are the sections over `V` of the direct image.** -/
def chartSectionsEquiv (M : U.toScheme.Modules) :
    (ModuleCat.restrictScalars (scalarMap (chartSituation I U V hU))).obj
        ((_root_.SheafOfModules.evaluation (chartSituation I U V hU).U.toScheme.ringCatSheaf
          (op ⊤)).obj
          ((Scheme.Modules.restrictFunctor (chartMap I U V hU)).obj M)) ≃ₗ[Γ(X, V)]
      (affineSectionFunctor V).obj ((Scheme.Modules.pushforward U.ι).obj M) where
  toAddEquiv :=
    (M.presheaf.mapIso (eqToIso (chartMap_image_top I U V hU).symm).op).addCommGroupIsoToAddEquiv
  map_smul' a x := chartSections_map_smul I U V hU M x a

/-- The identification `chartSectionsEquiv` is natural in the module on `U`. -/
theorem chartSectionsEquiv_naturality {M N : U.toScheme.Modules} (g : M ⟶ N)
    (x : (ModuleCat.restrictScalars (scalarMap (chartSituation I U V hU))).obj
        ((_root_.SheafOfModules.evaluation (chartSituation I U V hU).U.toScheme.ringCatSheaf
          (op ⊤)).obj
          ((Scheme.Modules.restrictFunctor (chartMap I U V hU)).obj M))) :
    chartSectionsEquiv I U V hU N
        (((ModuleCat.restrictScalars (scalarMap (chartSituation I U V hU))).map
          ((_root_.SheafOfModules.evaluation (chartSituation I U V hU).U.toScheme.ringCatSheaf
            (op ⊤)).map
            ((Scheme.Modules.restrictFunctor (chartMap I U V hU)).map g))) x) =
      ((affineSectionFunctor V).map ((Scheme.Modules.pushforward U.ι).map g))
        (chartSectionsEquiv I U V hU M x) :=
  (congr($(g.mapPresheaf.naturality (eqToHom (chartMap_image_top I U V hU).symm).op) x)).symm

/-- **The inverse system of sections of the chart system is the system of sections over `V` of
the direct images.** -/
def chartSectionsSystemIso (F : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι)) :
    globalSectionsSystem (chartSituation I U V hU) (chartSystem I U V hU F) ≅
      (F.obj ⋙ Scheme.Modules.pushforward U.ι) ⋙ affineSectionFunctor V :=
  NatIso.ofComponents (fun n => (chartSectionsEquiv I U V hU (F.obj.obj n)).toModuleIso)
    (fun {n n'} f => by
      ext x
      exact chartSectionsEquiv_naturality I U V hU (F.obj.map f) x)

/-- The range of the chart map is the range of the inclusion of `U ∩ V` into `U`. -/
theorem range_chartMap : Set.range (chartMap I U V hU) = Set.range (U.ι ⁻¹ᵁ (V : X.Opens)).ι := by
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← Scheme.Hom.image_top_eq_opensRange,
    chartMap_image_top]

/-- The open complement of the chart situation is `U ∩ V`. -/
def chartIso : (chartSituation I U V hU).U.toScheme ≅ (U.ι ⁻¹ᵁ (V : X.Opens)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartMap I U V hU) (U.ι ⁻¹ᵁ (V : X.Opens)).ι
    (range_chartMap I U V hU)

/-- The isomorphism `chartIso` followed by the inclusion of `U ∩ V` into `U` is the chart map. -/
@[reassoc (attr := simp)]
theorem chartIso_hom_ι :
    (chartIso I U V hU).hom ≫ (U.ι ⁻¹ᵁ (V : X.Opens)).ι = chartMap I U V hU :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The isomorphism `chartIso` followed by the restriction of `U ⟶ X` over `V` is the inclusion
of the open complement followed by `Spec Γ(X, V) ≅ V`. -/
theorem chartIso_hom_restrict :
    (chartIso I U V hU).hom ≫ (U.ι ∣_ (V : X.Opens)) =
      (chartSituation I U V hU).U.ι ≫ V.2.isoSpec.inv := by
  rw [← cancel_mono (V : X.Opens).ι, Category.assoc, morphismRestrict_ι, chartIso_hom_ι_assoc,
    chartMap_ι, Category.assoc]
  rfl

/-- The restriction to the chart, pushed forward along the identification with `U ∩ V`, is the
restriction to `U ∩ V`. -/
def chartRestrictIso (M : U.toScheme.Modules) :
    (Scheme.Modules.pushforward (chartIso I U V hU).hom).obj
        ((Scheme.Modules.restrictFunctor (chartMap I U V hU)).obj M) ≅
      (Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ (V : X.Opens)).ι).obj M :=
  let e := chartIso I U V hU
  let N := (Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ (V : X.Opens)).ι).obj M
  (Scheme.Modules.pushforward e.hom).mapIso
      ((Scheme.Modules.restrictFunctorCongr (chartIso_hom_ι I U V hU).symm).app M ≪≫
        (Scheme.Modules.restrictFunctorComp e.hom _).app M) ≪≫
    ((Stacks.AlgebraicGeometry.DerivedPushforward.restrictInvIsoPushforward e).app
      ((Scheme.Modules.restrictFunctor e.hom).obj N)).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).app N).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app N ≪≫
    Scheme.Modules.restrictFunctorId.app N

/-- The spectrum of `Γ(X, V)` is locally Noetherian, being an open subscheme of `X`. -/
private instance : IsLocallyNoetherian (chartSituation I U V hU).X :=
  isLocallyNoetherian_of_isOpenImmersion V.2.fromSpec

/-- **Coherence of the higher direct images on the chart.** If `R^p j_* M` is coherent on `X`,
then so is `R^p` of the chart restriction of `M` along `U' ⟶ Spec Γ(X, V)`. -/
theorem isCoherent_rightDerived_chart (M : U.toScheme.Modules) (q : ℕ)
    (h : (((Scheme.Modules.pushforward U.ι).rightDerived q).obj M).IsCoherent) :
    (((Scheme.Modules.pushforward (chartSituation I U V hU).U.ι).rightDerived q).obj
      ((Scheme.Modules.restrictFunctor (chartMap I U V hU)).obj M)).IsCoherent := by
  have : IsLocallyNoetherian (V : X.Opens).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (V : X.Opens).ι
  refine Stacks.AlgebraicGeometry.DerivedPushforward.isCoherent_rightDerived_of_transport
    (chartSituation I U V hU).U.ι (U.ι ∣_ (V : X.Opens)) (chartIso I U V hU) V.2.isoSpec.symm
    (chartIso_hom_restrict I U V hU) q _ ?_
  have h2 : (((Scheme.Modules.pushforward U.ι).rightDerivedPlus (q : ℤ)).obj M).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward U.ι) q).app M).symm
  have h3 := Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion
    (V : X.Opens).ι _ h2
  have h4 := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso
      U.ι (V : X.Opens) q M)
  have h5 := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (U.ι ∣_ (V : X.Opens)))
      q).app ((Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ (V : X.Opens)).ι).obj M))
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (((Scheme.Modules.pushforward (U.ι ∣_ (V : X.Opens))).rightDerived q).mapIso
      (chartRestrictIso I U V hU M))

/-- **Hypothesis (3) of Stacks 0EJU on the chart**, from the coherence of `j_* F_1` and
`R¹ j_* F_1`. -/
theorem hasFiniteLowDegreeCohomology_chartSystem
    (F : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι))
    (h0 : ((Scheme.Modules.pushforward U.ι).obj (F.obj.obj (op 0))).IsCoherent)
    (h1 : (((Scheme.Modules.pushforward U.ι).rightDerived 1).obj (F.obj.obj (op 0))).IsCoherent) :
    HasFiniteLowDegreeCohomology (chartSituation I U V hU) (chartSystem I U V hU F) := by
  have : (F.obj.obj (op 0)).IsQuasicoherent := F.property.isQuasicoherent 0
  constructor
  · obtain ⟨hq, hf⟩ :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pushforward U.ι).obj (F.obj.obj (op 0)))
    have hfin : Module.Finite Γ(X, V)
        Γ((Scheme.Modules.pushforward U.ι).obj (F.obj.obj (op 0)), V) :=
      AlgebraicGeometry.moduleFinite_sections_on_affine _ (V : X.Opens) V.2
    have hfin' : Module.Finite (chartSituation I U V hU).A
        (((F.obj ⋙ Scheme.Modules.pushforward U.ι) ⋙ affineSectionFunctor V).obj (op 0)) :=
      hfin
    exact Module.Finite.equiv
      ((chartSectionsSystemIso I U V hU F).app (op 0)).toLinearEquiv.symm
  · let F₀ := (Scheme.Modules.restrictFunctor (chartMap I U V hU)).obj (F.obj.obj (op 0))
    have hcoh := isCoherent_rightDerived_chart I U V hU (F.obj.obj (op 0)) 1 h1
    have : F₀.IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor (chartMap I U V hU) _
    have hfin :=
      Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_of_isCoherent
      (chartSituation I U V hU).U.ι F₀ 1 hcoh
    have happ : (chartSituation I U V hU).U.ι.appLE ⊤ ⊤ (by simp) =
        (chartSituation I U V hU).U.ι.appTop :=
      Scheme.Hom.appLE_eq_app _
    change Module.Finite Γ(X, V) ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of Γ(X, V))).inv ≫
        (chartSituation I U V hU).U.ι.appLE ⊤ ⊤ (by simp)).hom).obj _)
    rw [happ]
    exact (Module.finite_restrictScalars_ringEquiv_iff
      (Scheme.ΓSpecIso (.of Γ(X, V))).commRingCatIsoToRingEquiv.symm _).mpr hfin

end Chart

/-! ### The chart over a local base -/

section Base

open Stacks.Cohomology.FormalFunctions

/-- The ring map `R → 𝒪_{Y,y}` of a scheme over `Spec R`. -/
def baseToStalk (R : Type u) [CommRing R] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) (y : Y) :
    R →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ ⊤ y trivial).hom.comp ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (p : X ⟶ Spec (.of R)) (J : Ideal R) (U : X.Opens) (V : X.affineOpens)
  (hU : ((U : Set X))ᶜ ⊆ (baseIdealSheaf R J p).support)

/-- The ring map `R → Γ(X, V)`. -/
def chartBaseMap : R →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE le_top : (V : X.Opens) ⟶ ⊤).op).hom.comp
    ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom

omit [IsLocallyNoetherian X] in
/-- The sections over `V` of the ideal sheaf generated by `J` are the extension of `J` along
`R → Γ(X, V)`. -/
theorem baseIdealSheaf_ideal_eq_map_chartBaseMap :
    (baseIdealSheaf R J p).ideal V = J.map (chartBaseMap R p V) := by
  rw [baseIdealSheaf_ideal, baseIdeal, Ideal.map_map]
  rfl

omit [IsLocallyNoetherian X] in
/-- For an affine open `W`, the map on global sections of `Spec Γ(X, W) ⟶ X` is restriction from
`X` to `W` followed by the inverse of the canonical isomorphism. -/
theorem fromSpec_appTop_eq {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec.appTop = X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op ≫
      (Scheme.ΓSpecIso Γ(X, W)).inv := by
  rw [Scheme.Hom.appTop, IsAffineOpen.fromSpec_app_of_le _ _ le_top]
  have h : (Spec Γ(X, W)).presheaf.map (homOfLE (le_top : hW.fromSpec ⁻¹ᵁ ⊤ ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : hW.fromSpec ⁻¹ᵁ ⊤ ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _]
    exact (Spec Γ(X, W)).presheaf.map_id _
  rw [h]
  exact congrArg (fun g => X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op ≫ g)
    (Category.comp_id (Scheme.ΓSpecIso Γ(X, W)).inv)

/-- The base map to the stalks of the chart system is the restriction of the one on `U`. -/
theorem chartMap_baseToStalk (y : (chartSituation (baseIdealSheaf R J p) U V hU).U.toScheme) :
    ((chartMap (baseIdealSheaf R J p) U V hU).stalkMap y).hom.comp
        (baseToStalk R (U.ι ≫ p) (chartMap (baseIdealSheaf R J p) U V hU y)) =
      (((chartSituation (baseIdealSheaf R J p) U V hU).U.toScheme.presheaf.germ ⊤ y
        trivial).hom.comp (scalarMap (chartSituation (baseIdealSheaf R J p) U V hU))).comp
        (chartBaseMap R p V) := by
  have hmor : (Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ p).appTop ≫
      (chartMap (baseIdealSheaf R J p) U V hU).app ⊤ =
      (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫
        X.presheaf.map (homOfLE le_top : (V : X.Opens) ⟶ ⊤).op ≫
        (Scheme.ΓSpecIso Γ(X, V)).inv ≫
          (chartSituation (baseIdealSheaf R J p) U V hU).U.ι.appTop := by
    change (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫
      ((chartMap (baseIdealSheaf R J p) U V hU) ≫ U.ι).appTop = _
    rw [chartMap_ι]
    change (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫ V.2.fromSpec.appTop ≫ _ = _
    rw [fromSpec_appTop_eq V.2]
    rfl
  ext r
  simp only [RingHom.comp_apply, baseToStalk]
  refine (Scheme.Hom.germ_stalkMap_apply (chartMap (baseIdealSheaf R J p) U V hU) ⊤ y trivial
    _).trans ?_
  exact congrArg (fun z => ((chartSituation (baseIdealSheaf R J p) U V hU).U.toScheme.presheaf.germ
    ⊤ y trivial) z) congr($hmor r)

/-- **Hypothesis (2) of Stacks 0EJU on the chart**, from the flatness of the stalks of the
`F_n` over `R ⧸ Jⁿ⁺¹`. -/
theorem flatCompletedStalks_chartSystem [IsNoetherianRing R]
    (F : Stacks.Coherent.CoherentAdicSystems ((baseIdealSheaf R J p).comap U.ι))
    (hflat : ∀ n : ℕ, StalksFlatOverQuotient R (baseToStalk R (U.ι ≫ p)) (J ^ (n + 1))
      (F.obj.obj (op n))) :
    FlatCompletedStalks (chartSituation (baseIdealSheaf R J p) U V hU)
      (chartSystem (baseIdealSheaf R J p) U V hU F) (chartBaseMap R p V) := by
  intro y _
  have : IsLocallyNoetherian (chartSituation (baseIdealSheaf R J p) U V hU).U.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (chartSituation (baseIdealSheaf R J p) U V hU).U.ι
  have hK : IdealSheafData.stalk (idealOnOpen (chartSituation (baseIdealSheaf R J p) U V hU)) y =
      J.map ((((chartSituation (baseIdealSheaf R J p) U V hU).U.toScheme.presheaf.germ ⊤ y
        trivial).hom.comp (scalarMap (chartSituation (baseIdealSheaf R J p) U V hU))).comp
        (chartBaseMap R p V)) := by
    rw [stalk_idealOnOpen_eq_map_scalarMap]
    change ((baseIdealSheaf R J p).ideal V).map _ = _
    rw [baseIdealSheaf_ideal_eq_map_chartBaseMap, Ideal.map_map]
  refine flat_completedStalk _ _ y R J _ hK fun n => ?_
  have h := (hflat n).restrict (chartMap (baseIdealSheaf R J p) U V hU) y
  exact chartMap_baseToStalk R p J U V hU y ▸ h

/-- **The three conditions of Stacks 0EHH on an affine chart.** -/
theorem isStableAdicSystem_sections_of_flat [IsNoetherianRing R] [IsLocalRing R]
    (F : Stacks.Coherent.CoherentAdicSystems
      ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι))
    (hU : ((U : Set X))ᶜ ⊆ (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).support)
    (hflat : ∀ n : ℕ, StalksFlatOverQuotient R (baseToStalk R (U.ι ≫ p))
      (IsLocalRing.maximalIdeal R ^ (n + 1)) (F.obj.obj (op n)))
    (h0 : ((Scheme.Modules.pushforward U.ι).obj (F.obj.obj (op 0))).IsCoherent)
    (h1 : (((Scheme.Modules.pushforward U.ι).rightDerived 1).obj (F.obj.obj (op 0))).IsCoherent) :
    Stacks.Coherent.IsStableAdicSystem ((F.obj ⋙ Scheme.Modules.pushforward U.ι) ⋙
      affineSectionFunctor V) ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).ideal V) := by
  let B : FlatLocalBase (chartSituation (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U V hU)
      (chartSystem (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U V hU F) :=
    { R := R
      φ := chartBaseMap R p V
      I_eq := baseIdealSheaf_ideal_eq_map_chartBaseMap R p _ V
      flat := flatCompletedStalks_chartSystem R p _ U V hU F hflat }
  exact (isStableAdicSystem_globalSectionsSystem_of_flatLocalBase _ _ B
    (hasFiniteLowDegreeCohomology_chartSystem _ U V hU F h0 h1)).of_iso
      (chartSectionsSystemIso _ U V hU F)

end Base

end Stacks.Algebraization

end
