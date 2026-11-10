module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutRepresentedChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineDerivedAssociatedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescent
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.RingTheory.MilnorPatching.DerivedEssentialImagePullback

/-!
# The affine case of Stacks 0DL7 on represented affine squares

Let `gi ≫ gf' = gf ≫ gj` be a commutative square of objects of the big fppf site with affine
underlying schemes, whose rings of global functions form a fibre product along a surjection with
nil kernel. The proof of Stacks 0DL7 settles the isomorphism step on such a square on rings. This
file carries out the passage from the algebraic spaces represented by the square to the rings,
and with it completes the proof of Stacks 0DL7.

## Main results

* `AlgebraicGeometry.Space.pushoutGlueingIsIsoStepOnRepresentedAffine`: the isomorphism step of
  Stacks 0DL7 on represented affine squares. A pseudo-coherent object `M` of
  `D(𝒪_{yoneda.obj U})`, for `U` with affine underlying scheme of ring `R`, is the associated
  object `Φ(m)` of a pseudo-coherent object `m` of `D(R)` (Stacks 08JL and Stacks 08E7 for
  algebraic spaces, private lemmas of this file); the derived pullbacks and direct images of the
  square correspond under `Φ` to derived extension and restriction of scalars (Stacks 08DW and
  0DJK for represented affine spaces,
  `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso` and
  `AlgebraicGeometry.Space.isIso_representedAffineTransportUnit`), compatibly around the square
  up to a unit
  (`AlgebraicGeometry.Space.exists_representedAffineToposDerivedBaseChange_compat`);
  the ring-level statement
  `MilnorPatching.isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap_derivedExtension`
  is carried to the algebraic spaces by
  `MilnorPatching.isIso_homEquiv_symm_of_transport_models`.
* `AlgebraicGeometry.Space.derivedPushoutEssentialImage`: **Stacks 0DL7.**

## Implementation notes

The statement handed to `MilnorPatching.isIso_homEquiv_symm_of_transport_models` is built only
from the terms of the base lemmas it combines, spelled as they are there (the 2-cells of the
pasting are left to be inferred from it, the proofs of the square are the same terms): two
spellings that agree only up to unfolding, even of a proof argument or of an abbreviation, make
the kernel unfold the derived categories of the small étale sites, beyond its budget.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 068R](https://stacks.math.columbia.edu/tag/068R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe w₁ w₂ w₃ w₄ u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PseudoCoherent

/-- An isomorphism approximates its target from every degree. -/
private theorem approximatesFrom_of_isIso' {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {P K : DerivedCategory C} (φ : P ⟶ K) [IsIso φ] (m : ℤ) :
    DerivedCategory.ApproximatesFrom φ m :=
  ⟨fun _ _ ↦ inferInstance, inferInstance⟩

/-- **Approximations by bounded complexes of retracts of finite free modules pull back.** If
`φ : P ⟶ E` approximates `E ∈ D(𝒪_Y)` from `m`, then `Lf^* E` is approximated from `m` by the
degreewise pullback of `P`: the terms of `P` are flat, so `Lf^*` is computed degreewise on `P`,
and `Lf^*` is triangulated and preserves `D^{≤ n}`. -/
private theorem exists_approximation_pullback_of_approximation {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (m : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))
      (P.X j))
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    ∀ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      (φ : DerivedCategory.Q.obj P ⟶ E), DerivedCategory.ApproximatesFrom φ m →
    ∃ P' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ,
      (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))
        (P'.X j)) ∧
      (∃ a b : ℤ, P'.IsStrictlyGE a ∧ P'.IsStrictlyLE b) ∧
      ∃ φ' : DerivedCategory.Q.obj P' ⟶ (smallEtaleDerivedModulePullback B S hS f).obj E,
        DerivedCategory.ApproximatesFrom φ' m := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  intro E φ hφ
  obtain ⟨a, b, ha, hb⟩ := hb
  have : (modulePullback B S hS f).Additive := modulePullback_additive f
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback f P b
    (fun j ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hP j))
  have hLE : ∀ (E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      (n : ℤ), E'.IsLE n → ((smallEtaleDerivedModulePullback B S hS f).obj E').IsLE n :=
    fun E' n hE' ↦ isLE_smallEtaleDerivedModulePullback_obj f E' n hE'
  refine ⟨((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    fun j ↦ IsRetractOfFiniteFree.map (F := modulePullback B S hS f)
      (modulePullbackUnitIso B S hS f) (hP j),
    ⟨a, b, ⟨fun i hi ↦ (modulePullback B S hS f).map_isZero (ha.isZero i hi)⟩,
      ⟨fun i hi ↦ (modulePullback B S hS f).map_isZero (hb.isZero i hi)⟩⟩,
    e.inv ≫ (smallEtaleDerivedModulePullback B S hS f).map φ, ?_⟩
  exact (approximatesFrom_of_isIso' e.inv m).comp
    (DerivedCategory.ApproximatesFrom.map (smallEtaleDerivedModulePullback B S hS f) hLE hφ)

/-- **Pseudo-coherence from an approximation by a strictly perfect complex, on an affine
represented space.** If `Φ(N) ∈ D(𝒪_{yoneda.obj U})` receives an approximation from `m` by a
strictly perfect complex, then `N ∈ D(R)` is `m`-pseudo-coherent. The strictly perfect complex is
`Φ` of a perfect object `N'` of `D(R)`, so the approximation is `Φ` of a morphism `N' ⟶ N`
(`Φ` is fully faithful); since `Φ` commutes with cohomology and the associated-module functor is
fully faithful, that morphism approximates `N` from `m`, and `N'`, being perfect, is
pseudo-coherent. -/
private theorem isPseudoCoherentFrom_of_approximatesFrom_associated (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P) (m : ℤ) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    ∀ (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
      (ψ : DerivedCategory.Q.obj P ⟶ (representedAffineDerivedAssociated B S hS U).obj N),
      DerivedCategory.ApproximatesFrom ψ m →
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom N m := by
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  intro N ψ hψ
  obtain ⟨N', a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ :=
    exists_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect (DerivedCategory.Q.obj P) P
      hP (Iso.refl _)
  let Φ := representedAffineDerivedAssociated B S hS U
  let Φ₀ := representedAffineAssociated B S hS U
  let hΦ := representedAffineDerivedAssociatedFullyFaithful B S hS U
  have := (representedAffineAssociatedFullyFaithful B S hS U).full
  have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  let β : DerivedCategory.Q.obj N' ⟶ N := hΦ.preimage (e.inv ≫ ψ)
  have hβΦ : DerivedCategory.ApproximatesFrom (Φ.map β) m := by
    rw [hΦ.map_preimage]
    exact (approximatesFrom_of_isIso' e.inv m).comp hψ
  -- `Φ` commutes with cohomology, and `Φ₀` is fully faithful
  have hH : ∀ j : ℤ, Arrow.mk ((DerivedCategory.homologyFunctor _ j).map (Φ.map β)) ≅
      Arrow.mk (Φ₀.map ((DerivedCategory.homologyFunctor _ j).map β)) := fun j ↦
    Arrow.isoMk ((Φ₀.mapDerivedCategoryHomologyIso j).app _)
      ((Φ₀.mapDerivedCategoryHomologyIso j).app _)
      ((Φ₀.mapDerivedCategoryHomologyIso j).hom.naturality β).symm
  have hβ : DerivedCategory.ApproximatesFrom β m := by
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · have : IsIso (Φ₀.map ((DerivedCategory.homologyFunctor _ j).map β)) :=
        ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (hH j)).1 (hβΦ.1 j hj)
      exact isIso_of_fully_faithful Φ₀ _
    · have : Epi (Φ₀.map ((DerivedCategory.homologyFunctor _ m).map β)) :=
        ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff (hH m)).1 hβΦ.2
      exact Φ₀.epi_of_epi_map this
  -- the perfect object `N'` is `m`-pseudo-coherent
  have hN' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj N') :=
    ⟨N', a, b, hGE, hLE, hfin, hproj, ⟨Iso.refl _⟩⟩
  obtain ⟨E, hE, γ, hγi, hγe⟩ := (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.1 hN').1 m
  have hc := DerivedCategory.ApproximatesFrom.comp (φ := γ) ⟨hγi, hγe⟩ hβ
  exact ⟨E, hE, γ ≫ β, hc.1, hc.2⟩

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- **The derived sections of an `m`-pseudo-coherent object of `D_QCoh` on an affine represented
space are `m`-pseudo-coherent** (Stacks 08E7 for algebraic spaces). With `E = Φ(K)`, `K = RΓ(E)`:
on a finite family of affine étale charts `U_i = Spec R_i` covering `U`, refining the coverings
on which `E` is approximated from `m` by bounded complexes of retracts of finite free modules, the
pullback of `Φ(K)` to `U_i` is `Φ_{R_i}` of the termwise base change `K ⊗_R R_i` (the ring maps
are flat), so every `K ⊗_R R_i` is `m`-pseudo-coherent; as `R → ∏ R_i` is faithfully flat, `K` is
`m`-pseudo-coherent (Stacks 068R). -/
private theorem isPseudoCoherentFrom_representedAffineDerivedSections_obj'
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (m : ℤ) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    ∀ (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U))),
      QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E →
      (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom E m →
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((representedAffineDerivedSections B S hS U).obj E) m := by
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  intro E hQ hE
  classical
  let Z : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hQ
  set K := (representedAffineDerivedSections B S hS U).obj E
  let ε : (representedAffineDerivedAssociated B S hS U).obj K ≅ E :=
    asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj K₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let T := representedAffineFinalChart B S hS U
  obtain ⟨R, hR, happ⟩ := exists_chart_approximation_of_isPseudoCoherentFrom B S hS (X := Z) E m
    hE T
  obtain ⟨n, V, φ, haff, hmem, -, hpre⟩ := SmallEtale.exists_finite_affine_etale_ofArrows_le
    B S hS (yoneda.obj U) (isAffineChart_representedAffineFinalChart B S hS U) hR
  let Ui : Fin n → BigFppfOver B S hS := fun i => (SmallEtale.toOver B S hS _).obj (V i)
  have hUi : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ui i)) := haff
  let g : ∀ i, Ui i ⟶ U := fun i => (SmallEtale.toOver B S hS _).map (φ i)
  let f : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj (Ui i), ⊤) := fun i =>
    (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map (g i))).hom
  have hloc : ∀ i, @StacksDraft.PseudoCoherence.IsPseudoCoherentFrom _ _ (_)
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj
        (((ModuleCat.extendScalars.{u, u, u} (f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀)) m := by
    intro i
    have := hUi i
    -- an approximation of the pullback of `E` to `V i`
    obtain ⟨W, h, k, hk, -⟩ := hmem i
    let := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj (Ui i))
      (isAlgebraicSpace_yoneda B S hS (Ui i)))
    let := HasDerivedCategory.standard
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj (Ui i), ⊤))
    let := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Z (V i))))
    let := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS Z W)))
    obtain ⟨P, hP, hb, ψ, hψi, hψe⟩ := happ k hk
    obtain ⟨P', hP', ⟨a', b', ha', hb'⟩, ψ', hψ'⟩ :=
      exists_approximation_pullback_of_approximation (chartMap B S hS Z h) m P hP hb _ ψ
        ⟨hψi, hψe⟩
    have hchart : chartToSpace B S hS Z (V i) = representedSpaceMap B S hS (g i) :=
      ObjectProperty.hom_ext _ ((CostructuredArrow.w (φ i).hom).symm.trans (Category.comp_id _))
    have het : IsEtale B S hS (chartToSpace B S hS Z (V i)).hom :=
      isEtale_chartToSpace B S hS Z (V i)
    let L : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
        Modules.{u, u} B S hS (yoneda.obj (Ui i)) (isAlgebraicSpace_yoneda B S hS (Ui i)) :=
      etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Z (V i)) het
    let Φ₀ := representedAffineAssociated B S hS U
    let Φᵢ := representedAffineAssociated B S hS (Ui i)
    let ext := ModuleCat.extendScalars.{u, u, u} (f i)
    have hflat : (f i).Flat := flat_chartRestrict_of_isAffine
      (hF := isAlgebraicSpace_yoneda B S hS U) (φ i)
      (isAffineChart_representedAffineFinalChart B S hS U) (haff i)
    have : ext.Additive := extendScalars_additive.{u, u} _
    have : PreservesFiniteLimits ext := extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
    have : PreservesColimitsOfSize.{u, u} ext :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (f i)).leftAdjoint_preservesColimits
    have : PreservesFiniteColimits ext := PreservesColimitsOfSize.preservesFiniteColimits ext
    have : L.Additive := etaleModulePullback_additive B S hS _ _
    have : PreservesFiniteLimits L := preservesFiniteLimits_etaleModulePullback B S hS _ _
    have : PreservesFiniteColimits L := preservesFiniteColimits_etaleModulePullback B S hS _ _
    have : Φᵢ.Additive := additive_representedAffineAssociated B S hS (Ui i)
    have : Φ₀.Additive := additive_representedAffineAssociated B S hS U
    have : (ext ⋙ Φᵢ).Additive := inferInstance
    have : (Φ₀ ⋙ L).Additive := inferInstance
    have het' : IsEtale B S hS (representedSpaceMap B S hS (g i)).hom := hchart ▸ het
    have hL : L = etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS (g i)) het' :=
      etaleModulePullback_congr B S hS _ _ hchart
    let bc : Φ₀ ⋙ L ≅ ext ⋙ Φᵢ :=
      eqToIso (by rw [hL]) ≪≫
        Functor.isoWhiskerLeft Φ₀ (modulePullbackIsoEtaleModulePullback B S hS
          (representedSpaceMap B S hS (g i)) het').symm ≪≫
        representedAffineAssociatedModulePullbackIso B S hS (g i)
    let a₁ : (representedAffineDerivedAssociated B S hS (Ui i)).obj
        (DerivedCategory.Q.obj ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) ≅
        DerivedCategory.Q.obj (((ext ⋙ Φᵢ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) :=
      (Φᵢ.mapDerivedCategoryFactors.app _) ≪≫ DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ Φᵢ))
          (ComplexShape.up ℤ)).app K₀)
    let a₂ : DerivedCategory.Q.obj (((ext ⋙ Φᵢ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
        DerivedCategory.Q.obj (((Φ₀ ⋙ L).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) :=
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex bc (ComplexShape.up ℤ)).symm.app K₀)
    let a₃ : DerivedCategory.Q.obj (((Φ₀ ⋙ L).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
        L.mapDerivedCategory.obj ((representedAffineDerivedAssociated B S hS U).obj
          (DerivedCategory.Q.obj K₀)) :=
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (Φ₀ ⋙ L))
          (ComplexShape.up ℤ)).app K₀).symm ≪≫
        (L.mapDerivedCategoryFactors.app _).symm ≪≫
        L.mapDerivedCategory.mapIso (Φ₀.mapDerivedCategoryFactors.app K₀).symm
    let a₄ : L.mapDerivedCategory.obj ((representedAffineDerivedAssociated B S hS U).obj
          (DerivedCategory.Q.obj K₀)) ≅ L.mapDerivedCategory.obj E :=
      L.mapDerivedCategory.mapIso ((representedAffineDerivedAssociated B S hS U).mapIso eK ≪≫ ε)
    let a₅ : L.mapDerivedCategory.obj E ≅
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Z (V i))).obj E :=
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS _ het).app E).symm
    let a₆ : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Z (V i))).obj E ≅
        (smallEtaleDerivedModulePullback B S hS (chartMap B S hS Z h)).obj
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Z W)).obj E) :=
      ((smallEtaleDerivedModulePullbackCongr B S hS
          (chartMap_comp_chartToSpace B S hS Z h)).app E).symm ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS Z h)
          (chartToSpace B S hS Z W)).app E).symm
    let e₁ := a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅ ≪≫ a₆
    exact isPseudoCoherentFrom_of_approximatesFrom_associated (Ui i) _
      (isStrictlyPerfect_of_isRetractOfFiniteFree _ P' hP' a' b' ha' hb') m _ (ψ' ≫ e₁.inv)
      (hψ'.comp_iso _ e₁.symm m)
  -- the product of the `R_i` is faithfully flat over `R`
  have hff := faithfullyFlat_pi_chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (isAffineChart_representedAffineFinalChart B S hS U) φ haff hpre
  have hφ : (RingHom.pi f).FaithfullyFlat := hff
  let S' : Fin n → Type u := fun j => Γ((BigFppfOver.toScheme B S hS).obj (Ui j), ⊤)
  exact (Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_of_faithfullyFlat_pi
    (S := S') f hφ K₀ m hloc).ofIso eK

/-- **A pseudo-coherent object on an affine represented space is the associated object of a
pseudo-coherent object of `D(R)`.** For `U` with affine underlying scheme of ring `R` and `M`
pseudo-coherent in `D(𝒪_{yoneda.obj U})`, `M` lies in `D_QCoh` (Stacks 08JL), so the counit
`Φ(RΓ(M)) ⟶ M` is invertible, and `RΓ(M)` is pseudo-coherent (Stacks 08E7 for algebraic
spaces). -/
private theorem exists_iso_representedAffineDerivedAssociated_of_isPseudoCoherent
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M : @DerivedCategory _ _ _ (HasDerivedCategory.standard (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (representedAlgebraicSpace B S hS U)))))
    (hM : letI := HasDerivedCategory.standard (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (representedAlgebraicSpace B S hS U).1 (representedAlgebraicSpace B S hS U).2).O));
        (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS U).1
          (representedAlgebraicSpace B S hS U).2).IsPseudoCoherent M) :
    ∃ m : @DerivedCategory _ _ _ (HasDerivedCategory.standard
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))),
      @StacksDraft.PseudoCoherence.IsPseudoCoherentIn _ _ (HasDerivedCategory.standard _) m ∧
      Nonempty ((representedAffineDerivedAssociated B S hS U).obj m ≅ M) := by
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  have hQ : QcohDerived B S hS (representedAlgebraicSpace B S hS U) M :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ M hM
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U M hQ
  refine ⟨(representedAffineDerivedSections B S hS U).obj M, ?_,
    ⟨asIso ((representedAffineDerivedAdjunction B S hS U).counit.app M)⟩⟩
  refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m ↦ ?_
  obtain ⟨K, hK, ⟨e⟩⟩ := hM
  exact isPseudoCoherentFrom_representedAffineDerivedSections_obj' U m M hQ ⟨K, hK m, ⟨e⟩⟩

end PseudoCoherent

section Step

attribute [local instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- An object of a derived category is isomorphic to its image under the comparison of a model
with itself. -/
private def modelEquivFunctorObjIso {C : Type*} [Category* C] [Abelian C]
    (h : HasDerivedCategory C) (X : @DerivedCategory C _ _ h) :
    (StacksDraft.DerivedModel.modelEquiv h h).functor.obj X ≅ X :=
  letI := h
  (StacksDraft.DerivedModel.modelEquiv h h).functor.mapIso
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
    (StacksDraft.DerivedModel.modelCompQIso h h).app (DerivedCategory.Q.objPreimage X) ≪≫
    DerivedCategory.Q.objObjPreimageIso X

variable (B S hS) in
/-- **The isomorphism step of Stacks 0DL7 on represented affine squares.** For a commutative square
of objects of the site with affine underlying schemes whose rings form a fibre product
`Γ(UW) = Γ(UY) ×_{Γ(UX)} Γ(UX')` along a surjection with nil kernel, and pseudo-coherent `M`, `K'`
on the represented spaces, every distinguished triangle on the glueing map of `(M, K', α)` has
first map with components adjoint to isomorphisms `Lj^* M' ≅ M` and `L(f')^* M' ≅ K'`. As in the
source, `M = Φ(m)` and `K' = Φ(k)` for pseudo-coherent `m`, `k` (Stacks 08JL, 08E7), and the
statement is the one on rings carried along `Φ`. -/
theorem pushoutGlueingIsIsoStepOnRepresentedAffine :
    PushoutGlueingIsIsoStepOnRepresentedAffine B S hS := by
  intro UX UX' UY UW _ _ _ _ gi gf gf' gj w hpb hsurj hnil M K' hM hK' α
  obtain ⟨m, hm, ⟨eM⟩⟩ := exists_iso_representedAffineDerivedAssociated_of_isPseudoCoherent UY M hM
  obtain ⟨k, hk, ⟨eK⟩⟩ :=
    exists_iso_representedAffineDerivedAssociated_of_isPseudoCoherent UX' K' hK'
  obtain ⟨t, ht⟩ := exists_representedAffineToposDerivedBaseChange_compat B S hS gf' gj gf gi w
  intro M' u v hT
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj UW, ⊤))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS
      (⟨yoneda.obj UW, isAlgebraicSpace_yoneda B S hS UW⟩ : AlgebraicSpaces B S hS)))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj UY, ⊤))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS
      (⟨yoneda.obj UY, isAlgebraicSpace_yoneda B S hS UY⟩ : AlgebraicSpaces B S hS)))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj UX', ⊤))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS
      (⟨yoneda.obj UX', isAlgebraicSpace_yoneda B S hS UX'⟩ : AlgebraicSpaces B S hS)))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj UX, ⊤))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS
      (⟨yoneda.obj UX, isAlgebraicSpace_yoneda B S hS UX⟩ : AlgebraicSpaces B S hS)))
  let : (smallEtaleStdModelEquiv
      (⟨yoneda.obj UW, isAlgebraicSpace_yoneda B S hS UW⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _)).functor.CommShift ℤ :=
    StacksDraft.Perfect.derivedEquivalenceCommShift _ _
  have : (smallEtaleStdModelEquiv
      (⟨yoneda.obj UW, isAlgebraicSpace_yoneda B S hS UW⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _)).functor.IsTriangulated :=
    StacksDraft.Perfect.derivedEquivalence_isTriangulated _ _
  have : (smallEtaleStdModelEquiv
      (⟨yoneda.obj UW, isAlgebraicSpace_yoneda B S hS UW⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _)).functor.Additive :=
    StacksDraft.DerivedModel.modelEquiv_functor_additive _ _
  let c₁ := RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
    (representedAffineCommRingCatHom B S hS gj).hom (representedAffineCommRingCatHom B S hS gf).hom
    (representedAffineCommRingCatHom B S hS (gf ≫ gj)).hom
    (representedAffineRingHom_comp B S hS gf gj).symm
  let c₂ := RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
    (representedAffineCommRingCatHom B S hS gf').hom
    (representedAffineCommRingCatHom B S hS gi).hom
    (representedAffineCommRingCatHom B S hS (gf ≫ gj)).hom
    (representedAffineRingHom_square B S hS gf' gj gf gi w)
  let σ₁ := smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS gf)
    (representedSpaceMap B S hS gj)
  let σ₂ := smallEtaleDerivedModulePullbackCongr B S hS
    (representedSpaceMap_square B S hS gf' gj gf gi w).symm
  let σ₃ := smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS gi)
    (representedSpaceMap B S hS gf')
  let θi₀ := representedAffineToposDerivedBaseChangeIso B S hS gi
  have hp := MilnorPatching.pasting_of_compat (representedAffineToposDerivedBaseChangeIso B S hS gj)
    (representedAffineToposDerivedBaseChangeIso B S hS gf)
    (representedAffineToposDerivedBaseChangeIso B S hS gf') θi₀ c₁ c₂ σ₁
    (smallEtaleDerivedModulePullbackSquareIso B S hS (representedSpaceMap B S hS gf')
      (representedSpaceMap B S hS gj) (representedSpaceMap B S hS gf)
      (representedSpaceMap B S hS gi) (representedSpaceMap_square B S hS gf' gj gf gi w)) σ₃
    (smallEtaleDerivedModulePullbackCongr B S hS (representedSpaceMap_square B S hS gf' gj gf gi w))
    rfl σ₂ (MilnorPatching.eqToIso_congrArg_symm (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
      (representedSpaceMap_square B S hS gf' gj gf gi w)).symm t ht
  have hgj : IsAffineHom B S hS (representedSpaceMap B S hS gj).hom :=
    isAffineHom_yoneda_map_of_isAffineHom gj inferInstance
  have hgf : IsAffineHom B S hS (representedSpaceMap B S hS gf).hom :=
    isAffineHom_yoneda_map_of_isAffineHom gf inferInstance
  have hgf' : IsAffineHom B S hS (representedSpaceMap B S hS gf').hom :=
    isAffineHom_yoneda_map_of_isAffineHom gf' inferInstance
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj UW) (isAlgebraicSpace_yoneda B S hS UW))
  let iΦ : (representedAffineToposDerivedAssociated B S hS UW).CommShift ℤ :=
    inferInstanceAs ((representedAffineDerivedAssociated B S hS UW).CommShift ℤ)
  have : (representedAffineToposDerivedAssociated B S hS UW).IsTriangulated :=
    inferInstanceAs ((representedAffineDerivedAssociated B S hS UW).IsTriangulated)
  have : (representedAffineToposDerivedAssociated B S hS UW).Additive :=
    inferInstanceAs ((representedAffineDerivedAssociated B S hS UW).Additive)
  refine MilnorPatching.isIso_homEquiv_symm_of_transport_models
    (smallEtaleStdModelEquiv
      (⟨yoneda.obj UW, isAlgebraicSpace_yoneda B S hS UW⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _))
    (smallEtaleStdModelEquiv
      (⟨yoneda.obj UY, isAlgebraicSpace_yoneda B S hS UY⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _))
    (smallEtaleStdModelEquiv
      (⟨yoneda.obj UX', isAlgebraicSpace_yoneda B S hS UX'⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _))
    (smallEtaleStdModelEquiv
      (⟨yoneda.obj UX, isAlgebraicSpace_yoneda B S hS UX⟩ : AlgebraicSpaces B S hS)
      (HasDerivedCategory.standard _))
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS gj).hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS gf').hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS gf).hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS gi).hom)
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS gj))
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS gf'))
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS gf))
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS gi))
    _ _ _ _ _ _ _ _ hp (fun M ↦ isIso_representedAffineTransportUnit B S hS gj hgj M)
    (fun K ↦ isIso_representedAffineTransportUnit B S hS gf' hgf' K)
    (fun N ↦ isIso_representedAffineTransportUnit B S hS gf hgf N)
    (representedAffineDerivedAdjunction B S hS UX).fullyFaithfulLOfIsIsoUnit
    m k (fun αr M'' u' v' hT' ↦
      @MilnorPatching.isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap_derivedExtension
        _ _ _ _ _ _ _ _ _ _ _ _
        (representedAffineCommRingCatHom B S hS gj).hom
        (representedAffineCommRingCatHom B S hS gf).hom
        (representedAffineCommRingCatHom B S hS gf').hom
        (representedAffineCommRingCatHom B S hS gi).hom
        (representedAffineCommRingCatHom B S hS (gf ≫ gj)).hom
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gj).hom).functor
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gj).hom).comparison
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gj).hom).isLeftDerived
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gf').hom).functor
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gf').hom).comparison
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gf').hom).isLeftDerived
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gf).hom).functor
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gf).hom).comparison
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gf).hom).isLeftDerived
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gi).hom).functor
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gi).hom).comparison
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS gi).hom).isLeftDerived
        (representedAffineRingHom_comp B S hS gf gj).symm
        (representedAffineRingHom_square B S hS gf' gj gf gi w) hpb hsurj hnil m hm k hk αr M''
        u' v' hT')
    (modelEquivFunctorObjIso (HasDerivedCategory.standard _) _ ≪≫ eM)
    (modelEquivFunctorObjIso (HasDerivedCategory.standard _) _ ≪≫ eK) α u v hT

end Step

section Registration

variable (B S hS) in
/-- **Stacks 0DL7.** Let `S` be a scheme and let
```
X  --i-->  X'
|          |
f          f'
v          v
Y  --j-->  Y'
```
be a pushout in the category of algebraic spaces over `S` as in Stacks 07VX, with `i` a
thickening and `f` affine. Then the essential image of the functor
`D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})`, `M' ↦ (Lj^* M', L(f')^* M', can)`, given by derived
pullback, contains every triple `(M, K', α)` with `M ∈ D(𝒪_Y)` and `K' ∈ D(𝒪_{X'})`
pseudo-coherent: for every isomorphism `α : Lf^* M ≅ Li^* K'` there are `M' ∈ D(𝒪_{Y'})` and
isomorphisms `a : Lj^* M' ≅ M` and `b : L(f')^* M' ≅ K'` with `Li^* b` equal to `α ∘ Lf^* a`
through the 2-cell `Lf^* Lj^* ≅ Li^* L(f')^*` (Stacks 0D6D). This holds at any models of the four
derived categories; the statement is `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`.

The proof is the source's: the fibre `M'` of the glueing map
`Rj_* M ⊕ Rf'_* K' ⟶ Rj_* Rf_* Li^* K'`
(`AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_derivedPushoutGlueingIsIso`), the
isomorphism step checked on the affine étale charts of `Y'`
(`AlgebraicGeometry.Space.derivedPushoutGlueingIsIso_of_onAffineChart`), where the base change
of the square is a represented affine square whose rings form a fibre product along a surjection
with nil kernel (`AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_representedAffine`), and
on which the step is the ring-level statement
(`MilnorPatching.isIso_homEquiv_symm_of_isPullback_of_distinguished_glueingMap_derivedExtension`)
carried to the algebraic spaces along the derived associated-module functors
(`AlgebraicGeometry.Space.pushoutGlueingIsIsoStepOnRepresentedAffine`). -/
@[stacks 0DL7]
theorem derivedPushoutEssentialImage :
    DerivedPushoutEssentialImage.{w₁, w₂, w₃, w₄, u} B S hS :=
  derivedPushoutEssentialImage_of_representedAffine.{w₁, w₂, w₃, w₄, u} B S hS
    (pushoutGlueingIsIsoStepOnRepresentedAffine B S hS)

end Registration

end AlgebraicGeometry.Space

end
