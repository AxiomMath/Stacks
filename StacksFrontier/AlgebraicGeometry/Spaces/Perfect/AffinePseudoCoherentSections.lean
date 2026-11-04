module

public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.PseudoCoherentIffCoherentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded

/-!
# The sections of a pseudo-coherent object on an affine algebraic space are pseudo-coherent

Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring of
global functions `R`, and let `E` be an object of `D_QCoh(𝒪_{yoneda.obj U})` which is
`m`-pseudo-coherent. Then `RΓ(E)` is an `m`-pseudo-coherent object of `D(R)`.

Choose a finite étale covering of `U` by affine charts `U_i = Spec R_i` on which `E` is
approximated from `m` by a bounded complex of retracts of finite free modules. On `U_i` the
approximation is carried by `RΓ` to an approximation of `RΓ(U_i, E) = RΓ(E) ⊗^L_R R_i` by a
perfect object, so every `RΓ(E) ⊗^L_R R_i` is `m`-pseudo-coherent, and `R → ∏ R_i` is faithfully
flat (Stacks 068R).

## Main results

* `AlgebraicGeometry.Space.exists_approximation_smallEtaleDerivedModulePullback`: approximations
  by bounded complexes of retracts of finite free modules pull back.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedAffineDerivedSections_obj`: `RΓ(E)`
  is `m`-pseudo-coherent.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_iff_forall_isAffineChart`: `m`-pseudo-coherence
  of an object of `D_QCoh` is `m`-pseudo-coherence of its derived sections on the affine charts.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 068R](https://stacks.math.columbia.edu/tag/068R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An isomorphism approximates its target from every `m`. -/
private theorem _root_.DerivedCategory.ApproximatesFrom.of_isIso {C : Type*} [Category* C]
    [Abelian C] [HasDerivedCategory C] {K K' : DerivedCategory C} (f : K ⟶ K') [IsIso f] (m : ℤ) :
    DerivedCategory.ApproximatesFrom f m :=
  ⟨fun _ _ => inferInstance, inferInstance⟩

/-- **Approximations pull back.** If `φ : P ⟶ E` approximates `E ∈ D(𝒪_Y)` from `m`, with `P` a
bounded complex of retracts of finite free modules, then `Lf^*E` is approximated from `m` by the
degreewise pullback of `P`, again a bounded complex of retracts of finite free modules. -/
theorem exists_approximation_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (m : ℤ) (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))
      (P.X j))
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (φ : DerivedCategory.Q.obj P ⟶ E) (hφ : DerivedCategory.ApproximatesFrom φ m) :
    ∃ P' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ,
      (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))
        (P'.X j)) ∧
      (∃ a b : ℤ, P'.IsStrictlyGE a ∧ P'.IsStrictlyLE b) ∧
      ∃ φ' : DerivedCategory.Q.obj P' ⟶ (smallEtaleDerivedModulePullback B S hS f).obj E,
        DerivedCategory.ApproximatesFrom φ' m := by
  obtain ⟨a, b, ha, hb⟩ := hb
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  have : G.Additive := modulePullback_additive f
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback f P b
    (fun i ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hP i))
  exact ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    fun j ↦ IsRetractOfFiniteFree.map (F := modulePullback B S hS f)
      (modulePullbackUnitIso B S hS f) (hP j), ⟨a, b, inferInstance, inferInstance⟩,
    e'.inv ≫ (smallEtaleDerivedModulePullback B S hS f).map φ,
    (DerivedCategory.ApproximatesFrom.of_isIso e'.inv m).comp
    (DerivedCategory.ApproximatesFrom.map (smallEtaleDerivedModulePullback B S hS f)
      (fun E n hE => isLE_smallEtaleDerivedModulePullback_obj f E n hE) hφ)⟩

section Affine

variable (B S hS) (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **An approximation by a strictly perfect complex on an affine algebraic space.** If
`Φ(M) ∈ D(𝒪_{yoneda.obj U})` is approximated from `m` by a strictly perfect complex, then
`M ∈ D(R)` is `m`-pseudo-coherent: the strictly perfect complex is `Φ` of a perfect object of
`D(R)`, `Φ` is fully faithful, and `Φ` is exact and faithful on modules, so it reflects
isomorphisms and surjections on cohomology. -/
theorem isPseudoCoherentFrom_of_approximatesFrom_representedAffineDerivedAssociated
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P)
    (m : ℤ) (ψ : DerivedCategory.Q.obj P ⟶ (representedAffineDerivedAssociated B S hS U).obj M)
    (hψ : DerivedCategory.ApproximatesFrom ψ m) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom M m := by
  obtain ⟨N, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ :=
    exists_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect (DerivedCategory.Q.obj P) P
      hP (Iso.refl _)
  let Φ₀ := representedAffineAssociated B S hS U
  have hff : (representedAffineDerivedAssociated B S hS U).FullyFaithful :=
    (representedAffineDerivedAdjunction B S hS U).fullyFaithfulLOfIsIsoUnit
  have := (representedAffineAssociatedFullyFaithful B S hS U).full
  have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  let α := hff.preimage (e.inv ≫ ψ)
  have hα' : DerivedCategory.ApproximatesFrom
      ((representedAffineDerivedAssociated B S hS U).map α) m := by
    rw [hff.map_preimage]
    exact (DerivedCategory.ApproximatesFrom.of_isIso e.inv m).comp hψ
  have key : ∀ j : ℤ, Arrow.mk ((DerivedCategory.homologyFunctor _ j).map
      ((representedAffineDerivedAssociated B S hS U).map α)) ≅
      Arrow.mk (Φ₀.map ((DerivedCategory.homologyFunctor _ j).map α)) := fun j =>
    Arrow.isoMk ((Φ₀.mapDerivedCategoryHomologyIso j).app _)
      ((Φ₀.mapDerivedCategoryHomologyIso j).app _)
      ((Φ₀.mapDerivedCategoryHomologyIso j).hom.naturality α).symm
  have hα : DerivedCategory.ApproximatesFrom α m := by
    refine ⟨fun j hj => ?_, ?_⟩
    · have : IsIso (Φ₀.map ((DerivedCategory.homologyFunctor _ j).map α)) :=
        ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (key j)).1 (hα'.1 j hj)
      exact isIso_of_fully_faithful Φ₀ _
    · exact Φ₀.epi_of_epi_map
        (((MorphismProperty.epimorphisms _).arrow_mk_iso_iff (key m)).1 hα'.2)
  have hNperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj N) :=
    ⟨N, a, b, hGE, hLE, hfin, hproj, ⟨Iso.refl _⟩⟩
  obtain ⟨E, hE, β, hβi, hβe⟩ := (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.1 hNperf).1 m
  have hc := DerivedCategory.ApproximatesFrom.comp (φ := β) ⟨hβi, hβe⟩ hα
  exact ⟨E, hE, β ≫ α, hc.1, hc.2⟩

/-- **Pseudo-coherence of the derived sections after an affine étale base change.** If the
pullback of `E ∈ D_QCoh(𝒪_{yoneda.obj U})` to an affine chart `V` of `U` is approximated from `m`
by a bounded complex of retracts of finite free modules, then `RΓ(E) ⊗_R Γ(V, 𝒪_V)` is
`m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_extendScalars_representedAffineDerivedSections_of_approximation
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hQ : QcohDerived B S hS (schemeSpace U) E) (m : ℤ) {V : SmallEtale B S hS (yoneda.obj U)}
    (φ : V ⟶ representedAffineFinalChart B S hS U)
    [hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj V))]
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (chartSpace B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ V))) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
      (chartSpace B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ V))) (P.X j))
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (ψ : DerivedCategory.Q.obj P ⟶ (smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ V)).obj E)
    (hψ : DerivedCategory.ApproximatesFrom ψ m) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS _).map φ))).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage
          ((representedAffineDerivedSections B S hS U).obj E)))) m := by
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hQ
  let K := (representedAffineDerivedSections B S hS U).obj E
  let K₀ := DerivedCategory.Q.objPreimage K
  let g : (SmallEtale.toOver B S hS _).obj V ⟶ U := (SmallEtale.toOver B S hS _).map φ
  let f := (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g)).hom
  have hflat : f.Flat := flat_chartRestrict_of_isAffine
    (hF := isAlgebraicSpace_yoneda B S hS U)
    φ (isAffineChart_representedAffineFinalChart B S hS U) hV
  have hchart : chartToSpace B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ V =
      representedSpaceMap B S hS g :=
    ObjectProperty.hom_ext _ ((CostructuredArrow.w φ.hom).symm.trans (Category.comp_id _))
  let e := (smallEtaleDerivedModulePullbackCongr B S hS hchart).app E ≪≫
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso
      ((asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)).symm ≪≫
        (representedAffineDerivedAssociated B S hS U).mapIso
          (DerivedCategory.Q.objObjPreimageIso K).symm) ≪≫
    (representedAffineDerivedBaseChangeIso B S hS g).app (DerivedCategory.Q.obj K₀) ≪≫
    (representedAffineDerivedAssociated B S hS _).mapIso
      ((RingTheory.TorIndependence.flatDerivedExtensionScalarsIso f hflat).app
        (DerivedCategory.Q.obj K₀) ≪≫
        let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
        (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors.app K₀)
  exact isPseudoCoherentFrom_of_approximatesFrom_representedAffineDerivedAssociated B S hS _
    _ P (isStrictlyPerfect_of_isRetractOfFiniteFree _ P hP a b ha hb) m (ψ ≫ e.hom)
    (DerivedCategory.ApproximatesFrom.comp_iso ψ e m hψ)

/-- **The derived sections of an `m`-pseudo-coherent object on an affine represented algebraic
space are `m`-pseudo-coherent.** If `E ∈ D_QCoh(𝒪_{yoneda.obj U})` is `m`-pseudo-coherent and
`U` has affine underlying scheme `Spec R`, then `RΓ(E)` is an `m`-pseudo-coherent object of
`D(R)`. -/
theorem isPseudoCoherentFrom_representedAffineDerivedSections_obj
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hQ : QcohDerived B S hS (schemeSpace U) E) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom E m) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((representedAffineDerivedSections B S hS U).obj E) m := by
  classical
  set K := (representedAffineDerivedSections B S hS U).obj E
  let K₀ := DerivedCategory.Q.objPreimage K
  let X₀ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  obtain ⟨R, hR, happ⟩ := exists_chart_approximation_of_isPseudoCoherentFrom B S hS (X := X₀) E m hE
    (representedAffineFinalChart B S hS U)
  obtain ⟨n, V, φ, haff, hmem, -, hpre⟩ := SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS
    (yoneda.obj U) (isAffineChart_representedAffineFinalChart B S hS U) hR
  let Ui : Fin n → BigFppfOver B S hS := fun i => (SmallEtale.toOver B S hS _).obj (V i)
  let f : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj (Ui i), ⊤) := fun i =>
    (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS _).map (φ i)))).hom
  have hloc : ∀ i, StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀)) m := by
    intro i
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS _).obj (V i))) :=
      haff i
    obtain ⟨W, h, k, hk, -⟩ := hmem i
    obtain ⟨P, hP, hb, ψ, hψi, hψe⟩ := happ k hk
    obtain ⟨P', hP', ⟨a', b', ha', hb'⟩, ψ', hψ'⟩ :=
      exists_approximation_smallEtaleDerivedModulePullback
        (chartMap B S hS X₀ h) _ m P hP hb ψ ⟨hψi, hψe⟩
    let e := (smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS X₀ h)
        (chartToSpace B S hS X₀ W)).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (chartMap_comp_chartToSpace B S hS X₀ h)).app E
    exact isPseudoCoherentFrom_extendScalars_representedAffineDerivedSections_of_approximation
      B S hS U E hQ m (φ i) P' hP' a' b' ha' hb' (ψ' ≫ e.hom)
      (DerivedCategory.ApproximatesFrom.comp_iso ψ' e m hψ')
  have hφ : (RingHom.pi f).FaithfullyFlat := faithfullyFlat_pi_chartRing B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) (isAffineChart_representedAffineFinalChart B S hS U) φ
    haff hpre
  let S' : Fin n → Type u := fun j => Γ((BigFppfOver.toScheme B S hS).obj (Ui j), ⊤)
  exact (Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_of_faithfullyFlat_pi
    (S := S') f hφ K₀ m hloc).ofIso (DerivedCategory.Q.objObjPreimageIso K)

/-- **On an affine represented algebraic space, `m`-pseudo-coherence of an object of `D_QCoh` is
`m`-pseudo-coherence of its derived sections.** A global approximation of `E` comes from one of
`RΓ(E)` and restricts to every chart. -/
theorem isPseudoCoherentFrom_iff_representedAffineDerivedSections
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hQ : QcohDerived B S hS (schemeSpace U) E) (m : ℤ) :
    (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom E m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((representedAffineDerivedSections B S hS U).obj E) m := by
  refine ⟨isPseudoCoherentFrom_representedAffineDerivedSections_obj B S hS U E hQ m,
    fun h => ?_⟩
  obtain ⟨P, hP, hb, ψ, hψi, hψe⟩ :=
    exists_approximation_of_isPseudoCoherentFrom_representedAffineDerivedSections B S hS U E hQ m h
  refine isPseudoCoherentFrom_of_chart_approximation
    (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) E m fun V =>
      ⟨fun _ _ => True, ?_, fun W _ _ => exists_approximation_smallEtaleDerivedModulePullback
        (chartToSpace B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ W) E m P hP hb ψ
        ⟨hψi, hψe⟩⟩
  rw [show Sieve.generate (fun (W : SmallEtale B S hS (yoneda.obj U)) (_ : W ⟶ V) => True) = ⊤
    from top_unique fun W g _ => Sieve.le_generate _ _ g trivial]
  exact (SmallEtale.topology B S hS (yoneda.obj U)).top_mem V

end Affine

/-- **`m`-pseudo-coherence of an object of `D_QCoh` is read on the derived sections over the
affine étale charts** (Stacks 08E7 for algebraic spaces): `E ∈ D_QCoh(𝒪_X)` is
`m`-pseudo-coherent exactly when `RΓ(W, E|_W)` is an `m`-pseudo-coherent object of
`D(Γ(W, 𝒪_W))` for every affine étale chart `W` of `X`. -/
theorem isPseudoCoherentFrom_iff_forall_isAffineChart (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E)
    (m : ℤ) :
    RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2) E m ↔
      ∀ (W : SmallEtale B S hS X.1) (hW : IsAffineChart B S hS X.1 W),
        haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj W)) := hW
        StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
          ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj W)).obj
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X W)).obj E)) m := by
  refine ⟨fun h W hW => ?_, fun h => ?_⟩
  · have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj W)) := hW
    exact isPseudoCoherentFrom_representedAffineDerivedSections_obj B S hS _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X W) E hE) m
      (isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general (chartToSpace B S hS X W) E m h)
  · refine isPseudoCoherentFrom_of_chart_approximation E m fun U =>
      ⟨fun W _ => IsAffineChart B S hS X.1 W, generate_isAffineChart_mem_topology B S hS X U,
        fun W g hW => ?_⟩
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X.1).obj W)) := hW
    exact exists_approximation_of_isPseudoCoherentFrom_representedAffineDerivedSections B S hS _
      _ (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
        (chartToSpace B S hS X W) E hE) m
      (h W hW)

end AlgebraicGeometry.Space

end
