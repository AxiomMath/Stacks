module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedAboveGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartLocalPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation

/-!
# Pseudo-coherent objects on algebraic spaces: boundedness and étale restriction

Let `X` be an algebraic space and `E` an `m`-pseudo-coherent object of `D(𝒪_X)`. If `X` is
quasi-compact, the cohomology sheaves of `E` vanish in all large degrees: locally `E` is
approximated above `m` by a bounded complex, and finitely many such charts cover `|X|`.

## Main results

* `AlgebraicGeometry.Space.exists_isZero_homology_of_isPseudoCoherentFrom`: boundedness above
  on a quasi-compact algebraic space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u'

/-- The module form of Stacks 04M0 carries a direct summand of a finite free module on a slice to
a retract of a finite free module on the chart space, in the spelling of
`AlgebraicGeometry.Space.HasStrictlyPerfectModel`. -/
private theorem isRetractOfFiniteFree_sliceToChartModules_aux {B : BigFppfSite.{u'}}
    {S : Scheme.{u'}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (V : SmallEtale B S hS X.1) (M : SheafOfModules.{u'} ((structureRingSheaf B S hS X).over V))
    (hM : IsDirectSummandOfFiniteFree ((structureRingSheaf B S hS X).over V) M) :
    IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V)))
      ((sliceToChartModules V).obj M) := by
  let Fr := chartModuleSliceReindex B S hS X V
  have : PreservesFiniteLimits Fr := inferInstance
  have : Fr.Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryProducts Fr
    Functor.additive_of_preservesBinaryBiproducts Fr
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1 hM
  let O₁ := SheafOfModules.unit ((structureRingSheaf B S hS X).over V)
  let eb : SheafOfModules.free (R := (structureRingSheaf B S hS X).over V)
      (ULift.{u'} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
    (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u'} (Fin n) => O₁)).symm ≪≫
      (biproduct.isoCoproduct _).symm
  have hret : IsRetractOfFiniteFree O₁ M :=
    ⟨n, i ≫ eb.hom, eb.inv ≫ r, by simp [hir]⟩
  exact IsRetractOfFiniteFree.map (F := Fr)
    ((chartModuleRestrictionSliceIso B S hS X V).symm.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
      modulePullbackUnitIso B S hS (chartToSpace B S hS X V)) hret

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/-- **An `m`-pseudo-coherent object has strictly perfect approximations on an étale covering of
every chart**, read on the chart spaces: the converse of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_chart_approximation`. -/
private theorem exists_chart_approximation_of_isPseudoCoherentFrom_aux {B : BigFppfSite.{u'}}
    {S : Scheme.{u'}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u'} (ringedToposStructureRingSheaf B S hS X))) (m : ℤ)
    (hE : RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2) E m)
    (U : SmallEtale B S hS X.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
        ∃ P : CochainComplex (SheafOfModules.{u'}
            (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ,
          (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
            (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (P.X j)) ∧
          (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
          ∃ φ : (DerivedCategory.Q).obj P ⟶
              (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E,
            (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
            Epi ((DerivedCategory.homologyFunctor _ m).map φ) := by
  obtain ⟨E', hE', ⟨eE⟩⟩ := hE
  obtain ⟨R, hR, hP⟩ := hE' U
  refine ⟨R, hR, fun V g hg ↦ ?_⟩
  obtain ⟨P, ⟨hbd, hterm⟩, α, hαi, hαe⟩ := hP g hg
  have : HasSheafify ((SmallEtale.topology B S hS X.1).over V) AddCommGrpCat.{u'} :=
    SmallEtale.instHasSheafifyOver B S hS X.1 _ V
  have : ((SmallEtale.topology B S hS X.1).over V).WEqualsLocallyBijective AddCommGrpCat.{u'} :=
    SmallEtale.instWEqualsLocallyBijectiveOver B S hS X.1 _ V
  have : HasSheafify (SmallEtale.topology B S hS (chartSpace B S hS X V).1) AddCommGrpCat.{u'} :=
    SmallEtale.instHasSheafify B S hS _ _
  have : (SmallEtale.topology B S hS (chartSpace B S hS X V).1).WEqualsLocallyBijective
      AddCommGrpCat.{u'} :=
    SmallEtale.instWEqualsLocallyBijective B S hS _ _
  let E₀ : CochainComplex (SheafOfModules.{u'} (ringedToposStructureRingSheaf B S hS X)) ℤ := E'
  have eE₀ : (DerivedCategory.Q).obj E₀ ≅ E := eE
  let O := SheafOfModules.overFunctor.{u'} (structureRingSheaf B S hS X) V
  let P₀ : CochainComplex (SheafOfModules.{u'} ((structureRingSheaf B S hS X).over V)) ℤ := P
  let α₀ : P₀ ⟶ (O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀ := α
  let Fr' := sliceToChartModules (B := B) (S := S) (hS := hS) (X := X) V
  have : PreservesFiniteLimits Fr' := inferInstance
  have : PreservesFiniteColimits Fr' := inferInstance
  let P'' := (Fr'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  have e1 : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E₀) :=
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).mapIso eE₀.symm ≪≫
      smallEtaleDerivedModulePullbackObjQIsoOfIsEtale _ (isEtale_chartToSpace B S hS X V) E₀
  have e2 : ((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E₀ ≅
      (Fr'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (chartModuleRestrictionSliceIso B S hS X V).app (E₀.X i))
      (fun i j _ ↦ ((chartModuleRestrictionSliceIso B S hS X V).hom.naturality (E₀.d i j)).symm)
  let β := (DerivedCategory.Q).map α₀
  have hβi : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β) := fun j hj =>
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ j) α₀).2 (hαi j hj)
  have hβe : Epi ((DerivedCategory.homologyFunctor _ m).map β) :=
    (RingedSite.epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ m) α₀).2 hαe
  let eT : Fr'.mapDerivedCategory.obj ((DerivedCategory.Q).obj
      ((O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀)) ≅
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E :=
    Fr'.mapDerivedCategoryFactors.app _ ≪≫ (DerivedCategory.Q).mapIso e2.symm ≪≫ e1.symm
  let φ : (DerivedCategory.Q).obj P'' ⟶
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E :=
    (Fr'.mapDerivedCategoryFactors.app P₀).inv ≫ Fr'.mapDerivedCategory.map β ≫ eT.hom
  have hA : DerivedCategory.ApproximatesFrom (Fr'.mapDerivedCategory.map β) m :=
    ⟨fun j hj ↦ have := hβi j hj
      (Fr'.isIso_homologyFunctor_map_mapDerivedCategory_map_iff β j).2 (Functor.map_isIso Fr' _),
      (RingedSite.epi_map_iff_of_natIso (Fr'.mapDerivedCategoryHomologyIso m) β).2
        (Fr'.map_epi _)⟩
  have hφ : DerivedCategory.ApproximatesFrom φ m :=
    (DerivedCategory.approximatesFrom_iso_comp_iff
      (Fr'.mapDerivedCategoryFactors.app P₀).symm _ m).2
      ((DerivedCategory.approximatesFrom_comp_iso_iff _ eT m).2 hA)
  refine ⟨P'', fun j ↦ isRetractOfFiniteFree_sliceToChartModules_aux V _ (hterm j), ?_, φ,
    hφ.1, hφ.2⟩
  obtain ⟨b, hb⟩ := hbd.bddAbove
  obtain ⟨a, ha⟩ := hbd.bddBelow
  exact ⟨a, b, (CochainComplex.isStrictlyGE_iff P'' a).2 fun i hi ↦
      Fr'.map_isZero (not_not.1 fun h ↦ absurd (ha h) (by omega)),
    (CochainComplex.isStrictlyLE_iff P'' b).2 fun i hi ↦
      Fr'.map_isZero (not_not.1 fun h ↦ absurd (hb h) (by omega))⟩


end AlgebraicGeometry.Space

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf of modules restricting to zero on the slice at a chart `V` has empty support over the
image of `V`. -/
theorem supportOfSheaf_inter_range_eq_empty_of_isZero_over (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (hM : IsZero (M.over (V : (smallEtaleRingedSite B S hS X.1 X.2).C))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ∩
      Set.range (pointsMap B S hS _ (chartToSpace B S hS X V).hom) = ∅ := by
  have h0 : IsZero ((etaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj M) := by
    refine (isZero_etaleModulePullback_chartToSpace_iff B S hS X V M).2 fun W g => ?_
    have hz := (SheafOfModules.evaluation _ (op (Over.mk g))).map_isZero hM
    exact ModuleCat.subsingleton_of_isZero hz
  have hempty := (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X V) _).2 h0
  rw [supportOfSheaf_chartToSpace] at hempty
  refine Set.eq_empty_of_forall_notMem fun x ⟨hx, y, hy⟩ => ?_
  subst hy
  exact (Set.eq_empty_iff_forall_notMem.mp hempty) y hx

/-- **An `m`-pseudo-coherent object on a quasi-compact algebraic space is bounded above**: its
cohomology sheaves vanish in all sufficiently large degrees. -/
theorem exists_isZero_homology_of_isPseudoCoherentFrom (X : AlgebraicSpaces B S hS)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m) :
    ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) j).obj E) := by
  classical
  let := pointTopology B S hS X.1
  have := compactSpace_points_of_isQuasiCompactSpace B S hS X.2 hX
  obtain ⟨U₀, a, ha_surj, ha_et⟩ := X.2.exists_atlas
  let C₀ : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, ha_et⟩
  obtain ⟨R, hR, hbd⟩ := RingedSite.exists_local_isZero_homology_gt_general
    (smallEtaleRingedSite B S hS X.1 X.2) E m hE (C₀ : (smallEtaleRingedSite B S hS X.1 X.2).C)
  let I := Σ V : SmallEtale B S hS X.1, {h : V ⟶ C₀ // R h}
  let O : I → Set (points B S hS X.1) := fun i =>
    Set.range (pointsMap B S hS _ (chartToSpace B S hS X i.1).hom)
  have hO : ∀ i, IsOpen (O i) := fun i =>
    let := pointTopology B S hS (yoneda.obj i.1.1.left)
    (isOpenMap_pointsMap_of_isEtale B S hS _ (isAlgebraicSpace_yoneda B S hS _) X.2
      ((isEtale_iff_presheaf_of_yoneda B S hS _).2 i.1.2)).isOpen_range
  have hcov : Set.univ ⊆ ⋃ i, O i := by
    intro x _
    obtain ⟨u, rfl⟩ := (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U₀ a).1 ha_surj x
    obtain ⟨V, g, hg, w, hw⟩ := (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 _).1 hR
      (pointsToScheme B S hS U₀ u)
    obtain ⟨V', k, h, hh, rfl⟩ := hg
    let V'' : SmallEtale B S hS X.1 := V'
    let h' : V'' ⟶ C₀ := h
    let k' : V ⟶ V'' := k
    obtain ⟨w', rfl⟩ := surjective_pointsToScheme B S hS _ w
    refine Set.mem_iUnion.2 ⟨⟨V'', h', hh⟩, pointsMap B S hS _ (yoneda.map
      ((SmallEtale.toOver B S hS X.1).map k')) w', ?_⟩
    have hu : pointsMap B S hS _ (yoneda.map ((SmallEtale.toOver B S hS X.1).map (k' ≫ h'))) w' =
        u := by
      refine injective_pointsToScheme B S hS U₀ ?_
      rw [pointsToScheme_pointsMap_yoneda]
      exact hw
    have hV : V''.1.hom = yoneda.map ((SmallEtale.toOver B S hS X.1).map h') ≫ a :=
      (CostructuredArrow.w h'.hom).symm
    rw [← hu]
    have e1 := congrFun (pointsMap_comp B S hS _ (yoneda.map
      ((SmallEtale.toOver B S hS X.1).map k')) V''.1.hom) w'
    have e2 := congrFun (pointsMap_comp B S hS _ (yoneda.map
      ((SmallEtale.toOver B S hS X.1).map (k' ≫ h'))) a) w'
    show pointsMap B S hS _ V''.1.hom _ = _
    refine e1.symm.trans (Eq.trans ?_ e2)
    rw [hV, Functor.map_comp, Functor.map_comp, Category.assoc]
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  choose b hb using fun i : I => hbd i.2.1 i.2.2
  refine ⟨∑ i ∈ F, |b i|, fun j hj => ?_⟩
  refine isZero_of_supportOfSheaf_eq_empty B S hS X _ ?_
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  have hbi : b i < j := by
    have h1 : |b i| ≤ ∑ i ∈ F, |b i| :=
      Finset.single_le_sum (f := fun i => |b i|) (fun _ _ => abs_nonneg _) hi
    have h2 := le_abs_self (b i)
    omega
  have hz := hb i j hbi
  have := supportOfSheaf_inter_range_eq_empty_of_isZero_over B S hS X _ i.1 hz
  exact (Set.eq_empty_iff_forall_notMem.mp this) x ⟨hx, hxi⟩



/-- **An `m`-pseudo-coherent object has strictly perfect approximations on an étale covering of
every chart**, read on the chart spaces: the converse of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_chart_approximation`. -/
theorem exists_chart_approximation_of_isPseudoCoherentFrom {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (m : ℤ)
    (hE : RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2) E m)
    (U : SmallEtale B S hS X.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
        ∃ P : CochainComplex (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ,
          (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
            (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (P.X j)) ∧
          (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
          ∃ φ : (DerivedCategory.Q).obj P ⟶
              (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E,
            (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
            Epi ((DerivedCategory.homologyFunctor _ m).map φ) :=
  exists_chart_approximation_of_isPseudoCoherentFrom_aux E m hE U

/-- Composing an approximation from `m` with an isomorphism of the target is an approximation
from `m`. -/
theorem _root_.DerivedCategory.ApproximatesFrom.comp_iso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {P K K' : DerivedCategory C} (φ : P ⟶ K) (e : K ≅ K') (m : ℤ)
    (h : DerivedCategory.ApproximatesFrom φ m) :
    DerivedCategory.ApproximatesFrom (φ ≫ e.hom) m := by
  exact (DerivedCategory.approximatesFrom_comp_iso_iff φ e m).2 h

/-- **Étale restriction preserves `m`-pseudo-coherence**: for `f : X ⟶ Y` étale and `E`
`m`-pseudo-coherent in `D(𝒪_Y)`, the restriction `E|_X` is `m`-pseudo-coherent. A chart of `X`
is a chart of `Y`, and the strictly perfect approximations of `E` on a covering of that chart of
`Y` are approximations of `E|_X` on the corresponding covering of the chart of `X`. -/
theorem isPseudoCoherentFrom_etaleRestrict {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom E m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom
      ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E) m := by
  refine RingedSite.isPseudoCoherentFrom_of_iso _ m ?_
    ((smallEtaleDerivedModulePullbackIsoEtale B S hS f hf).app E).symm
  refine isPseudoCoherentFrom_of_chart_approximation _ m fun U => ?_
  let U' := (smallEtalePostcomp B S hS f hf).obj U
  obtain ⟨R', hR', happ⟩ := exists_chart_approximation_of_isPseudoCoherentFrom B S hS E m hE U'
  refine ⟨fun V _ => ∃ P : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ,
    (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (P.X j)) ∧
    (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
    ∃ φ : (DerivedCategory.Q).obj P ⟶ (smallEtaleDerivedModulePullback B S hS
        (chartToSpace B S hS X V)).obj ((smallEtaleDerivedModulePullback B S hS f).obj E),
      (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map φ), ?_, fun V g hg => hg⟩
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro z
  obtain ⟨W', m₁, ⟨W'', m', m'', hm'', rfl⟩, w', hw'⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS Y.1 _).1 hR' z
  have hm''w : yoneda.map ((SmallEtale.toOver B S hS Y.1).map m'') ≫ U.1.hom ≫ f.hom =
      W''.1.hom := CostructuredArrow.w m''.hom
  let q : W''.1.left ⟶ U.1.left := (SmallEtale.toOver B S hS Y.1).map m''
  have hWx : IsEtaleChart B S hS X.1 (CostructuredArrow.mk (yoneda.map q ≫ U.1.hom)) :=
    etale_comp_of_scheme B S hS q U.1.hom (etale_toScheme_toOver_map B S hS Y.1 m'') U.2
  let Wx : SmallEtale B S hS X.1 := ⟨_, hWx⟩
  let gx : Wx ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk q rfl)
  have hc : chartToSpace B S hS X Wx ≫ f = chartToSpace B S hS Y W'' := by
    refine ObjectProperty.hom_ext _ ?_
    show (yoneda.map q ≫ U.1.hom) ≫ f.hom = W''.1.hom
    rw [Category.assoc]
    exact hm''w
  refine ⟨Wx, gx, Sieve.le_generate _ _ _ ?_, ?_⟩
  · obtain ⟨P, hP, hb, φ, hiso, hepi⟩ := happ m'' hm''
    let e : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W'')).obj E ≅
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X Wx)).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
      (smallEtaleDerivedModulePullbackCongr B S hS hc).symm.app E ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS X Wx) f).app E).symm
    obtain ⟨h1, h2⟩ := DerivedCategory.ApproximatesFrom.comp_iso φ e m ⟨hiso, hepi⟩
    exact ⟨P, hP, hb, φ ≫ e.hom, h1, h2⟩
  · refine ⟨(BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y.1).map m') w', ?_⟩
    rw [← hw', Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply]
    rfl

end AlgebraicGeometry.Space

end
