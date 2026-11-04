module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.CategoryTheory.Preadditive.RetractsOfFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects

/-!
# The derived pullback along an étale morphism, and perfect objects on charts

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces. Pullback of modules along `f` is
exact, so `Lf^*` is computed on every complex by degreewise pullback, and the cohomology sheaves
of `Lf^*K` are the pullbacks of those of `K`. A perfect object of `D(𝒪_X)` is, on an étale
covering of every étale chart `U` of `X`, isomorphic to a bounded complex of retracts of finite
free modules, read in the model of `𝒪`-modules on the small étale site of each chart.

## Main definitions

* `AlgebraicGeometry.Space.HasStrictlyPerfectModel`: an object of `D(𝒪_Y)` isomorphic to a
  bounded complex of retracts of finite free `𝒪_Y`-modules.

## Main results

* `AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_of_isEtale`:
  `Lf^*K = f^*K` for `f` étale and every complex `K`.
* `AlgebraicGeometry.Space.nonempty_homology_smallEtaleDerivedModulePullback_obj_iso_of_isEtale`:
  `H^j(Lf^*K) = f^*H^j(K)` for `f` étale.
* `AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback`:
  `Lf^*K = f^*K` for a bounded above complex of flat modules, with `f^* = modulePullback f`.
* `AlgebraicGeometry.Space.HasStrictlyPerfectModel.smallEtaleDerivedModulePullback_obj` and
  `AlgebraicGeometry.Space.HasStrictlyPerfectModel.chartRestriction`: strictly perfect models
  pull back along every morphism, in particular along morphisms of charts.
* `AlgebraicGeometry.Space.exists_hasStrictlyPerfectModel_chart_of_isPerfect`: a perfect object
  has strictly perfect models on the members of an étale covering of every chart.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- For `f` étale, `Lf^*` of a complex is its degreewise pullback. -/
def smallEtaleDerivedModulePullbackObjQIsoOfIsEtale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.Q).obj K) ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  haveI := etaleModulePullback_additive B S hS f hf
  haveI := preservesFiniteLimits_etaleModulePullback B S hS f hf
  haveI := preservesFiniteColimits_etaleModulePullback B S hS f hf
  (smallEtaleDerivedModulePullbackIsoEtale B S hS f hf).app _ ≪≫
    (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryFactors.app K ≪≫
    (DerivedCategory.Q).mapIso ((NatIso.mapHomologicalComplex
      (modulePullbackIsoEtaleModulePullback B S hS f hf).symm (ComplexShape.up ℤ)).app K)

/-- For `f` étale, `Lf^*` of every complex is its degreewise pullback. -/
theorem nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_of_isEtale (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.Q).obj K) ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  ⟨smallEtaleDerivedModulePullbackObjQIsoOfIsEtale f hf K⟩

/-- For `f` étale, the cohomology sheaves of `Lf^*K` are the pullbacks of those of `K`. -/
def smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (j : ℤ) :
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        j).obj ((smallEtaleDerivedModulePullback B S hS f).obj K) ≅
      (modulePullback B S hS f).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) j).obj K) :=
  haveI := etaleModulePullback_additive B S hS f hf
  haveI := preservesFiniteLimits_etaleModulePullback B S hS f hf
  haveI := preservesFiniteColimits_etaleModulePullback B S hS f hf
  (DerivedCategory.homologyFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      j).mapIso ((smallEtaleDerivedModulePullbackIsoEtale B S hS f hf).app K) ≪≫
    ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryHomologyIso j).app K ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS f hf).symm.app _

/-- For `f` étale, the cohomology sheaves of `Lf^*K` are the pullbacks of those of `K`. -/
theorem nonempty_homology_smallEtaleDerivedModulePullback_obj_iso_of_isEtale (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (j : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) j).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj K) ≅
      (modulePullback B S hS f).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) j).obj K)) :=
  ⟨smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale f hf K j⟩

/-- **The derived pullback of a bounded above complex of flat modules is its degreewise
pullback**, with the pullback of modules `modulePullback`. -/
theorem nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (n : ℤ)
    [K.IsStrictlyLE n]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (K.X i)) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.Q).obj K) ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso f K n hflat
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  have : G.Additive := modulePullback_additive f
  exact ⟨e ≪≫ (DerivedCategory.Q).mapIso ((NatIso.mapHomologicalComplex (F := F) (G := G)
    (pullbackModulesIsoModulePullback B S hS f) (ComplexShape.up ℤ)).app K)⟩

variable (B S hS) in
/-- An object of `D(𝒪_Y)` *has a strictly perfect model* when it is isomorphic to a bounded
complex whose terms are retracts of finite free `𝒪_Y`-modules. -/
def HasStrictlyPerfectModel {Y : AlgebraicSpaces B S hS}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ,
    (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))
      (P.X j)) ∧
    (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
    Nonempty (K ≅ (DerivedCategory.Q).obj P)

/-- A strictly perfect model is carried by every derived pullback to a strictly perfect
model. -/
theorem HasStrictlyPerfectModel.smallEtaleDerivedModulePullback_obj (f : X ⟶ Y)
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hK : HasStrictlyPerfectModel B S hS K) :
    HasStrictlyPerfectModel B S hS ((smallEtaleDerivedModulePullback B S hS f).obj K) := by
  obtain ⟨P, hP, ⟨a, b, ha, hb⟩, ⟨e⟩⟩ := hK
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  have : G.Additive := modulePullback_additive f
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback f P b
    (fun i ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hP i))
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    fun j ↦ IsRetractOfFiniteFree.map (F := modulePullback B S hS f)
      (modulePullbackUnitIso B S hS f) (hP j), ⟨a, b, inferInstance, inferInstance⟩,
    ⟨(smallEtaleDerivedModulePullback B S hS f).mapIso e ≪≫ e'⟩⟩

/-- Strictly perfect models are invariant under isomorphism. -/
theorem HasStrictlyPerfectModel.of_iso
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hK : HasStrictlyPerfectModel B S hS K) (e : K ≅ K') :
    HasStrictlyPerfectModel B S hS K' := by
  obtain ⟨P, hP, hb, ⟨e'⟩⟩ := hK
  exact ⟨P, hP, hb, ⟨e.symm ≪≫ e'⟩⟩

/-- **Restriction of a strictly perfect model along a morphism of charts.**  If the restriction
of `E` to the chart `V` has a strictly perfect model, so has its restriction to every chart
`V'` mapping to `V`. -/
theorem HasStrictlyPerfectModel.chartRestriction
    {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {V V' : SmallEtale B S hS X.1} (k : V' ⟶ V)
    (hV : HasStrictlyPerfectModel B S hS
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E)) :
    HasStrictlyPerfectModel B S hS
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V')).obj E) :=
  (hV.smallEtaleDerivedModulePullback_obj (chartMap B S hS X k)).of_iso
    ((smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS X k)
        (chartToSpace B S hS X V)).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (chartMap_comp_chartToSpace B S hS X k)).app E)

/-- **A perfect object has strictly perfect models on an étale covering of every chart.** -/
theorem exists_hasStrictlyPerfectModel_chart_of_isPerfect
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (U : SmallEtale B S hS X.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
        HasStrictlyPerfectModel B S hS
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) := by
  obtain ⟨E', hE', ⟨eE⟩⟩ := hE
  obtain ⟨R, hR, hP⟩ := hE' U
  refine ⟨R, hR, fun V g hg ↦ ?_⟩
  obtain ⟨P, ⟨hbd, hterm⟩, q, hq⟩ := hP g hg
  let E₀ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ := E'
  have eE₀ : (DerivedCategory.Q).obj E₀ ≅ E := eE
  let O := SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V
  let P₀ : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over V)) ℤ := P
  let q₀ : P₀ ⟶ (O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀ := q
  have hq₀ : QuasiIso q₀ := hq
  let Fr := chartModuleSliceReindex B S hS X V
  have : PreservesFiniteLimits Fr := inferInstance
  have : Fr.Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryProducts Fr
    Functor.additive_of_preservesBinaryBiproducts Fr
  have : PreservesFiniteColimits Fr := inferInstance
  let P' := (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  have hq' : QuasiIso ((Fr.mapHomologicalComplex (ComplexShape.up ℤ)).map q₀) := inferInstance
  have e1 : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E₀) :=
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).mapIso eE₀.symm ≪≫
      smallEtaleDerivedModulePullbackObjQIsoOfIsEtale _ (isEtale_chartToSpace B S hS X V) E₀
  have e2 : ((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E₀ ≅
      (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (chartModuleRestrictionSliceIso B S hS X V).app (E₀.X i))
      (fun i j _ ↦ ((chartModuleRestrictionSliceIso B S hS X V).hom.naturality (E₀.d i j)).symm)
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _
    ((Fr.mapHomologicalComplex (ComplexShape.up ℤ)).map q₀)).2 hq'
  refine ⟨P', fun j ↦ ?_, ?_, ⟨e1 ≪≫ (DerivedCategory.Q).mapIso e2 ≪≫
    (asIso ((DerivedCategory.Q).map
      ((Fr.mapHomologicalComplex (ComplexShape.up ℤ)).map q₀))).symm⟩⟩
  · have hsum : IsDirectSummandOfFiniteFree ((structureRingSheaf B S hS X).over V) (P₀.X j) :=
      hterm j
    obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1 hsum
    let O₁ := SheafOfModules.unit ((structureRingSheaf B S hS X).over V)
    let eb : SheafOfModules.free (R := (structureRingSheaf B S hS X).over V)
        (ULift.{u} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
      (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
        (biproduct.isoCoproduct _).symm
    have hret : IsRetractOfFiniteFree O₁ (P₀.X j) :=
      ⟨n, i ≫ eb.hom, eb.inv ≫ r, by simp [hir]⟩
    exact IsRetractOfFiniteFree.map (F := Fr)
      ((chartModuleRestrictionSliceIso B S hS X V).symm.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
        modulePullbackUnitIso B S hS (chartToSpace B S hS X V)) hret
  · obtain ⟨b, hb⟩ := hbd.bddAbove
    obtain ⟨a, ha⟩ := hbd.bddBelow
    exact ⟨a, b, (CochainComplex.isStrictlyGE_iff P' a).2 fun i hi ↦
      Fr.map_isZero (by_contra fun h ↦ by have := ha h; omega),
      (CochainComplex.isStrictlyLE_iff P' b).2 fun i hi ↦
        Fr.map_isZero (by_contra fun h ↦ by have := hb h; omega)⟩

end AlgebraicGeometry.Space

end
