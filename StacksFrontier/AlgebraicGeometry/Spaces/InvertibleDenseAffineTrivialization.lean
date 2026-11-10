module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFpqcDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitOverComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementChartOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOfOpenMorphismLift
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart
public import StacksFrontier.RingTheory.Module.LocallyFree.DenseGenerator

/-!
# An invertible module on a Noetherian algebraic space is trivial on a dense affine open

Let `X` be a Noetherian algebraic space over a scheme `S` and let `L` be an invertible
`𝒪_X`-module.  Then there is a dense affine open subspace `U ⊆ X`, presented by an étale chart
`C` of `X` whose structure morphism is an open immersion, and a section `s` of `L` over `C`
such that `b ↦ b • s` is a bijection `𝒪_X(C) ≅ L(C)`.  This is the first sentence of the proof
of Stacks 0DMM: "Choose a dense affine open `U ⊂ X` such that `L|_U` is trivial."

## The argument

A Noetherian algebraic space has a dense affine open subspace `C₀`, by Stacks 0ADD.  Write
`A = 𝒪_X(C₀)` and `M = L(C₀)`; `A` is a Noetherian ring.  The module `M` is a finite locally
free `A`-module of rank one: `L` is free of rank one on the members of an étale covering of
`C₀` (Stacks 0B8Q), which is refined by finitely many affine charts `V_i` with
`A ⟶ ∏ 𝒪_X(V_i)` faithfully flat; over each `V_i` the sections `L(V_i) = 𝒪_X(V_i) ⊗_A M` are
free of rank one, so `(∏ 𝒪_X(V_i)) ⊗_A M` is free of rank one, and finite local freeness of a
given rank descends along faithfully flat ring maps.  By
`Module.exists_isFreeGeneratorAway_forall_notMem_minimalPrimes` there are `f ∈ A` outside every
minimal prime and `s ∈ M` generating `M_f` freely.  The basic open `D(f) ⊆ C₀` is dense and
affine, it is an open subspace of `X`, and the sections of `L` over it are `M_f`.

## Main results

* `AlgebraicGeometry.Space.bijective_smul_map_of_bijective_smul`: a free generator of the
  sections of a quasi-coherent module over an affine chart restricts to a free generator over
  every affine chart above it.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_sections_of_isInvertible`: over an
  affine chart the sections of an invertible module are finite locally free of rank one.
* `AlgebraicGeometry.dense_basicOpen_of_forall_notMem_minimalPrimes`: on an affine scheme the
  basic open of a function lying in no minimal prime is dense.
* `AlgebraicGeometry.Space.exists_denseAffineOpenChart_bijective_smul`: the trivializing dense
  affine open subspace.

## References

* [Stacks Project, Tag 0DMM](https://stacks.math.columbia.edu/tag/0DMM)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **On an affine scheme the basic open of a function lying in no minimal prime of the ring of
global functions is dense.**  Every point specializes from a minimal prime, which lies in the
basic open. -/
theorem dense_basicOpen_of_forall_notMem_minimalPrimes (X : Scheme.{u}) [IsAffine X]
    (f : Γ(X, ⊤)) (hf : ∀ p ∈ minimalPrimes Γ(X, ⊤), f ∉ p) :
    Dense (X.basicOpen f : Set X) := by
  have hD : Dense (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, ⊤))) := by
    refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun q => ?_)
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.asIdeal)
    have hmem : (⟨p, hp.1.1⟩ : PrimeSpectrum Γ(X, ⊤)) ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, ⊤))) := hf p hp
    exact closure_mono (Set.singleton_subset_iff.mpr hmem)
      ((PrimeSpectrum.le_iff_specializes ⟨p, hp.1.1⟩ q).mp hpq).mem_closure
  rw [← Scheme.map_PrimeSpectrum_basicOpen_of_affine X f]
  exact hD.preimage (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).isOpenMap

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A free generator over an affine chart restricts to a free generator over every affine
chart above it**, for a module cartesian on affine charts.  The map `b ↦ b • m|_V` is the
composite of `b ↦ b ⊗ 1`, of the base change of `b ↦ b • m`, and of the base change comparison
of the module, all three bijective. -/
theorem bijective_smul_map_of_bijective_smul (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U V : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (g : V ⟶ U)
    {m : G.val.obj (op U)} (hm : Function.Bijective (fun b : chartRing B S hS F hF U => b • m)) :
    Function.Bijective (fun b : chartRing B S hS F hF V => b • chartRestrictLinear G g m) := by
  let _ := chartAlgebra (hF := hF) g
  let β := LinearMap.toSpanSingleton (chartRing B S hS F hF U) (G.val.obj (op U)) m
  have hfun : (fun b : chartRing B S hS F hF V => b • chartRestrictLinear G g m) =
      (sectionsBaseChange G g) ∘ (LinearMap.lTensor (chartRing B S hS F hF V) β) ∘
        (TensorProduct.rid (chartRing B S hS F hF U) (chartRing B S hS F hF V)).symm := by
    funext b
    simpa only [Function.comp_apply, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, β,
      LinearMap.toSpanSingleton_apply, one_smul] using (chartBaseChange_tmul G g b m).symm
  exact hfun ▸ (hG U V hU hV g).comp ((bijective_lTensor_of_bijective _ β hm).comp
    (TensorProduct.rid _ _).symm.bijective)

/-- A basis indexed by `Fin 1` makes `r ↦ r • b 0` a bijection. -/
theorem bijective_smul_basis_zero {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (b : Module.Basis (Fin 1) R N) : Function.Bijective (fun r : R => r • b 0) := by
  refine ⟨fun r r' h => ?_, fun y => ⟨b.repr y 0, ?_⟩⟩
  · simpa using congrArg (fun z => b.repr z 0) h
  · simpa using b.sum_repr y

variable (hF) in
/-- **The affine charts over which a module of rank one has a free generator cover every chart.**
This is `AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`
with the basis of rank one read as a single free generator. -/
theorem generatorPresieve_mem_topology (H : Modules.{u, u} B S hS F hF)
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) H 1)
    (U : SmallEtale B S hS F) :
    Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
      IsAffine (chartScheme V) ∧ ∃ m : H.val.obj (op V),
        Function.Bijective (fun b : chartRing B S hS F hF V => b • m)) ∈
      SmallEtale.topology B S hS F U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
  obtain ⟨I, A, a, hcov, hfree⟩ := h U
  have hcov' : Sieve.ofArrows A a ∈ SmallEtale.topology B S hS F U := hcov
  obtain ⟨V₁, g₁, hg₁, z₁, hz₁⟩ := exists_mem_sieve_scheme_point B S hS F U hcov' z
  obtain ⟨Z, t, ff, ⟨i⟩, hfac⟩ := hg₁
  obtain ⟨T₀, j, hT₀aff, w₀, hw₀⟩ := exists_affine_chart_at B S hS F V₁ z₁
  obtain ⟨κ, ⟨hcofan⟩⟩ := hfree i
  obtain ⟨b⟩ := RingedSite.nonempty_basis_sections_of_isColimitCofanUnit
    (smallEtaleRingedSite B S hS F hF) H 1 (A i) κ hcofan (j ≫ t)
  refine ⟨T₀, j ≫ g₁, ⟨T₀, 𝟙 _, j ≫ g₁, ⟨hT₀aff, b 0, bijective_smul_basis_zero b⟩,
    Category.id_comp _⟩, w₀, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact (congrArg _ hw₀).trans hz₁

variable (hF) in
/-- **Over an affine chart the sections of a module of rank one which is cartesian on affine
charts are a finite locally free module of rank one.**  The charts carrying a free generator
cover the chart; finitely many affine ones among them, `V_i`, have `A ⟶ ∏ 𝒪(V_i)` faithfully
flat; the base change of the sections to `∏ 𝒪(V_i)` is free of rank one, componentwise by the
cartesian property; and finite local freeness of rank one descends along faithfully flat maps
(`Module.IsFiniteLocallyFreeOfRank.of_baseChange`). -/
theorem isFiniteLocallyFreeOfRank_one_sections (H : Modules.{u, u} B S hS F hF)
    (hH : IsCartesianOnAffineCharts H)
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) H 1)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U)) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF U) (H.val.obj (op U)) 1 := by
  classical
  obtain ⟨ι, hι, V, f, hVaff, hR, hff⟩ :=
    SmallEtale.exists_finite_affine_faithfullyFlat_refinement B S hS F hF U hU
      (generatorPresieve_mem_topology hF H h U)
  have _ : Fintype ι := Fintype.ofFinite ι
  choose Y k g hP hfac using fun i => hR i
  choose m' hm' using fun i => (hP i).2
  -- A free generator over each `V i`.
  have hm : ∀ i, Function.Bijective (fun b : chartRing B S hS F hF (V i) =>
      b • chartRestrictLinear H (k i) (m' i)) := fun i =>
    bijective_smul_map_of_bijective_smul H hH (hP i).1 (hVaff i) (k i) (hm' i)
  let Bi := fun i => chartRing B S hS F hF (V i)
  let : ∀ i, Algebra (chartRing B S hS F hF U) (Bi i) := fun i => chartAlgebra (hF := hF) (f i)
  let : ∀ i, Module (chartRing B S hS F hF U) (H.val.obj (op (V i))) := fun i =>
    chartSectionsModule H (f i)
  have : ∀ i, IsScalarTower (chartRing B S hS F hF U) (Bi i) (H.val.obj (op (V i))) :=
    fun i => chartSections_isScalarTower H (f i)
  have : Module.FaithfullyFlat (chartRing B S hS F hF U) (∀ i, Bi i) :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  -- The componentwise trivializations of the base change.
  let e : ∀ i, Bi i ⊗[chartRing B S hS F hF U] H.val.obj (op U) ≃ₗ[Bi i] Bi i := fun i =>
    (LinearEquiv.ofBijective (sectionsBaseChange H (f i))
        (hH U (V i) hU (hVaff i) (f i))).trans
      (LinearEquiv.ofBijective (LinearMap.toSpanSingleton (Bi i) _
        (chartRestrictLinear H (k i) (m' i))) (hm i)).symm
  have hE : ∀ (b' : ∀ i, Bi i) (x : H.val.obj (op U)) (i : ι),
      TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi) (N := H.val.obj (op U))
        (b' ⊗ₜ x) i = b' i ⊗ₜ x := fun b' x i => by
    simp [TensorProduct.piLeft]
  let E : (∀ i, Bi i) ⊗[chartRing B S hS F hF U] H.val.obj (op U) →ₗ[∀ i, Bi i] ∀ i, Bi i :=
    { toFun := fun z i => e i (TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi)
        (N := H.val.obj (op U)) z i)
      map_add' := fun z z' => by funext i; simp
      map_smul' := fun b z => by
        funext i
        simp only [smul_eq_mul, RingHom.id_apply, Pi.mul_apply]
        induction z using TensorProduct.inductionOn with
        | tmul b' x =>
          rw [TensorProduct.smul_tmul', hE, hE, show (b • b') i = b i • b' i from rfl,
            ← TensorProduct.smul_tmul', LinearEquiv.map_smul, smul_eq_mul]
        | add z z' hz hz' =>
          rw [smul_add, map_add, Pi.add_apply, map_add, hz, hz', map_add, Pi.add_apply,
            map_add, mul_add] }
  have hEbij : Function.Bijective E := by
    have hfun : (E : _ → _) = (fun y i => e i (y i)) ∘
        TensorProduct.piLeft (R := chartRing B S hS F hF U) (M := Bi) (N := H.val.obj (op U)) :=
      rfl
    rw [hfun]
    refine Function.Bijective.comp ⟨fun y y' hy => funext fun i => (e i).injective
      (congrFun hy i), fun y => ⟨fun i => (e i).symm (y i), funext fun i => by simp⟩⟩
      (LinearEquiv.bijective _)
  have hfree : Module.IsFiniteLocallyFreeOfRank (∀ i, Bi i)
      ((∀ i, Bi i) ⊗[chartRing B S hS F hF U] H.val.obj (op U)) 1 :=
    Module.IsFiniteLocallyFreeOfRank.of_basis
      ((Module.Basis.singleton (Fin 1) (∀ i, Bi i)).map (LinearEquiv.ofBijective E hEbij).symm)
  exact Module.IsFiniteLocallyFreeOfRank.of_baseChange (∀ i, Bi i) hfree

end Space

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An invertible module on a Noetherian algebraic space is trivial on a dense affine open
subspace.**  There is an étale chart `C` of `X` with affine scheme whose structure morphism is an
open immersion with dense image, and a section `s` of `L` over `C` with `b ↦ b • s` a bijection
`𝒪_X(C) ≅ L(C)`.  This is the first sentence of the proof of Stacks 0DMM. -/
theorem exists_denseAffineOpenChart_bijective_smul (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L) :
    ∃ C : SmallEtale B S hS X.1, IsAffine (chartScheme C) ∧ IsOpenImmersion B S hS C.1.hom ∧
      DenseRange (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) ∧
      ∃ s : L.val.obj (op C),
        Function.Bijective (fun b : chartRing B S hS X.1 X.2 C => b • s) := by
  obtain ⟨W, u, hWaff, hu, hudense⟩ := exists_dense_affine_openImmersion_self B S hS hZ X.1 X.2 hN
  let C₀ : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk u, presheaf_etale_of_isOpenImmersion B S hS hu⟩
  have hC₀aff : IsAffine (chartScheme C₀) := hWaff
  have : IsLocallyNoetherian (chartScheme C₀) :=
    isLocallyNoetherian_chartScheme B S hS X hN.2.2 C₀
  have : IsNoetherianRing (chartRing B S hS X.1 X.2 C₀) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (chartScheme C₀)⟩
  have hLq := isQuasicoherentOnSite_of_isInvertible B S hS X L hL
  have hLc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 L hLq
  have hflf := isFiniteLocallyFreeOfRank_one_sections X.2 L hLc
    (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X L hL) C₀ hC₀aff
  have := hflf.finite
  obtain ⟨f, hf, s, hs⟩ := Module.exists_isFreeGeneratorAway_forall_notMem_minimalPrimes
    (fun p hp => have := hp.1.1; hflf.exists_isFreeGeneratorAway p)
  refine ⟨openChart B S hS X.1 C₀ ((chartScheme C₀).basicOpen f),
    isAffine_chartScheme_openChart_basicOpen B S hS X.1 C₀ hC₀aff f,
    isOpenImmersion_openChart C₀ hu _,
    denseRange_pointsMap_openChart C₀ hudense _
      (dense_basicOpen_of_forall_notMem_minimalPrimes (chartScheme C₀) f hf),
    L.val.map (openChartInclusion B S hS X.1 C₀ ((chartScheme C₀).basicOpen f)).op s, ?_⟩
  let _ := chartAlgebra (hF := X.2) (openChartInclusion B S hS X.1 C₀
    ((chartScheme C₀).basicOpen f))
  let _ := chartSectionsModule L (openChartInclusion B S hS X.1 C₀
    ((chartScheme C₀).basicOpen f))
  have := chartSections_isScalarTower L (openChartInclusion B S hS X.1 C₀
    ((chartScheme C₀).basicOpen f))
  have := isLocalization_away_chartRing_openChart_basicOpen B S hS X.2 C₀ hC₀aff f
  have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS X.2 L hLc C₀ hC₀aff f
  exact Module.isFreeGeneratorAway_bijective_smul
    (chartRestrictLinear L (openChartInclusion B S hS X.1 C₀ ((chartScheme C₀).basicOpen f))) hs

/-! ### The trivialization over the complement of a sheaf of ideals -/

variable {B S hS}

/-- Two morphisms of étale charts into a chart whose structure morphism is a monomorphism are
equal. -/
theorem hom_ext_of_mono_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V C : SmallEtale B S hS F}
    (hC : Mono C.1.hom) (g g' : V ⟶ C) :
    g = g' := by
  have h1 : yoneda.map g.hom.left ≫ C.1.hom = yoneda.map g'.hom.left ≫ C.1.hom :=
    (CostructuredArrow.w g.hom).trans (CostructuredArrow.w g'.hom).symm
  have h3 : g.hom.left = g'.hom.left := yoneda.map_injective ((cancel_mono _).mp h1)
  exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h3)

variable (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)
    (C : SmallEtale B S hS X.1) (hC : IsOpenImmersion B S hS C.1.hom)
    (hsub : idealUnitLocus B S hS X I ⊆
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))

include hC hsub in
/-- **Every étale chart of `U = X ∖ V(ℐ)` maps to an open immersion chart `C` of `X` containing
the unit locus of `ℐ`**, as a chart of `X`: its image lies in the unit locus, which is the point
set of `U`, and a morphism from a representable presheaf factors through an open immersion
chart as soon as it does so on point sets. -/
theorem nonempty_pc_hom (P : SmallEtale B S hS (idealComplement B S hS X I).1) :
    Nonempty (pc B S hS X I P ⟶ C) := by
  have hrange : Set.range (pointsMap B S hS (yoneda.obj (pc B S hS X I P).obj.left)
      (pc B S hS X I P).1.hom) ⊆ Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) := by
    refine subset_trans ?_ hsub
    rw [← range_pointsMap_idealComplementι B S hS X I]
    rintro _ ⟨z, rfl⟩
    exact ⟨pointsMap B S hS _ P.1.hom z,
      (congrFun (pointsMap_comp B S hS _ P.1.hom (idealComplementι B S hS X I).hom) z).symm⟩
  obtain ⟨σ, hσ⟩ := exists_hom_of_range_pointsMap_subset C hC (pc B S hS X I P).1.hom hrange
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk σ hσ)⟩

/-- The morphism of `AlgebraicGeometry.Space.nonempty_pc_hom`, chosen. -/
noncomputable def pcHom (P : SmallEtale B S hS (idealComplement B S hS X I).1) :
    pc B S hS X I P ⟶ C :=
  (nonempty_pc_hom X I C hC hsub P).some

/-- The restriction maps of an étale pullback are those of the module over the composite charts.
Stated on variables, so that it is crossed in one definitional step. -/
theorem etaleModulePullback_obj_val_map_apply {Y Z : AlgebraicSpaces B S hS} (w : Y ⟶ Z)
    (hw : IsEtale B S hS w.hom) (M : Modules.{u, u} B S hS Z.1 Z.2)
    {P Q : SmallEtale B S hS Y.1} (k : Q ⟶ P)
    (m : M.val.obj (op ((smallEtalePostcomp B S hS w hw).obj P))) :
    ((etaleModulePullback B S hS w hw).obj M).val.map k.op m =
      M.val.map ((smallEtalePostcomp B S hS w hw).map k).op m := rfl

/-- Restricting a section along two composable chart morphisms is restricting it along the
composite.  Stated on variables. -/
theorem val_map_val_map_of_comp_eq {Y : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS Y.1 Y.2)
    {V W T : SmallEtale B S hS Y.1} (a : V ⟶ W) (b : W ⟶ T) (c : V ⟶ T) (h : a ≫ b = c)
    (m : M.val.obj (op T)) : M.val.map a.op (M.val.map b.op m) = M.val.map c.op m := by
  subst h
  exact (PresheafOfModules.map_comp_apply M.val b.op a.op m).symm

/-- The section of `L|_U` obtained by restricting a section of `L` over `C` to every chart of `U`
along `AlgebraicGeometry.Space.pcHom`. -/
noncomputable def pcSection (L : Modules.{u, u} B S hS X.1 X.2) (s : L.val.obj (op C)) :
    ((restrictToIdealComplement B S hS X I).obj L).sections :=
  PresheafOfModules.sectionsMk
    (fun P => (L.val.map (pcHom X I C hC hsub P.unop).op s :
      L.val.obj (op (pc B S hS X I P.unop))))
    (fun P Q k => by
      have hk : pcMap B S hS X I k.unop ≫ pcHom X I C hC hsub P.unop =
          pcHom X I C hC hsub Q.unop :=
        hom_ext_of_mono_chart (mono_of_presheaf_isOpenImmersion hC) _ _
      refine (etaleModulePullback_obj_val_map_apply (idealComplementι B S hS X I)
        (isEtale_idealComplementι B S hS X I) L k.unop _).trans ?_
      exact val_map_val_map_of_comp_eq L _ _ _ hk s)

include hC hsub in
/-- **A free generator of a cartesian module over `C` trivializes its restriction to
`U = X ∖ V(ℐ)`.**  The morphism `𝒪_U ⟶ L|_U` attached to the restricted section is bijective on
the sections over every affine chart of `U`, by
`AlgebraicGeometry.Space.bijective_smul_map_of_bijective_smul`, hence an isomorphism, the affine
charts being cover dense. -/
theorem isIso_unitHomEquiv_symm_pcSection (hCaff : IsAffine (chartScheme C))
    (L : Modules.{u, u} B S hS X.1 X.2) (hLc : IsCartesianOnAffineCharts L)
    (s : L.val.obj (op C))
    (hs : Function.Bijective (fun b : chartRing B S hS X.1 X.2 C => b • s)) :
    IsIso ((SheafOfModules.unitHomEquiv _).symm (pcSection X I C hC hsub L s)) := by
  set θ := (SheafOfModules.unitHomEquiv _).symm (pcSection X I C hC hsub L s)
  have happ : ∀ (P : SmallEtale B S hS (idealComplement B S hS X I).1)
      (b : chartRing B S hS X.1 X.2 (pc B S hS X I P)),
      θ.val.app (op P) b = b • chartRestrictLinear L (pcHom X I C hC hsub P) s :=
    fun _ _ => rfl
  have hbij : ∀ P : SmallEtale B S hS (idealComplement B S hS X I).1,
      IsAffine (chartScheme P) → Function.Bijective (θ.val.app (op P)) := by
    intro P hP
    have hP' : IsAffine (chartScheme (pc B S hS X I P)) := hP
    have := bijective_smul_map_of_bijective_smul L hLc hCaff hP' (pcHom X I C hC hsub P) hs
    exact (show (fun b : chartRing B S hS X.1 X.2 (pc B S hS X I P) =>
      b • chartRestrictLinear L (pcHom X I C hC hsub P) s) = ⇑(θ.val.app (op P)) from
        funext fun b => (happ P b).symm) ▸ this
  have hdense := SmallEtale.isCoverDense_affineEtaleInclusion B S hS
    (idealComplement B S hS X I).1 (idealComplement B S hS X I).2
  have : PresheafOfModules.IsLocallyInjective
      (smallEtaleRingedSite B S hS (idealComplement B S hS X I).1
        (idealComplement B S hS X I).2).J θ.val :=
    isLocallyInjective_of_injective_of_isCoverDense _ (AffineEtale.inclusion B S hS _) hdense
      _ fun V => (hbij _ V.2).injective
  have : PresheafOfModules.IsLocallySurjective
      (smallEtaleRingedSite B S hS (idealComplement B S hS X I).1
        (idealComplement B S hS X I).2).J θ.val :=
    Stacks.PresheafOfModules.isLocallySurjective_of_surjective_of_isCoverDense _
      (AffineEtale.inclusion B S hS _) hdense _ fun V => (hbij _ V.2).surjective
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective _

end Space

end AlgebraicGeometry
