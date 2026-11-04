module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingUniqueness.ChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingComplexLocalShift

/-!
# Two objects of `D(𝒪_X)` which are shifts of each other on étale charts
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- `K'` restricts to a shift of `K` on the étale chart `c`. -/
def IsShiftOnChart (K K' : @DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ _
      (HasDerivedCategory.standard _))
    (c : SmallEtale B S hS X.1) : Prop :=
  ∃ n : ℤ, Nonempty ((representedChartDerivedRestriction B S hS X.2 c.obj.left c.obj.hom
      (isEtale_chartToSpace B S hS X c)).obj K' ≅
    ((representedChartDerivedRestriction B S hS X.2 c.obj.left c.obj.hom
      (isEtale_chartToSpace B S hS X c)).obj K)⟦n⟧)

variable {B S hS X}

/-- Being a shift on a chart passes to every chart mapping to it. -/
theorem IsShiftOnChart.of_hom {K K' : @DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ _
      (HasDerivedCategory.standard _)}
    {c c' : SmallEtale B S hS X.1} (g : c' ⟶ c) (h : IsShiftOnChart B S hS X K K' c) :
    IsShiftOnChart B S hS X K K' c' := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj c.obj.left) (isAlgebraicSpace_yoneda B S hS c.obj.left))
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj c'.obj.left) (isAlgebraicSpace_yoneda B S hS c'.obj.left))
  obtain ⟨n, ⟨e⟩⟩ := h
  let q := (SmallEtale.toOver B S hS X.1).map g
  have hq : IsEtale B S hS (representedSpaceMap B S hS q).hom :=
    isEtale_schemeSpaceMap B S hS _ q (SmallEtale.etale_map B S hS X.1 g)
  have hw : yoneda.map q ≫ c.obj.hom = c'.obj.hom := CostructuredArrow.w g.hom
  have hχ : IsEtale B S hS (yoneda.map q ≫ c.obj.hom) := hw ▸ isEtale_chartToSpace B S hS X c'
  have hres : ∀ (a b : yoneda.obj c'.obj.left ⟶ X.1) (ha : IsEtale B S hS a)
      (hb : IsEtale B S hS b), a = b →
      Nonempty (representedChartDerivedRestriction B S hS X.2 _ a ha ≅
        representedChartDerivedRestriction B S hS X.2 _ b hb) := by
    rintro a _ _ _ rfl
    exact ⟨Iso.refl _⟩
  obtain ⟨eχ⟩ := hres _ _ (isEtale_chartToSpace B S hS X c') hχ hw.symm
  let ι := representedChartDerivedRestrictionCompIso B S hS X.2 c.obj.hom
    (isEtale_chartToSpace B S hS X c) q hq hχ
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj c))
      (isAlgebraicSpace_yoneda B S hS _))
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj c'))
      (isAlgebraicSpace_yoneda B S hS _))
  have := etaleModulePullback_additive.{u, u} B S hS (representedSpaceMap B S hS q) hq
  have := preservesFiniteLimits_etaleModulePullback B S hS (representedSpaceMap B S hS q) hq
  have := preservesFiniteColimits_etaleModulePullback B S hS (representedSpaceMap B S hS q) hq
  refine ⟨n, ⟨eχ.app K' ≪≫ ι.app K' ≪≫ (representedDerivedPullback B S hS q hq).mapIso e ≪≫ ?_ ≪≫
    (shiftFunctor _ n).mapIso ((eχ.app K ≪≫ ι.app K).symm)⟩⟩
  exact ((etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS q)
    hq).mapDerivedCategory.commShiftIso n).app _

/-- A shift on the chart under an object of the model is a shift on the slice of the model. -/
theorem exists_restrictDer_iso_shift_of_isShiftOnChart
    {K K' : @DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ _
      (HasDerivedCategory.standard _)}
    (V : (smallEtaleModelRingedSite B S hS X.1 X.2).C)
    (h : IsShiftOnChart B S hS X K K' ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)) :
    ∃ n : ℤ, Nonempty ((RingedSite.InvertibleDerived.restrictDer
        (smallEtaleModelRingedSite B S hS X.1 X.2) V).obj
          ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K') ≅
      ((RingedSite.InvertibleDerived.restrictDer (smallEtaleModelRingedSite B S hS X.1 X.2)
        V).obj ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K))⟦n⟧) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  obtain ⟨e₁⟩ := nonempty_over_iso_shift_of_chart B S hS X _ K K' n e
  exact ⟨n, nonempty_restrictDer_iso_shift_of_over B S hS X V K K' n e₁⟩

/-- For an equivalence `e : C ≌ D`, a morphism `g : c' ⟶ e.functor.obj U` factors as
`e.counitInv.app c'` followed by the image under `e.functor` of
`e.inverse.map g ≫ e.unitInv.app U`. -/
theorem eq_counitInv_comp_map {C D : Type*} [Category C] [Category D] (e : C ≌ D) {c' : D} {U : C}
    (g : c' ⟶ e.functor.obj U) :
    g = e.counitInv.app c' ≫ e.functor.map (e.inverse.map g ≫ e.unitInv.app U) := by
  rw [Functor.map_comp, Equivalence.fun_inv_map, ← Equivalence.counit_app_functor]
  simp

/-- **Charts on which `K'` is a shift of `K` give a covering on the model.** If every chart of `X`
is covered by charts on which `K'` is a shift of `K`, then every object of the equi-universe
model is covered by objects over which the transports of `K'` and `K` differ by a shift. -/
theorem model_locallyShift {K K' : @DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ _
      (HasDerivedCategory.standard _)}
    (hcov : ∀ c : SmallEtale B S hS X.1,
      (⟨fun {c'} (_ : c' ⟶ c) => IsShiftOnChart B S hS X K K' c',
        fun {_ _} {_} h g => h.of_hom g⟩ : Sieve c) ∈ SmallEtale.topology B S hS X.1 c) :
    ∀ U : (smallEtaleModelRingedSite B S hS X.1 X.2).C,
      ∃ T : Presieve U, Sieve.generate T ∈ (smallEtaleModelRingedSite B S hS X.1 X.2).J U ∧
        ∀ ⦃V : (smallEtaleModelRingedSite B S hS X.1 X.2).C⦄ (f : V ⟶ U), T f → ∃ n : ℤ,
          Nonempty ((RingedSite.InvertibleDerived.restrictDer
              (smallEtaleModelRingedSite B S hS X.1 X.2) V).obj
                ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K') ≅
            ((RingedSite.InvertibleDerived.restrictDer (smallEtaleModelRingedSite B S hS X.1 X.2)
              V).obj ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K))⟦n⟧) := by
  intro U
  let e := smallEtaleModelEquivalence B S hS X.1
  refine ⟨fun {V} _ => IsShiftOnChart B S hS X K K' (e.functor.obj V), ?_,
    fun V f hf => exists_restrictDer_iso_shift_of_isShiftOnChart V hf⟩
  change Sieve.generate _ ∈ smallEtaleModelTopology B S hS X.1 U
  refine (Functor.functorPushforward_mem_iff (G := e.functor) (smallEtaleModelTopology B S hS X.1)
    (SmallEtale.topology B S hS X.1)).1 ?_
  exact (SmallEtale.topology B S hS X.1).superset_covering (fun c' g hg =>
    ⟨e.inverse.obj c', e.inverse.map g ≫ e.unitInv.app U, e.counitInv.app c',
      ⟨_, 𝟙 _, _, IsShiftOnChart.of_hom (e.counit.app c') hg, Category.id_comp _⟩,
      eq_counitInv_comp_map e g⟩) (hcov (e.functor.obj U))

variable (B S hS X) in
/-- **On a locally Noetherian algebraic space, two dualizing complexes are, on a covering of every
étale chart, shifts of each other.** -/
theorem isShiftOnChart_covering
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hK : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K)
    (hK' : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K') (c : SmallEtale B S hS X.1) :
    (⟨fun {c'} (_ : c' ⟶ c) => IsShiftOnChart B S hS X K.obj K'.obj c',
        fun {_ _} {_} h g => h.of_hom g⟩ : Sieve c) ∈ SmallEtale.topology B S hS X.1 c := by
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 c _ fun z => ?_
  let T := BigFppfOver.toScheme B S hS
  have : IsLocallyNoetherian (T.obj c.obj.left) :=
    isLocallyNoetherian_of_etaleChart B S hS X.1 X.2 hN c.obj.left c.obj.hom c.property
  obtain ⟨ωa, ha, ⟨ea⟩⟩ := hK c.obj.left c.obj.hom c.property
  obtain ⟨ωb, hb, ⟨eb⟩⟩ := hK' c.obj.left c.obj.hom c.property
  obtain ⟨V, hzV, n, e⟩ :=
    Stacks.Duality.exists_mem_derivedPullback_iso_shift_of_isDualizingComplex ωa ωb ha hb z
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing (T.obj c.obj.left).toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing V.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing
      (T.obj (chartOpenRestriction B S hS X.1 c V).obj.left).toRingedSpace))
  let := HasDerivedCategory.standard
    ((T.obj (chartOpenRestriction B S hS X.1 c V).obj.left).Modules)
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj (chartOpenRestriction B S hS X.1 c V).obj.left)
      (isAlgebraicSpace_yoneda B S hS _))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing
    (T.obj ((SmallEtale.toOver B S hS X.1).obj
      (chartOpenRestriction B S hS X.1 c V))).toSheafedSpace))
  let q := (SmallEtale.toOver B S hS X.1).map (chartOpenRestrictionHom B S hS X.1 c V)
  have hTq : T.map q = V.ι := chartOpenRestrictionHom_toScheme B S hS X.1 c V
  refine ⟨_, chartOpenRestrictionHom B S hS X.1 c V, ?_, ⟨z, hzV⟩, ?_⟩
  · have hqE : AlgebraicGeometry.Etale (T.map q) :=
      SmallEtale.etale_map B S hS X.1 (chartOpenRestrictionHom B S hS X.1 c V)
    have hq : IsEtale B S hS (representedSpaceMap B S hS q).hom :=
      isEtale_schemeSpaceMap B S hS _ q hqE
    have hχ : IsEtale B S hS (yoneda.map q ≫ c.obj.hom) :=
      isEtale_chartToSpace B S hS X (chartOpenRestriction B S hS X.1 c V)
    let ι := representedChartDerivedRestrictionCompIso B S hS X.2 c.obj.hom
      (isEtale_chartToSpace B S hS X c) q hq hχ
    let μ := representedDerivedAssociatedModulePullbackIso B S hS q hq
    obtain ⟨e'⟩ := e (T.map q) hTq
    have := additive_representedAssociatedModule B S hS
      (chartOpenRestriction B S hS X.1 c V).obj.left (isAlgebraicSpace_yoneda B S hS _)
    refine ⟨n, ⟨ι.app K'.obj ≪≫ (representedDerivedPullback B S hS q hq).mapIso eb ≪≫ μ.app ωb ≪≫
      (representedDerivedAssociatedModule B S hS _).mapIso e' ≪≫
      (((representedAssociatedModule B S hS (chartOpenRestriction B S hS X.1 c V).obj.left
        (isAlgebraicSpace_yoneda B S hS _)).mapDerivedCategory.commShiftIso n).app _) ≪≫
      (shiftFunctor _ n).mapIso ((μ.app ωa).symm ≪≫
        (representedDerivedPullback B S hS q hq).mapIso ea.symm ≪≫ (ι.app K.obj).symm)⟩⟩
  · rw [hTq]
    rfl

end AlgebraicGeometry.Space
