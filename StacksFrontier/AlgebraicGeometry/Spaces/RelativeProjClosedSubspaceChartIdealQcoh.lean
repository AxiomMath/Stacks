module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceChartIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuotientPointKernelZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSubmodules

/-!
# The degree `d` part of the graded ideal of a closed subspace of the relative Proj is
quasi-coherent

Let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Situation 0849 constructed in
Stacks 084A–084B, `i : Z ⟶ P` a closed immersion with `π` quasi-compact, and
`ℐ_d ⊆ 𝒜_d` the submodule of chart equations of `Z` of degree `d`
(`AlgebraicGeometry.Space.RelativeProjSituation.chartIdeal`): over an étale chart its sections are
those whose readings on the affine étale charts above are equations of the fibres of `Z`.  This
file proves that `ℐ_d` is quasi-coherent (part of Stacks 085L), and that over an affine étale
chart `V = (T, v)` its sections are exactly the sections of `𝒜_d` whose reading on `T` is an
equation of the fibre `Z_V ⊆ Proj_T(v^*𝒜)`.

The reading `𝒜_d(V) ⟶ Γ(T, (v^*𝒜)_d)` (`AlgebraicGeometry.Space.chartOpenReading` at `⊤`) is
`Γ(T, 𝒪_T)`-linear and, on an affine chart and for `𝒜_d` quasi-coherent, bijective: it is the
base-change comparison of Descent 03DX (2) along the identification of the chart of `⊤ ⊆ T` with
`V`.  Quasi-coherence is then the chart criterion of Descent 03DX (2): along a morphism of affine
étale charts `T' ⟶ T` (flat), the equations of `Z_{T'}` are combinations of restrictions of
equations of `Z_T`
(`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_span_of_twistEquationSection_eq_zero`,
Stacks 02KH in degree zero).

## Main results

* `AlgebraicGeometry.Space.chartOpenReading_top_smul`,
  `AlgebraicGeometry.Space.bijective_chartOpenReading_top`: the reading over an étale chart is
  semilinear, and bijective over an affine chart for a quasi-coherent piece.
* `AlgebraicGeometry.Space.RelativeProjSituation.isChartEquation_iff_twistEquationSection_eq_zero`:
  over an affine étale chart, the sections of `ℐ_d` are exactly the sections whose reading is an
  equation of the fibre of `Z`.
* `AlgebraicGeometry.Space.RelativeProjSituation.isQuasicoherentOnSite_chartIdeal`: **`ℐ_d` is
  quasi-coherent.**

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

universe u

/-- If `R ⟶ A` is bijective, then `m ↦ 1 ⊗ m : M ⟶ A ⊗_R M` is bijective. -/
theorem _root_.TensorProduct.bijective_one_tmul_of_bijective_algebraMap {R A M : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    (h : Function.Bijective (algebraMap R A)) :
    Function.Bijective (fun m : M => (1 : A) ⊗ₜ[R] m) := by
  let E : M ≃ₗ[R] A ⊗[R] M := (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr (LinearEquiv.ofBijective (Algebra.linearMap R A) h)
      (LinearEquiv.refl R M))
  convert E.bijective using 1
  funext m
  exact congrArg (· ⊗ₜ[R] m) (map_one (algebraMap R A)).symm

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The scheme morphism of the chart diagram `⊤ ⊆ T ⟶ V` of an étale chart `V = (T, v)`: the
identification of the chart of `⊤` with the open subscheme `⊤`, followed by its inclusion. -/
theorem inclusion_map_counit_comp_ι_eq_toScheme_map_selfOpensChartDiagram_g
    (V : SmallEtale B S hS X.1) :
    (associatedBigEtaleSite B).inclusion.map
          ((representedSmallEtaleEquivalence B S hS V.1.left).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V.1.left) V.1.left.left.property ⊤)).hom.left ≫
        (⊤ : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens).ι =
      (BigFppfOver.toScheme B S hS).map (selfOpensChartDiagram V ⊤).g := by
  have ha : (associatedBigEtaleSite B).inclusion.map
          ((representedSmallEtaleEquivalence B S hS V.1.left).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V.1.left) V.1.left.left.property ⊤)).hom.left ≫
        (⊤ : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens).ι =
      (BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((selfOpensFunctor B S hS V.1.left).obj ⊤).1.hom) :=
    ((associatedBigEtaleSite B).inclusion.map_comp _ _).symm.trans
      (congrArg (associatedBigEtaleSite B).inclusion.map
        (Over.w ((representedSmallEtaleEquivalence B S hS V.1.left).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V.1.left) V.1.left.left.property ⊤)).hom))
  refine ha.trans (congrArg (BigFppfOver.toScheme B S hS).map ?_)
  refine Eq.trans ?_ (yonedaEquiv_yoneda_map _)
  exact congrArg yonedaEquiv (yoneda_map_selfOpensChartDiagram_g V ⊤).symm

/-- **The coefficient map of the chart diagram `⊤ ⊆ T ⟶ V` is the structure map of the chart of
`⊤`**, on a function on `T`. -/
theorem chartDiagramPullback_selfOpensChartDiagram_top (V : SmallEtale B S hS X.1)
    (c : (structureRingSheaf B S hS X).obj.obj (op V)) :
    chartDiagramPullback B S hS (pointHom V.1.hom) (selfOpensChartDiagram V ⊤) c =
      (selfOpensStructureMap B S hS V.1.left).hom.app (op ⊤) c := by
  refine Eq.trans ?_ (selfOpensStructureMap_hom_app V.1.left ⊤ c).symm
  show Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (selfOpensChartDiagram V ⊤).g).op c =
    Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
          ((representedSmallEtaleEquivalence B S hS V.1.left).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V.1.left) V.1.left.left.property ⊤)).hom.left).op
      ((Scheme.Opens.topIso ⊤).inv c)
  have h := congrArg (fun f => f.appTop c)
    (inclusion_map_counit_comp_ι_eq_toScheme_map_selfOpensChartDiagram_g V)
  simp only [Scheme.Hom.comp_appTop] at h
  refine h.symm.trans ?_
  show _ = Scheme.Hom.appTop _ _
  congr 1

/-- **The reading over an étale chart `V = (T, v)` is `Γ(T, 𝒪_T)`-linear**: a function on `V`
acts on the reading through its value as a function on `T`. -/
theorem chartOpenReading_top_smul
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1) (n : ℤ) (c : (structureRingSheaf B S hS X).obj.obj (op V))
    (a : (A.piece n).val.obj (op V)) :
    (show Γ((show (chartScheme (idEtaleChart B S hS V.1.left)).Modules from
          (zariskiReading V.1.left (etalePointAlgebra A V.1.left V.1.hom)).piece n), ⊤) from
        chartOpenReading A V ⊤ n (c • a)) =
      (show Γ(chartScheme (idEtaleChart B S hS V.1.left), ⊤) from c) •
        (show Γ((show (chartScheme (idEtaleChart B S hS V.1.left)).Modules from
          (zariskiReading V.1.left (etalePointAlgebra A V.1.left V.1.hom)).piece n), ⊤) from
          chartOpenReading A V ⊤ n a) := by
  refine ((modulePushforwardHomFMap B S hS (pointHom V.1.hom) _ (A.piece n)
    ((modulePullbackAdjunction B S hS (pointHom V.1.hom)).unit.app (A.piece n))).map_smul
      (selfOpensChartDiagram V ⊤) c a).trans ?_
  rw [chartDiagramPullback_selfOpensChartDiagram_top V c]
  rfl

/-- The coefficient map of the chart diagram `⊤ ⊆ T ⟶ V` is bijective. -/
theorem bijective_chartDiagramPullback_selfOpensChartDiagram_top (V : SmallEtale B S hS X.1) :
    Function.Bijective
      (chartDiagramPullback B S hS (pointHom V.1.hom) (selfOpensChartDiagram V ⊤)) := by
  have e : ⇑(chartDiagramPullback B S hS (pointHom V.1.hom) (selfOpensChartDiagram V ⊤)) =
      ⇑((representedSchemeStructureSheaf B S hS V.1.left).obj.map
        ((representedSmallEtaleEquivalence B S hS V.1.left).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V.1.left) V.1.left.left.property ⊤)).op) ∘
        ⇑((forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso ⊤).inv) :=
    funext fun c => (chartDiagramPullback_selfOpensChartDiagram_top V c).trans
      (selfOpensStructureMap_hom_app V.1.left ⊤ c)
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _)

/-- **Over an affine étale chart `V = (T, v)` the reading of a quasi-coherent piece is
bijective**: it is the base-change comparison `Γ(T) ⊗_{𝒪(V)} 𝒜_n(V) ⟶ Γ(T, (v^*𝒜)_n)` of
Descent 03DX (2), whose coefficient map is bijective, precomposed with `a ↦ 1 ⊗ a`. -/
theorem bijective_chartOpenReading_top
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) (n : ℤ)
    (hA : (A.piece n).IsQuasicoherentOnSite) :
    Function.Bijective (chartOpenReading A V ⊤ n) := by
  let := chartDiagramAlgebra B S hS (pointHom V.1.hom) (selfOpensChartDiagram V ⊤)
  have hbc := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS
    (pointHom V.1.hom) (A.piece n) hA (selfOpensChartDiagram V ⊤)
    (isAffine_selfOpensTop V.1.left) hV
  have h1 := TensorProduct.bijective_one_tmul_of_bijective_algebraMap
    (R := chartRing B S hS X.1 X.2 (selfOpensChartDiagram V ⊤).V)
    (A := chartRing B S hS (yoneda.obj V.1.left) (isAlgebraicSpace_yoneda B S hS V.1.left)
      (selfOpensChartDiagram V ⊤).U)
    (M := (show Modules.{u, u} B S hS X.1 X.2 from A.piece n).val.obj
      (op (selfOpensChartDiagram V ⊤).V))
    (bijective_chartDiagramPullback_selfOpensChartDiagram_top V)
  have e : chartOpenReading A V ⊤ n =
      modulePullbackChartBaseChange B S hS (pointHom V.1.hom) (A.piece n)
        (selfOpensChartDiagram V ⊤) ∘ fun m => (1 : chartRing B S hS (yoneda.obj V.1.left)
          (isAlgebraicSpace_yoneda B S hS V.1.left) (selfOpensChartDiagram V ⊤).U) ⊗ₜ[_] m := by
    funext m
    refine (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS
      (pointHom V.1.hom) (A.piece n) (selfOpensChartDiagram V ⊤) m).trans ?_
    exact ((modulePullbackChartBaseChange_tmul B S hS (pointHom V.1.hom) (A.piece n)
      (selfOpensChartDiagram V ⊤) 1 m).trans (one_smul _ _)).symm
  rw [e]
  exact hbc.comp h1

end AlgebraicGeometry.Space

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

open _root_.AlgebraicGeometry Stacks.AlgebraicGeometry.RelativeProjBridge

variable {T : Scheme.{u}} (A : SheafGradedAlgebra T) {Z : Scheme.{u}}
  (i : Z ⟶ (relativeProj A).scheme)

/-- A multiple of an equation is an equation. -/
theorem twistEquationSection_smul_eq_zero (n : ℕ) (c : Γ(T, ⊤)) (a : Γ(A.piece (n : ℤ), ⊤))
    (ha : twistEquationSection A i n a = 0) : twistEquationSection A i n (c • a) = 0 := by
  have h1 : Scheme.Modules.sectionsLinearMap
      (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n) ⊤ a = 0 :=
    (twistRestrictMapNat_app A _ i n ⊤ a).trans ha
  refine (twistRestrictMapNat_app A _ i n ⊤ (c • a)).symm.trans ?_
  show Scheme.Modules.sectionsLinearMap
      (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i n) ⊤ (c • a) = 0
  rw [map_smul, h1, smul_zero]

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

namespace AlgebraicGeometry.Space.RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

variable (s : RelativeProjSituation.{u, u})
    {Z : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {i : Z ⟶ s.relativeProjFunctor}
    (hi : IsClosedImmersion s.site s.base s.containsBase i)

/-- **A section whose reading is an equation of the fibre of `Z` is a chart equation**: the
readings of its restrictions are equations (equations restrict), and so are those of their
multiples (the reading is linear). -/
theorem isChartEquation_of_twistEquationSection_eq_zero {d : ℕ}
    {V : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1}
    (a : (s.shrink.algebra.piece (d : ℤ)).val.obj (op V))
    (ha : twistEquationSection (s.shrink.pointAlgebra V.1.left V.1.hom)
      (s.fibreClosedImmersion hi V.1.left V.1.hom) d
      (chartOpenReading s.shrink.algebra V ⊤ (d : ℤ) a) = 0) :
    s.IsChartEquation hi d V a := by
  intro E k hE y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h0 := s.twistEquationSection_chartOpenReading_restrict hi k d a ha
  have hsm := chartOpenReading_top_smul s.shrink.algebra E (d : ℤ) c
    ((s.shrink.algebra.piece (d : ℤ)).val.restrictₛₗ k.op a)
  refine (congrArg (twistEquationSection (s.shrink.pointAlgebra E.1.left E.1.hom)
    (s.fibreClosedImmersion hi E.1.left E.1.hom) d) hsm).trans ?_
  exact twistEquationSection_smul_eq_zero _ _ d _ _ h0

/-- **Over a flat morphism of affine test objects, the equations of the fibre of `Z` are
combinations of restrictions of equations**, through the restriction datum of Stacks 084A: the
flat base change of the equations of Stacks 02KH in degree zero
(`mem_span_of_twistEquationSection_eq_zero`) at the base-change square of Stacks 084B (3). -/
theorem mem_span_of_twistEquationSection_eq_zero_of_pointRestrict
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    {T T' : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1) (τ : T' ⟶ T)
    (f' : yoneda.obj T' ⟶ s.space.1) (hf : yoneda.map τ ≫ f = f')
    [_root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)]
    [_root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T')]
    [_root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)]
    (d : ℕ) (r : Γ((s.shrink.pointAlgebra T f).piece (d : ℤ), ⊤) →
      Γ((s.shrink.pointAlgebra T' f').piece (d : ℤ), ⊤))
    (hr : ∀ a, Scheme.Modules.sectionsLinearMap (M := (s.shrink.pointAlgebra T' f').piece (d : ℤ))
      (N := (Scheme.Modules.pullback
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)).obj
        ((s.shrink.pointAlgebra T f).piece (d : ℤ)))
      ((s.quadrupleRestriction.restrict τ f f' hf).app (d : ℤ)) ⊤ (r a) =
      Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
        ((s.shrink.pointAlgebra T f).piece (d : ℤ)) ⊤ ⊤
        (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top _ ⊤) a)
    (x : Γ((s.shrink.pointAlgebra T' f').piece (d : ℤ), ⊤))
    (hx : twistEquationSection (s.shrink.pointAlgebra T' f') (s.fibreClosedImmersion hi T' f') d
      x = 0) :
    x ∈ Submodule.span Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T', ⊤)
      (r '' {a | twistEquationSection (s.shrink.pointAlgebra T f) (s.fibreClosedImmersion hi T f)
        d a = 0}) := by
  obtain ⟨z, hz⟩ := s.exists_isPullback_fibreClosedImmersion_of_eq hi f τ f' hf
  have : _root_.AlgebraicGeometry.QuasiCompact (relativeProj (s.shrink.pointAlgebra T f)).toBase :=
    s.quasiCompact_fibre_toBase T f hπ ‹_›
  exact mem_span_of_twistEquationSection_eq_zero
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
    (s.shrink.pointAlgebra T f) (A₁ := s.shrink.pointAlgebra T' f')
    (s.quadrupleRestriction.restrict τ f f' hf)
    (s.quadrupleRestriction.isIso_restrict_app τ f f' hf) _ rfl
    (s.fibreClosedImmersion hi T f) (s.fibreClosedImmersion hi T' f') z hz d r hr x hx

/-- If every member of `P` is the reading of a section of `L`, then so is every member of the
`Γ(T')`-span of `P`, the reading being linear. -/
theorem exists_chartOpenReading_eq_of_mem_span (d : ℕ)
    (T' : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1)
    (P : Set Γ((s.shrink.pointAlgebra T'.1.left T'.1.hom).piece (d : ℤ), ⊤))
    (L : Submodule (chartRing s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1
      s.shrink.space.2 T') ((show Modules.{u, u} s.shrink.site s.shrink.base
        s.shrink.containsBase s.shrink.space.1 s.shrink.space.2 from
          s.shrink.algebra.piece (d : ℤ)).val.obj (op T')))
    (hP : ∀ y ∈ P, ∃ x0 ∈ L, chartOpenReading s.shrink.algebra T' ⊤ (d : ℤ) x0 = y) :
    ∀ y ∈ Submodule.span Γ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T'.1.left, ⊤)
      P, ∃ x0 ∈ L, chartOpenReading s.shrink.algebra T' ⊤ (d : ℤ) x0 = y := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hP y hy
  | zero => exact ⟨0, zero_mem _, chartOpenReading_zero _ _ _ _⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨x₁, hx₁, e₁⟩ := h₁
    obtain ⟨x₂, hx₂, e₂⟩ := h₂
    exact ⟨x₁ + x₂, add_mem hx₁ hx₂,
      (chartOpenReading_add _ _ _ _ _ _).trans (congrArg₂ (· + ·) e₁ e₂)⟩
  | smul c y _ h =>
    obtain ⟨x0, hx0, e⟩ := h
    refine ⟨(show chartRing s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1
      s.shrink.space.2 T' from c) • x0, Submodule.smul_mem _ _ hx0, ?_⟩
    refine (chartOpenReading_top_smul s.shrink.algebra T' (d : ℤ) _ x0).trans ?_
    rw [e]
    rfl

/-- **The sections of `ℐ_d` over an affine étale chart are spanned by the restrictions of its
sections over any affine étale chart below**, the hypothesis of the chart criterion of
Descent 03DX (2) for a submodule: read on the charts (bijectively), it is the flat base change of
the equations of the fibres of `Z`. -/
theorem chartIdeal_obj_le_span_chartRes
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ) (d : ℕ)
    {T T' : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1}
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T.1.left))
    (hT' : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T'.1.left))
    (g : T' ⟶ T) :
    (s.chartIdeal hi hπ d).obj (op T') ≤ Submodule.span (chartRing s.shrink.site s.shrink.base
        s.shrink.containsBase s.shrink.space.1 s.shrink.space.2 T')
      (chartRes (s.shrink.algebra.piece (d : ℤ)) g ''
        ((s.chartIdeal hi hπ d).obj (op T) : Set ((s.shrink.algebra.piece (d : ℤ)).val.obj
          (op T)))) := by
  intro x hx
  classical
  have := hT
  have := hT'
  have : _root_.AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map g.hom.left) :=
    (Etale.iff_flat_and_formallyUnramified.1 (etale_toScheme_toOver_map _ _ _ _ g)).1
  have hρT := bijective_chartOpenReading_top s.shrink.algebra T hT (d : ℤ)
    (s.shrink.isQuasicoherent (d : ℤ))
  have hρT' := bijective_chartOpenReading_top s.shrink.algebra T' hT' (d : ℤ)
    (s.shrink.isQuasicoherent (d : ℤ))
  let ρinv := Function.surjInv hρT.2
  have hρinv : ∀ a, chartOpenReading s.shrink.algebra T ⊤ (d : ℤ) (ρinv a) = a :=
    Function.surjInv_eq hρT.2
  let r : Γ((s.shrink.pointAlgebra T.1.left T.1.hom).piece (d : ℤ), ⊤) →
      Γ((s.shrink.pointAlgebra T'.1.left T'.1.hom).piece (d : ℤ), ⊤) := fun a =>
    chartOpenReading s.shrink.algebra T' ⊤ (d : ℤ)
      ((s.shrink.algebra.piece (d : ℤ)).val.map g.op (ρinv a))
  set L := Submodule.span (chartRing s.shrink.site s.shrink.base
        s.shrink.containsBase s.shrink.space.1 s.shrink.space.2 T')
      (chartRes (s.shrink.algebra.piece (d : ℤ)) g ''
        ((s.chartIdeal hi hπ d).obj (op T) : Set ((s.shrink.algebra.piece (d : ℤ)).val.obj
          (op T))))
  have hx' := IsChartEquation.twistEquationSection_eq_zero s hi hT' hx
  have hmem := s.mem_span_of_twistEquationSection_eq_zero_of_pointRestrict hi hπ T.1.hom
    g.hom.left T'.1.hom (CostructuredArrow.w g.hom) d r
    (fun a => (s.shrink.pointRestrict_app_val_app_chartOpenReading g (d : ℤ) (ρinv a)).trans
      (congrArg (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom _ _ _ _ _)
        (hρinv a))) _ hx'
  obtain ⟨x0, hx0, he⟩ := s.exists_chartOpenReading_eq_of_mem_span d T'
    (r '' {a | twistEquationSection (s.shrink.pointAlgebra T.1.left T.1.hom)
        (s.fibreClosedImmersion hi T.1.left T.1.hom) d a = 0})
    L (fun y hy => by
    obtain ⟨a, ha, e⟩ := hy
    refine ⟨_, Submodule.subset_span ⟨ρinv a, ?_, rfl⟩, e⟩
    exact s.isChartEquation_of_twistEquationSection_eq_zero hi (ρinv a)
      ((congrArg _ (hρinv a)).trans ha)) _ hmem
  exact (hρT'.1 he) ▸ hx0

/-- **Over an affine étale chart, the sections of `ℐ_d` are exactly the sections of `𝒜_d` whose
reading is an equation of the fibre of `Z`.** -/
theorem isChartEquation_iff_twistEquationSection_eq_zero {d : ℕ}
    {V : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1}
    (hV : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj V.1.left))
    (a : (s.shrink.algebra.piece (d : ℤ)).val.obj (op V)) :
    s.IsChartEquation hi d V a ↔
      twistEquationSection (s.shrink.pointAlgebra V.1.left V.1.hom)
        (s.fibreClosedImmersion hi V.1.left V.1.hom) d
        (chartOpenReading s.shrink.algebra V ⊤ (d : ℤ) a) = 0 :=
  ⟨IsChartEquation.twistEquationSection_eq_zero s hi hV,
    s.isChartEquation_of_twistEquationSection_eq_zero hi a⟩

/-- **The degree `d` part `ℐ_d ⊆ 𝒜_d` of the graded ideal of `Z` is quasi-coherent** (Stacks
085L), for `π` quasi-compact: by the chart criterion of Descent 03DX (2) for submodules of the
quasi-coherent `𝒜_d` (`isCartesianOnAffineCharts_toSheafOfModules_of_le_span`), whose hypothesis is
`chartIdeal_obj_le_span_chartRes`. -/
theorem isQuasicoherentOnSite_chartIdeal
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ) (d : ℕ) :
    (s.chartIdeal hi hπ d).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_toSheafOfModules_of_le_span
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite _ _ _ _ _ _
        (s.shrink.isQuasicoherent (d : ℤ)))
      (s.chartIdeal hi hπ d) fun {_ _} hT hT' g =>
        s.chartIdeal_obj_le_span_chartRes hi hπ d hT hT' g)

end AlgebraicGeometry.Space.RelativeProjSituation
