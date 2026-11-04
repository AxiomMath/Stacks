module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackPointChartSection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackHomRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportFlatPullback

/-!
# Sections of a module on a groupoid at the points of its charts

Let `(𝒢, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces. An
étale chart `W` of `U` is a point `u_W` of `U` over `W`; the chart section along `u_W` is a map
`𝒢(W) ⟶ Γ(W, u_W^*𝒢)`. It is bijective when `W` is affine, and it is natural in `W` for the
restriction maps of `(T, a) ↦ Γ(T, a^*𝒢)`.

## Main definitions

* `AlgebraicGeometry.Stack.chartPointSection`: the map `𝒢(W) ⟶ Γ(W, u_W^*𝒢)`.

## Main results

* `AlgebraicGeometry.Stack.bijective_chartPointSection`: it is bijective for affine `W`.
* `AlgebraicGeometry.Stack.pointSectionRestrict_chartPointSection`: it is natural in `W`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

/-- Over a bijective algebra map `R → R'`, a bijective linear map out of `R' ⊗_R M` restricts to a
bijection on `m ↦ 1 ⊗ m`. -/
theorem Stacks.bijective_one_tmul_comp {R R' M N : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N]
    (hφ : Function.Bijective (algebraMap R R')) (L : TensorProduct R R' M →ₗ[R'] N)
    (hL : Function.Bijective L) :
    Function.Bijective (fun m : M => L ((1 : R') ⊗ₜ[R] m)) := by
  refine ⟨hL.1.comp (Stacks.injective_one_tmul_of_bijective hφ), fun n => ?_⟩
  obtain ⟨t, rfl⟩ := hL.2 n
  suffices h : ∃ m : M, (1 : R') ⊗ₜ[R] m = t by
    obtain ⟨m, rfl⟩ := h
    exact ⟨m, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul r' m =>
    obtain ⟨r, rfl⟩ := hφ.2 r'
    refine ⟨r • m, ?_⟩
    rw [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul' r (1 : R') m
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨m₁, rfl⟩ := h₁
    obtain ⟨m₂, rfl⟩ := h₂
    exact ⟨m₁ + m₂, TensorProduct.tmul_add _ _ _⟩

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **Chart sections are bijective over affine charts along a bijective change of rings.** -/
theorem bijective_modulePullbackChartSection {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Modules.{u, u} C S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite)
    (d : ChartDiagram C S hS X.1 Y.1 f.hom)
    (haU : IsAffine ((SmallEtale.toOver C S hS X.1 ⋙ BigFppfOver.toScheme C S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver C S hS Y.1 ⋙ BigFppfOver.toScheme C S hS).obj d.V))
    (hφ : Function.Bijective (chartDiagramRestrict C S hS f d)) :
    Function.Bijective (modulePullbackChartSection C S hS f N d) := by
  let := chartDiagramAlgebra C S hS f d
  have hb := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite C S hS f N hN d
    haU haV
  have key : ∀ m, modulePullbackChartBaseChange C S hS f N d (TensorProduct.tmul _ 1 m) =
      modulePullbackChartSection C S hS f N d m := fun m =>
    (modulePullbackChartBaseChange_tmul C S hS f N d 1 m).trans (one_smul _ _)
  have h := Stacks.bijective_one_tmul_comp (M := N.val.obj (op d.V)) hφ _ hb
  exact (funext key : (fun m => modulePullbackChartBaseChange C S hS f N d
    (TensorProduct.tmul _ 1 m)) = _) ▸ h

/-- **Chart sections are compatible with restriction of the target chart.** -/
theorem modulePullbackChartSection_restrictTarget {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (N : Modules.{u, u} C S hS Y.1 Y.2) {U : SmallEtale C S hS X.1} {V V' : SmallEtale C S hS Y.1}
    (j : V' ⟶ V)
    (g : (SmallEtale.toOver C S hS X.1).obj U ⟶ (SmallEtale.toOver C S hS Y.1).obj V')
    (h : U.1.hom ≫ f.hom = yoneda.map (g ≫ (SmallEtale.toOver C S hS Y.1).map j) ≫ V.1.hom)
    (h' : U.1.hom ≫ f.hom = yoneda.map g ≫ V'.1.hom) (s : N.val.obj (op V)) :
    modulePullbackChartSection C S hS f N ⟨U, V, g ≫ (SmallEtale.toOver C S hS Y.1).map j, h⟩ s =
      modulePullbackChartSection C S hS f N ⟨U, V', g, h'⟩ (N.val.map j.op s) := by
  have hn := (modulePullbackChartFMap C S hS f N).naturality
    ⟨U, V, g ≫ (SmallEtale.toOver C S hS Y.1).map j, h⟩ ⟨U, V', g, h'⟩ (𝟙 U) j
    (by simp) s
  have h1 := modulePullbackChartFMap_app C S hS f N
    ⟨U, V, g ≫ (SmallEtale.toOver C S hS Y.1).map j, h⟩ s
  have h2 := modulePullbackChartFMap_app C S hS f N ⟨U, V', g, h'⟩ (N.val.map j.op s)
  have h3 := PresheafOfModules.map_id_apply ((modulePullback C S hS f).obj N).val (op U)
    ((modulePullbackChartFMap C S hS f N).app
      ⟨U, V, g ≫ (SmallEtale.toOver C S hS Y.1).map j, h⟩ s)
  exact h1.symm.trans (h3.symm.trans (hn.symm.trans h2))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- For an étale chart `W` of `U`, the structure morphism of `W` (precomposed with the identity
of `W`) is the morphism classified by the point `u_W`. -/
theorem chartPoint_comm (W : Space.SmallEtale C S hS G.objects.obj) :
    yoneda.map (𝟙 ((Space.SmallEtale.toOver C S hS G.objects.obj).obj W)) ≫ W.obj.hom =
      yonedaEquiv.symm (chartPoint G W).fiber := by
  refine ((congrArg (· ≫ W.obj.hom) (yoneda.map_id _)).trans (Category.id_comp _)).trans ?_
  exact (Equiv.symm_apply_apply yonedaEquiv W.obj.hom).symm

/-- **The chart section `𝒢(W) ⟶ Γ(W, u_W^*𝒢)`** along the point `u_W` of `U` given by an étale
chart `W`. -/
def chartPointSection (W : Space.SmallEtale C S hS G.objects.obj)
    (x : M.F.obj.val.obj (op W)) : pointSections G M (chartPoint G W) :=
  pointChartSection G M (chartPoint G W) W (𝟙 _) (chartPoint_comm G W) x

/-- **The chart section along `u_W` is bijective for an affine chart `W`.** -/
theorem bijective_chartPointSection (W : Space.SmallEtale C S hS G.objects.obj)
    (hW : IsAffine ((Space.SmallEtale.toOver C S hS G.objects.obj ⋙
      BigFppfOver.toScheme C S hS).obj W)) :
    Function.Bijective (chartPointSection G M W) := by
  have hφ : Function.Bijective (Space.chartDiagramRestrict C S hS (pointMap G (chartPoint G W))
      (pointChartDiagram G (chartPoint G W) W (𝟙 _) (chartPoint_comm G W))) := by
    rw [Space.chartDiagramRestrict_eq_appTop]
    exact bijective_toScheme_map_id_appTop _
  exact Space.bijective_modulePullbackChartSection (pointMap G (chartPoint G W)) M.F.obj
    M.F.property (pointChartDiagram G (chartPoint G W) W (𝟙 _) (chartPoint_comm G W)) hW hW hφ

/-- **Naturality of the chart section along `u_W` in the chart `W`.** -/
theorem pointSectionRestrict_chartPointSection {W₁ W₂ : Space.SmallEtale C S hS G.objects.obj}
    (i : W₁ ⟶ W₂) (x : M.F.obj.val.obj (op W₂)) :
    pointSectionRestrict G M (chartPointHom G i) (chartPointSection G M W₂ x) =
      chartPointSection G M W₁ (M.F.obj.val.map i.op x) := by
  have hm : pointwiseArrow G (chartPointHom G i) =
      G.toGroupoidInFunctors.identity _ (chartPoint G W₁).fiber :=
    evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _ (chartPointHom_eq i)
  have hk' : yoneda.map ((chartPointHom G i).base ≫ 𝟙 _) ≫ W₂.obj.hom =
      yonedaEquiv.symm (chartPoint G W₁).fiber := by
    rw [Category.comp_id, ← chartPoint_comm G W₁, yoneda.map_id, Category.id_comp]
    exact CostructuredArrow.w i.hom
  refine (pointSectionRestrict_pointChartSection G M (chartPointHom G i) hm W₂ (𝟙 _)
    (chartPoint_comm G W₂) hk' x).trans ?_
  have h₁ := (pointChartDiagram G (chartPoint G W₁) W₂ ((chartPointHom G i).base ≫ 𝟙 _) hk').comm
  have hg : (chartPointHom G i).base ≫ 𝟙 _ =
      𝟙 _ ≫ (Space.SmallEtale.toOver C S hS G.objects.obj).map i := by
    rw [Category.comp_id, Category.id_comp]
    rfl
  have h₂ : (Space.selfChart C S hS (chartPoint G W₁).base).1.hom ≫
      (pointMap G (chartPoint G W₁)).hom =
      yoneda.map (𝟙 _ ≫ (Space.SmallEtale.toOver C S hS G.objects.obj).map i) ≫ W₂.1.hom := by
    rw [← hg]
    exact h₁
  have e := Space.modulePullbackChartSection_restrictTarget (pointMap G (chartPoint G W₁))
    M.F.obj (U := Space.selfChart C S hS (chartPoint G W₁).base) i (𝟙 _) h₂
    (pointChartDiagram G (chartPoint G W₁) W₁ (𝟙 _) (chartPoint_comm G W₁)).comm x
  exact (Space.modulePullbackChartSection_congr C S hS _ M.F.obj h₁ h₂ hg x).trans e

end AlgebraicGeometry.Stack

end
