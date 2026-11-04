module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage

/-!
# Morphisms out of an iterated inverse image are determined on iterated chart sections

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big
fppf site `B` and let `M` be an `𝒪_Z`-module.  A morphism out of `f^*g^*M` is determined by its
values on the sections `f^*(g^*s)` attached to a chart diagram over `f` followed by a chart
diagram over `g` (`AlgebraicGeometry.Space.modulePullback_comp_hom_ext`).

The values of a morphism out of `(f ≫ g)^*M` on the chart sections of *all* chart diagrams over
`f ≫ g` determine it; through the chart formula of the comparison of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackCompIso_inv_chartSection`) the chart sections of the
diagrams which factor through an étale chart of `Y` are iterated chart sections.  The factoring
diagrams are not all diagrams, but every chart diagram over `f ≫ g` factors étale locally on
its source (`AlgebraicGeometry.Space.restrictSource_mem_topology`): an atlas of `Y`, base
changed along the target chart, is an étale chart of `Y` mapping to the target chart, and a
neighbourhood of every point of the source maps to it.  Sections of a sheaf are separated, and
chart sections are compatible with restriction of the source chart.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.restrictSource`: a chart diagram restricted along a
  morphism into its source chart.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartSection_restrictSource`: chart sections are
  compatible with that restriction.
* `AlgebraicGeometry.Space.restrictSource_mem_topology`: every chart diagram over `f ≫ g`
  factors on a covering of its source.
* `AlgebraicGeometry.Space.modulePullback_comp_hom_ext`: **the extensionality principle.**

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- A chart diagram over `f` restricted along a morphism `i : U' ⟶ e.U` of étale charts of the
source: the same target chart, with vertical morphism `i` followed by that of `e`. -/
def ChartDiagram.restrictSource {f : X ⟶ Y} (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    {U' : SmallEtale B S hS X.1} (i : U' ⟶ e.U) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := U'
  V := e.V
  g := (SmallEtale.toOver B S hS X.1).map i ≫ e.g
  comm := by
    have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map i) ≫ e.U.1.hom = U'.1.hom :=
      CostructuredArrow.w i.hom
    rw [Functor.map_comp, Category.assoc, ← e.comm, ← Category.assoc, hw]

/-- **Chart sections are compatible with restriction of the source chart.** -/
theorem modulePullbackChartSection_restrictSource (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (e : ChartDiagram B S hS X.1 Y.1 f.hom) {U' : SmallEtale B S hS X.1} (i : U' ⟶ e.U)
    (s : M.val.obj (op e.V)) :
    ((modulePullback B S hS f).obj M).val.map i.op (modulePullbackChartSection B S hS f M e s) =
      modulePullbackChartSection B S hS f M (e.restrictSource B S hS i) s := by
  have h := (modulePullbackChartFMap B S hS f M).naturality e (e.restrictSource B S hS i) i
    (𝟙 e.V) (by simp [ChartDiagram.restrictSource]) s
  have h₁ : M.val.map (𝟙 e.V).op s = s := PresheafOfModules.map_id_apply M.val (op e.V) s
  exact (congrArg (fun x ↦ ((modulePullback B S hS f).obj M).val.map i.op x)
      (modulePullbackChartFMap_app B S hS f M e s).symm).trans
    (h.symm.trans ((congrArg ((modulePullbackChartFMap B S hS f M).app
      (e.restrictSource B S hS i)) h₁).trans
      (modulePullbackChartFMap_app B S hS f M (e.restrictSource B S hS i) s)))

/-- Chart sections over two chart diagrams with the same charts and equal vertical morphisms
agree. -/
theorem modulePullbackChartSection_congr (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g₁ g₂ : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    (h₁ : U.1.hom ≫ f.hom = yoneda.map g₁ ≫ V.1.hom)
    (h₂ : U.1.hom ≫ f.hom = yoneda.map g₂ ≫ V.1.hom) (hg : g₁ = g₂) (s : M.val.obj (op V)) :
    modulePullbackChartSection B S hS f M ⟨U, V, g₁, h₁⟩ s =
      modulePullbackChartSection B S hS f M ⟨U, V, g₂, h₂⟩ s := by
  subst hg
  rfl

/-- Restriction along a composite, when the restrictions along the second factor agree. -/
theorem _root_.Stacks.SheafOfModules.ChangeOfRings.map_comp_eq_of_map_eq {C : Type*}
    [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (N : SheafOfModules.{u} R) {A A' A'' : C} (k : A' ⟶ A) (j : A'' ⟶ A')
    {t t' : N.val.obj (op A)} (h : N.val.map k.op t = N.val.map k.op t') :
    N.val.map (j ≫ k).op t = N.val.map (j ≫ k).op t' := by
  rw [op_comp, PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply, h]

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A chart diagram over `f ≫ g` *factors* when it is the composite of a chart diagram over `f`
and a chart diagram over `g`. -/
def ChartDiagram.Factors (e : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) : Prop :=
  ∃ (V : SmallEtale B S hS Y.1)
    (a : (SmallEtale.toOver B S hS X.1).obj e.U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj e.V)
    (_ : e.U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (_ : V.1.hom ≫ g.hom = yoneda.map b ≫ e.V.1.hom), e.g = a ≫ b

/-- **Every chart diagram over `f ≫ g` factors on a covering of its source.**  The sieve of
morphisms into the source chart along which the restricted diagram factors is a covering sieve
of the small étale site of `X`. -/
theorem restrictSource_mem_topology (e : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) :
    Sieve.generate (fun (U' : SmallEtale B S hS X.1) (i : U' ⟶ e.U) ↦
        ChartDiagram.Factors B S hS f g (e.restrictSource B S hS i)) ∈
      SmallEtale.topology B S hS X.1 e.U := by
  obtain ⟨A₀, g₀, hg₀S, hg₀E⟩ := Y.2.exists_atlas
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 e.U _ fun z ↦ ?_
  obtain ⟨U₁, π, q, hq, z₁, hz₁⟩ :=
    exists_chart_over B S hS f e.U ⟨CostructuredArrow.mk g₀, hg₀E⟩ hg₀S z
  have hW := e.V.property
  set P := hW.rep.pullback (g₀ ≫ g.hom)
  have hsnd : Etale ((BigFppfOver.toScheme B S hS).map (hW.rep.snd (g₀ ≫ g.hom))) :=
    hW.property (g₀ ≫ g.hom) (hW.rep.fst (g₀ ≫ g.hom)) (hW.rep.snd (g₀ ≫ g.hom))
      (hW.rep.isPullback (g₀ ≫ g.hom))
  let VP : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk (yoneda.map (hW.rep.snd (g₀ ≫ g.hom)) ≫ g₀),
      etale_comp_of_scheme B S hS _ _ hsnd hg₀E⟩
  have hsq : yoneda.map ((SmallEtale.toOver B S hS X.1).map π ≫ e.g) ≫ e.V.1.hom =
      yoneda.map q ≫ (g₀ ≫ g.hom) := by
    refine (e.restrictSource B S hS π).comm.symm.trans ?_
    change U₁.1.hom ≫ f.hom ≫ g.hom = _
    rw [← Category.assoc, ← hq, Category.assoc]
    rfl
  let ℓ : (SmallEtale.toOver B S hS X.1).obj U₁ ⟶ P :=
    hW.rep.lift' ((SmallEtale.toOver B S hS X.1).map π ≫ e.g) q hsq
  have hmem : ChartDiagram.Factors B S hS f g (e.restrictSource B S hS π) := by
    refine ⟨VP, ℓ, hW.rep.fst' (g₀ ≫ g.hom), ?_, ?_, ?_⟩
    · change U₁.1.hom ≫ f.hom = yoneda.map ℓ ≫ yoneda.map (hW.rep.snd (g₀ ≫ g.hom)) ≫ g₀
      rw [← Category.assoc, ← Functor.map_comp, hW.rep.lift'_snd]
      exact hq.symm
    · change (yoneda.map (hW.rep.snd (g₀ ≫ g.hom)) ≫ g₀) ≫ g.hom = _
      rw [Category.assoc]
      exact ((hW.rep.isPullback' (g₀ ≫ g.hom)).w).symm
    · exact (hW.rep.lift'_fst _ _ hsq).symm
  exact ⟨U₁, π, Sieve.le_generate _ U₁ π hmem, z₁, hz₁⟩

/-- **Morphisms out of an iterated inverse image are determined on iterated chart sections.**
Two morphisms `f^*g^*M ⟶ N` which agree on every section `f^*(g^*s)` attached to a chart
diagram over `f` followed by a chart diagram over `g` are equal. -/
theorem modulePullback_comp_hom_ext (M : Modules.{u, u} B S hS Z.1 Z.2)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (P Q : (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M) ⟶ N)
    (h : ∀ {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
      (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
      (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
      (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom) (s : M.val.obj (op W)),
      P.val.app (op U) (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M)
          ⟨U, V, a, ha⟩ (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s)) =
        Q.val.app (op U) (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M)
          ⟨U, V, a, ha⟩ (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s))) :
    P = Q := by
  suffices hc : (modulePullbackCompIso B S hS f g).inv.app M ≫ P =
      (modulePullbackCompIso B S hS f g).inv.app M ≫ Q from
    (Iso.cancel_iso_inv_left ((modulePullbackCompIso B S hS f g).app M) P Q).1 hc
  refine injective_modulePullbackHomFMap B S hS (f ≫ g) M N
    (ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_))
  rw [modulePullbackHomFMap_app, modulePullbackHomFMap_app,
    modulePullbackUnitSection_eq_modulePullbackChartSection]
  refine Stacks.SheafOfModules.ChangeOfRings.sections_ext N
    (restrictSource_mem_topology B S hS f g e) ?_
  rintro U' i ⟨U'', j, k, ⟨V, a, b, ha, hb, hk⟩, rfl⟩
  refine Stacks.SheafOfModules.ChangeOfRings.map_comp_eq_of_map_eq N k j ?_
  have key : ∀ T : (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M) ⟶ N,
      N.val.map k.op (((modulePullbackCompIso B S hS f g).inv.app M ≫ T).val.app (op e.U)
          (modulePullbackChartSection B S hS (f ≫ g) M e s)) =
        T.val.app (op U'') (modulePullbackChartSection B S hS f
          ((modulePullback B S hS g).obj M) ⟨U'', V, a, ha⟩
          (modulePullbackChartSection B S hS g M ⟨V, e.V, b, hb⟩ s)) := by
    intro T
    refine (PresheafOfModules.naturality_apply
      ((modulePullbackCompIso B S hS f g).inv.app M ≫ T).val k.op _).symm.trans ?_
    refine (congrArg (fun x ↦ (((modulePullbackCompIso B S hS f g).inv.app M ≫ T).val.app
      (op U'')) x) (modulePullbackChartSection_restrictSource B S hS (f ≫ g) M e k s)).trans ?_
    refine (congrArg (fun x ↦ (((modulePullbackCompIso B S hS f g).inv.app M ≫ T).val.app
      (op U'')) x) (modulePullbackChartSection_congr B S hS (f ≫ g) M _
        (ChartDiagram.comp B S hS f g a b ha hb).comm hk s)).trans ?_
    refine (comp_val_app_apply B S hS ((modulePullbackCompIso B S hS f g).inv.app M) T
      (op U'') _).trans ?_
    exact congrArg (fun x ↦ T.val.app (op U'') x)
      (modulePullbackCompIso_inv_chartSection B S hS f g M a b ha hb s)
  exact (key P).trans ((h a b ha hb s).trans (key Q).symm)

end AlgebraicGeometry.Space

end
