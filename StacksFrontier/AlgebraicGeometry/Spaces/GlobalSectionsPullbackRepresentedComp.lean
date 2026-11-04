module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionTransitionCocycle

/-!
# Pulling a global section back along a scheme point and then along a morphism of schemes

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `N` an `𝒪_X`-module and `σ` a
global section of `N`. For a scheme point `t : h_T ⟶ X` and a morphism `h : T' ⟶ T` of the site,
the global section `σ` can be pulled back to `h_{T'}` in two ways: along `t` and then along `h`,
or along the composite. This file proves that the comparison `h^*t^*N ≅ (h ≫ t)^*N` of
[Stacks, Tag 03LU] carries the first to the second.

## Main definitions

* `AlgebraicGeometry.Space.representedMap`: a morphism of the site, as a morphism of the
  algebraic spaces it represents.
* `AlgebraicGeometry.Space.representedChartPullback`: the étale chart `T ×_X V` of `h_T` cut out
  by an étale chart `V` of `X` along a scheme point `t`, with
  `AlgebraicGeometry.Space.representedChartPullbackDiagram` its diagram of charts over `t`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_globalSectionsPullbackMap_chartDiagram`: on a
  chart admitting a diagram of charts over the composite, the comparison of iterated inverse
  images carries the iterated pullback of a global section to its pullback along the composite.
* `AlgebraicGeometry.Space.modulePullbackCompIso_globalSectionsPullbackMap_represented`: the
  same on every étale chart of `h_{T'}`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site over `S`, as a morphism of the algebraic spaces it represents:
an abbreviation of `AlgebraicGeometry.schemeSpaceMap`. -/
abbrev representedMap {T' T : BigFppfOver B S hS} (h : T' ⟶ T) :
    representedAlgebraicSpace B S hS T' ⟶ representedAlgebraicSpace B S hS T :=
  schemeSpaceMap h

variable {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- The étale chart `T ×_X V` of `h_T` cut out by an étale chart `V` of `X` along a scheme
point `t : h_T ⟶ X`: the chosen represented pullback of the structure morphism of `V` along `t`,
with its projection to `T`, which is étale. -/
def representedChartPullback (t : yoneda.obj T ⟶ X.1) (V : SmallEtale B S hS X.1) :
    SmallEtale B S hS (yoneda.obj T) :=
  ⟨CostructuredArrow.mk (yoneda.map (V.2.rep.snd t)), by
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      inverseImage_isStableUnderBaseChange B S hS inferInstance
    exact MorphismProperty.relative_map (V.2.property_snd t)⟩

/-- The diagram of étale charts `T ×_X V ⟶ V` over a scheme point `t`. -/
def representedChartPullbackDiagram (t : representedAlgebraicSpace B S hS T ⟶ X)
    (V : SmallEtale B S hS X.1) :
    ChartDiagram B S hS (yoneda.obj T) X.1 t.hom where
  U := representedChartPullback B S hS t.hom V
  V := V
  g := V.2.rep.fst' t.hom
  comm := (V.2.rep.isPullback' t.hom).w.symm

/-- The chart section along a diagram of charts depends only on its two charts and its morphism
of charts. -/
theorem modulePullbackChartSection_congr_g {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (g' : (SmallEtale.toOver B S hS X.1).obj d.U ⟶ (SmallEtale.toOver B S hS Y.1).obj d.V)
    (hg' : g' = d.g) (hc : d.U.1.hom ≫ f.hom = yoneda.map g' ≫ d.V.1.hom)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f M ⟨d.U, d.V, g', hc⟩ s =
      modulePullbackChartSection B S hS f M d s := by
  subst hg'
  rfl

variable {T' : BigFppfOver B S hS}

/-- On a chart admitting a diagram of charts over the composite, the comparison of iterated
inverse images carries the iterated pullback of a global section to its pullback along the
composite. -/
theorem modulePullbackCompIso_globalSectionsPullbackMap_chartDiagram (h : T' ⟶ T)
    (t : representedAlgebraicSpace B S hS T ⟶ X) (N : Modules.{u, u} B S hS X.1 X.2)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj N)
    (e : ChartDiagram B S hS (yoneda.obj T') X.1 (representedMap B S hS h ≫ t).hom) :
    ((modulePullbackCompIso B S hS (representedMap B S hS h) t).hom.app N).val.app (op e.U)
        (((globalSectionsPullbackMap B S hS (representedMap B S hS h)
          ((modulePullback B S hS t).obj N)).hom
            ((globalSectionsPullbackMap B S hS t N).hom σ)).1 (op e.U)) =
      ((globalSectionsPullbackMap B S hS (representedMap B S hS h ≫ t) N).hom σ).1 (op e.U) := by
  let V := e.V
  let pre : e.U.obj.left ⟶ T' := Yoneda.fullyFaithful.preimage e.U.obj.hom
  have hpre : yoneda.map pre = e.U.obj.hom := Yoneda.fullyFaithful.map_preimage _
  have hi : yoneda.map e.g ≫ V.obj.hom = yoneda.map (pre ≫ h) ≫ t.hom := by
    rw [Functor.map_comp, Category.assoc, hpre]
    exact e.comm.symm
  let ℓ := V.2.rep.lift' e.g (pre ≫ h) hi
  have hℓ₁ : ℓ ≫ V.2.rep.fst' t.hom = e.g := V.2.rep.lift'_fst _ _ hi
  have hℓ₂ : ℓ ≫ V.2.rep.snd t.hom = pre ≫ h := V.2.rep.lift'_snd _ _ hi
  have ha : e.U.1.hom ≫ (representedMap B S hS h).hom =
      yoneda.map ℓ ≫ (representedChartPullback B S hS t.hom V).1.hom := by
    show e.U.obj.hom ≫ yoneda.map h = yoneda.map ℓ ≫ yoneda.map (V.2.rep.snd t.hom)
    rw [← Functor.map_comp, hℓ₂, Functor.map_comp, hpre]
  have hk : e.U.1.hom ≫ (representedMap B S hS h ≫ t).hom =
      yoneda.map (ℓ ≫ V.2.rep.fst' t.hom) ≫ V.1.hom := by
    rw [hℓ₁]
    exact e.comm
  have h1 := globalSectionsPullbackMap_val_chartDiagram B S hS (representedMap B S hS h)
    ((modulePullback B S hS t).obj N) ((globalSectionsPullbackMap B S hS t N).hom σ)
    ⟨e.U, representedChartPullback B S hS t.hom V, ℓ, ha⟩
  refine (congrArg (fun z => ((modulePullbackCompIso B S hS (representedMap B S hS h) t).hom.app
    N).val.app (op e.U) z) (h1.trans (congrArg _ (globalSectionsPullbackMap_val_chartDiagram B S hS
      t N σ (representedChartPullbackDiagram B S hS t V))))).trans ?_
  refine (modulePullbackCompIso_hom_chartSection (representedMap B S hS h) t N
    (U := e.U) (V := representedChartPullback B S hS t.hom V) (W := V) ℓ
    (V.2.rep.fst' t.hom) ha (representedChartPullbackDiagram B S hS t V).comm hk
    (σ.1 (op V))).trans ?_
  refine Eq.trans ?_
    (globalSectionsPullbackMap_val_chartDiagram B S hS (representedMap B S hS h ≫ t) N σ e).symm
  exact modulePullbackChartSection_congr_g B S hS (representedMap B S hS h ≫ t) N e _ hℓ₁ hk _

/-- The comparison of iterated inverse images carries the iterated pullback of a global section
to its pullback along the composite, on every étale chart of `h_{T'}`. -/
theorem modulePullbackCompIso_globalSectionsPullbackMap_represented (h : T' ⟶ T)
    (t : representedAlgebraicSpace B S hS T ⟶ X) (N : Modules.{u, u} B S hS X.1 X.2)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj N)
    (U : SmallEtale B S hS (yoneda.obj T')) :
    ((modulePullbackCompIso B S hS (representedMap B S hS h) t).hom.app N).val.app (op U)
        (((globalSectionsPullbackMap B S hS (representedMap B S hS h)
          ((modulePullback B S hS t).obj N)).hom
            ((globalSectionsPullbackMap B S hS t N).hom σ)).1 (op U)) =
      ((globalSectionsPullbackMap B S hS (representedMap B S hS h ≫ t) N).hom σ).1 (op U) := by
  obtain ⟨I, W, a, d, hdU, -, -, hcov⟩ :=
    exists_affine_chartDiagram_ofArrows B S hS (representedMap B S hS h ≫ t) U
  let a' : ∀ i, (d i).U ⟶ U := fun i => eqToHom (hdU i) ≫ a i
  have hcov' :
      Sieve.ofArrows (fun i => (d i).U) a' ∈ SmallEtale.topology B S hS (yoneda.obj T') U := by
    refine GrothendieckTopology.superset_covering _ ?_ hcov
    rintro Y f ⟨Z, g, k, ⟨i⟩, rfl⟩
    refine ⟨(d i).U, g ≫ eqToHom (hdU i).symm, a' i, ⟨i⟩, ?_⟩
    simp only [a', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  let κ := (modulePullbackCompIso B S hS (representedMap B S hS h) t).hom.app N
  let s₁ := (globalSectionsPullbackMap B S hS (representedMap B S hS h)
    ((modulePullback B S hS t).obj N)).hom ((globalSectionsPullbackMap B S hS t N).hom σ)
  let s₂ := (globalSectionsPullbackMap B S hS (representedMap B S hS h ≫ t) N).hom σ
  refine (Presieve.isSeparatedFor_iff_generate.2
    (Stacks.SheafOfModules.isSeparated_presheaf
      ((modulePullback B S hS (representedMap B S hS h ≫ t)).obj N) _ hcov')).ext ?_
  rintro Y f ⟨i⟩
  refine (PresheafOfModules.naturality_apply κ.val (a' i).op (s₁.1 (op U))).symm.trans ?_
  refine Eq.trans ?_ ((modulePullbackCompIso_globalSectionsPullbackMap_chartDiagram B S hS h t N σ
    (d i)).trans (s₂.2 (a' i).op).symm)
  exact congrArg (κ.val.app (op (d i).U)) (s₁.2 (a' i).op)

end AlgebraicGeometry.Space

end
