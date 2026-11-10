module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionTransitionCocycle
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackChartPointSection

/-!
# Sections of a module on a groupoid along the points of the charts of the arrows

Let `(𝒢, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces. An
étale chart `V` of `R` is a point `v` of `R` over `V`; a section of `s^*𝒢` over `V` gives, by the
chart section along `v`, a section of `(s ∘ v)^*𝒢` over `V`. This file computes the restriction
of `(T, a) ↦ Γ(T, a^*𝒢)` (the presheaf of the proof of Stacks 06WT) along the arrow of the
pointwise quotient given by `v`, on chart sections: it is `α` read on `V`.

## Main definitions

* `AlgebraicGeometry.Stack.arrowChartRestrict`: `(s^*𝒢)(V) ⟶ Γ(V, (s ∘ v)^*𝒢)`.

## Main results

* `AlgebraicGeometry.Space.transitionTwist_chartSection`: a transition read along a morphism,
  on chart sections.
* `AlgebraicGeometry.Stack.pointSectionRestrict_arrowChart`: the restriction along the arrow of
  `v` of the chart section of `x ∈ 𝒢(W)` is `α(t^*x)` read on `V`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Generic

variable {U V X : AlgebraicSpaces C S hS} (F : Modules.{u, u} C S hS U.1 U.2) {a b : V ⟶ U}
  (α : (modulePullback C S hS a).obj F ⟶ (modulePullback C S hS b).obj F)
  (r : X ⟶ V) {x y : X ⟶ U} (hx : r ≫ b = x) (hy : r ≫ a = y)
  (U₀ : SmallEtale C S hS X.1) (V₀ : SmallEtale C S hS V.1) (W₀ : SmallEtale C S hS U.1)
  (g₁ : (SmallEtale.toOver C S hS X.1).obj U₀ ⟶ (SmallEtale.toOver C S hS V.1).obj V₀)
  (g₂ : (SmallEtale.toOver C S hS V.1).obj V₀ ⟶ (SmallEtale.toOver C S hS U.1).obj W₀)
  (h₁ : U₀.1.hom ≫ r.hom = yoneda.map g₁ ≫ V₀.1.hom)
  (h₂ : V₀.1.hom ≫ a.hom = yoneda.map g₂ ≫ W₀.1.hom)
  (h : U₀.1.hom ≫ y.hom = yoneda.map (g₁ ≫ g₂) ≫ W₀.1.hom) (s : F.val.obj (op W₀))

/-- Transport along `r ≫ a = y` carries the chart section of `s` over the chart diagram with
morphism `g₁ ≫ g₂` to the chart section of `s` over the composed chart diagram of `r ≫ a`. -/
theorem pullbackTransport_symm_chartSection :
    (pullbackTransport F hy.symm).val.app (op U₀)
      (modulePullbackChartSection C S hS y F ⟨U₀, W₀, g₁ ≫ g₂, h⟩ s) =
      modulePullbackChartSection C S hS (r ≫ a) F
        (ChartDiagram.comp C S hS r a g₁ g₂ h₁ h₂) s := by
  subst hy
  rfl

/-- The reindexing of `α` along `r` carries the chart section of `s` over the composed chart
diagram of `r ≫ a` to the image under the comparison of `(r ≫ b)^*` with `r^* b^*` of the chart
section along `r` of `α` applied to the chart section of `s` along `a`. -/
theorem transitionReindex_chartSection :
    (transitionReindex C S hS F α r).val.app (op U₀)
      (modulePullbackChartSection C S hS (r ≫ a) F (ChartDiagram.comp C S hS r a g₁ g₂ h₁ h₂) s) =
      ((modulePullbackCompIso C S hS r b).app F).hom.val.app (op U₀)
        (modulePullbackChartSection C S hS r ((modulePullback C S hS b).obj F) ⟨U₀, V₀, g₁, h₁⟩
          (α.val.app (op V₀) (modulePullbackChartSection C S hS a F ⟨V₀, W₀, g₂, h₂⟩ s))) := by
  have e1 : ((modulePullbackCompIso C S hS r a).app F).inv.val.app (op U₀)
      (modulePullbackChartSection C S hS (r ≫ a) F (ChartDiagram.comp C S hS r a g₁ g₂ h₁ h₂) s) =
      modulePullbackChartSection C S hS r ((modulePullback C S hS a).obj F) ⟨U₀, V₀, g₁, h₁⟩
        (modulePullbackChartSection C S hS a F ⟨V₀, W₀, g₂, h₂⟩ s) :=
    modulePullbackCompIso_inv_chartSection C S hS r a F g₁ g₂ h₁ h₂ s
  have e2 := modulePullbackChartSection_map C S hS r _ α ⟨U₀, V₀, g₁, h₁⟩
    (modulePullbackChartSection C S hS a F ⟨V₀, W₀, g₂, h₂⟩ s)
  unfold transitionReindex
  refine (comp_val_app_apply C S hS _ _ _ _).trans ?_
  refine (comp_val_app_apply C S hS _ _ _ _).trans ?_
  rw [e1, e2]

/-- **A transition read along a morphism, on chart sections**: `α` twisted along `r` carries the
chart section of `s` over a composed chart diagram to the restriction along `r` of `α` applied to
the chart section of `s`. -/
theorem transitionTwist_chartSection :
    (transitionTwist F α r hx hy).val.app (op U₀)
      (modulePullbackChartSection C S hS y F ⟨U₀, W₀, g₁ ≫ g₂, h⟩ s) =
      (comp₃ ((modulePullbackCompIso C S hS r b).app F).hom (pullbackTransport F hx) (𝟙 _)).val.app
        (op U₀) (modulePullbackChartSection C S hS r ((modulePullback C S hS b).obj F)
          ⟨U₀, V₀, g₁, h₁⟩
          (α.val.app (op V₀) (modulePullbackChartSection C S hS a F ⟨V₀, W₀, g₂, h₂⟩ s))) := by
  have t : transitionTwist F α r hx hy = comp₃ (pullbackTransport F hy.symm)
      (transitionReindex C S hS F α r) (pullbackTransport F hx) := rfl
  rw [t]
  unfold comp₃
  refine (comp_val_app_apply C S hS _ _ _ _).trans ?_
  refine (comp_val_app_apply C S hS _ _ _ _).trans ?_
  rw [pullbackTransport_symm_chartSection F r hy U₀ V₀ W₀ g₁ g₂ h₁ h₂ h s,
    transitionReindex_chartSection F α r U₀ V₀ W₀ g₁ g₂ h₁ h₂ s]
  refine Eq.trans ?_ (comp_val_app_apply C S hS _ _ _ _).symm
  rw [Category.comp_id]

/-- The comparison of Stacks 03LU on iterated chart sections, landing on a chart diagram with
any vertical morphism equal to the composite. -/
theorem modulePullbackCompIso_app_hom_chartSection_of_eq {X' X Y : AlgebraicSpaces C S hS}
    (f : X' ⟶ X) (a : X ⟶ Y) (N : Modules.{u, u} C S hS Y.1 Y.2)
    (U : SmallEtale C S hS X'.1) (V : SmallEtale C S hS X.1) (W : SmallEtale C S hS Y.1)
    (g₁ : (SmallEtale.toOver C S hS X'.1).obj U ⟶ (SmallEtale.toOver C S hS X.1).obj V)
    (g₂ : (SmallEtale.toOver C S hS X.1).obj V ⟶ (SmallEtale.toOver C S hS Y.1).obj W)
    (h₁ : U.1.hom ≫ f.hom = yoneda.map g₁ ≫ V.1.hom)
    (h₂ : V.1.hom ≫ a.hom = yoneda.map g₂ ≫ W.1.hom)
    {g : (SmallEtale.toOver C S hS X'.1).obj U ⟶ (SmallEtale.toOver C S hS Y.1).obj W}
    (hg : g₁ ≫ g₂ = g) (h : U.1.hom ≫ (f ≫ a).hom = yoneda.map g ≫ W.1.hom) (x : N.val.obj (op W)) :
    ((modulePullbackCompIso C S hS f a).app N).hom.val.app (op U)
      (modulePullbackChartSection C S hS f ((modulePullback C S hS a).obj N) ⟨U, V, g₁, h₁⟩
        (modulePullbackChartSection C S hS a N ⟨V, W, g₂, h₂⟩ x)) =
      modulePullbackChartSection C S hS (f ≫ a) N ⟨U, W, g, h⟩ x := by
  subst hg
  exact modulePullbackCompIso_hom_chartSection f a N g₁ g₂ h₁ h₂ h x

end Generic

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- The point `v` of `R` given by an étale chart `V` of `R`. -/
def chartArrowMap (V : Space.SmallEtale C S hS G.arrows.obj) :
    Space.yonedaSpace C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V) ⟶ G.arrows :=
  ObjectProperty.homMk V.obj.hom

/-- The composite `s ∘ v` of the point `v` of a chart `V` of `R` with the source is the point of
the objects given by `arrowChartPoint G V`. -/
theorem chartArrowMap_source (V : Space.SmallEtale C S hS G.arrows.obj) :
    chartArrowMap G V ≫ G.source = pointMap G (arrowChartPoint G V) := by
  refine ObjectProperty.hom_ext _ ?_
  change V.obj.hom ≫ G.source.hom = yonedaEquiv.symm (G.source.hom.app _ (yonedaEquiv V.obj.hom))
  rw [← yonedaEquiv_symm_comp', Equiv.symm_apply_apply]

/-- The self chart of `V` and the identity form a commutative square over the point `v` of `R`
given by `V`. -/
theorem chartArrowMap_comm (V : Space.SmallEtale C S hS G.arrows.obj) :
    (Space.selfChart C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V)).1.hom ≫
      (chartArrowMap G V).hom = yoneda.map (𝟙 _) ≫ V.1.hom :=
  (Category.id_comp _).trans ((Category.id_comp _).symm.trans
    (congrArg (· ≫ V.1.hom) (yoneda.map_id _).symm))

/-- A section of `s^*𝒢` over a chart `V` of `R`, restricted along a point `r` of `R` through
`V`, read as a section of `(s ∘ r)^*𝒢`. -/
def arrowRestrict {T : BigFppfOver C S hS} (V : Space.SmallEtale C S hS G.arrows.obj)
    (r : Space.yonedaSpace C S hS T ⟶ G.arrows)
    (b : T ⟶ (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V)
    (hd : (Space.selfChart C S hS T).1.hom ≫ r.hom = yoneda.map b ≫ V.1.hom)
    {x : Space.yonedaSpace C S hS T ⟶ G.objects} (hx : r ≫ G.source = x)
    (z : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    ((Space.modulePullback C S hS x).obj M.F.obj).val.obj (op (Space.selfChart C S hS T)) :=
  chartRestrict r ((Space.modulePullback C S hS G.source).obj M.F.obj)
    ((Space.modulePullback C S hS x).obj M.F.obj)
    (comp₃ ((Space.modulePullbackCompIso C S hS r G.source).app M.F.obj).hom
      (Space.pullbackTransport M.F.obj hx) (𝟙 _)) ⟨Space.selfChart C S hS T, V, b, hd⟩ z

/-- `arrowRestrict` takes equal values on equal points `r = r'` and equal morphisms `b = b'`. -/
theorem arrowRestrict_congr {T : BigFppfOver C S hS} (V : Space.SmallEtale C S hS G.arrows.obj)
    {r r' : Space.yonedaSpace C S hS T ⟶ G.arrows}
    {b b' : T ⟶ (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V} (hr : r = r') (hb : b = b')
    (hd : (Space.selfChart C S hS T).1.hom ≫ r.hom = yoneda.map b ≫ V.1.hom)
    (hd' : (Space.selfChart C S hS T).1.hom ≫ r'.hom = yoneda.map b' ≫ V.1.hom)
    {x : Space.yonedaSpace C S hS T ⟶ G.objects} (hx : r ≫ G.source = x) (hx' : r' ≫ G.source = x)
    (z : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    arrowRestrict G M V r b hd hx z = arrowRestrict G M V r' b' hd' hx' z := by
  subst hr hb
  rfl

/-- **`(s^*𝒢)(V) ⟶ Γ(V, (s ∘ v)^*𝒢)`**, the chart section along the point `v` of `R` given by an
étale chart `V` of `R`, read through `s ∘ v`. -/
def arrowChartRestrict (V : Space.SmallEtale C S hS G.arrows.obj)
    (z : ((Space.modulePullback C S hS G.source).obj M.F.obj).val.obj (op V)) :
    pointSections G M (arrowChartPoint G V) :=
  arrowRestrict G M V (chartArrowMap G V) (𝟙 _) (chartArrowMap_comm G V)
    (chartArrowMap_source G V) z

/-- **The transition along points on chart sections**: restricting the chart section of `x` along
`f` through the transition of an arrow `r` is restricting `α(t^*x)` along `r`. -/
theorem chartRestrict_pointTransition {X X' : AlgebraicSpaces C S hS} (f : X' ⟶ X)
    (a : X ⟶ G.objects) {a' : X' ⟶ G.objects} (r : X' ⟶ G.arrows) (hs : r ≫ G.source = a')
    (ht : r ≫ G.target = f ≫ a) (U₀ : Space.SmallEtale C S hS X'.1)
    (V₀ : Space.SmallEtale C S hS X.1) (V₁ : Space.SmallEtale C S hS G.arrows.obj)
    (W₀ : Space.SmallEtale C S hS G.objects.obj)
    (g₁ : (Space.SmallEtale.toOver C S hS X'.1).obj U₀ ⟶
      (Space.SmallEtale.toOver C S hS X.1).obj V₀)
    (g₂ : (Space.SmallEtale.toOver C S hS X.1).obj V₀ ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W₀)
    (h₁ : U₀.1.hom ≫ f.hom = yoneda.map g₁ ≫ V₀.1.hom)
    (h₂ : V₀.1.hom ≫ a.hom = yoneda.map g₂ ≫ W₀.1.hom)
    (b : (Space.SmallEtale.toOver C S hS X'.1).obj U₀ ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₁)
    (k : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₁ ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W₀)
    (hb : U₀.1.hom ≫ r.hom = yoneda.map b ≫ V₁.1.hom)
    (hk : V₁.1.hom ≫ G.target.hom = yoneda.map k ≫ W₀.1.hom) (heq : g₁ ≫ g₂ = b ≫ k)
    (x : M.F.obj.val.obj (op W₀))
    (φ : (Space.modulePullback C S hS f).obj ((Space.modulePullback C S hS a).obj M.F.obj) ⟶
      (Space.modulePullback C S hS a').obj M.F.obj)
    (hφ : φ = comp₃ ((Space.modulePullbackCompIso C S hS f a).app M.F.obj).hom
      (Space.transitionTwist M.F.obj M.alpha r hs ht) (𝟙 _)) :
    chartRestrict f ((Space.modulePullback C S hS a).obj M.F.obj)
        ((Space.modulePullback C S hS a').obj M.F.obj) φ
        ⟨U₀, V₀, g₁, h₁⟩ (Space.modulePullbackChartSection C S hS a M.F.obj ⟨V₀, W₀, g₂, h₂⟩ x) =
      chartRestrict r ((Space.modulePullback C S hS G.source).obj M.F.obj)
        ((Space.modulePullback C S hS a').obj M.F.obj)
        (comp₃ ((Space.modulePullbackCompIso C S hS r G.source).app M.F.obj).hom
          (Space.pullbackTransport M.F.obj hs) (𝟙 _)) ⟨U₀, V₁, b, hb⟩
        (M.alpha.val.app (op V₁)
          (Space.modulePullbackChartSection C S hS G.target M.F.obj ⟨V₁, W₀, k, hk⟩ x)) := by
  have h' : U₀.1.hom ≫ (f ≫ a).hom = yoneda.map (b ≫ k) ≫ W₀.1.hom :=
    heq ▸ (Space.ChartDiagram.comp C S hS f a g₁ g₂ h₁ h₂).comm
  have hC := Space.modulePullbackCompIso_app_hom_chartSection_of_eq f a M.F.obj U₀ V₀ W₀ g₁ g₂
    h₁ h₂ heq h' x
  have hT := Space.transitionTwist_chartSection M.F.obj M.alpha r hs ht U₀ V₁ W₀ b k hb hk h' x
  refine (chartRestrict_mk f _ _ φ U₀ V₀ g₁ h₁ _).trans ?_
  rw [hφ]
  exact (comp₃_id_val_app_eq ((Space.modulePullbackCompIso C S hS f a).app M.F.obj).hom
    (Space.transitionTwist M.F.obj M.alpha r hs ht) _ _ _ hC hT).trans
    (chartRestrict_mk r _ _ _ U₀ V₁ b hb _).symm

/-- The point of `R` of an arrow of the pointwise quotient whose point of `R` is that of a chart
`V` of `R` is the point `v` of `V`. -/
theorem arrowMap_eq_chartArrowMap {V : Space.SmallEtale C S hS G.arrows.obj}
    {Y : PointwiseFibration G} (gt : arrowChartPoint G V ⟶ Y)
    (harr : pointwiseArrow G gt = yonedaEquiv V.obj.hom) :
    arrowMap G gt = chartArrowMap G V :=
  ObjectProperty.hom_ext _ ((congrArg yonedaEquiv.symm harr).trans
    (Equiv.symm_apply_apply yonedaEquiv V.obj.hom))

/-- For an arrow `gt` of the pointwise quotient out of the chart point of `V` with identity base
whose point of `R` is that of `V`, the self chart of `V` and `gt.base` form a commutative square
over the point of `R` of `gt`. -/
theorem arrowMap_comm {V : Space.SmallEtale C S hS G.arrows.obj}
    {y : G.objects.obj.obj (op ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V))}
    (gt : arrowChartPoint G V ⟶ (⟨_, y⟩ : PointwiseFibration G)) (hb : gt.base = 𝟙 _)
    (harr : pointwiseArrow G gt = yonedaEquiv V.obj.hom) :
    (Space.selfChart C S hS ((Space.SmallEtale.toOver C S hS G.arrows.obj).obj V)).1.hom ≫
      (arrowMap G gt).hom = yoneda.map gt.base ≫ V.1.hom := by
  rw [hb, arrowMap_eq_chartArrowMap G gt harr]
  exact chartArrowMap_comm G V

/-- **The restriction along the arrow of a chart `V` of `R`**: the restriction of
`(T, a) ↦ Γ(T, a^*𝒢)` along the arrow `(V, s ∘ v) ⟶ (V, t ∘ v)` of the pointwise quotient given
by `v` carries the chart section of `x ∈ 𝒢(W)` (through a square `k` over `t`) to
`α(t^*x)` read on `V`. -/
theorem pointSectionRestrict_arrowChart (V : Space.SmallEtale C S hS G.arrows.obj)
    (W : Space.SmallEtale C S hS G.objects.obj)
    (k : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hcomm : V.1.hom ≫ G.target.hom = yoneda.map k ≫ W.1.hom)
    (gt : arrowChartPoint G V ⟶ (⟨(Space.SmallEtale.toOver C S hS G.arrows.obj).obj V,
      G.target.hom.app _ (yonedaEquiv V.obj.hom)⟩ : PointwiseFibration G))
    (hb : gt.base = 𝟙 _) (harr : pointwiseArrow G gt = yonedaEquiv V.obj.hom)
    (hk : yoneda.map k ≫ W.obj.hom = yonedaEquiv.symm (G.target.hom.app _ (yonedaEquiv V.obj.hom)))
    (x : M.F.obj.val.obj (op W)) :
    pointSectionRestrict G M gt (pointChartSection G M ⟨_, _⟩ W k hk x) =
      arrowChartRestrict G M V (M.alpha.val.app (op V)
        (Space.modulePullbackChartSection C S hS G.target M.F.obj ⟨V, W, k, hcomm⟩ x)) := by
  have h₁ := arrowMap_comm G gt hb harr
  refine (chartRestrict_pointTransition G M (baseMap gt.base) (pointMap G _) (arrowMap G gt)
    (arrowMap_source G gt) (arrowMap_target G gt) (Space.selfChart C S hS _)
    (Space.selfChart C S hS _) V W gt.base k (Space.selfChartDiagram C S hS gt.base).comm
    (pointChartDiagram G ⟨_, _⟩ W k hk).comm gt.base k h₁ hcomm rfl x
    (pointwiseTransition G M gt) rfl).trans ?_
  exact arrowRestrict_congr G M V (arrowMap_eq_chartArrowMap G gt harr) hb h₁
    (chartArrowMap_comm G V) (arrowMap_source G gt) (chartArrowMap_source G V) _

end AlgebraicGeometry.Stack

end
