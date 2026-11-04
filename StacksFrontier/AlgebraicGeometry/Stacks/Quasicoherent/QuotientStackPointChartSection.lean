module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointTransitionUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionTransitionCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompHomExt
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackPointSections

/-!
# Chart sections at points of the pointwise quotient

Let `(𝒢, α)` be a quasi-coherent module on a groupoid `(U, R, s, t, c)` in algebraic spaces and
let `(T, a)` be a point of `U` whose map `a : T ⟶ U` factors through an étale chart `W` of `U`.
A section `x` of `𝒢` over `W` gives the *chart section* `a^*x ∈ Γ(T, a^*𝒢)`. This file shows that
the restriction maps of the presheaf `(T, a) ↦ Γ(T, a^*𝒢)` of the proof of Stacks 06WT carry
chart sections to chart sections along every arrow whose point of `R` is an identity: there the
transition `α` drops out by the unit condition of Stacks 0441.

## Main definitions

* `AlgebraicGeometry.Stack.pointChartSection`: the chart section `a^*x ∈ Γ(T, a^*𝒢)`.

## Main results

* `AlgebraicGeometry.Stack.pointSectionRestrict_pointChartSection`: restriction along an arrow
  with identity point of `R` carries `a^*x` to `a'^*x`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

omit G in
/-- Evaluating `comp₃ a b 𝟙` on a section is evaluating `a`, then `b`. -/
theorem comp₃_id_val_app_apply {Z : AlgebraicSpaces C S hS}
    {M₁ M₂ M₃ : Space.Modules.{u, u} C S hS Z.1 Z.2} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (W : (Space.SmallEtale C S hS Z.1)ᵒᵖ) (w : M₁.val.obj W) :
    (comp₃ a b (𝟙 M₃)).val.app W w = b.val.app W (a.val.app W w) := by
  unfold comp₃
  rw [Category.comp_id]
  exact Space.comp_val_app_apply C S hS a b W w

omit G in
/-- Evaluating `comp₃ a b 𝟙` on a section, factor by factor. -/
theorem comp₃_id_val_app_eq {Z : AlgebraicSpaces C S hS}
    {M₁ M₂ M₃ : Space.Modules.{u, u} C S hS Z.1 Z.2} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    {W : (Space.SmallEtale C S hS Z.1)ᵒᵖ} (w : M₁.val.obj W) (w' : M₂.val.obj W)
    (w'' : M₃.val.obj W) (ha : a.val.app W w = w') (hb : b.val.app W w' = w'') :
    (comp₃ a b (𝟙 M₃)).val.app W w = w'' :=
  (comp₃_id_val_app_apply a b W w).trans ((congrArg (b.val.app W) ha).trans hb)

section ChartSections

omit G

variable {X' X Y : AlgebraicSpaces C S hS} (f : X' ⟶ X) (a : X ⟶ Y) {a' : X' ⟶ Y}
  (hfa : f ≫ a = a') (N : Space.Modules.{u, u} C S hS Y.1 Y.2)
  (U : Space.SmallEtale C S hS X'.1) (V : Space.SmallEtale C S hS X.1)
  (W : Space.SmallEtale C S hS Y.1)
  (g₁ : (Space.SmallEtale.toOver C S hS X'.1).obj U ⟶ (Space.SmallEtale.toOver C S hS X.1).obj V)
  (g₂ : (Space.SmallEtale.toOver C S hS X.1).obj V ⟶ (Space.SmallEtale.toOver C S hS Y.1).obj W)
  (h₁ : U.1.hom ≫ f.hom = yoneda.map g₁ ≫ V.1.hom) (h₂ : V.1.hom ≫ a.hom = yoneda.map g₂ ≫ W.1.hom)
  (h : U.1.hom ≫ a'.hom = yoneda.map (g₁ ≫ g₂) ≫ W.1.hom) (x : N.val.obj (op W))

/-- `chartRestrict` at a chart diagram given by its components. -/
theorem chartRestrict_mk (N' : Space.Modules.{u, u} C S hS X.1 X.2)
    (P : Space.Modules.{u, u} C S hS X'.1 X'.2)
    (φ : (Space.modulePullback C S hS f).obj N' ⟶ P) (U : Space.SmallEtale C S hS X'.1)
    (V : Space.SmallEtale C S hS X.1)
    (g₁ : (Space.SmallEtale.toOver C S hS X'.1).obj U ⟶ (Space.SmallEtale.toOver C S hS X.1).obj V)
    (h₁ : U.1.hom ≫ f.hom = yoneda.map g₁ ≫ V.1.hom) (s : N'.val.obj (op V)) :
    chartRestrict f N' P φ ⟨U, V, g₁, h₁⟩ s =
      φ.val.app (op U) (Space.modulePullbackChartSection C S hS f N' ⟨U, V, g₁, h₁⟩ s) :=
  rfl

/-- The comparison of Stacks 03LU on iterated chart sections, written with `Iso.app`. -/
theorem modulePullbackCompIso_app_hom_chartSection :
    ((Space.modulePullbackCompIso C S hS f a).app N).hom.val.app (op U)
      (Space.modulePullbackChartSection C S hS f ((Space.modulePullback C S hS a).obj N)
        ⟨U, V, g₁, h₁⟩ (Space.modulePullbackChartSection C S hS a N ⟨V, W, g₂, h₂⟩ x)) =
      Space.modulePullbackChartSection C S hS (f ≫ a) N
        (Space.ChartDiagram.comp C S hS f a g₁ g₂ h₁ h₂) x :=
  Space.modulePullbackCompIso_hom_chartSection_comp f a N g₁ g₂ h₁ h₂ x

/-- The transport along `f ≫ a = a'` on the chart section of a composed chart diagram. -/
theorem pullbackTransport_comp_chartSection :
    (Space.pullbackTransport N hfa).val.app (op U)
      (Space.modulePullbackChartSection C S hS (f ≫ a) N
        (Space.ChartDiagram.comp C S hS f a g₁ g₂ h₁ h₂) x) =
      Space.modulePullbackChartSection C S hS a' N ⟨U, W, g₁ ≫ g₂, h⟩ x := by
  subst hfa
  rfl

/-- **The comparison of Stacks 03LU followed by a transport, on iterated chart sections.** -/
theorem chartRestrict_compIso_transport
    (φ : (Space.modulePullback C S hS f).obj ((Space.modulePullback C S hS a).obj N) ⟶
      (Space.modulePullback C S hS a').obj N)
    (hφ : φ = comp₃ ((Space.modulePullbackCompIso C S hS f a).app N).hom
      (Space.pullbackTransport N hfa) (𝟙 _)) :
    chartRestrict f ((Space.modulePullback C S hS a).obj N) ((Space.modulePullback C S hS a').obj N)
        φ ⟨U, V, g₁, h₁⟩ (Space.modulePullbackChartSection C S hS a N ⟨V, W, g₂, h₂⟩ x) =
      Space.modulePullbackChartSection C S hS a' N ⟨U, W, g₁ ≫ g₂, h⟩ x := by
  refine (chartRestrict_mk f _ _ φ U V g₁ h₁ _).trans ?_
  rw [hφ]
  exact comp₃_id_val_app_eq ((Space.modulePullbackCompIso C S hS f a).app N).hom
    (Space.pullbackTransport N hfa) _ _ _
    (modulePullbackCompIso_app_hom_chartSection f a N U V W g₁ g₂ h₁ h₂ x)
    (pullbackTransport_comp_chartSection f a hfa N U V W g₁ g₂ h₁ h₂ h x)

end ChartSections

/-- The chart diagram of a point `(T, a)` of `U` through an étale chart `W` of `U`: the identity
chart of `T` over `W`, joined by a factorization `k` of `a`. -/
def pointChartDiagram (X : PointwiseFibration G) (W : Space.SmallEtale C S hS G.objects.obj)
    (k : X.base ⟶ (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hk : yoneda.map k ≫ W.obj.hom = yonedaEquiv.symm X.fiber) :
    Space.ChartDiagram C S hS (Space.yonedaSpace C S hS X.base).1 G.objects.obj
      (pointMap G X).hom where
  U := Space.selfChart C S hS X.base
  V := W
  g := k
  comm := (Category.id_comp _).trans hk.symm

/-- **The chart section `a^*x ∈ Γ(T, a^*𝒢)`** of a section `x` of `𝒢` over an étale chart `W`
of `U` through which the point `a` factors. -/
def pointChartSection (X : PointwiseFibration G) (W : Space.SmallEtale C S hS G.objects.obj)
    (k : X.base ⟶ (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hk : yoneda.map k ≫ W.obj.hom = yonedaEquiv.symm X.fiber)
    (x : M.F.obj.val.obj (op W)) : pointSections G M X :=
  Space.modulePullbackChartSection C S hS (pointMap G X) M.F.obj (pointChartDiagram G X W k hk) x

/-- An arrow of the pointwise fibration whose point of `R` is an identity is classified by the
unit composed with its source. -/
theorem arrowMap_eq_comp_identityArrow {X Y : PointwiseFibration G} (m : X ⟶ Y)
    (hm : pointwiseArrow G m = G.toGroupoidInFunctors.identity _ X.fiber) :
    arrowMap G m = pointMap G X ≫ GroupoidInAlgebraicSpaces.identityArrow G := by
  refine ObjectProperty.hom_ext _ ?_
  change yonedaEquiv.symm (pointwiseArrow G m) =
    yonedaEquiv.symm X.fiber ≫ (GroupoidInAlgebraicSpaces.identityArrow G).hom
  exact (congrArg yonedaEquiv.symm (hm.trans
    (GroupoidInAlgebraicSpaces.identityArrow_hom_app G _ X.fiber).symm)).trans
    (yonedaEquiv_symm_comp' X.fiber _).symm

/-- Along an arrow whose point of `R` is an identity the two points agree after restriction. -/
theorem baseMap_comp_pointMap_of_identity {X Y : PointwiseFibration G} (m : X ⟶ Y)
    (hm : pointwiseArrow G m = G.toGroupoidInFunctors.identity _ X.fiber) :
    baseMap m.base ≫ pointMap G Y = pointMap G X := by
  refine (arrowMap_target G m).symm.trans ?_
  rw [arrowMap_eq_comp_identityArrow G m hm, Category.assoc,
    GroupoidInAlgebraicSpaces.identityArrow_comp_target, Category.comp_id]

/-- **Restriction carries chart sections to chart sections** along an arrow of the pointwise
fibration whose point of `R` is an identity. -/
theorem pointSectionRestrict_pointChartSection {X Y : PointwiseFibration G} (m : X ⟶ Y)
    (hm : pointwiseArrow G m = G.toGroupoidInFunctors.identity _ X.fiber)
    (W : Space.SmallEtale C S hS G.objects.obj)
    (k : Y.base ⟶ (Space.SmallEtale.toOver C S hS G.objects.obj).obj W)
    (hk : yoneda.map k ≫ W.obj.hom = yonedaEquiv.symm Y.fiber)
    (hk' : yoneda.map (m.base ≫ k) ≫ W.obj.hom = yonedaEquiv.symm X.fiber)
    (x : M.F.obj.val.obj (op W)) :
    pointSectionRestrict G M m (pointChartSection G M Y W k hk x) =
      pointChartSection G M X W (m.base ≫ k) hk' x := by
  have hr := arrowMap_eq_comp_identityArrow G m hm
  have hfa := baseMap_comp_pointMap_of_identity G m hm
  have hPT := Space.pointTransition_of_eq_comp_identityArrow M (baseMap m.base) (pointMap G Y)
    (arrowMap G m) (arrowMap_source G m) (arrowMap_target G m) hr hfa
  exact chartRestrict_compIso_transport (baseMap m.base) (pointMap G Y) hfa M.F.obj
    (Space.selfChart C S hS X.base) (Space.selfChart C S hS Y.base) W m.base k
    (Space.selfChartDiagram C S hS m.base).comm (pointChartDiagram G Y W k hk).comm
    (pointChartDiagram G X W (m.base ≫ k) hk').comm x (pointwiseTransition G M m) hPT

end AlgebraicGeometry.Stack

end
