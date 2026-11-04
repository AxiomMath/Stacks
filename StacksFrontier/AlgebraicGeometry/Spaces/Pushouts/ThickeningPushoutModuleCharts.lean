module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutModuleTriples
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentablePushforwardChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitChart

/-!
# The glued module of Stacks 08KV on the étale charts of `V'`

In the situation of
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/ThickeningPushoutModuleTriples.lean`
— a thickening `i : X ⟶ X'`, an affine `f : X ⟶ Y`, the pushout `Y' = Y ⨿_X X'` and a morphism
`g : V' ⟶ Y'` with base changes `V`, `U'` and `U` — the glued module of a triple `(𝒢, ℱ', φ)`
is the fibre product of `(V ⟶ V')_*𝒢` and `(U' ⟶ V')_*ℱ'` over the direct image along
`U ⟶ V'`.  This file reads the two maps of that fibre product on the sections over an étale
chart `W` of `V'`, projected to the chart `W_U = W ×_{V'} U`: the first is `φ` applied to the
chart section of the given section of `𝒢` over `W_V = W ×_{V'} V`, the second is the chart section
of the given section of `ℱ'` over `W_{U'} = W ×_{V'} U'`.

The two statements are proved for an arbitrary pair of factorizations `U ⟶ V ⟶ V'` and
`U ⟶ U' ⟶ V'` of one morphism, with every space a variable: instantiated at the pullbacks of the
situation, the kernel would otherwise have to unfold those pullbacks while comparing the spellings
of the charts.

## Main results

* `AlgebraicGeometry.Space.PushoutModules.chartModProj_targetMap_of_comp`: the first map.
* `AlgebraicGeometry.Space.PushoutModules.chartModProj_compTransport`: the chart projection of the
  comparison of direct images along two factorizations of one morphism.
* `AlgebraicGeometry.Space.PushoutModules.chartModProj_ambientMap_of_comp`: the second map.
* `AlgebraicGeometry.Space.PushoutModules.targetChart`,
  `AlgebraicGeometry.Space.PushoutModules.ambientChart`,
  `AlgebraicGeometry.Space.PushoutModules.commonChart`: the three base changes of a chart of `V'`.

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Base change of charts along equal morphisms gives equal charts. -/
theorem smallBaseChange_obj_congr {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} {f f' : X ⟶ Y} (h : f = f')
    (hf : yoneda.relativelyRepresentable f.hom) (hf' : yoneda.relativelyRepresentable f'.hom)
    (V : SmallEtale B S hS Y.1) :
    (smallBaseChange B S hS f hf).obj V = (smallBaseChange B S hS f' hf').obj V := by
  subst h
  rfl

section Unfold

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {𝒱 : Type*} [Category 𝒱] {𝒰' : Type*} [Category 𝒰'] {𝒰 : Type*} [Category 𝒰]
    {qV : 𝒱 ⥤ Modules.{u, u} B S hS F hF} {qA : 𝒰' ⥤ Modules.{u, u} B S hS F hF}
    {pT : 𝒱 ⥤ 𝒰} {qT : 𝒰 ⥤ 𝒱} (aT : pT ⊣ qT) {pC : 𝒰' ⥤ 𝒰} {qC : 𝒰 ⥤ 𝒰'} (aC : pC ⊣ qC)
    {Q : 𝒰 ⥤ Modules.{u, u} B S hS F hF}

/-- The first map of a gluing fibre product of modules, on sections. -/
theorem targetMap_val_app (ε : qT ⋙ qV ≅ Q) (T : TripleGluing.Triple pT pC)
    (X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (x : (qV.obj T.target).val.obj X) :
    (TripleGluing.targetMap aT ε T).val.app X x =
      (ε.hom.app (pC.obj T.ambient)).val.app X
        ((qV.map (aT.unit.app T.target ≫ qT.map T.comparison.hom)).val.app X x) := rfl

/-- The second map of a gluing fibre product of modules, on sections. -/
theorem ambientMap_val_app (s : qC ⋙ qA ⟶ Q) (T : TripleGluing.Triple pT pC)
    (X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (y : (qA.obj T.ambient).val.obj X) :
    (TripleGluing.ambientMap (aC := aC) s T).val.app X y =
      (s.app (pC.obj T.ambient)).val.app X ((qA.map (aC.unit.app T.ambient)).val.app X y) := rfl

/-- A composite of natural transformations into modules, on sections. -/
theorem natTrans_comp_app_val_app {E : Type*} [Category E]
    {F₁ F₂ F₃ : E ⥤ Modules.{u, u} B S hS F hF} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) (N : E)
    (X : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (y : (F₁.obj N).val.obj X) :
    ((α ≫ β).app N).val.app X y = (β.app N).val.app X ((α.app N).val.app X y) := rfl

/-- The identity of a sheaf of modules, on sections. -/
theorem sheafOfModules_id_val_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) (X : Cᵒᵖ) (y : M.val.obj X) :
    (𝟙 M : M ⟶ M).val.app X y = y := rfl

end Unfold

namespace PushoutModules

/-! ### The two maps of the gluing fibre product on chart sections, for any square -/

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V V' U' : AlgebraicSpaces B S hS} (t : U ⟶ V) (v : V ⟶ V') (a : U ⟶ U') (u' : U' ⟶ V')

/-- The first map of the gluing fibre product along `U ⟶ V ⟶ V'`, on sections over a chart `W`
of `V'`, read on the chart `W ×_{V'} U`. -/
theorem chartModProj_targetMap_of_comp (ht : yoneda.relativelyRepresentable t.hom)
    (hv : yoneda.relativelyRepresentable v.hom) (htv : yoneda.relativelyRepresentable (t ≫ v).hom)
    (T : TripleGluing.Triple (modulePullback B S hS t) (modulePullback B S hS a))
    (W : SmallEtale B S hS V'.1)
    (x : ((modulePushforward B S hS v).obj T.target).val.obj (op W)) :
    chartModProj B S hS (t ≫ v) htv ((modulePullback B S hS a).obj T.ambient) W
        ((TripleGluing.targetMap (qV := modulePushforward B S hS v)
          (modulePullbackAdjunction B S hS t) (modulePushforwardCompIso B S hS t v)
            T).val.app _ x) =
      T.comparison.hom.val.app _
        (modulePullbackChartSection B S hS t T.target
          ((baseChangeChartDiagram B S hS t ht ((smallBaseChange B S hS v hv).obj W)).precompSource
            (chartBaseChangeCompComparison B S hS t v ht hv htv W))
          (chartModProj B S hS v hv T.target W x)) := by
  have h1 := chartModProj_modulePushforwardCompIso B S hS t v ht hv htv
    ((modulePullback B S hS a).obj T.ambient) W
    (((modulePushforward B S hS v).map
      ((modulePullbackAdjunction B S hS t).unit.app T.target ≫
        (modulePushforward B S hS t).map T.comparison.hom)).val.app _ x)
  have h2 : chartModProj B S hS t ht ((modulePullback B S hS a).obj T.ambient)
      ((smallBaseChange B S hS v hv).obj W)
      (chartModProj B S hS v hv _ W
        (((modulePushforward B S hS v).map
          ((modulePullbackAdjunction B S hS t).unit.app T.target ≫
            (modulePushforward B S hS t).map T.comparison.hom)).val.app _ x)) =
      T.comparison.hom.val.app _
        (modulePullbackChartSection B S hS t T.target
          (baseChangeChartDiagram B S hS t ht ((smallBaseChange B S hS v hv).obj W))
          (chartModProj B S hS v hv T.target W x)) := by
    rw [chartModProj_naturality, chartModProj_comp_apply, chartModProj_naturality,
      chartModProj_modulePullbackAdjunction_unit]
    rfl
  have h3 := modulePullbackChartSection_precomp B S hS t T.target
    (baseChangeChartDiagram B S hS t ht ((smallBaseChange B S hS v hv).obj W))
    (chartBaseChangeCompComparison B S hS t v ht hv htv W)
    (chartModProj B S hS v hv T.target W x)
  rw [targetMap_val_app, h1, h2]
  exact (PresheafOfModules.naturality_apply T.comparison.hom.val _ _).symm.trans
    (congrArg _ h3.symm)

/-- Restriction of a module along the identity of a chart, spelled in the small étale category. -/
theorem modules_map_id_op_apply {Z : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS Z.1 Z.2)
    (V : SmallEtale B S hS Z.1) (s : N.val.obj (op V)) : N.val.map (𝟙 V).op s = s :=
  presheafOfModules_map_id_apply N.val _ s

/-- The chart projection of the comparison of direct images along `U ⟶ U' ⟶ V'`, transported
along the reflexive equality. -/
theorem chartModProj_compTransport_self (ha : yoneda.relativelyRepresentable a.hom)
    (hu' : yoneda.relativelyRepresentable u'.hom)
    (hau : yoneda.relativelyRepresentable (a ≫ u').hom)
    (N : Modules.{u, u} B S hS U.1 U.2) (W : SmallEtale B S hS V'.1)
    (z : ((modulePushforward B S hS a ⋙ modulePushforward B S hS u').obj N).val.obj (op W)) :
    chartModProj B S hS (a ≫ u') hau N W (((compTransport a u' (a ≫ u') rfl).app N).val.app _ z) =
      N.val.map (chartBaseChangeCompComparison B S hS a u' ha hu' hau W).op
          (chartModProj B S hS a ha N ((smallBaseChange B S hS u' hu').obj W)
            (chartModProj B S hS u' hu' ((modulePushforward B S hS a).obj N) W z)) :=
  chartModProj_modulePushforwardCompIso B S hS a u' ha hu' hau N W z

/-- The chart projection of the transported comparison of direct images along `U ⟶ U' ⟶ V'`
and a morphism `k` equal to the composite. -/
theorem chartModProj_compTransport (ha : yoneda.relativelyRepresentable a.hom)
    (hu' : yoneda.relativelyRepresentable u'.hom)
    (hau : yoneda.relativelyRepresentable (a ≫ u').hom) {k : U ⟶ V'} (h : a ≫ u' = k)
    (hk : yoneda.relativelyRepresentable k.hom)
    (N : Modules.{u, u} B S hS U.1 U.2) (W : SmallEtale B S hS V'.1)
    (z : ((modulePushforward B S hS a ⋙ modulePushforward B S hS u').obj N).val.obj (op W)) :
    chartModProj B S hS k hk N W (((compTransport a u' k h).app N).val.app _ z) =
      N.val.map (eqToHom (smallBaseChange_obj_congr h.symm hk hau W)).op
        (N.val.map (chartBaseChangeCompComparison B S hS a u' ha hu' hau W).op
          (chartModProj B S hS a ha N ((smallBaseChange B S hS u' hu').obj W)
            (chartModProj B S hS u' hu' ((modulePushforward B S hS a).obj N) W z))) := by
  subst h
  have e : eqToHom (smallBaseChange_obj_congr (rfl : a ≫ u' = a ≫ u').symm hk hau W) =
      𝟙 ((smallBaseChange B S hS (a ≫ u') hk).obj W) := eqToHom_refl _ _
  rw [e]
  exact (chartModProj_compTransport_self a u' ha hu' hk N W z).trans
    (modules_map_id_op_apply N ((smallBaseChange B S hS (a ≫ u') hk).obj W)
      (N.val.map (chartBaseChangeCompComparison B S hS a u' ha hu' hau W).op
        (chartModProj B S hS a ha N ((smallBaseChange B S hS u' hu').obj W)
          (chartModProj B S hS u' hu' ((modulePushforward B S hS a).obj N) W z)))).symm

/-- The second map of the gluing fibre product along `U ⟶ U' ⟶ V'`, transported to a morphism
`k = U ⟶ U' ⟶ V'`, on sections over a chart `W` of `V'`, read on `W ×_{V'} U`. -/
theorem chartModProj_ambientMap_of_comp
    (ha : yoneda.relativelyRepresentable a.hom) (hu' : yoneda.relativelyRepresentable u'.hom)
    (hau : yoneda.relativelyRepresentable (a ≫ u').hom) {k : U ⟶ V'} (h : a ≫ u' = k)
    (hk : yoneda.relativelyRepresentable k.hom)
    (T : TripleGluing.Triple (modulePullback B S hS t) (modulePullback B S hS a))
    (W : SmallEtale B S hS V'.1)
    (y : ((modulePushforward B S hS u').obj T.ambient).val.obj (op W)) :
    chartModProj B S hS k hk ((modulePullback B S hS a).obj T.ambient) W
        ((TripleGluing.ambientMap (aC := modulePullbackAdjunction B S hS a)
          (compTransport a u' k h) T).val.app _ y) =
      modulePullbackChartSection B S hS a T.ambient
        ((baseChangeChartDiagram B S hS a ha ((smallBaseChange B S hS u' hu').obj W)).precompSource
          (eqToHom (smallBaseChange_obj_congr h.symm hk hau W) ≫
            chartBaseChangeCompComparison B S hS a u' ha hu' hau W))
        (chartModProj B S hS u' hu' T.ambient W y) := by
  have h3 : chartModProj B S hS a ha ((modulePullback B S hS a).obj T.ambient)
      ((smallBaseChange B S hS u' hu').obj W)
      (chartModProj B S hS u' hu' _ W
        (((modulePushforward B S hS u').map
          ((modulePullbackAdjunction B S hS a).unit.app T.ambient)).val.app _ y)) =
      modulePullbackChartSection B S hS a T.ambient
        (baseChangeChartDiagram B S hS a ha ((smallBaseChange B S hS u' hu').obj W))
        (chartModProj B S hS u' hu' T.ambient W y) := by
    rw [chartModProj_naturality, chartModProj_modulePullbackAdjunction_unit]
    rfl
  rw [ambientMap_val_app, chartModProj_compTransport a u' ha hu' hau h hk, h3]
  refine (PresheafOfModules.map_comp_apply _ _ _ _).symm.trans ?_
  exact (modulePullbackChartSection_precomp B S hS a T.ambient
    (baseChangeChartDiagram B S hS a ha ((smallBaseChange B S hS u' hu').obj W))
    (eqToHom (smallBaseChange_obj_congr h.symm hk hau W) ≫
      chartBaseChangeCompComparison B S hS a u' ha hu' hau W)
    (chartModProj B S hS u' hu' T.ambient W y)).symm

end Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
    {V' : AlgebraicSpaces B S hS} (g : V' ⟶ pushout i f)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-! ### Representability -/

include hi hf

/-- The projection `V ⟶ V'` is representable. -/
theorem rep_targetRestriction : yoneda.relativelyRepresentable (targetRestriction i f g).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_targetRestriction i f g hi hf)

/-- The projection `U' ⟶ V'` is representable. -/
theorem rep_ambientRestriction : yoneda.relativelyRepresentable (ambientRestriction i f g).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_ambientRestriction i f g hi hf)

/-- The morphism `U ⟶ V` is representable. -/
theorem rep_commonToTarget : yoneda.relativelyRepresentable (commonToTarget i f g).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_commonToTarget i f g hi hf)

/-- The morphism `U ⟶ U'` is representable. -/
theorem rep_commonToAmbient : yoneda.relativelyRepresentable (commonToAmbient i f g).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (isAffineHom_commonToAmbient i f g hi hf)

/-- The composite `U ⟶ V ⟶ V'` is representable. -/
theorem rep_commonTargetComp :
    yoneda.relativelyRepresentable (commonToTarget i f g ≫ targetRestriction i f g).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (by
    rw [commonToTarget_restriction]
    exact isAffineHom_commonRestriction i f g hi hf)

/-- The composite `U ⟶ U' ⟶ V'` is representable. -/
theorem rep_commonAmbientComp :
    yoneda.relativelyRepresentable (commonToAmbient i f g ≫ ambientRestriction i f g).hom :=
  relativelyRepresentable_of_isAffineHom B S hS _ (by
    rw [commonToAmbient_restriction]
    exact isAffineHom_commonRestriction i f g hi hf)

/-! ### The three base changes of a chart of `V'` -/

/-- The chart `W_V = W ×_{V'} V` of `V`. -/
abbrev targetChart (W : SmallEtale B S hS V'.1) : SmallEtale B S hS (targetSpace i f g).1 :=
  (smallBaseChange B S hS (targetRestriction i f g) (rep_targetRestriction i f g hi hf)).obj W

/-- The chart `W_{U'} = W ×_{V'} U'` of `U'`. -/
abbrev ambientChart (W : SmallEtale B S hS V'.1) : SmallEtale B S hS (ambientSpace i f g).1 :=
  (smallBaseChange B S hS (ambientRestriction i f g) (rep_ambientRestriction i f g hi hf)).obj W

/-- The chart `W_U = W ×_{V'} U` of `U`, as the base change along `U ⟶ V ⟶ V'`. -/
abbrev commonChart (W : SmallEtale B S hS V'.1) : SmallEtale B S hS (commonSpace i f g).1 :=
  (smallBaseChange B S hS (commonToTarget i f g ≫ targetRestriction i f g)
    (rep_commonTargetComp i f g hi hf)).obj W

end PushoutModules

end AlgebraicGeometry.Space

end
