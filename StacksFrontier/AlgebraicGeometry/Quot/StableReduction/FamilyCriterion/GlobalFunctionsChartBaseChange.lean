module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Global functions on the base change of a representable morphism, chart by chart

Let `g : T ⟶ U` be a morphism of the big fppf site over `S` and `γ : Y ⟶ U` a morphism of
presheaves on that site. Every scheme chart `c : W ⟶ Y` of `Y` base changes to the scheme chart
`T ×_U W ⟶ T ×_U Y` of the presheaf fibre product, and every scheme chart of `T ×_U Y` factors
through the base change of its image chart of `Y`. Consequently, if pullback of global functions
along `T ×_U W ⟶ W` is bijective for every object `W` of the site over `U`, then pullback of
compatible families of regular functions on all scheme charts along `T ×_U Y ⟶ Y` is bijective.
For algebraic spaces those families are the global functions
(`AlgebraicGeometry.Space.globalFunctionsChartEquiv`), so the scheme case of a statement about
global functions on base changes gives the case of an arbitrary algebraic space.

## Main results

* `AlgebraicGeometry.Space.chartFunctionsMap_pullback_snd_bijective`: the chartwise statement.
* `AlgebraicGeometry.Space.globalFunctionsMap_bijective_of_chartFunctionsMap_bijective`: pullback
  of global functions on algebraic spaces is bijective when it is so on all-chart families.

## Implementation notes

No étale descent is needed here: it is already paid for by the comparison between the global
sections of the small étale structure sheaf and the compatible families on all scheme charts
(`AlgebraicGeometry.Space.chartFunctionsToSmall_bijective`), and on all scheme charts the
base-changed charts are cofinal in the required sense.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A compatible family of regular functions on the scheme charts of `F` is compatible with
restriction along every morphism of charts. -/
theorem chartFunctions_val_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : chartFunctions B S hS F) {j k : CostructuredArrow yoneda F} (h : j ⟶ k) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h.left).op).hom (s.val (op k)) =
      s.val (op j) :=
  s.property h.op

/-- Pullback of global functions along the underlying morphisms of schemes of a composite in
the big fppf site over `S` is the composite of the pullbacks. -/
theorem gamma_toScheme_map_comp {X Y Z : BigFppfOver B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj Z))) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom s) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (f ≫ g)).op).hom s := by
  rw [Functor.map_comp]
  exact gamma_map_comp _ _ _

/-- The morphism to the base underlying a scheme chart of a presheaf over a representable. -/
def chartMorphismToBase {U : BigFppfOver B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (γ : Y ⟶ yoneda.obj U) (c : CostructuredArrow yoneda Y) : c.left ⟶ U :=
  Yoneda.fullyFaithful.preimage (c.hom ≫ γ)

/-- The Yoneda image of the morphism to the base of a chart is the composite with `γ`. -/
theorem yoneda_map_chartMorphismToBase {U : BigFppfOver B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (γ : Y ⟶ yoneda.obj U) (c : CostructuredArrow yoneda Y) :
    yoneda.map (chartMorphismToBase γ c) = c.hom ≫ γ :=
  Yoneda.fullyFaithful.map_preimage _

variable {T U : BigFppfOver B S hS} (g : T ⟶ U) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (γ : Y ⟶ yoneda.obj U)

/-- The base change along `g` of a scheme chart `c` of `Y`: the scheme chart
`T ×_U c ⟶ T ×_U Y` of the presheaf fibre product. -/
abbrev representableBaseChangeChart (c : CostructuredArrow yoneda Y) :
    CostructuredArrow yoneda (pullback (yoneda.map g) γ) :=
  CostructuredArrow.mk (Y := pullback g (chartMorphismToBase γ c))
    (pullback.lift (yoneda.map (pullback.fst _ _)) (yoneda.map (pullback.snd _ _) ≫ c.hom) (by
      rw [Category.assoc, ← yoneda_map_chartMorphismToBase, ← Functor.map_comp,
        ← Functor.map_comp, pullback.condition]))

/-- The projection from the image of the base-changed chart to the chart itself. -/
def representableBaseChangeChartProj (c : CostructuredArrow yoneda Y) :
    (CostructuredArrow.map (pullback.snd (yoneda.map g) γ)).obj
      (representableBaseChangeChart g γ c) ⟶ c :=
  CostructuredArrow.homMk (pullback.snd g (chartMorphismToBase γ c))
    (pullback.lift_snd _ _ _).symm

/-- Pullback along the projection `T ×_U W ⟶ W` of the value of a chart family at the chart
`W` is the value of its pullback to `T ×_U Y` at the base-changed chart. -/
theorem gamma_representableBaseChangeChartProj (s : chartFunctions B S hS Y)
    (c : CostructuredArrow yoneda Y) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (pullback.snd g (chartMorphismToBase γ c))).op).hom (s.val (op c)) =
      (chartFunctionsMap B S hS (pullback.snd (yoneda.map g) γ) s).val
        (op (representableBaseChangeChart g γ c)) :=
  chartFunctions_val_map s (representableBaseChangeChartProj g γ c)

/-- The morphism of base-changed charts induced by a morphism of charts. -/
def representableBaseChangeChartMap {c c' : CostructuredArrow yoneda Y} (h : c' ⟶ c) :
    representableBaseChangeChart g γ c' ⟶ representableBaseChangeChart g γ c :=
  CostructuredArrow.homMk
    (pullback.map g (chartMorphismToBase γ c') g (chartMorphismToBase γ c) (𝟙 T) h.left (𝟙 U)
      (by simp) (by
        refine Yoneda.fullyFaithful.map_injective ?_
        rw [Functor.map_comp, Functor.map_comp, yoneda_map_chartMorphismToBase,
          yoneda_map_chartMorphismToBase, CategoryTheory.Functor.map_id, Category.comp_id,
          ← CostructuredArrow.w h, Category.assoc]))
    (by
      refine pullback.hom_ext ?_ ?_
      · dsimp only [representableBaseChangeChart, CostructuredArrow.mk_hom_eq_self]
        simp only [Category.assoc, pullback.lift_fst, ← Functor.map_comp, Category.comp_id]
      · simp only [representableBaseChangeChart, CostructuredArrow.mk_left,
          CostructuredArrow.mk_hom_eq_self, Category.assoc, pullback.lift_snd]
        rw [← CostructuredArrow.w h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
          ← Functor.map_comp, pullback.lift_snd])

/-- The induced morphism of base-changed charts lies over the given morphism of charts. -/
theorem representableBaseChangeChartMap_left {c c' : CostructuredArrow yoneda Y} (h : c' ⟶ c) :
    (representableBaseChangeChartMap g γ h).left ≫ pullback.snd g (chartMorphismToBase γ c) =
      pullback.snd g (chartMorphismToBase γ c') ≫ h.left := by
  exact pullback.lift_snd _ _ _

/-- A scheme chart of the fibre product `T ×_U Y` maps to the base change of its image chart
of `Y`, by its first projection and the identity. -/
def representableBaseChangeChartSection
    (j : CostructuredArrow yoneda (pullback (yoneda.map g) γ)) :
    j ⟶ representableBaseChangeChart g γ
      ((CostructuredArrow.map (pullback.snd (yoneda.map g) γ)).obj j) :=
  CostructuredArrow.homMk
    (pullback.lift (Yoneda.fullyFaithful.preimage (j.hom ≫ pullback.fst (yoneda.map g) γ))
      (𝟙 _) (by
        refine Yoneda.fullyFaithful.map_injective ?_
        rw [Functor.map_comp, Functor.map_comp, yoneda_map_chartMorphismToBase,
          Yoneda.fullyFaithful.map_preimage, CategoryTheory.Functor.map_id, Category.id_comp,
          Category.assoc, pullback.condition]
        rfl))
    (by
      refine pullback.hom_ext ?_ ?_
      · dsimp only [representableBaseChangeChart, CostructuredArrow.mk_hom_eq_self]
        rw [Category.assoc, pullback.lift_fst, ← Functor.map_comp, pullback.lift_fst,
          Yoneda.fullyFaithful.map_preimage]
      · dsimp only [representableBaseChangeChart, CostructuredArrow.mk_hom_eq_self]
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← Functor.map_comp,
          pullback.lift_snd, CategoryTheory.Functor.map_id, Category.id_comp]
        rfl)

/-- The morphism to the base-changed chart is a section of the projection `T ×_U W ⟶ W`. -/
theorem representableBaseChangeChartSection_left_snd
    (j : CostructuredArrow yoneda (pullback (yoneda.map g) γ)) :
    (representableBaseChangeChartSection g γ j).left ≫ pullback.snd g _ = 𝟙 _ := by
  exact pullback.lift_snd _ _ _

/-- **Chart functions of a base change of a representable morphism.** Let `g : T ⟶ U` be a
morphism of the big fppf site over `S` and `γ : Y ⟶ U` a morphism of presheaves. If pullback of
global functions along the projection `T ×_U W ⟶ W` is bijective for every object `W` of the
site over `U`, then pullback of compatible families of regular functions on all scheme charts
along the projection `T ×_U Y ⟶ Y` is bijective. -/
theorem chartFunctionsMap_pullback_snd_bijective
    (hΓ : ∀ {W : BigFppfOver B S hS} (w : W ⟶ U), Function.Bijective
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (pullback.snd g w)).op).hom) :
    Function.Bijective (chartFunctionsMap B S hS (pullback.snd (yoneda.map g) γ)) := by
  refine ⟨fun s₁ s₂ hs => ?_, fun t => ?_⟩
  · refine Functor.sections_ext_iff.mpr fun c => ?_
    cases c with | op c => ?_
    refine (hΓ (chartMorphismToBase γ c)).1 ?_
    rw [gamma_representableBaseChangeChartProj, gamma_representableBaseChangeChartProj, hs]
  · let sv : ∀ c : CostructuredArrow yoneda Y,
        Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj c.left)) :=
      fun c => Function.surjInv (hΓ (chartMorphismToBase γ c)).2
          (t.val (op (representableBaseChangeChart g γ c)))
    have hsv : ∀ c, (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (pullback.snd g (chartMorphismToBase γ c))).op).hom (sv c) =
          t.val (op (representableBaseChangeChart g γ c)) := fun c => Function.surjInv_eq _ _
    have hcompat : ∀ {c c' : CostructuredArrow yoneda Y} (h : c' ⟶ c),
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h.left).op).hom (sv c) = sv c' := by
      intro c c' h
      refine (hΓ (chartMorphismToBase γ c')).1 ?_
      rw [hsv, gamma_toScheme_map_comp, ← representableBaseChangeChartMap_left,
        ← gamma_toScheme_map_comp, hsv,
        chartFunctions_val_map t (representableBaseChangeChartMap g γ h)]
    let s : chartFunctions B S hS Y := ⟨fun c => sv c.unop, fun h => hcompat h.unop⟩
    refine ⟨s, Functor.sections_ext_iff.mpr fun j => ?_⟩
    cases j with | op j => ?_
    calc (chartFunctionsMap B S hS (pullback.snd (yoneda.map g) γ) s).val (op j)
        = sv ((CostructuredArrow.map (pullback.snd (yoneda.map g) γ)).obj j) := rfl
      _ = (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (representableBaseChangeChartSection g γ j).left).op).hom
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (pullback.snd g (chartMorphismToBase γ
              ((CostructuredArrow.map (pullback.snd (yoneda.map g) γ)).obj j)))).op).hom
            (sv ((CostructuredArrow.map (pullback.snd (yoneda.map g) γ)).obj j))) := by
        rw [gamma_toScheme_map_comp, representableBaseChangeChartSection_left_snd,
          CategoryTheory.Functor.map_id, op_id]
        rfl
      _ = t.val (op j) := by
        rw [hsv, chartFunctions_val_map t (representableBaseChangeChartSection g γ j)]

/-- Pullback of global functions along a morphism of algebraic spaces is bijective as soon as
precomposition of compatible families of regular functions on all scheme charts is. -/
theorem globalFunctionsMap_bijective_of_chartFunctionsMap_bijective
    {U V : AlgebraicSpaces B S hS} (f : V ⟶ U)
    (hf : Function.Bijective (chartFunctionsMap B S hS f.hom)) :
    Function.Bijective (globalFunctionsMap B S hS f) :=
  (globalFunctionsChartEquiv B S hS V).val.symm.bijective.comp
    (hf.comp (globalFunctionsChartEquiv B S hS U).val.bijective)

end AlgebraicGeometry.Space

end
