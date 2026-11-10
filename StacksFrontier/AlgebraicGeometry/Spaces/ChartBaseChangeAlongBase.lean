module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Base change of an étale chart along an object of the base site

Let `B` be a big fppf site containing a scheme `S`, let `X` be a presheaf on the big fppf site
of `S` with structure morphism `f : X ⟶ *` to the terminal object, let `W` be an object of the
site, and let

```
X' --r--> W
|         |
q         |
v         v
X ------> *
```

be a cartesian square, so that `X'` is the base change `X ×_S W`. For an object `U` of the
site, base change of `U` is the fibre product `U ×_S W` *formed in the site*, and it carries the
base change of charts:

* a chart `a : U ⟶ X` base changes to a chart `U ×_S W ⟶ X'`, and the resulting square is
  cartesian, so an étale chart base changes to an étale chart;
* a morphism `α : V ⟶ U` of the site base changes to `V ×_S W ⟶ U ×_S W`, compatibly with the
  charts;
* a *kernel pair* of a chart base changes to a kernel pair of the base-changed chart.

## Main definitions

* `AlgebraicGeometry.Space.siteTerminalHom`: the unique morphism of the big fppf site over `S`
  from an object to the terminal object.
* `AlgebraicGeometry.Space.siteBaseChangeChartMap`: the chart `U ×_S W ⟶ X'` obtained from a chart
  `a : U ⟶ X` by base change.
* `AlgebraicGeometry.Space.siteBaseChangeHom`: the morphism `V ×_S W ⟶ U ×_S W` obtained from a
  morphism `V ⟶ U` of the site by base change.

## Main results

* `AlgebraicGeometry.Space.isPullback_siteBaseChangeChartMap`: the base change of a chart is
  the fibre product of that chart with the projection `X' ⟶ X`.
* `AlgebraicGeometry.Space.isEtale_siteBaseChangeChartMap`: the base change of an étale chart is an
  étale chart.
* `AlgebraicGeometry.Space.isPullback_kernelPair_siteBaseChangeChartMap`: the base change of a
  kernel pair of a chart is a kernel pair of the base-changed chart.
* `AlgebraicGeometry.Space.isPullback_toScheme_siteBaseChangeObj`: the underlying scheme of
  `U ×_S W` is the fibre product of the underlying schemes.

## References

* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The unique morphism of the big fppf site over `S` from an object to the terminal object
`Over.mk (𝟙 (B.obj hS))`, that is, the structure morphism of that object read in the site. -/
abbrev siteTerminalHom (U : BigFppfOver B S hS) : U ⟶ Over.mk (𝟙 (B.obj hS)) :=
  Over.homMk U.hom

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))

/-- A chart of a presheaf over `S`, followed by the structure morphism of that presheaf, is the
represented structure morphism of the chart. -/
theorem comp_eq_yoneda_siteTerminalHom {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    a ≫ f = yoneda.map (siteTerminalHom B S hS U) := by
  rw [← yoneda.map_preimage (a ≫ f),
    Over.mkIdTerminal.hom_ext (yoneda.preimage (a ≫ f)) (siteTerminalHom B S hS U)]

variable {W : BigFppfOver B S hS} {q : X' ⟶ X} {r : X' ⟶ yoneda.obj W}
    (hX' : IsPullback q r f (yoneda.map (siteTerminalHom B S hS W)))

include hX'

/-! ### The base change of a chart -/

omit hX' in
/-- The fibre-product square defining `U ×_S W` still commutes over `S` after its first
projection is composed with a chart `a : U ⟶ X`. -/
theorem siteBaseChangeChart_condition {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    (yoneda.map (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) ≫ a) ≫ f =
      yoneda.map (pullback.snd (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) ≫
        yoneda.map (siteTerminalHom B S hS W) := by
  rw [Category.assoc, comp_eq_yoneda_siteTerminalHom B S hS f a, ← Functor.map_comp,
    pullback.condition, Functor.map_comp]

/-- The base change of a chart: the morphism `U ×_S W ⟶ X'` induced by a chart
`a : U ⟶ X` of a presheaf over `S`. -/
def siteBaseChangeChartMap {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    yoneda.obj (pullback (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) ⟶ X' :=
  hX'.lift (yoneda.map (pullback.fst (siteTerminalHom B S hS U)
      (siteTerminalHom B S hS W)) ≫ a)
    (yoneda.map (pullback.snd (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)))
    (siteBaseChangeChart_condition B S hS f a)

/-- The base change of a chart `a`, followed by `q : X' ⟶ X`, is the first projection of
`U ×_S W` followed by `a`. -/
@[simp] theorem siteBaseChangeChartMap_comp_fst {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    siteBaseChangeChartMap B S hS f hX' a ≫ q =
      yoneda.map (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) ≫ a :=
  hX'.lift_fst _ _ _

/-- The base change of a chart, followed by `r : X' ⟶ W`, is the second projection of
`U ×_S W`. -/
@[simp] theorem siteBaseChangeChartMap_comp_snd {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    siteBaseChangeChartMap B S hS f hX' a ≫ r =
      yoneda.map (pullback.snd (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) :=
  hX'.lift_snd _ _ _

/-- The represented presheaf of `U ×_S W` is the fibre product of a chart `a : U ⟶ X` and the
projection `q : X' ⟶ X`. -/
theorem isPullback_siteBaseChangeChartMap {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    IsPullback (yoneda.map (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)))
      (siteBaseChangeChartMap B S hS f hX' a) a q := by
  have hmap := (IsPullback.of_hasPullback (siteTerminalHom B S hS U)
    (siteTerminalHom B S hS W)).map yoneda
  rw [← comp_eq_yoneda_siteTerminalHom B S hS f a,
    ← siteBaseChangeChartMap_comp_snd B S hS f hX' a] at hmap
  exact hmap.of_bot (siteBaseChangeChartMap_comp_fst B S hS f hX' a).symm hX'

/-- The base change of an étale chart is an étale chart. -/
theorem isEtale_siteBaseChangeChartMap {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
    (ha : IsEtale B S hS a) : IsEtale B S hS (siteBaseChangeChartMap B S hS f hX' a) :=
  isEtale_of_isPullback_yoneda B S hS (isPullback_siteBaseChangeChartMap B S hS f hX' a) ha

omit hX'

/-! ### The base change of a morphism of the site -/

/-- The base change of a morphism of the site: the morphism `V ×_S W ⟶ U ×_S W` induced by a
morphism `α : V ⟶ U` of the big fppf site over `S`. -/
def siteBaseChangeHom {U V : BigFppfOver B S hS} (α : V ⟶ U) :
    pullback (siteTerminalHom B S hS V) (siteTerminalHom B S hS W) ⟶
      pullback (siteTerminalHom B S hS U) (siteTerminalHom B S hS W) :=
  pullback.lift (pullback.fst (siteTerminalHom B S hS V) (siteTerminalHom B S hS W) ≫ α)
    (pullback.snd (siteTerminalHom B S hS V) (siteTerminalHom B S hS W))
    (Over.mkIdTerminal.hom_ext _ _)

/-- The base change of `α : V ⟶ U`, followed by the first projection of `U ×_S W`, is the first
projection of `V ×_S W` followed by `α`. -/
@[simp] theorem siteBaseChangeHom_comp_fst {U V : BigFppfOver B S hS} (α : V ⟶ U) :
    siteBaseChangeHom B S hS (W := W) α ≫
        pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W) =
      pullback.fst (siteTerminalHom B S hS V) (siteTerminalHom B S hS W) ≫ α :=
  pullback.lift_fst _ _ _

/-- The base change of `α : V ⟶ U`, followed by the second projection of `U ×_S W`, is the
second projection of `V ×_S W`. -/
@[simp] theorem siteBaseChangeHom_comp_snd {U V : BigFppfOver B S hS} (α : V ⟶ U) :
    siteBaseChangeHom B S hS (W := W) α ≫
        pullback.snd (siteTerminalHom B S hS U) (siteTerminalHom B S hS W) =
      pullback.snd (siteTerminalHom B S hS V) (siteTerminalHom B S hS W) :=
  pullback.lift_snd _ _ _

/-- The base change of a morphism `α : V ⟶ U` of the site is cartesian over `α`. -/
theorem isPullback_siteBaseChangeHom {U V : BigFppfOver B S hS} (α : V ⟶ U) :
    IsPullback (pullback.fst (siteTerminalHom B S hS V) (siteTerminalHom B S hS W))
      (siteBaseChangeHom B S hS (W := W) α) α
      (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) := by
  have hU := IsPullback.of_hasPullback (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)
  have hV : IsPullback (pullback.fst (siteTerminalHom B S hS V) (siteTerminalHom B S hS W))
      (siteBaseChangeHom B S hS (W := W) α ≫
        pullback.snd (siteTerminalHom B S hS U) (siteTerminalHom B S hS W))
      (α ≫ siteTerminalHom B S hS U) (siteTerminalHom B S hS W) := by
    rw [siteBaseChangeHom_comp_snd,
      show α ≫ siteTerminalHom B S hS U = siteTerminalHom B S hS V from
        Over.mkIdTerminal.hom_ext _ _]
    exact IsPullback.of_hasPullback _ _
  exact hV.of_bot (by simp) hU

/-- A chart of `V` obtained from a chart of `U` by precomposition base changes to the
precomposition of the base-changed chart. -/
theorem siteBaseChangeChartMap_siteBaseChangeHom
    (hX' : IsPullback q r f (yoneda.map (siteTerminalHom B S hS W)))
    {U V : BigFppfOver B S hS} (α : V ⟶ U) (a : yoneda.obj U ⟶ X) :
    siteBaseChangeChartMap B S hS f hX' (yoneda.map α ≫ a) =
      yoneda.map (siteBaseChangeHom B S hS (W := W) α) ≫
        siteBaseChangeChartMap B S hS f hX' a := by
  refine hX'.hom_ext ?_ ?_
  · simp only [siteBaseChangeChartMap_comp_fst, Category.assoc]
    conv_rhs => rw [← Functor.map_comp_assoc, siteBaseChangeHom_comp_fst]
    simp
  · simp only [siteBaseChangeChartMap_comp_snd, Category.assoc]
    conv_rhs => rw [← Functor.map_comp, siteBaseChangeHom_comp_snd]

/-! ### The base change of a kernel pair -/

/-- If `α, β : V ⟶ U` exhibit `V` as the fibre product `U ×_X U` of a chart `a : U ⟶ X` with
itself, then their base changes exhibit `V ×_S W` as the fibre product of the base-changed
chart `U ×_S W ⟶ X'` with itself. -/
theorem isPullback_kernelPair_siteBaseChangeChartMap
    (hX' : IsPullback q r f (yoneda.map (siteTerminalHom B S hS W)))
    {U V : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X} (α β : V ⟶ U)
    (hkp : IsPullback (yoneda.map α) (yoneda.map β) a a) :
    IsPullback (yoneda.map (siteBaseChangeHom B S hS (W := W) α))
      (yoneda.map (siteBaseChangeHom B S hS (W := W) β))
      (siteBaseChangeChartMap B S hS f hX' a) (siteBaseChangeChartMap B S hS f hX' a) := by
  have hcU := isPullback_siteBaseChangeChartMap B S hS f hX' a
  have hα := ((isPullback_siteBaseChangeHom B S hS (W := W) α).map yoneda).flip
  have hs : IsPullback (yoneda.map (siteBaseChangeHom B S hS (W := W) α))
      (yoneda.map (pullback.fst (siteTerminalHom B S hS V) (siteTerminalHom B S hS W)) ≫
        yoneda.map β)
      (yoneda.map (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) ≫ a) a :=
    hα.paste_vert hkp
  rw [show yoneda.map (pullback.fst (siteTerminalHom B S hS V) (siteTerminalHom B S hS W)) ≫
        yoneda.map β =
      yoneda.map (siteBaseChangeHom B S hS (W := W) β) ≫
        yoneda.map (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) from by
      rw [← Functor.map_comp, ← Functor.map_comp, siteBaseChangeHom_comp_fst],
    show yoneda.map (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)) ≫ a =
      siteBaseChangeChartMap B S hS f hX' a ≫ q from
        (siteBaseChangeChartMap_comp_fst _ _ _ _ _ _).symm]
    at hs
  refine hs.of_bot ?_ hcU.flip
  rw [← siteBaseChangeChartMap_siteBaseChangeHom B S hS f hX' α a,
    ← siteBaseChangeChartMap_siteBaseChangeHom B S hS f hX' β a, hkp.w]

/-! ### The base change at the level of schemes -/

/-- The underlying scheme of `U ×_S W` is the fibre product of the underlying schemes. -/
theorem isPullback_toScheme_siteBaseChangeObj (U W : BigFppfOver B S hS) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (siteTerminalHom B S hS U) (siteTerminalHom B S hS W)))
      ((BigFppfOver.toScheme B S hS).map (siteTerminalHom B S hS U))
      ((BigFppfOver.toScheme B S hS).map (siteTerminalHom B S hS W)) :=
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  (IsPullback.of_hasPullback (siteTerminalHom B S hS U)
    (siteTerminalHom B S hS W)).map (BigFppfOver.toScheme B S hS)

end AlgebraicGeometry.Space

end
