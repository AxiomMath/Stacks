module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple

/-!
# The value at a codimension-zero point of a section of a trivialised module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`M` be a sheaf of `𝒪_Y`-modules and let `τ : f^*M ⟶ N` be a morphism of `𝒪_X`-modules.  A
section `s` of `M` over the chart `d.V` of a commuting square `d` of étale scheme charts over `f`
has an inverse image `f^*s` over `d.U` — the chart component of the unit of the Stacks 03D7
adjunction, `AlgebraicGeometry.Space.modulePullbackChartFMap` — and `τ` turns that into a section
of `N` over `d.U`.  This file calls that section the **value of `s` through `τ`** and records
that it is additive, semilinear over pullback of regular functions, and natural in the square.

Take `f = j_η : Spec(𝒪_{X, η}) ⟶ X` at a point `η` of codimension `0`, with
`N = 𝒪_{Spec(𝒪_{X, η})}` and `τ` a **trivialisation** of `j_η^*M`, as in
`AlgebraicGeometry.Space.IsTrivialAtCodimensionZeroPoints`.  The value of a section of `M` over
an étale chart `U` of `X` is then a regular function on the base-changed chart
`U ×_X Spec(𝒪_{X, η})`, that is a section over `U` of the sheaf of rings `j_{η, *}𝒪_{X, η}`;
this is the **value at `η`**.

**Multiplication by the value at `η` of a free generator is injective.**  If `e` is a compatible
family of free generators of `M` over the charts over a chart `V` of `X`, then for every chart `U`
over `V` multiplication by the value at `η` of `e` is injective on the regular functions over
`U ×_X Spec(𝒪_{X, η})`.  The inverse image of a free generator is a free generator over a
covering sieve (`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`),
so the value is a unit there; and injectivity is local because the structure sheaf of
`Spec(𝒪_{X, η})` is a sheaf.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackChartValue` is the value of a chart section through a
  morphism out of the inverse image.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointValue` is the value at a
  codimension-zero point.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartValue_add`,
  `…modulePullbackChartValue_smul`, `…modulePullbackChartValue_map`: additivity, semilinearity
  and naturality.
* `…CodimensionZeroPresentation.genericPointValue_add`, `…genericPointValue_smul`,
  `…genericPointValue_map`: the same at a codimension-zero point, with the coefficient map
  spelled as the structure map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}`.
* `…CodimensionZeroPresentation.injective_mul_genericPointValue`: **multiplication by the value
  at `η` of a free generator is injective.**

## Implementation notes

The value is defined for arbitrary `N` and `τ` first: with these as variables the elaborator
never unfolds `AlgebraicGeometry.Space.modulePullback` at a specific morphism, whereas the same
three proofs written directly at `j_η` and a trivialisation exhaust the heartbeat budget on the
module instances of `j_η^*M`.

The value at `η` takes its values in `…genericPointStructureSheaf`, the sheaf of rings
`j_{η, *}𝒪_{X, η}`, rather than in the `𝒪_X`-module it underlies: that is the spelling in which
`…bijective_pi_genericPointComparison_app_of_isIso` states the first conclusion of Stacks 0ENA.
The two readings have the same sections on the nose, the module being
`AlgebraSheaf.underlyingModule` of the algebra sheaf on those very sections, and the semilinearity
of the value map is what identifies the module structures.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The value of a chart section through a morphism out of the inverse image -/

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (N : Modules.{u, u} B S hS X.1 X.2) (τ : (modulePullback B S hS f).obj M ⟶ N)

/-- **The value of a chart section through a morphism out of the inverse image.**  The section
`s` of `M` over `d.V` has an inverse image over `d.U`, the chart component of the unit of the
Stacks 03D7 adjunction, and `τ` carries it into `N`. -/
noncomputable def modulePullbackChartValue (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) : N.val.obj (op d.U) :=
  τ.val.app (op d.U) ((modulePullbackChartFMap B S hS f M).app d s)

/-- The value of a chart section is the image of the chart section of the inverse image. -/
theorem modulePullbackChartValue_eq (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartValue B S hS f M N τ d s =
      (τ.val.app (op d.U)).hom ((modulePullbackChartFMap B S hS f M).app d s) :=
  rfl

/-- **The value of a chart section is additive.** -/
theorem modulePullbackChartValue_add (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s s' : M.val.obj (op d.V)) :
    modulePullbackChartValue B S hS f M N τ d (s + s') =
      modulePullbackChartValue B S hS f M N τ d s +
        modulePullbackChartValue B S hS f M N τ d s' := by
  show (τ.val.app (op d.U)).hom ((modulePullbackChartFMap B S hS f M).app d (s + s')) = _
  rw [(modulePullbackChartFMap B S hS f M).map_add d s s', map_add]
  rfl

/-- **The value of a chart section is semilinear** over pullback of regular functions along the
vertical scheme morphism of the square. -/
theorem modulePullbackChartValue_smul (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op d.V))
    (s : M.val.obj (op d.V)) :
    modulePullbackChartValue B S hS f M N τ d (r • s) =
      chartDiagramPullback B S hS f d r • modulePullbackChartValue B S hS f M N τ d s := by
  show (τ.val.app (op d.U)).hom ((modulePullbackChartFMap B S hS f M).app d (r • s)) = _
  rw [(modulePullbackChartFMap B S hS f M).map_smul d r s, map_smul]
  rfl

/-- **The value of a chart section is natural** in the commuting square. -/
theorem modulePullbackChartValue_map (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hij : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartValue B S hS f M N τ d' ((M.val.map j.op).hom s) =
      (N.val.map i.op).hom (modulePullbackChartValue B S hS f M N τ d s) := by
  show (τ.val.app (op d'.U)).hom
      ((modulePullbackChartFMap B S hS f M).app d' ((M.val.map j.op).hom s)) = _
  rw [(modulePullbackChartFMap B S hS f M).naturality d d' i j hij s]
  exact PresheafOfModules.naturality_apply τ.val i.op _

/-- **Restricting the value is taking the value of the restricted inverse image.** -/
theorem modulePullbackChartValue_restrict (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : M.val.obj (op d.V)) {Z : SmallEtale B S hS X.1} (ι : Z ⟶ d.U) :
    (N.val.map ι.op).hom (modulePullbackChartValue B S hS f M N τ d s) =
      (τ.val.app (op Z)).hom (modulePullbackChartSectionRestrict B S hS f M d s ι) :=
  (PresheafOfModules.naturality_apply τ.val ι.op _).symm

/-- **An isomorphism carries a free generator to a free generator.**  If `r ↦ r • y` is a
bijection onto the sections of `f^*M` over a chart and `τ` is an isomorphism, then
`r ↦ r • τ(y)` is a bijection onto the sections of `N` there. -/
theorem bijective_smul_map_of_isIso (hτ : IsIso τ) (Z : SmallEtale B S hS X.1)
    (y : ((modulePullback B S hS f).obj M).val.obj (op Z))
    (h : Function.Bijective fun r : chartRing B S hS X.1 X.2 Z ↦ r • y) :
    Function.Bijective fun r : chartRing B S hS X.1 X.2 Z ↦ r • (τ.val.app (op Z)).hom y := by
  have := hτ
  have hbij : Function.Bijective
      ((SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) (op Z)).map τ) :=
    ConcreteCategory.bijective_of_isIso _
  have hcomp : (fun r : chartRing B S hS X.1 X.2 Z ↦ r • (τ.val.app (op Z)).hom y) =
      (fun w : ((modulePullback B S hS f).obj M).val.obj (op Z) ↦ (τ.val.app (op Z)).hom w) ∘
        fun r : chartRing B S hS X.1 X.2 Z ↦ r • y := by
    funext r
    exact ((τ.val.app (op Z)).hom.map_smul r y).symm
  rw [hcomp]
  exact hbij.comp h

end General

/-! ### The value at a codimension-zero point -/

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {x : points B S hS X.1}
    (hx : localRingDimension B S hS x = 0) (M : Modules.{u, u} B S hS X.1 X.2)
    (t : P.genericPointPullback hx M ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).O))

/-- **The value at `η` of a section of `M` over an étale chart**, through a trivialisation `t` of
`j_η^*M`: a regular function on the base-changed chart `U ×_X Spec(𝒪_{X, η})`, that is a section
over `U` of the sheaf of rings `j_{η, *}𝒪_{X, η}`. -/
noncomputable def genericPointValue (U : SmallEtale B S hS X.1) (s : M.val.obj (op U)) :
    (P.genericPointStructureSheaf hx).obj.obj (op U) :=
  modulePullbackChartValue B S hS (P.genericMorphism hx X.2) M _ t
    (P.genericPointChartDiagram hx U) s

/-- The value at `η` is additive. -/
theorem genericPointValue_add (U : SmallEtale B S hS X.1) (s s' : M.val.obj (op U)) :
    P.genericPointValue hx M t U (s + s') =
      P.genericPointValue hx M t U s + P.genericPointValue hx M t U s' :=
  modulePullbackChartValue_add B S hS (P.genericMorphism hx X.2) M _ t
    (P.genericPointChartDiagram hx U) s s'

/-- The value at `η` is semilinear over the structure map `𝒪_X ⟶ j_{η, *}𝒪_{X, η}`. -/
theorem genericPointValue_smul (U : SmallEtale B S hS X.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op U))
    (s : M.val.obj (op U)) :
    P.genericPointValue hx M t U (r • s) =
      ((P.genericPointSharp hx).hom.app (op U)).hom r * P.genericPointValue hx M t U s :=
  modulePullbackChartValue_smul B S hS (P.genericMorphism hx X.2) M _ t
    (P.genericPointChartDiagram hx U) r s

/-- The commuting square of the chart diagrams at two charts of `X`: base change of charts is
compatible with the cartesian projections. -/
theorem genericPointChartDiagram_comm {U V : SmallEtale B S hS X.1} (k : U ⟶ V) :
    (SmallEtale.toOver B S hS (P.specStalkSpace hx).1).map
          ((smallBaseChange B S hS (P.genericMorphism hx X.2)
            (P.representable_genericMorphism hx)).map k) ≫
        (P.genericPointChartDiagram hx V).g =
      (P.genericPointChartDiagram hx U).g ≫ (SmallEtale.toOver B S hS X.1).map k :=
  smallBaseChange_map_snd B S hS (P.genericMorphism hx X.2)
    (P.representable_genericMorphism hx) k

/-- The value at `η` is natural in the chart. -/
theorem genericPointValue_map {U V : SmallEtale B S hS X.1} (k : U ⟶ V)
    (s : M.val.obj (op V)) :
    P.genericPointValue hx M t U ((M.val.map k.op).hom s) =
      ((P.genericPointStructureSheaf hx).obj.map k.op).hom
        (P.genericPointValue hx M t V s) :=
  modulePullbackChartValue_map B S hS (P.genericMorphism hx X.2) M _ t
    (P.genericPointChartDiagram hx V) (P.genericPointChartDiagram hx U)
    ((smallBaseChange B S hS (P.genericMorphism hx X.2)
      (P.representable_genericMorphism hx)).map k) k
    (P.genericPointChartDiagram_comm hx k) s

/-! ### The two readings of the sections over a base-changed chart -/

/-- The restriction maps of `𝒪_{Spec(𝒪_{X, η})}` read on the unit module and on the structure
sheaf are the same map: the unit module is the structure sheaf acting on itself. -/
theorem unitModule_map_eq_structureSheaf_map
    {W W' : SmallEtale B S hS (P.specStalkSpace hx).1} (g : W' ⟶ W)
    (y : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1
        (P.specStalkSpace hx).2).O)).val.obj (op W)) :
    ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).O)).val.map g.op).hom y =
      (((structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.map
        g.op).hom y :
        (structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.obj (op W')) :=
  rfl

/-- Scalar multiplication on the unit module is multiplication in the structure sheaf. -/
theorem unitModule_smul_eq_mul (W : SmallEtale B S hS (P.specStalkSpace hx).1)
    (r : chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2 W)
    (y : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1
        (P.specStalkSpace hx).2).O)).val.obj (op W)) :
    (show (structureSheaf B S hS (P.specStalkSpace hx).1
        (P.specStalkSpace hx).2).obj.obj (op W) from r • y) =
      (show (structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.obj (op W) from r) *
        (show (structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.obj (op W) from y) :=
  rfl

/-- The restriction maps of `j_{η, *}𝒪_{X, η}` are the restriction maps of
`𝒪_{Spec(𝒪_{X, η})}` along base change of charts. -/
theorem genericPointStructureSheaf_map {U V : SmallEtale B S hS X.1} (k : U ⟶ V)
    (y : (P.genericPointStructureSheaf hx).obj.obj (op V)) :
    ((P.genericPointStructureSheaf hx).obj.map k.op).hom y =
      (((structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.map
          ((smallBaseChange B S hS (P.genericMorphism hx X.2)
            (P.representable_genericMorphism hx)).map k).op).hom y :
        (structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.obj
          (op (P.genericPointChart hx U))) :=
  rfl

/-! ### The value at `η` of a free generator multiplies injectively -/

/-- **The value at `η` of a free generator is a unit over a covering sieve.**  The inverse image
of a free generator generates `j_η^*M` freely over the charts of a covering sieve of
`V ×_X Spec(𝒪_{X, η})`, and a trivialisation of `j_η^*M` carries a free generator of it to a free
generator of the structure sheaf, that is to a unit. -/
theorem exists_sieve_isUnit_genericPointValue (hiso : IsIso t)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (V : SmallEtale B S hS X.1)
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k) :
    ∃ T : Sieve (P.genericPointChart hx V),
      T ∈ SmallEtale.topology B S hS (P.specStalkSpace hx).1 (P.genericPointChart hx V) ∧
      ∀ ⦃Q : SmallEtale B S hS (P.specStalkSpace hx).1⦄ (ι : Q ⟶ P.genericPointChart hx V), T ι →
        IsUnit (((structureSheaf B S hS (P.specStalkSpace hx).1
            (P.specStalkSpace hx).2).obj.map ι.op).hom
          (P.genericPointValue hx M t V (e V (𝟙 V)))) := by
  obtain ⟨T, hT, hfree⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS
    (P.genericMorphism hx X.2) M hM (P.genericPointChartDiagram hx V) e hcompat hbij
  refine ⟨T, hT, fun Q ι hι ↦ ?_⟩
  have hrestrict : (((structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.map ι.op).hom
        (P.genericPointValue hx M t V (e V (𝟙 V)))) =
      (t.val.app (op Q)).hom (modulePullbackChartSectionRestrict B S hS
        (P.genericMorphism hx X.2) M (P.genericPointChartDiagram hx V) (e V (𝟙 V)) ι) :=
    (P.unitModule_map_eq_structureSheaf_map hx ι _).symm.trans
      (modulePullbackChartValue_restrict B S hS (P.genericMorphism hx X.2) M _ t
        (P.genericPointChartDiagram hx V) (e V (𝟙 V)) ι)
  have hb : Function.Bijective
      fun r : chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2 Q ↦
        r • modulePullbackChartSectionRestrict B S hS (P.genericMorphism hx X.2) M
          (P.genericPointChartDiagram hx V) (e V (𝟙 V)) ι :=
    Eq.mpr (congrArg
      (fun j : Q ⟶ P.genericPointChart hx V ↦ Function.Bijective
        fun r : chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2 Q ↦
          r • modulePullbackChartSectionRestrict B S hS (P.genericMorphism hx X.2) M
            (P.genericPointChartDiagram hx V) (e V (𝟙 V)) j)
      (Category.id_comp ι).symm) (hfree ι hι Q (𝟙 Q))
  obtain ⟨r, hr⟩ := (bijective_smul_map_of_isIso B S hS (P.genericMorphism hx X.2) M _ t hiso Q
    _ hb).surjective
    (show (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).O)).val.obj (op Q) from
      (1 : (structureSheaf B S hS (P.specStalkSpace hx).1
        (P.specStalkSpace hx).2).obj.obj (op Q)))
  refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
  rw [hrestrict]
  refine Eq.trans (mul_comm _ _) ?_
  exact (P.unitModule_smul_eq_mul hx Q r
    ((t.val.app (op Q)).hom (modulePullbackChartSectionRestrict B S hS
      (P.genericMorphism hx X.2) M (P.genericPointChartDiagram hx V) (e V (𝟙 V)) ι))).symm.trans hr

/-- **Multiplication by the value at `η` of a free generator is injective.**  Over the charts of
a covering sieve of `U ×_X Spec(𝒪_{X, η})` the value is a unit, so multiplication by it is
injective there, and injectivity is local because `𝒪_{Spec(𝒪_{X, η})}` is a sheaf. -/
theorem injective_mul_genericPointValue (hiso : IsIso t)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M)
    (V : SmallEtale B S hS X.1)
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (U : SmallEtale B S hS X.1) (k : U ⟶ V) :
    Function.Injective fun z : (P.genericPointStructureSheaf hx).obj.obj (op U) ↦
      z * P.genericPointValue hx M t U (e U k) := by
  obtain ⟨T, hT, hunit⟩ :=
    P.exists_sieve_isUnit_genericPointValue hx M t hiso hM V e hcompat hbij
  have hval : P.genericPointValue hx M t U (e U k) =
      (((structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.map
          ((smallBaseChange B S hS (P.genericMorphism hx X.2)
            (P.representable_genericMorphism hx)).map k).op).hom
        (P.genericPointValue hx M t V (e V (𝟙 V))) :
        (structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.obj
          (op (P.genericPointChart hx U))) := by
    refine Eq.trans ?_ (P.genericPointStructureSheaf_map hx k
      (P.genericPointValue hx M t V (e V (𝟙 V))))
    refine Eq.trans ?_ (P.genericPointValue_map hx M t k (e V (𝟙 V)))
    exact congrArg (P.genericPointValue hx M t U)
      ((hcompat V U (𝟙 V) k).trans (congrArg (e U) (Category.comp_id k))).symm
  intro z z' hz
  have hz' : z * P.genericPointValue hx M t U (e U k) =
      z' * P.genericPointValue hx M t U (e U k) := hz
  refine (structureSheaf B S hS (P.specStalkSpace hx).1
    (P.specStalkSpace hx).2).property.isSeparated (P.genericPointChart hx U)
    (T.pullback ((smallBaseChange B S hS (P.genericMorphism hx X.2)
      (P.representable_genericMorphism hx)).map k))
    ((SmallEtale.topology B S hS (P.specStalkSpace hx).1).pullback_stable _ hT) z z' ?_
  intro Q g hg
  have hcomp : ∀ w : (structureSheaf B S hS (P.specStalkSpace hx).1
        (P.specStalkSpace hx).2).obj.obj (op (P.genericPointChart hx V)),
      ((structureSheaf B S hS (P.specStalkSpace hx).1
            (P.specStalkSpace hx).2).obj.map g.op).hom
          (((structureSheaf B S hS (P.specStalkSpace hx).1
            (P.specStalkSpace hx).2).obj.map
              ((smallBaseChange B S hS (P.genericMorphism hx X.2)
                (P.representable_genericMorphism hx)).map k).op).hom w) =
        ((structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.map
          (g ≫ (smallBaseChange B S hS (P.genericMorphism hx X.2)
            (P.representable_genericMorphism hx)).map k).op).hom w :=
    fun w => (ConcreteCategory.congr_hom
      ((structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.map_comp
        ((smallBaseChange B S hS (P.genericMorphism hx X.2)
          (P.representable_genericMorphism hx)).map k).op g.op) w).symm
  have e3 : ((structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.map g.op).hom
        (P.genericPointValue hx M t U (e U k)) =
      ((structureSheaf B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2).obj.map
        (g ≫ (smallBaseChange B S hS (P.genericMorphism hx X.2)
          (P.representable_genericMorphism hx)).map k).op).hom
        (P.genericPointValue hx M t V (e V (𝟙 V))) := by
    rw [hval]
    exact hcomp _
  have key : ((structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.map g.op).hom z *
        ((structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.map g.op).hom
          (P.genericPointValue hx M t U (e U k)) =
      ((structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.map g.op).hom z' *
        ((structureSheaf B S hS (P.specStalkSpace hx).1
          (P.specStalkSpace hx).2).obj.map g.op).hom
          (P.genericPointValue hx M t U (e U k)) := by
    exact (RingHom.map_mul _ _ _).symm.trans ((congrArg _ hz').trans (RingHom.map_mul _ _ _))
  rw [e3] at key
  exact (IsUnit.mul_left_inj (hunit _ hg)).mp key

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
