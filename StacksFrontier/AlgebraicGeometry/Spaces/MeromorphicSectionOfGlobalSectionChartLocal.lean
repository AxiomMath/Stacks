module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionOfGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent

/-!
# The canonical meromorphic section of a global section, read on a chart

Let `F` be an algebraic space over a base scheme `S` and let `M` be a sheaf of `𝒪_F`-modules.
A *global* section `m ∈ Γ(F, M)` is in particular a *meromorphic* section of `M`: over an étale
chart `V` its value is the pure meromorphic section `1 ⊗ m|_V` of
`AlgebraicGeometry.Space.toMeromorphicSectionValue`, and those values are compatible with
restriction. This file constructs that section, `AlgebraicGeometry.Space.toMeromorphicSection`,
and computes it on a chart.

The point of the construction is that the divisor `div_ℒ(-)` of Stacks 0EPU is a function of a
meromorphic section, while the left-hand side of Stacks 0EQF is indexed by a global section
`s ∈ Γ(X, ℒ)` of an invertible module. The two are connected here: `s` is carried to a
meromorphic section, that section is regular as soon as `s ≠ 0` on a locally Noetherian integral
algebraic space, and over a chart trivializing `ℒ` its chart ratio against the free generator is
the image of the *regular* coordinate function of `s` in that trivialization. The last statement
is what makes `ord_{Z, ℒ}(s)` computable as the order of vanishing of a regular function, which
is the form Stacks 0846 needs in order to recognise it as a local equation for the zero scheme
`Z(s)`.

## Main results

* `AlgebraicGeometry.Space.toMeromorphicSection`: the canonical meromorphic section of a global
  section, with `AlgebraicGeometry.Space.toMeromorphicSection_eval`,
  `AlgebraicGeometry.Space.toMeromorphicSection_zero` and
  `AlgebraicGeometry.Space.toMeromorphicSection_add`.
* `AlgebraicGeometry.Space.injective_toMeromorphicSection` and
  `AlgebraicGeometry.Space.toMeromorphicSection_ne_zero`: for an invertible module the
  construction is injective, so a nonzero global section has a nonzero meromorphic section.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_toMeromorphicSection`: on a locally
  Noetherian integral algebraic space that section is regular — the identification
  "regular (i.e., nonzero)" of Stacks 0EPS.
* `AlgebraicGeometry.Space.chartDual` and `AlgebraicGeometry.Space.chartDual_smul`: the
  coordinate functional `l₀` of a free generator over a chart, with its defining property
  `l₀(x) · t = x`.
* `AlgebraicGeometry.Space.chartRatio_toMeromorphicSection` and
  `AlgebraicGeometry.Space.chartRatio_toMeromorphicSection_dual`: the chart-coordinate formula,
  in terms of the coefficient of `s|_V` and in terms of `l₀`.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space


attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The canonical meromorphic section of a global section -/

/-- **The canonical meromorphic section of a global section.**  A global section `m` of a sheaf
of `𝒪_F`-modules `M` is a meromorphic section of `M`: its value over an étale chart `V` is the
pure meromorphic section `1 ⊗ m|_V` of
`AlgebraicGeometry.Space.toMeromorphicSectionValue`, and those values are compatible with
restriction by `AlgebraicGeometry.Space.toMeromorphicSectionValue_map`.

This is the map along which a *global* section `s ∈ Γ(X, ℒ)` is the argument of the divisor
`div_ℒ(-)` of Stacks 0EPU, which is a function of a *meromorphic* section; it is what the
left-hand side of Stacks 0EQF denotes. -/
def toMeromorphicSection (M : Modules.{u, u} B S hS F hF) (m : M.sections) :
    MeromorphicSection.{u, u} B S hS F hF M :=
  PresheafOfModules.sectionsMk (M := (meromorphicSectionSheaf.{u, u} B S hS F hF M).val)
    (fun V ↦ toMeromorphicSectionValue B S hS F hF M V.unop (m.eval V))
    fun {V W} f ↦
      (toMeromorphicSectionValue_map B S hS F hF M V.unop W.unop f.unop (m.eval V)).trans
        (congrArg (toMeromorphicSectionValue B S hS F hF M W.unop)
          (PresheafOfModules.sections_property (M := M.val) m f))

/-- **The value of the canonical meromorphic section over a chart** is the pure meromorphic
section `1 ⊗ m|_V` of `AlgebraicGeometry.Space.toMeromorphicSectionValue`. -/
@[simp]
theorem toMeromorphicSection_eval (M : Modules.{u, u} B S hS F hF) (m : M.sections)
    (V : SmallEtale B S hS F) :
    (toMeromorphicSection B S hS F hF M m).eval (op V) =
      toMeromorphicSectionValue B S hS F hF M V (m.eval (op V)) :=
  rfl

/-- The canonical meromorphic section of the zero section is zero. -/
@[simp]
theorem toMeromorphicSection_zero (M : Modules.{u, u} B S hS F hF) :
    toMeromorphicSection B S hS F hF M 0 = 0 :=
  PresheafOfModules.sections_ext _ _ fun V ↦
    toMeromorphicSectionValue_zero B S hS F hF M V.unop

/-- Taking the canonical meromorphic section of a global section is additive. -/
theorem toMeromorphicSection_add (M : Modules.{u, u} B S hS F hF) (m m' : M.sections) :
    toMeromorphicSection B S hS F hF M (m + m') =
      toMeromorphicSection B S hS F hF M m + toMeromorphicSection B S hS F hF M m' :=
  PresheafOfModules.sections_ext _ _ fun V ↦
    toMeromorphicSectionValue_add B S hS F hF M V.unop (m.eval V) (m'.eval V)

/-! ### Injectivity, and regularity of the section of a nonzero global section -/

section Invertible

variable (X : AlgebraicSpaces B S hS)

/-- **The canonical meromorphic section of an invertible module determines the global section.**
Being injective over every chart (`AlgebraicGeometry.Space.injective_toMeromorphicSectionValue`,
where invertibility of `ℒ` is used), the canonical map is injective on global sections. -/
theorem injective_toMeromorphicSection (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) :
    Function.Injective (toMeromorphicSection B S hS X.1 X.2 L) := by
  intro m m' hmm
  refine PresheafOfModules.sections_ext (M := L.val) m m' fun V ↦ ?_
  refine injective_toMeromorphicSectionValue B S hS X L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) V.unop ?_
  exact congrArg (fun z : MeromorphicSection.{u, u} B S hS X.1 X.2 L ↦ z.eval V) hmm

/-- **A nonzero global section of an invertible module has a nonzero canonical meromorphic
section.**  This is `AlgebraicGeometry.Space.injective_toMeromorphicSection`, and it is what
feeds the identification "regular (i.e., nonzero)" of Stacks 0EPS. -/
theorem toMeromorphicSection_ne_zero (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) (s : L.sections) (hs : s ≠ 0) :
    toMeromorphicSection B S hS X.1 X.2 L s ≠ 0 :=
  ((injective_toMeromorphicSection B S hS X L hL).ne_iff'
    (toMeromorphicSection_zero B S hS X.1 X.2 L)).mpr hs

end Invertible

section Regular

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (hInt : IsIntegralSpace B S hS X)
  (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **The canonical meromorphic section of a nonzero global section of an invertible module on a
locally Noetherian integral algebraic space is regular.**  This is the hypothesis every consumer
of the divisor `div_ℒ(-)` of Stacks 0EPU carries, for the meromorphic section attached to a
global section `s ∈ Γ(X, ℒ)` — so it is what makes the left-hand side of Stacks 0EQF a term.

The section is nonzero by `AlgebraicGeometry.Space.toMeromorphicSection_ne_zero`, and a nonzero
meromorphic section of an invertible module on such a space is regular by
`AlgebraicGeometry.Space.isRegularMeromorphicSection_of_ne_zero`, which is the identification
"regular (i.e., nonzero)" of Stacks 0EPS. -/
theorem isRegularMeromorphicSection_toMeromorphicSection (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) (s : L.sections) (hs : s ≠ 0) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX L
      (toMeromorphicSection B S hS X hX L s) :=
  isRegularMeromorphicSection_of_ne_zero B S hS hX hInt hN L hL _
    (toMeromorphicSection_ne_zero B S hS ⟨X, hX⟩ L hL s hs)

end Regular

/-! ### The chart-coordinate formula -/

/-- **The coordinate functional of a free generator of a module over a chart.**  If `t` generates
`M(V)` freely over the regular functions of the chart, this is the inverse of `r ↦ r · t`: the
linear functional `l₀` with `l₀(x) · t = x`.

It is the `l₀` that Stacks 0846, part (4) takes as a hypothesis
(`AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_span_singleton`), produced from the
bijectivity hypothesis in which the chart-ratio API
(`AlgebraicGeometry.Space.chartRatio`) states freeness. -/
def chartDual (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (t : M.val.obj (op V))
    (ht : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • t) :
    Module.Dual (chartRing B S hS F hF V) (M.val.obj (op V)) :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (chartRing B S hS F hF V) (M.val.obj (op V)) t) ht).symm.toLinearMap

/-- **The defining property of the coordinate functional**: `l₀(x) · t = x`, which is the
hypothesis `hb` of `AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_span_singleton`. -/
theorem chartDual_smul (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (t : M.val.obj (op V))
    (ht : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • t)
    (x : M.val.obj (op V)) :
    chartDual B S hS F hF M V t ht x • t = x :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (chartRing B S hS F hF V) (M.val.obj (op V)) t)
    ht).apply_symm_apply x

variable (L : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
  (e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W))

/-- **The chart-coordinate formula.**  Let `V` be an étale chart over which `ℒ` is free on the
compatible family `e`, and let `s` be a global section of `ℒ` whose restriction to `V` is
`s|_V = r · e`.  Then the chart ratio
(`AlgebraicGeometry.Space.chartRatio`) of the canonical meromorphic section of `s` against `e` is
the image of `r` under the canonical map `𝒪_F(V) → 𝒦_F(V)` of the regular functions into the
meromorphic ones.

This is the step connecting the two sides of Stacks 0EQF: the order of vanishing
`ord_{Z,ℒ}(s)` read on a trivializing chart is, by
`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`,
the order of vanishing of this chart ratio in `Q(𝒪_{V, v})`, and the formula identifies it with
the order of vanishing of the *regular* function `r` — which by Stacks 0846 is a local equation
for the zero scheme `Z(s)` at `v`.

Both sides are the unique meromorphic function presenting the section over `V` against `e`
(`AlgebraicGeometry.Space.chartRatio_eq_of_eval_eq`): the value of the canonical meromorphic
section over `V` is the pure meromorphic section `1 ⊗ r · e`, which is `(algebraMap r) ⊗ e` by
`AlgebraicGeometry.Space.pureMeromorphicSection_smul_eq_algebraMap_tmul`. -/
theorem chartRatio_toMeromorphicSection
    (hecompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (s : L.sections) (r : chartRing B S hS F hF V) (hr : r • e V (𝟙 V) = s.eval (op V)) :
    chartRatio B S hS F hF L V e hecompat hebij
        (toMeromorphicSection B S hS F hF L s) =
      (algebraMap (chartRing B S hS F hF V)
        ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) r :
          meromorphicChartRing B S hS F hF V) := by
  refine chartRatio_eq_of_eval_eq B S hS F hF L V e hecompat hebij _ _ ?_
  rw [toMeromorphicSection_eval, toMeromorphicSectionValue_eq, ← hr,
    pureMeromorphicSection_smul_eq_algebraMap_tmul]

/-- **The chart-coordinate formula at the coordinate functional of Stacks 0846, part (4).**  In
the situation of `AlgebraicGeometry.Space.chartRatio_toMeromorphicSection`, the coordinate of
`s|_V` against the generator is `l₀(s|_V)` for the coordinate functional `l₀` of
`AlgebraicGeometry.Space.chartDual`, so the chart ratio of the canonical meromorphic section of
`s` is the image of `l₀(s|_V)` in `𝒦_F(V)`.

This is the shape in which the local equation of the zero scheme `Z(s)` is stated: the defining
ideal of `Z(s)` on the affine chart `V` is generated by `l₀(s|_V)`, which is Stacks 0846 through
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_span_singleton`.  So the two coefficients of
Stacks 0EQF at a prime divisor through `V` are the order of vanishing and the length of the
quotient by the *same* regular function. -/
theorem chartRatio_toMeromorphicSection_dual
    (hecompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (s : L.sections) :
    chartRatio B S hS F hF L V e hecompat hebij
        (toMeromorphicSection B S hS F hF L s) =
      (algebraMap (chartRing B S hS F hF V)
        ((meromorphicChartSheaf B S hS F hF).obj.obj (op V))
        (chartDual B S hS F hF L V (e V (𝟙 V)) (hebij V (𝟙 V)) (s.eval (op V))) :
          meromorphicChartRing B S hS F hF V) :=
  chartRatio_toMeromorphicSection B S hS F hF L V e hecompat hebij s _
    (chartDual_smul B S hS F hF L V (e V (𝟙 V)) (hebij V (𝟙 V)) (s.eval (op V)))


/-! ### The two spellings of the meromorphic section of a global section

`AlgebraicGeometry.Space.toMeromorphicSection` and
`AlgebraicGeometry.Space.globalSectionMeromorphic` are the same
construction: both send a global section to the pure tensor `1 ⊗ s|_V` over every chart.  The
identification below is definitional, so either name may be used. -/

/-- The two constructions of the meromorphic section of a global section agree: this one is
`AlgebraicGeometry.Space.globalSectionMeromorphic`. -/
theorem toMeromorphicSection_eq_globalSectionMeromorphic
    (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2) (s : L.sections) :
    toMeromorphicSection B S hS X.1 X.2 L s = globalSectionMeromorphic B S hS X.2 L s :=
  rfl

end AlgebraicGeometry.Space

end
