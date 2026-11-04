module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent

/-!
# The ideal of denominators of a meromorphic section

Let `X` be an algebraic space, `ℒ` an invertible `𝒪_X`-module and `t` a meromorphic section of
`ℒ`. The *ideal of denominators* of `t` is the ideal `𝓘 ⊆ 𝒪_X` whose sections over an étale
chart `V` are the regular functions `a` with `a · t|_V` an honest section of `ℒ` over `V`:

`𝓘(V) = {a ∈ 𝒪_X(V) : a · t|_V ∈ ℒ(V) ⊆ 𝒦_X(ℒ)(V)}`.

Multiplication by `t` is then a map `𝓘 ⟶ ℒ`.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicDenominatorIdeal`: the ideal of denominators of `t`, as a
  submodule of the structure sheaf.

## Implementation notes

Membership is a local condition because lying in `ℒ` is a local condition on a meromorphic
section of `ℒ` (`AlgebraicGeometry.Space.exists_toMeromorphicSectionValue_eq_of_sieve`), which is
where invertibility of `ℒ` is used.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
  (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)

/-- A regular function over a chart, read as a meromorphic function at the spelling over which
the meromorphic sections of a module are modules. -/
noncomputable abbrev chartMeromorphicScalar (V : SmallEtale B S hS X.1) :
    chartRing B S hS X.1 X.2 V →+* meromorphicChartRing B S hS X.1 X.2 V :=
  algebraMap (chartRing B S hS X.1 X.2 V)
    ((meromorphicChartSheaf B S hS X.1 X.2).obj.obj (op V))

/-- The predicate cutting out the ideal of denominators over a chart: `a · t|_V` is the image of
a section of `ℒ` over `V`. -/
def IsMeromorphicDenominator (V : SmallEtale B S hS X.1) (a : chartRing B S hS X.1 X.2 V) :
    Prop :=
  ∃ m : L.val.obj (op V), toMeromorphicSectionValue B S hS X.1 X.2 L V m =
    chartMeromorphicScalar B S hS X V a • t.eval (op V)

/-- `0` is a denominator of `t` over every chart. -/
theorem isMeromorphicDenominator_zero (V : SmallEtale B S hS X.1) :
    IsMeromorphicDenominator B S hS X L t V 0 := by
  refine ⟨0, ?_⟩
  rw [toMeromorphicSectionValue_zero, map_zero]
  exact (zero_smul (meromorphicChartRing B S hS X.1 X.2 V) _).symm

/-- Sums of chosen sections realising `a · t` and `b · t` realise `(a + b) · t`. -/
private theorem toMeromorphicSectionValue_choose_add {V : SmallEtale B S hS X.1}
    {a b : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a)
    (hb : IsMeromorphicDenominator B S hS X L t V b) :
    toMeromorphicSectionValue B S hS X.1 X.2 L V (ha.choose + hb.choose) =
      chartMeromorphicScalar B S hS X V (a + b) • t.eval (op V) := by
  rw [toMeromorphicSectionValue_add, ha.choose_spec, hb.choose_spec, map_add]
  exact (add_smul _ _ _).symm

/-- Scaling a chosen section realising `a · t` by `r` realises `(r * a) · t`. -/
private theorem toMeromorphicSectionValue_smul_choose {V : SmallEtale B S hS X.1}
    (r : chartRing B S hS X.1 X.2 V) {a : chartRing B S hS X.1 X.2 V}
    (ha : IsMeromorphicDenominator B S hS X L t V a) :
    toMeromorphicSectionValue B S hS X.1 X.2 L V (r • ha.choose) =
      chartMeromorphicScalar B S hS X V (r * a) • t.eval (op V) := by
  rw [toMeromorphicSectionValue_smul B S hS X.1 X.2 L V r _ _ rfl, ha.choose_spec, map_mul]
  exact (mul_smul _ _ _).symm

/-- The denominators of `t` over a chart are closed under addition. -/
theorem isMeromorphicDenominator_add {V : SmallEtale B S hS X.1}
    {a b : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a)
    (hb : IsMeromorphicDenominator B S hS X L t V b) :
    IsMeromorphicDenominator B S hS X L t V (a + b) := by
  exact ⟨_, toMeromorphicSectionValue_choose_add B S hS X L t ha hb⟩

/-- A multiple `r * a` of a denominator `a` of `t` over a chart is a denominator of `t`. -/
theorem isMeromorphicDenominator_mul {V : SmallEtale B S hS X.1}
    (r : chartRing B S hS X.1 X.2 V) {a : chartRing B S hS X.1 X.2 V}
    (ha : IsMeromorphicDenominator B S hS X L t V a) :
    IsMeromorphicDenominator B S hS X L t V (r * a) := by
  exact ⟨_, toMeromorphicSectionValue_smul_choose B S hS X L t r ha⟩

/-- Restricting `a · t` along a morphism of charts is `a|_W · t|_W`. -/
theorem meromorphicSectionSheaf_map_chartMeromorphicScalar_smul {V W : SmallEtale B S hS X.1}
    (g : W ⟶ V) (a : chartRing B S hS X.1 X.2 V) :
    ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 L).val.map g.op).hom
        (chartMeromorphicScalar B S hS X V a • t.eval (op V)) =
      chartMeromorphicScalar B S hS X W
          (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g.op).hom a) • t.eval (op W) := by
  rw [PresheafOfModules.map_smul, PresheafOfModules.sections_property t g.op]
  congr 1
  exact (ConcreteCategory.congr_hom
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.naturality g.op) a).symm

/-- The restriction of a denominator of `t` along a morphism of charts `W ⟶ V` is a denominator
of `t` over `W`. -/
theorem isMeromorphicDenominator_map {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    {a : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a) :
    IsMeromorphicDenominator B S hS X L t W
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g.op).hom a) := by
  obtain ⟨m, hm⟩ := ha
  refine ⟨(L.val.map g.op).hom m, ?_⟩
  rw [← toMeromorphicSectionValue_map, hm,
    meromorphicSectionSheaf_map_chartMeromorphicScalar_smul]

variable (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
  (structureRingSheaf B S hS X).property L)

/-- The ideal of denominators of `t` over a chart `V`: the `a ∈ 𝒪_X(V)` with `a · t|_V ∈ ℒ(V)`. -/
noncomputable def meromorphicDenominatorIdealAt (V : SmallEtale B S hS X.1) :
    Ideal (chartRing B S hS X.1 X.2 V) where
  carrier := {a | IsMeromorphicDenominator B S hS X L t V a}
  zero_mem' := isMeromorphicDenominator_zero B S hS X L t V
  add_mem' := isMeromorphicDenominator_add B S hS X L t
  smul_mem' := fun r _ ha => isMeromorphicDenominator_mul B S hS X L t r ha

/-- Membership in the ideal of denominators over `V` is being a denominator of `t` over `V`. -/
theorem mem_meromorphicDenominatorIdealAt_iff (V : SmallEtale B S hS X.1)
    (a : chartRing B S hS X.1 X.2 V) :
    a ∈ meromorphicDenominatorIdealAt B S hS X L t V ↔
      IsMeromorphicDenominator B S hS X L t V a :=
  Iff.rfl

/-- **The ideal of denominators of a meromorphic section** of an invertible module, as a
submodule of the structure sheaf: over a chart `V` it consists of the `a ∈ 𝒪_X(V)` for which
`a · t|_V` is a section of `ℒ`. -/
noncomputable def meromorphicDenominatorIdeal :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).Submodule where
  obj V := meromorphicDenominatorIdealAt B S hS X L t V.unop
  map {V W} g a ha := isMeromorphicDenominator_map B S hS X L t g.unop ha
  isSheaf {V} a ha := by
    obtain ⟨m, hm⟩ := exists_toMeromorphicSectionValue_eq_of_sieve B S hS X L hL V.unop
      (chartMeromorphicScalar B S hS X V.unop a • t.eval (op V.unop)) _ ha (fun W k hk => by
        obtain ⟨e, he⟩ := hk
        refine ⟨e, he.trans ?_⟩
        exact (meromorphicSectionSheaf_map_chartMeromorphicScalar_smul B S hS X L t k a).symm)
    exact ⟨m, hm⟩

/-- The section `a · t|_V` of `ℒ` attached to a denominator `a` of `t` over `V`. -/
noncomputable def meromorphicDenominatorNumerator {V : SmallEtale B S hS X.1}
    {a : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a) :
    L.val.obj (op V) :=
  ha.choose

/-- The meromorphic value of the numerator attached to a denominator `a` is `a · t|_V`. -/
theorem toMeromorphicSectionValue_meromorphicDenominatorNumerator {V : SmallEtale B S hS X.1}
    {a : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a) :
    toMeromorphicSectionValue B S hS X.1 X.2 L V
        (meromorphicDenominatorNumerator B S hS X L t ha) =
      chartMeromorphicScalar B S hS X V a • t.eval (op V) :=
  ha.choose_spec

include hL in
/-- The numerator `a · t|_V` is the only section of `ℒ` with that meromorphic value. -/
theorem eq_meromorphicDenominatorNumerator {V : SmallEtale B S hS X.1}
    {a : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a)
    {m : L.val.obj (op V)}
    (hm : toMeromorphicSectionValue B S hS X.1 X.2 L V m =
      chartMeromorphicScalar B S hS X V a • t.eval (op V)) :
    m = meromorphicDenominatorNumerator B S hS X L t ha :=
  injective_toMeromorphicSectionValue B S hS X L hL V
    (hm.trans (toMeromorphicSectionValue_meromorphicDenominatorNumerator B S hS X L t ha).symm)

include hL in
/-- The numerator of a sum of denominators is the sum of their numerators. -/
theorem meromorphicDenominatorNumerator_add {V : SmallEtale B S hS X.1}
    {a b : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a)
    (hb : IsMeromorphicDenominator B S hS X L t V b)
    (hab : IsMeromorphicDenominator B S hS X L t V (a + b)) :
    meromorphicDenominatorNumerator B S hS X L t hab =
      meromorphicDenominatorNumerator B S hS X L t ha +
        meromorphicDenominatorNumerator B S hS X L t hb := by
  exact (eq_meromorphicDenominatorNumerator B S hS X L t hL hab
    (toMeromorphicSectionValue_choose_add B S hS X L t ha hb)).symm

include hL in
/-- The numerator of `r * a` is `r` times the numerator of `a`. -/
theorem meromorphicDenominatorNumerator_mul {V : SmallEtale B S hS X.1}
    (r : chartRing B S hS X.1 X.2 V) {a : chartRing B S hS X.1 X.2 V}
    (ha : IsMeromorphicDenominator B S hS X L t V a)
    (hra : IsMeromorphicDenominator B S hS X L t V (r * a)) :
    meromorphicDenominatorNumerator B S hS X L t hra =
      r • meromorphicDenominatorNumerator B S hS X L t ha := by
  exact (eq_meromorphicDenominatorNumerator B S hS X L t hL hra
    (toMeromorphicSectionValue_smul_choose B S hS X L t r ha)).symm

include hL in
/-- The numerator of the restriction of a denominator along `W ⟶ V` is the restriction of its
numerator. -/
theorem meromorphicDenominatorNumerator_map {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    {a : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a)
    (ha' : IsMeromorphicDenominator B S hS X L t W
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.map g.op).hom a)) :
    meromorphicDenominatorNumerator B S hS X L t ha' =
      (L.val.map g.op).hom (meromorphicDenominatorNumerator B S hS X L t ha) := by
  refine (eq_meromorphicDenominatorNumerator B S hS X L t hL ha' ?_).symm
  rw [← toMeromorphicSectionValue_map, toMeromorphicSectionValue_meromorphicDenominatorNumerator,
    meromorphicSectionSheaf_map_chartMeromorphicScalar_smul]

/-- **Multiplication by `t` on its ideal of denominators**, `𝓘 ⟶ ℒ`, `a ↦ a · t`. -/
noncomputable def meromorphicDenominatorMul :
    (meromorphicDenominatorIdeal B S hS X L t hL).toSheafOfModules ⟶ L where
  val :=
    { app V := ModuleCat.ofHom
        { toFun a := meromorphicDenominatorNumerator B S hS X L t (V := V.unop) a.2
          map_add' a b := meromorphicDenominatorNumerator_add B S hS X L t hL (V := V.unop)
            a.2 b.2 (a + b).2
          map_smul' r a := meromorphicDenominatorNumerator_mul B S hS X L t hL (V := V.unop) r
            a.2 (r • a).2 }
      naturality {V W} g := by
        ext a
        exact meromorphicDenominatorNumerator_map B S hS X L t hL g.unop a.2 _ }

/-- For a *regular* meromorphic section, distinct denominators have distinct numerators. -/
theorem eq_of_meromorphicDenominatorNumerator_eq
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) {V : SmallEtale B S hS X.1}
    {a b : chartRing B S hS X.1 X.2 V} (ha : IsMeromorphicDenominator B S hS X L t V a)
    (hb : IsMeromorphicDenominator B S hS X L t V b)
    (hab : meromorphicDenominatorNumerator B S hS X L t ha =
      meromorphicDenominatorNumerator B S hS X L t hb) : a = b := by
  have h := congrArg (toMeromorphicSectionValue B S hS X.1 X.2 L V) hab
  rw [toMeromorphicSectionValue_meromorphicDenominatorNumerator,
    toMeromorphicSectionValue_meromorphicDenominatorNumerator] at h
  exact injective_toMeromorphicFunctionSheaf B S hS X.1 X.2 V (ht V h)

include hL in
/-- Multiplication by a *regular* meromorphic section on its ideal of denominators is injective
over every chart. -/
theorem injective_meromorphicDenominatorMul_app
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) (V : SmallEtale B S hS X.1) :
    Function.Injective ((meromorphicDenominatorMul B S hS X L t hL).val.app (op V)) :=
  fun a b hab => Subtype.ext (eq_of_meromorphicDenominatorNumerator_eq B S hS X L t ht a.2 b.2 hab)

include hL in
/-- Multiplication by a *regular* meromorphic section on its ideal of denominators is a
monomorphism. -/
theorem mono_meromorphicDenominatorMul
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) :
    Mono (meromorphicDenominatorMul B S hS X L t hL) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun V =>
      injective_meromorphicDenominatorMul_app B S hS X L t hL ht V.unop)

end AlgebraicGeometry.Space
