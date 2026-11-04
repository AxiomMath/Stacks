module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTensorGlobal

/-!
# The product of two meromorphic sections read against a product of generators

Let `X` be an algebraic space over a scheme `S` satisfying the hypotheses (a) and (b) of
Stacks 0EN6, let `ℒ` and `𝒩` be quasi-coherent `𝒪_X`-modules and let `s` and `t` be meromorphic
sections of `ℒ` and of `𝒩`.  Over a chart `V` carrying a family of sections of `ℒ` compatible
with restriction, `s` is `a · e` for a meromorphic function `a` on `V`, and likewise `t` is
`b · f`; the global product `s ⊗ t`, `AlgebraicGeometry.Space.meromorphicSectionTensor`, then
satisfies

`(s ⊗ t)|_V = (a b) · (e ⊗ f)`.

That identity is what reads the product against a generator, and it is **not** restricted to
affine charts: the characterisation of `s ⊗ t` gives its restriction to the affine charts over
`V`, and over each of them both sides are the same pure tensor, so the two agree by
separatedness of `𝒦_X(ℒ ⊗ 𝒩)`.

With it, regularity of the product follows.  `e ⊗ f` is a free generator of `ℒ ⊗ 𝒪_X 𝒩` over
every chart over `V` when `e` and `f` are free generators of `ℒ` and of `𝒩`
(`AlgebraicGeometry.Space.bijective_smul_tensorChartSection`), and the coefficient `a b` can be
cancelled: the coefficient of a *regular* meromorphic section against any section is a
nonzerodivisor, which is exactly what multiplication by the section being injective says.  So
multiplication by `s ⊗ t` is injective over every chart over which both modules are free, and
those charts cover.

## Main results

* `AlgebraicGeometry.Space.eval_meromorphicSectionTensor_eq_tmul`: the identity above.
* `AlgebraicGeometry.Space.mul_right_cancel_of_isRegularMeromorphicSection`: the coefficient of a
  regular meromorphic section against a section of the module is a nonzerodivisor.
* `AlgebraicGeometry.Space.injective_smul_eval_meromorphicSectionTensor_of_generators`:
  multiplication by the product is injective over a chart carrying free generators of both
  modules.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_meromorphicSectionTensor`: **the product
  of two regular meromorphic sections of invertible modules is regular**, which is Stacks 0ENB
  for the product.

## Implementation notes

The coefficient has to be cancelled and not inverted: it is a nonzerodivisor of the total
fraction ring over the chart, and nothing makes it a unit there.  That is why
`AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit` is not what is applied — its
hypothesis `IsUnit c` is the form in which Stacks 0ENC part (2) produces a coefficient, not the
form regularity gives.  The statement below replaces it by the cancellation property, which
regularity delivers over *every* chart over `V` at once, and which is all the proof of that lemma
uses of `IsUnit c`.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] tensorChartModule
attribute [local instance] tensorChartMeromorphicAlgebra
attribute [local instance] tensorChartMeromorphicSectionModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (L N : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)

/-- The product of the generators of the family restricts to the product of the restricted
generators. -/
private theorem map_tensorChartSection_generators (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (f : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (Z : SmallEtale B S hS X) (g : Z ⟶ V) :
    ((picardTensorModule B S hS hX L N).val.map g.op).hom
        (tensorChartSection B S hS hX L N V (e V (𝟙 V)) (f V (𝟙 V))) =
      tensorChartSection B S hS hX L N Z (e Z g) (f Z g) := by
  simpa only [Category.comp_id] using
    tensorChartSection_restrict_family B S hS hX L N V e f hecompat hfcompat V (𝟙 V) Z g

/-- Multiplying a meromorphic section by `z` multiplies the element it is the image of. -/
private theorem smul_eval_eq_toMeromorphicSectionSheaf_smul (M : Modules.{u, u} B S hS X hX)
    (σ : MeromorphicSection.{u, u} B S hS X hX M) (V : SmallEtale B S hS X)
    (m : (meromorphicSectionModule B S hS X hX M).obj (op V))
    (h : σ.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V m)
    (z : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj (op V)) :
    z • σ.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V (z • m) :=
  (congrArg (fun w ↦ z • w) h).trans (toMeromorphicSectionSheaf_smul B S hS X hX M V z m).symm

include hwa hfin in
/-- **The product of two meromorphic sections read against a product of generators.**  If over a
chart `V` the meromorphic section `s` is `a · e` and `t` is `b · f`, with `e` and `f` families of
sections of `ℒ` and of `𝒩` over the charts over `V` compatible with restriction, then the global
product `s ⊗ t` is `(a b) · (e ⊗ f)` over `V`.

Both sides restrict, over an affine chart `W` over `V`, to the chartwise product of `a|_W · e|_W`
and `b|_W · f|_W`: the left-hand side by the characterisation
`AlgebraicGeometry.Space.isChartwiseTensorMul_meromorphicSectionTensor` of the product together
with `AlgebraicGeometry.Space.meromorphicSectionTensorMul_tmul`, the right-hand side because the
restriction maps of the meromorphic sections carry a pure tensor to the tensor of the
restrictions.  The affine charts over `V` cover it, so the two sides agree.

No freeness of `e` or of `f` is used, and `V` need not be affine. -/
theorem eval_meromorphicSectionTensor_eq_tmul (hLqc : L.IsQuasicoherentOnSite)
    (hNqc : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (f : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (a b : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj (op V))
    (hs : s.eval (op V) = toMeromorphicSectionSheaf B S hS X hX L V
      (a ⊗ₜ[chartRing B S hS X hX V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS X hX L).obj (op V)))
    (ht : t.eval (op V) = toMeromorphicSectionSheaf B S hS X hX N V
      (b ⊗ₜ[chartRing B S hS X hX V] f V (𝟙 V) :
        (meromorphicSectionModule B S hS X hX N).obj (op V))) :
    (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc).eval (op V) =
      toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V
        ((a * b) ⊗ₜ[chartRing B S hS X hX V]
            tensorChartSection B S hS hX L N V (e V (𝟙 V)) (f V (𝟙 V)) :
          (meromorphicSectionModule B S hS X hX
            (picardTensorModule B S hS hX L N)).obj (op V)) := by
  obtain ⟨I, Y, κ, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X V
  refine meromorphicSectionSheaf_eq_of_cover B S hS X hX (picardTensorModule B S hS hX L N) V
    Y κ hcov _ _ fun i ↦ ?_
  -- the two coefficients, restricted to the affine chart
  have hres := isChartwiseTensorMul_meromorphicSectionTensor B S hS hX hwa hfin L N s t
    hLqc hNqc V (Y i) (κ i) (haff i) _ _
    (eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X hX L s V e hecompat a hs
      (Y i) (κ i))
    (eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X hX N t V f hfcompat b ht
      (Y i) (κ i))
  refine Eq.trans hres ?_
  refine Eq.trans (congrArg (toMeromorphicSectionSheaf B S hS X hX
      (picardTensorModule B S hS hX L N) (Y i))
    (meromorphicSectionTensorMul_tmul B S hS hX L N (Y i)
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.map (κ i).op).hom a)
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.map (κ i).op).hom b)
      (e (Y i) (κ i)) (f (Y i) (κ i)))) ?_
  refine Eq.trans ?_ (toMeromorphicSectionSheaf_map B S hS X hX
    (picardTensorModule B S hS hX L N) V (Y i) (κ i) _).symm
  refine congrArg (toMeromorphicSectionSheaf B S hS X hX
    (picardTensorModule B S hS hX L N) (Y i)) ?_
  refine Eq.trans ?_ (meromorphicSectionModule_map_tmul B S hS X hX
    (picardTensorModule B S hS hX L N) V (Y i) (κ i) (a * b)
    (tensorChartSection B S hS hX L N V (e V (𝟙 V)) (f V (𝟙 V)))).symm
  refine Eq.trans (congrArg (fun z : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj
      (op (Y i)) ↦
    (z ⊗ₜ[chartRing B S hS X hX (Y i)]
        tensorChartSection B S hS hX L N (Y i) (e (Y i) (κ i)) (f (Y i) (κ i)) :
      (meromorphicSectionModule B S hS X hX
        (picardTensorModule B S hS hX L N)).obj (op (Y i))))
    (map_mul ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map (κ i).op).hom a b).symm) ?_
  refine congrArg (fun z : (picardTensorModule B S hS hX L N).val.obj (op (Y i)) ↦
    ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map (κ i).op).hom (a * b))
        ⊗ₜ[chartRing B S hS X hX (Y i)] z :
      (meromorphicSectionModule B S hS X hX
        (picardTensorModule B S hS hX L N)).obj (op (Y i)))) ?_
  exact (map_tensorChartSection_generators B S hS hX L N V e f hecompat hfcompat (Y i)
    (κ i)).symm

/-- **The coefficient of a regular meromorphic section is a nonzerodivisor.**  If a meromorphic
section `s` of a sheaf of `𝒪_X`-modules is over a chart `V` the image of `α ⊗ m`, then `α` can be
cancelled from a product of meromorphic functions on `V`: multiplying `α` by `x` multiplies `s`
by `x`, and multiplication by `s` is injective.

Nothing is asked of `m`. -/
theorem mul_right_cancel_of_isRegularMeromorphicSection (M : Modules.{u, u} B S hS X hX)
    (σ : MeromorphicSection.{u, u} B S hS X hX M)
    (hσ : IsRegularMeromorphicSection.{u, u} B S hS X hX M σ) (V : SmallEtale B S hS X)
    (m : M.val.obj (op V)) (α : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj (op V))
    (hpres : σ.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V
      (α ⊗ₜ[chartRing B S hS X hX V] m :
        (meromorphicSectionModule B S hS X hX M).obj (op V)))
    {x y : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj (op V)}
    (h : x * α = y * α) : x = y := by
  refine hσ V ?_
  have hmul : ∀ z : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op V),
      z • σ.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V
        ((z * α) ⊗ₜ[chartRing B S hS X hX V] m :
          (meromorphicSectionModule B S hS X hX M).obj (op V)) := by
    intro z
    refine (smul_eval_eq_toMeromorphicSectionSheaf_smul B S hS hX M σ V _ hpres z).trans ?_
    exact congrArg (toMeromorphicSectionSheaf B S hS X hX M V)
      (meromorphicSectionModule_smul_tmul B S hS X hX M V _ z α m rfl)
  exact ((hmul x).trans (congrArg (fun w ↦ toMeromorphicSectionSheaf B S hS X hX M V
    (w ⊗ₜ[chartRing B S hS X hX V] m :
      (meromorphicSectionModule B S hS X hX M).obj (op V))) h)).trans (hmul y).symm

/-! ### Regularity of the product -/

include hwa hfin in
/-- **Multiplication by the product is injective over a chart carrying free generators of both
modules.**  Over such a chart the product is `(a b) · (e ⊗ f)`
(`AlgebraicGeometry.Space.eval_meromorphicSectionTensor_eq_tmul`) and `e ⊗ f` is a free generator
of `ℒ ⊗_{𝒪_X} 𝒩` over every chart over it
(`AlgebraicGeometry.Space.bijective_smul_tensorChartSection`).

Two multiples of the product agree in `𝒦_X(ℒ ⊗ 𝒩)` only over a covering sieve of the chart
(`AlgebraicGeometry.Space.equalizerSieve_toMeromorphicSectionSheaf_mem`); over a member of it the
restricted generator is still free, so the coefficients `r · a · b` agree there, and `b` and then
`a` are cancelled by regularity of `t` and of `s`
(`AlgebraicGeometry.Space.mul_right_cancel_of_isRegularMeromorphicSection`).  Separatedness of
`𝒦_X` gives the equality over the chart. -/
theorem injective_smul_eval_meromorphicSectionTensor_of_generators
    (hLqc : L.IsQuasicoherentOnSite) (hNqc : N.IsQuasicoherentOnSite)
    (hsreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (htreg : IsRegularMeromorphicSection.{u, u} B S hS X hX N t)
    (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W))
    (f : (W : SmallEtale B S hS X) → (W ⟶ V) → N.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (hfcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (N.val.map g.op).hom (f W k) = f W' (g ≫ k))
    (hfbij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • f W k) :
    Function.Injective fun r :
        (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS X hX).O).obj.obj (op V) ↦
      r • (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc).eval (op V) := by
  obtain ⟨a, ha⟩ := (bijective_toMeromorphicSectionSheaf_tmul B S hS X hX L V e hecompat
    hebij).2 (s.eval (op V))
  obtain ⟨b, hb⟩ := (bijective_toMeromorphicSectionSheaf_tmul B S hS X hX N V f hfcompat
    hfbij).2 (t.eval (op V))
  have hP := eval_meromorphicSectionTensor_eq_tmul B S hS hX hwa hfin L N s t hLqc hNqc V
    e f hecompat hfcompat a b ha.symm hb.symm
  set tc : (meromorphicSectionModule B S hS X hX
      (picardTensorModule B S hS hX L N)).obj (op V) :=
    ((a * b) ⊗ₜ[chartRing B S hS X hX V]
      tensorChartSection B S hS hX L N V (e V (𝟙 V)) (f V (𝟙 V))) with htc
  -- a multiple of the product over `V` is the corresponding multiple of the coefficient
  have hmul : ∀ z : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op V),
      z • (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc).eval (op V) =
        toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V (z • tc) :=
    fun z ↦ smul_eval_eq_toMeromorphicSectionSheaf_smul B S hS hX _ _ V _ hP z
  intro r r' hrr'
  have heq : toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V
        (r • tc) =
      toMeromorphicSectionSheaf B S hS X hX (picardTensorModule B S hS hX L N) V (r' • tc) :=
    ((hmul r).symm.trans hrr').trans (hmul r')
  have hE := equalizerSieve_toMeromorphicSectionSheaf_mem B S hS X hX
    (picardTensorModule B S hS hX L N) V (r • tc) (r' • tc) heq
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).property.isSeparated V _ hE r r' ?_
  intro Z g hg
  -- the generator restricts
  have htcs : ((picardTensorModule B S hS hX L N).val.map g.op).hom
        (tensorChartSection B S hS hX L N V (e V (𝟙 V)) (f V (𝟙 V))) =
      tensorChartSection B S hS hX L N Z (e Z g) (f Z g) :=
    map_tensorChartSection_generators B S hS hX L N V e f hecompat hfcompat Z g
  -- a multiple of the pure tensor restricts to the corresponding multiple over `Z`
  have hrestrict : ∀ z : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op V),
      ((meromorphicSectionModule B S hS X hX
            (picardTensorModule B S hS hX L N)).map g.op).hom (z • tc) =
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom (z * (a * b)))
            ⊗ₜ[chartRing B S hS X hX Z] tensorChartSection B S hS hX L N Z (e Z g) (f Z g) :
          (meromorphicSectionModule B S hS X hX
            (picardTensorModule B S hS hX L N)).obj (op Z)) := by
    intro z
    refine Eq.trans (congrArg ((meromorphicSectionModule B S hS X hX
        (picardTensorModule B S hS hX L N)).map g.op).hom
      (meromorphicSectionModule_smul_tmul B S hS X hX (picardTensorModule B S hS hX L N) V tc z
        (a * b) (tensorChartSection B S hS hX L N V (e V (𝟙 V)) (f V (𝟙 V))) htc)) ?_
    refine Eq.trans (meromorphicSectionModule_map_tmul B S hS X hX
      (picardTensorModule B S hS hX L N) V Z g (z * (a * b)) _) ?_
    exact congrArg (fun w : (picardTensorModule B S hS hX L N).val.obj (op Z) ↦
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom (z * (a * b)))
          ⊗ₜ[chartRing B S hS X hX Z] w :
        (meromorphicSectionModule B S hS X hX
          (picardTensorModule B S hS hX L N)).obj (op Z))) htcs
  have hgm : ((meromorphicSectionModule B S hS X hX
          (picardTensorModule B S hS hX L N)).map g.op).hom (r • tc) =
      ((meromorphicSectionModule B S hS X hX
          (picardTensorModule B S hS hX L N)).map g.op).hom (r' • tc) :=
    congrArg ULift.down hg
  -- the coefficients agree over `Z`
  have hcoeff : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom
        (r * (a * b)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom (r' * (a * b)) :=
    (bijective_meromorphicSectionModule_tmul B S hS X hX (picardTensorModule B S hS hX L N) Z
      (tensorChartSection B S hS hX L N Z (e Z g) (f Z g))
      (bijective_smul_tensorChartSection B S hS hX L N V e f hecompat hebij hfcompat hfbij
        Z g)).1
      (((hrestrict r).symm.trans hgm).trans (hrestrict r'))
  -- cancel the two coefficients, by regularity of `t` and then of `s`
  have hb' := mul_right_cancel_of_isRegularMeromorphicSection B S hS hX N t htreg Z (f Z g)
    (((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom b)
    (eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X hX N t V f hfcompat b hb.symm Z g)
    (x := ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom r *
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom a)
    (y := ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom r' *
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom a)
    (by simpa only [map_mul, mul_assoc] using hcoeff)
  exact mul_right_cancel_of_isRegularMeromorphicSection B S hS hX L s hsreg Z (e Z g)
    (((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map g.op).hom a)
    (eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X hX L s V e hecompat a ha.symm Z g)
    hb'

include hwa hfin in
/-- **The product of two regular meromorphic sections of invertible modules is regular**, which
is Stacks 0ENB for the product of Stacks 02SL.

Multiplication by the product is injective over every chart carrying free generators of both
modules
(`AlgebraicGeometry.Space.injective_smul_eval_meromorphicSectionTensor_of_generators`), and those
charts cover every chart: `ℒ` is free over a covering family of it and so is `𝒩`
(`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`), and the intersection of
the two covering sieves is still a covering sieve.  Injectivity over the members of a covering
sieve gives injectivity over the chart
(`AlgebraicGeometry.Space.injective_smul_eval_of_sieve`). -/
theorem isRegularMeromorphicSection_meromorphicSectionTensor
    (hLqc : L.IsQuasicoherentOnSite) (hNqc : N.IsQuasicoherentOnSite)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (hsreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (htreg : IsRegularMeromorphicSection.{u, u} B S hS X hX N t) :
    IsRegularMeromorphicSection.{u, u} B S hS X hX (picardTensorModule B S hS hX L N)
      (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) := by
  intro V
  obtain ⟨I₁, V₁, a₁, hcov₁, hgen₁⟩ := exists_generator_cover_smul_of_isInvertible B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) V
  obtain ⟨I₂, V₂, a₂, hcov₂, hgen₂⟩ := exists_generator_cover_smul_of_isInvertible B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) N
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hNinv) V
  refine injective_smul_eval_of_sieve B S hS X hX (picardTensorModule B S hS hX L N)
    (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) V
    (Sieve.ofArrows V₁ a₁ ⊓ Sieve.ofArrows V₂ a₂)
    ((SmallEtale.topology B S hS X).intersection_covering hcov₁ hcov₂) ?_
  intro Z g hg
  obtain ⟨i₁, h₁, hfac₁⟩ := (Sieve.mem_ofArrows_iff V₁ a₁ g).1 hg.1
  obtain ⟨i₂, h₂, hfac₂⟩ := (Sieve.mem_ofArrows_iff V₂ a₂ g).1 hg.2
  obtain ⟨e, hecompat, hebij⟩ := hgen₁ i₁
  obtain ⟨f, hfcompat, hfbij⟩ := hgen₂ i₂
  exact injective_smul_eval_meromorphicSectionTensor_of_generators B S hS hX hwa hfin L N s t
    hLqc hNqc hsreg htreg Z (fun W k ↦ e W (k ≫ h₁)) (fun W k ↦ f W (k ≫ h₂))
    (fun W W' k j ↦ (hecompat W W' (k ≫ h₁) j).trans
      (congrArg (e W') (Category.assoc j k h₁).symm))
    (fun W k ↦ hebij W (k ≫ h₁))
    (fun W W' k j ↦ (hfcompat W W' (k ≫ h₂) j).trans
      (congrArg (f W') (Category.assoc j k h₂).symm))
    (fun W k ↦ hfbij W (k ≫ h₂))

end AlgebraicGeometry.Space

end
