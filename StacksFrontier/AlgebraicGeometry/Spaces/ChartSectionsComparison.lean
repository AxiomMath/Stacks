module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections

/-!
# Functoriality of the base change comparison on étale charts

`AlgebraicGeometry.Space.sectionsBaseChange` attaches to a morphism `f : V ⟶ U` of étale charts
of an algebraic space `F` and an `𝒪_F`-module `G` the comparison

`𝒪_F(V) ⊗_{𝒪_F(U)} G(U) ⟶ G(V)`,

and `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` says that this comparison is bijective
whenever both charts are affine.  That file constructs the comparison for a *fixed* module and a
*fixed* chart morphism.  This file records how it varies: it is natural in the module, hence
invariant under isomorphism of modules, and it is multiplicative in the chart morphism, so that
bijectivity over `f : V ⟶ U` and over `g : W ⟶ V` gives bijectivity over `g ≫ f`.

Both are needed before the comparison can be derived from quasi-coherence.  Naturality is what
lets a quasi-coherent module be replaced by an isomorphic one with a global presentation, and
multiplicativity is what lets the comparison be checked on a family of chart morphisms closed
under composition rather than on every chart morphism separately.

## Main results

* `AlgebraicGeometry.Space.chartRestrictLinear_smul` and
  `AlgebraicGeometry.Space.chartRestrictLinear_comp`: restriction of sections along a chart
  morphism is semilinear over restriction of functions, and is functorial in the chart morphism.
* `AlgebraicGeometry.Space.app_sectionsBaseChange_of_commSq` and
  `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_bijective_app`: the comparison is
  natural in, and its bijectivity transfers along, a commuting square of maps on the sections
  over the two charts — not necessarily the components of a morphism of `𝒪_F`-modules.
* `AlgebraicGeometry.Space.app_sectionsBaseChange`: the comparison is natural in the module.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_bijective` and
  `AlgebraicGeometry.Space.IsCartesianOnAffineCharts.of_iso`: bijectivity of the comparison, and
  being cartesian on affine charts, transfer along an isomorphism of `𝒪_F`-modules.
* `AlgebraicGeometry.Space.chartAlgebra_isScalarTower`: the three algebra structures carried by
  a composable pair of chart morphisms form a scalar tower.
* `AlgebraicGeometry.Space.sectionsBaseChange_comp`: the comparison over `g ≫ f` is the
  comparison over `g` applied to the base change of the comparison over `f`, transported along
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_comp`: bijectivity of the comparison is
  stable under composition of chart morphisms.
* `AlgebraicGeometry.Space.bijective_lTensor_of_bijective`: a bijective linear map stays
  bijective after tensoring on the left.

## Implementation notes

The three `AlgebraicGeometry.Space.chartAlgebra` structures attached to `f : V ⟶ U`,
`g : W ⟶ V` and `g ≫ f` are `@[instance_reducible]` definitions rather than instances, so every
statement below introduces the ones it needs by `letI`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections`.  The scalar tower relating them is the
restriction law `AlgebraicGeometry.Space.chartRestrict_comp` read through
`IsScalarTower.of_algebraMap_eq`, and it is what makes
`TensorProduct.AlgebraTensorModule.cancelBaseChange` available for the composition statement.

`AlgebraicGeometry.Space.chartRestrictLinear_smul` and
`AlgebraicGeometry.Space.chartRestrictLinear_comp` are not conveniences.  `CategoryTheory.`
`PresheafOfModules.map_smul` and `CategoryTheory.PresheafOfModules.map_comp_apply` state the same
two facts with the codomain spelled as `(ModuleCat.restrictScalars _).obj (G.val.obj _)`, and
instance search does not see the module structure of the sections through that functor
application, so neither statement can be used where the ambient scalars are those of the smaller
chart.  Restating them with the codomain `(G.val.obj _ : Type m)` of
`AlgebraicGeometry.Space.chartRestrictLinear` fixes the scalars, and the restatements are proved
from the Mathlib lemmas by `exact`, that is, by definitional unfolding alone.

For the same reason the last step of `AlgebraicGeometry.Space.sectionsBaseChange_comp` goes
through `smul_smul_comm_aux`, a scalar identity stated for an abstract module: the rewrite
`rw [PresheafOfModules.map_smul]` fails its motive check on the goal there, the two sides being
definitionally but not syntactically equal types.

No `@[stacks]` attribute is claimed.  Deriving the comparison from quasi-coherence is
Stacks 03DX(2); what that needs is Stacks 03DT (the fpqc sheaf condition for the cartesian
presheaf of a module) together with flatness of the chart restrictions and a finite affine
refinement of an étale covering of an affine chart, *not* Stacks 03DW — see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections`.  Nothing here proves either, and nothing
here is a part of either statement.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0CZ5](https://stacks.math.columbia.edu/tag/0CZ5)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### Tensoring a bijection -/

/-- A bijective linear map remains bijective after tensoring with a fixed module on the left.

The inverse is the left tensor of the inverse linear map: `LinearMap.lTensor M h` underlies the
linear equivalence `LinearEquiv.lTensor M (LinearEquiv.ofBijective h hh)`. -/
theorem bijective_lTensor_of_bijective {R : Type*} [CommRing R] (M : Type*) {N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (h : N →ₗ[R] P) (hh : Function.Bijective h) :
    Function.Bijective (LinearMap.lTensor M h) :=
  (LinearEquiv.lTensor M (LinearEquiv.ofBijective h hh)).bijective

/-- Reassociating a double scalar multiplication over a commutative ring.

This is `smul_smul` followed by `mul_comm`, stated separately because the goal it discharges in
`AlgebraicGeometry.Space.sectionsBaseChange_comp` cannot be rewritten in place. -/
private theorem smul_smul_comm_aux {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b c : R) (y : M) : b • (c • y) = (c * b) • y := by
  rw [smul_smul, mul_comm]

/-- If `x ∘ p = q ∘ r` with `p`, `q` and `r` bijective, then `x` is bijective. -/
private theorem bijective_of_comp_eq_comp {α β γ δ : Type*} {x : β → δ} {p : α → β} {q : γ → δ}
    {r : α → γ} (h : x ∘ p = q ∘ r) (hp : Function.Bijective p)
    (hq : Function.Bijective q) (hr : Function.Bijective r) : Function.Bijective x :=
  (Function.Bijective.of_comp_iff x hp).1 (h ▸ hq.comp hr)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### Restriction of sections along a chart morphism -/

/-- Restriction of sections along a chart morphism `g : W ⟶ V` is semilinear over restriction of
regular functions along `g`.

This is `CategoryTheory.PresheafOfModules.map_smul` with the codomain spelled as the sections
over `W` rather than as their restriction of scalars along `g`, which is what makes the ambient
`𝒪_F(W)`-module structure visible to instance search. -/
theorem chartRestrictLinear_smul (G : Modules.{u, m} B S hS F hF)
    {V W : SmallEtale B S hS F} (g : W ⟶ V) (a : chartRing B S hS F hF V)
    (y : G.val.obj (op V)) :
    chartRestrictLinear G g (a • y) =
      chartRestrict (hF := hF) g a • chartRestrictLinear G g y :=
  G.val.map_smul g.op a y

/-- Restriction of sections is functorial in the chart morphism: restricting along `g ≫ f` is
restricting along `f` and then along `g`. -/
theorem chartRestrictLinear_comp (G : Modules.{u, m} B S hS F hF)
    {U V W : SmallEtale B S hS F} (f : V ⟶ U) (g : W ⟶ V) (x : G.val.obj (op U)) :
    chartRestrictLinear G (g ≫ f) x =
      chartRestrictLinear G g (chartRestrictLinear G f x) := by
  rw [chartRestrictLinear_apply, chartRestrictLinear_apply, chartRestrictLinear_apply,
    CategoryTheory.op_comp]
  exact G.val.map_comp_apply f.op g.op x

/-! ### Naturality of the comparison in a commuting square of section maps -/

/-- **The base change comparison of Stacks 03DX(2) is natural in a commuting square of section
maps.**  Let `φU` and `φV` be maps of the sections of two `𝒪_F`-modules over the charts `U` and
`V` of a chart morphism `f : V ⟶ U` which commute with restriction along `f`.  Then they commute
with the base change comparison over `f`, after tensoring `φU` with the functions on `V`.

The two maps need not be the components of a morphism of `𝒪_F`-modules, which is what makes this
usable for a morphism defined only on the restrictions to a slice; the proof uses nothing but
the square and `chartRing B S hS F hF V`-linearity of `φV`. -/
theorem app_sectionsBaseChange_of_commSq {G G' : Modules.{u, m} B S hS F hF}
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (φU : G.val.obj (op U) ⟶ G'.val.obj (op U))
    (φV : G.val.obj (op V) ⟶ G'.val.obj (op V))
    (hsq : ∀ x : G.val.obj (op U),
      φV.hom (chartRestrictLinear G f x) = chartRestrictLinear G' f (φU.hom x)) :
    letI := chartAlgebra (hF := hF) f
    ∀ z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
        (G.val.obj (op U)),
      φV.hom (sectionsBaseChange G f z) =
        sectionsBaseChange G' f
          (LinearMap.lTensor (chartRing B S hS F hF V) φU.hom z) := by
  let _ := chartAlgebra (hF := hF) f
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [chartBaseChange_tmul, LinearMap.lTensor_tmul, chartBaseChange_tmul, map_smul, hsq]
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

/-- **Bijectivity of the base change comparison transfers along a commuting square of bijective
section maps.**  The hypotheses are those of
`AlgebraicGeometry.Space.app_sectionsBaseChange_of_commSq` together with bijectivity of the two
maps; no morphism of `𝒪_F`-modules is involved.

`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_bijective` is the special case where
the two maps are the components of an isomorphism of `𝒪_F`-modules. -/
theorem bijective_sectionsBaseChange_of_bijective_app {G G' : Modules.{u, m} B S hS F hF}
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (φU : G.val.obj (op U) ⟶ G'.val.obj (op U))
    (φV : G.val.obj (op V) ⟶ G'.val.obj (op V))
    (hsq : ∀ x : G.val.obj (op U),
      φV.hom (chartRestrictLinear G f x) = chartRestrictLinear G' f (φU.hom x))
    (hU : Function.Bijective φU) (hV : Function.Bijective φV)
    (hG : Function.Bijective (sectionsBaseChange G f)) :
    Function.Bijective (sectionsBaseChange G' f) := by
  let _ := chartAlgebra (hF := hF) f
  exact bijective_of_comp_eq_comp
    (funext fun z => (app_sectionsBaseChange_of_commSq f φU φV hsq z).symm)
    (bijective_lTensor_of_bijective _ _ hU) hV hG

/-! ### Naturality of the comparison in the module -/

/-- A morphism `φ : G ⟶ G'` of `𝒪_F`-modules, evaluated over `U` and tensored with the functions
on `V`, commutes with the base change comparison over a chart morphism `f : V ⟶ U`.

This is the naturality of `AlgebraicGeometry.Space.sectionsBaseChange` in the module; it reduces,
on a generator `b ⊗ x`, to the naturality of `φ` over `f`. -/
theorem app_sectionsBaseChange {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G')
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    letI := chartAlgebra (hF := hF) f
    ∀ z : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
        (G.val.obj (op U)),
      φ.val.app (op V) (sectionsBaseChange G f z) =
        sectionsBaseChange G' f
          (LinearMap.lTensor (chartRing B S hS F hF V) (φ.val.app (op U)).hom z) :=
  app_sectionsBaseChange_of_commSq f (φ.val.app (op U)) (φ.val.app (op V))
    (PresheafOfModules.naturality_apply φ.val f.op)

/-! ### Transfer along an isomorphism of modules -/

/-- Two mutually inverse morphisms of `𝒪_F`-modules have mutually inverse sections maps over
every étale chart. -/
theorem moduleHom_app_comp_eq_id {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G') (ψ : G' ⟶ G)
    (h : φ ≫ ψ = 𝟙 G) (U : SmallEtale B S hS F) :
    (ψ.val.app (op U)).hom.comp (φ.val.app (op U)).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, h]
  rfl

/-- An isomorphism of `𝒪_F`-modules is bijective on the sections over every étale chart. -/
theorem bijective_moduleHom_app {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G') (ψ : G' ⟶ G)
    (h₁ : φ ≫ ψ = 𝟙 G) (h₂ : ψ ≫ φ = 𝟙 G') (U : SmallEtale B S hS F) :
    Function.Bijective (φ.val.app (op U)) :=
  Function.bijective_iff_has_inverse.2
    ⟨ψ.val.app (op U),
      fun x => congrArg (fun l => l x) (moduleHom_app_comp_eq_id φ ψ h₁ U),
      fun x => congrArg (fun l => l x) (moduleHom_app_comp_eq_id ψ φ h₂ U)⟩

/-- An isomorphism of `𝒪_F`-modules stays bijective after tensoring the sections over the larger
chart with the functions on the smaller one. -/
theorem bijective_lTensor_moduleHom_app {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G')
    (ψ : G' ⟶ G) (h₁ : φ ≫ ψ = 𝟙 G) (h₂ : ψ ≫ φ = 𝟙 G')
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    letI := chartAlgebra (hF := hF) f
    Function.Bijective (LinearMap.lTensor (chartRing B S hS F hF V)
      (φ.val.app (op U)).hom) :=
  let := chartAlgebra (hF := hF) f
  bijective_lTensor_of_bijective _ _ (bijective_moduleHom_app φ ψ h₁ h₂ U)

/-- Bijectivity of the base change comparison over a chart morphism transfers along an
isomorphism of `𝒪_F`-modules. -/
theorem bijective_sectionsBaseChange_of_bijective
    {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G') (ψ : G' ⟶ G)
    (h₁ : φ ≫ ψ = 𝟙 G) (h₂ : ψ ≫ φ = 𝟙 G') {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hG : Function.Bijective (sectionsBaseChange G f)) :
    Function.Bijective (sectionsBaseChange G' f) :=
  bijective_sectionsBaseChange_of_bijective_app f (φ.val.app (op U)) (φ.val.app (op V))
    (PresheafOfModules.naturality_apply φ.val f.op)
    (bijective_moduleHom_app φ ψ h₁ h₂ U) (bijective_moduleHom_app φ ψ h₁ h₂ V) hG

/-- Being cartesian on affine charts is invariant under isomorphism of `𝒪_F`-modules. -/
theorem IsCartesianOnAffineCharts.of_iso {G G' : Modules.{u, m} B S hS F hF} (e : G ≅ G')
    (hG : IsCartesianOnAffineCharts G) : IsCartesianOnAffineCharts G' :=
  fun U V hU hV f =>
    bijective_sectionsBaseChange_of_bijective e.hom e.inv e.hom_inv_id e.inv_hom_id f
      (hG U V hU hV f)

/-! ### Composition of chart morphisms -/

/-- For a composable pair of chart morphisms `g : W ⟶ V` and `f : V ⟶ U`, the three algebra
structures on the rings of functions form a scalar tower.

This is the restriction law `AlgebraicGeometry.Space.chartRestrict_comp`: the structure map of
`𝒪_F(W)` over `𝒪_F(U)` is restriction along `g ≫ f`, which is restriction along `f` followed by
restriction along `g`. -/
theorem chartAlgebra_isScalarTower {U V W : SmallEtale B S hS F} (f : V ⟶ U) (g : W ⟶ V) :
    letI := chartAlgebra (hF := hF) f
    letI := chartAlgebra (hF := hF) g
    letI := chartAlgebra (hF := hF) (g ≫ f)
    IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (chartRing B S hS F hF W) := by
  let _ := chartAlgebra (hF := hF) f
  let _ := chartAlgebra (hF := hF) g
  let _ := chartAlgebra (hF := hF) (g ≫ f)
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  show chartRestrict (hF := hF) (g ≫ f) x = chartRestrict (hF := hF) g (chartRestrict f x)
  rw [chartRestrict_comp]
  rfl

/-- **The base change comparison is multiplicative in the chart morphism.**  For `f : V ⟶ U` and
`g : W ⟶ V`, the comparison over `g` applied to the base change along `g` of the comparison over
`f` agrees with the comparison over `g ≫ f`, read through the cancellation isomorphism

`𝒪_F(W) ⊗_{𝒪_F(V)} (𝒪_F(V) ⊗_{𝒪_F(U)} G(U)) ≅ 𝒪_F(W) ⊗_{𝒪_F(U)} G(U)`.

On a generator `b ⊗ (a ⊗ x)` both sides are `(a • b) · (x restricted along g ≫ f)`, by
semilinearity and functoriality of restriction. -/
theorem sectionsBaseChange_comp (G : Modules.{u, m} B S hS F hF)
    {U V W : SmallEtale B S hS F} (f : V ⟶ U) (g : W ⟶ V) :
    letI := chartAlgebra (hF := hF) f
    letI := chartAlgebra (hF := hF) g
    letI := chartAlgebra (hF := hF) (g ≫ f)
    haveI := chartAlgebra_isScalarTower (hF := hF) f g
    ∀ z : TensorProduct (chartRing B S hS F hF V) (chartRing B S hS F hF W)
        (TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
          (G.val.obj (op U))),
      sectionsBaseChange G g (LinearMap.lTensor (chartRing B S hS F hF W)
          (sectionsBaseChange G f) z) =
        sectionsBaseChange G (g ≫ f)
          (TensorProduct.AlgebraTensorModule.cancelBaseChange (chartRing B S hS F hF U)
            (chartRing B S hS F hF V) (chartRing B S hS F hF W) (chartRing B S hS F hF W)
            (G.val.obj (op U)) z) := by
  let _ := chartAlgebra (hF := hF) f
  let _ := chartAlgebra (hF := hF) g
  let _ := chartAlgebra (hF := hF) (g ≫ f)
  have _ := chartAlgebra_isScalarTower (hF := hF) f g
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b w =>
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero, map_zero]
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, chartBaseChange_tmul, chartBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, chartBaseChange_tmul,
        chartRestrictLinear_smul, chartRestrictLinear_comp G f g x, smul_smul_comm_aux]
      rfl
    | add w w' hw hw' =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hw, hw']
  | add z z' hz hz' => rw [map_add, map_add, map_add, map_add, hz, hz']

/-- Bijectivity of the base change comparison is stable under composition of chart morphisms: if
the sections over `V` are the base change of the sections over `U`, and the sections over `W` are
the base change of the sections over `V`, then the sections over `W` are the base change of the
sections over `U`.

No flatness is needed: the middle map is a left tensor of a bijection, by
`AlgebraicGeometry.Space.bijective_lTensor_of_bijective`, and the outer one is the cancellation
isomorphism. -/
theorem bijective_sectionsBaseChange_comp (G : Modules.{u, m} B S hS F hF)
    {U V W : SmallEtale B S hS F} (f : V ⟶ U) (g : W ⟶ V)
    (hf : Function.Bijective (sectionsBaseChange G f))
    (hg : Function.Bijective (sectionsBaseChange G g)) :
    Function.Bijective (sectionsBaseChange G (g ≫ f)) := by
  let _ := chartAlgebra (hF := hF) f
  let _ := chartAlgebra (hF := hF) g
  let _ := chartAlgebra (hF := hF) (g ≫ f)
  have _ := chartAlgebra_isScalarTower (hF := hF) f g
  exact bijective_of_comp_eq_comp (funext fun z => (sectionsBaseChange_comp G f g z).symm)
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (chartRing B S hS F hF U)
      (chartRing B S hS F hF V) (chartRing B S hS F hF W) (chartRing B S hS F hF W)
      (G.val.obj (op U))).bijective hg (bijective_lTensor_of_bijective _ _ hf)

end AlgebraicGeometry.Space

end
