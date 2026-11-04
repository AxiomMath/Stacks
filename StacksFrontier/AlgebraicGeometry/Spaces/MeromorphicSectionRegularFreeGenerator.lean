module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularOneChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart

/-!
# A meromorphic section with a unit coefficient on a free generator is regular over a chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `L` be a
sheaf of `𝒪_F`-modules. If a meromorphic section of `L` is, over an étale scheme chart `V`, the
image of `c ⊗ m` with `c` a unit of `𝒦_F(V)` and `m` a free generator of `L` over every chart over
`V`, then multiplication by it is injective on the meromorphic functions over `V`.

## Main results

* `AlgebraicGeometry.Space.injective_smul_eval_of_sieve`: multiplication by a meromorphic section
  is injective over a chart as soon as it is injective over the members of a covering *sieve* of
  that chart.
* `AlgebraicGeometry.Space.bijective_meromorphicSectionModule_tmul`: a free generator stays free
  after the base change to the meromorphic functions.
* `AlgebraicGeometry.Space.toMeromorphicSectionSheaf_map` and
  `AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionSheaf_tmul_restrict`: the sheafification
  map of Stacks 0EN5 is natural, so a presentation of a meromorphic section restricts.
* `AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit`: a meromorphic section presented
  over a chart as a unit multiple of a free generator multiplies injectively there.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Pure meromorphic sections over a chart -/

/-- Restricting a pure meromorphic section `a ⊗ m` to a chart `W` over `V` restricts the
coefficient and the module element separately. -/
theorem meromorphicSectionModule_map_tmul (M : Modules.{u, u} B S hS F hF)
    (V W : SmallEtale B S hS F) (g : W ⟶ V)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj (op V))
    (m : M.val.obj (op V)) :
    ((meromorphicSectionModule B S hS F hF M).map g.op).hom
        (a ⊗ₜ[chartRing B S hS F hF V] m :
          (meromorphicSectionModule B S hS F hF M).obj (op V)) =
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.map g.op).hom a) ⊗ₜ[
        chartRing B S hS F hF W] ((M.val.map g.op).hom m) :
          (meromorphicSectionModule B S hS F hF M).obj (op W)) :=
  cofMap_tmul
    (regularSectionsSubpresheaf B S hS F hF).toLocalizationSheaf.hom M.val g.op a m

/-- A meromorphic function multiplying a pure meromorphic section `c ⊗ m` multiplies its
coefficient: `r • (c ⊗ m) = (r * c) ⊗ m`. -/
theorem meromorphicSectionModule_smul_tmul (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (t : (meromorphicSectionModule B S hS F hF M).obj (op V))
    (r c : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj (op V))
    (m : M.val.obj (op V))
    (ht : t = (c ⊗ₜ[chartRing B S hS F hF V] m :
      (meromorphicSectionModule B S hS F hF M).obj (op V))) :
    r • t = ((r * c) ⊗ₜ[chartRing B S hS F hF V] m :
      (meromorphicSectionModule B S hS F hF M).obj (op V)) := by
  rw [ht]
  rfl

/-- A free generator stays free after the base change to the meromorphic functions: if
`r ↦ r • m` is a bijection of the regular functions over a chart onto the sections of `M` there,
then `a ↦ a ⊗ m` is a bijection of the meromorphic functions onto the meromorphic sections. -/
theorem bijective_meromorphicSectionModule_tmul (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (m : M.val.obj (op V))
    (h : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • m) :
    Function.Bijective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      (a ⊗ₜ[chartRing B S hS F hF V] m :
        (meromorphicSectionModule B S hS F hF M).obj (op V)) :=
  ⟨(Stacks.bijective_tmul_of_bijective_smul
      (K := (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) m h).1,
    (Stacks.bijective_tmul_of_bijective_smul
      (K := (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) m h).2⟩

/-- The sheafification map `𝒦_F(V) ⊗_{𝒪_F(V)} M(V) ⟶ 𝒦_F(M)(V)` of Stacks 0EN5 commutes with
restriction along `W ⟶ V`. -/
theorem toMeromorphicSectionSheaf_map (M : Modules.{u, u} B S hS F hF)
    (V W : SmallEtale B S hS F) (g : W ⟶ V)
    (t : (meromorphicSectionModule B S hS F hF M).obj (op V)) :
    ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map g.op).hom
        (toMeromorphicSectionSheaf B S hS F hF M V t) =
      toMeromorphicSectionSheaf B S hS F hF M W
        (((meromorphicSectionModule B S hS F hF M).map g.op).hom t) := by
  let := moduleHasWeakSheafify.{u, u} B S hS F
  let := moduleWEqualsLocallyBijective.{u, u} B S hS F
  let : Presheaf.IsLocallyInjective (meromorphicRingedSite B S hS F hF).J
      (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
        (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf) :=
    ((meromorphicRingedSite B S hS F hF).J.W_toSheafify _).isLocallyInjective
  let : Presheaf.IsLocallySurjective (meromorphicRingedSite B S hS F hF).J
      (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
        (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf) :=
    ((meromorphicRingedSite B S hS F hF).J.W_toSheafify _).isLocallySurjective
  exact (PresheafOfModules.naturality_apply (PresheafOfModules.toSheafify
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)
    (CategoryTheory.toSheafify (meromorphicRingedSite B S hS F hF).J
      (meromorphicSectionPresheaf.{u, u} B S hS F hF M).presheaf)) g.op (ULift.up t)).symm

/-- Restricting the generator `e V (𝟙 V)` along `k : W ⟶ V` gives `e W k`. -/
private theorem map_free_generator_eq (L : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    {W : SmallEtale B S hS F} (k : W ⟶ V) :
    (L.val.map k.op).hom (e V (𝟙 V)) = e W k :=
  (hcompat V W (𝟙 V) k).trans (congrArg (e W) (Category.comp_id k))

/-- If a meromorphic section `s` is over a chart `V` the image
of `c ⊗ e V (𝟙 V)`, with `e` a family of sections of `L` over the charts over `V` compatible with
restriction, then over a chart `W` over `V` it is the image of `c|_W ⊗ e W k`. -/
theorem eval_eq_toMeromorphicSectionSheaf_tmul_restrict
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (V : SmallEtale B S hS F)
    (e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj (op V))
    (hpres : s.eval (op V) = toMeromorphicSectionSheaf B S hS F hF L V
      (c ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS F hF L).obj (op V)))
    (W : SmallEtale B S hS F) (k : W ⟶ V) :
    s.eval (op W) = toMeromorphicSectionSheaf B S hS F hF L W
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.map k.op).hom c) ⊗ₜ[
          chartRing B S hS F hF W] e W k :
        (meromorphicSectionModule B S hS F hF L).obj (op W)) := by
  refine Eq.trans (PresheafOfModules.sections_property
    (M := (meromorphicSectionSheaf.{u, u} B S hS F hF L).val) s k.op).symm ?_
  refine Eq.trans (congrArg
    ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map k.op).hom hpres) ?_
  refine Eq.trans (toMeromorphicSectionSheaf_map B S hS F hF L V W k _) ?_
  refine congrArg (toMeromorphicSectionSheaf B S hS F hF L W) ?_
  refine Eq.trans
    (meromorphicSectionModule_map_tmul B S hS F hF L V W k c (e V (𝟙 V))) ?_
  exact congrArg (fun z : L.val.obj (op W) ↦
    ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.map k.op).hom c) ⊗ₜ[
        chartRing B S hS F hF W] z :
      (meromorphicSectionModule B S hS F hF L).obj (op W)))
    (map_free_generator_eq B S hS F hF L V e hcompat k)

/-! ### Injectivity of multiplication over one chart -/

/-- Multiplication by a meromorphic section is injective over a chart as soon as it is injective
over the members of a covering sieve of that chart. -/
theorem injective_smul_eval_of_sieve
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (V : SmallEtale B S hS F) (T : Sieve V) (hT : T ∈ SmallEtale.topology B S hS F V)
    (hinj : ∀ ⦃W : SmallEtale B S hS F⦄ (k : W ⟶ V), T k → Function.Injective fun r :
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op W) ↦
      r • s.eval (op W)) :
    Function.Injective fun r :
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      r • s.eval (op V) := by
  intro r r' hr
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
    (meromorphicRingedSite B S hS F hF).O).property.isSeparated V T hT r r' ?_
  intro Z g hg
  exact hinj g hg <| ((meromorphicSectionSheaf_map_smul_eval B S hS F hF L s g r).symm.trans
    (congrArg ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map g.op) hr)).trans
    (meromorphicSectionSheaf_map_smul_eval B S hS F hF L s g r')

/-! ### Regularity of a unit multiple of a free generator -/

/-- Let `s` be a meromorphic section of a sheaf of `𝒪_F`-modules `L`
which over an étale scheme chart `V` is the image of `c ⊗ m`, with `c` a unit of `𝒦_F(V)` and `m`
a section of `L` over `V` whose restriction to every chart over `V` freely generates `L` there.
Then multiplication by `s` is injective on the meromorphic functions over `V`. -/
theorem injective_smul_eval_of_tmul_isUnit
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (V : SmallEtale B S hS F)
    (e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (t : (meromorphicSectionModule B S hS F hF L).obj (op V))
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj (op V))
    (ht : t = (c ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
      (meromorphicSectionModule B S hS F hF L).obj (op V)))
    (hc : IsUnit c)
    (hs : s.eval (op V) = toMeromorphicSectionSheaf B S hS F hF L V t) :
    Function.Injective fun r :
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      r • s.eval (op V) := by
  intro r r' hrr'
  have hr : toMeromorphicSectionSheaf B S hS F hF L V (r • t) =
      toMeromorphicSectionSheaf B S hS F hF L V (r' • t) := by
    rw [toMeromorphicSectionSheaf_smul, toMeromorphicSectionSheaf_smul, ← hs]
    exact hrr'
  have hE := equalizerSieve_toMeromorphicSectionSheaf_mem B S hS F hF L V (r • t) (r' • t) hr
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
    (meromorphicRingedSite B S hS F hF).O).property.isSeparated V _ hE r r' ?_
  intro Z g hg
  have hgm : ((meromorphicSectionModule B S hS F hF L).map g.op).hom (r • t) =
      ((meromorphicSectionModule B S hS F hF L).map g.op).hom (r' • t) :=
    congrArg ULift.down hg
  have hstep : ∀ x : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V),
      ((meromorphicSectionModule B S hS F hF L).map g.op).hom (x • t) =
        (((((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.map g.op).hom x) *
              (((Stacks.SheafOfModules.Tensor.ringSheaf
                (meromorphicRingedSite B S hS F hF).O).obj.map g.op).hom c)) ⊗ₜ[
            chartRing B S hS F hF Z] e Z g :
          (meromorphicSectionModule B S hS F hF L).obj (op Z)) := by
    intro x
    rw [meromorphicSectionModule_smul_tmul B S hS F hF L V t x c (e V (𝟙 V)) ht,
      meromorphicSectionModule_map_tmul, map_free_generator_eq B S hS F hF L V e hcompat g,
      map_mul]
  have hcoeff := (bijective_meromorphicSectionModule_tmul B S hS F hF L Z
    (e Z g) (hbij Z g)).1 (((hstep r).symm.trans hgm).trans (hstep r'))
  exact (hc.map (((Stacks.SheafOfModules.Tensor.ringSheaf
    (meromorphicRingedSite B S hS F hF).O).obj.map g.op).hom)).mul_right_cancel
    hcoeff

end AlgebraicGeometry.Space

end
