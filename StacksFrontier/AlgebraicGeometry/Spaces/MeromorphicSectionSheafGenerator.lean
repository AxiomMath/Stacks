module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionNumerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart

/-!
# The sections of the sheaf of meromorphic sections at a free generator

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `L` be a
sheaf of `𝒪_F`-modules. The sheaf `𝒦_F(L)` of meromorphic sections of Stacks 0EN5 is the
sheafification of the presheaf `L ⊗_{𝒪_F} 𝒦_F`, so a section of it over an étale scheme chart is
only *locally* a meromorphic section. This file computes those sections over a chart `V` on which
`L` is free: **if `e` restricts to a free generator of `L` over every chart over `V`, then
`a ↦ a ⊗ e` is a bijection of the meromorphic functions `𝒦_F(V)` onto the sections of `𝒦_F(L)`
over `V`.**

This is the module analogue of Stacks 0EN6, part (2), which computes `𝒦_F(U)` over an affine
chart as the total ring of fractions of `𝒪_F(U)`. The generator replaces affineness: no
hypothesis on `F` and none on the chart is needed.

Injectivity is the argument of
`AlgebraicGeometry.Space.injective_smul_eval_of_tmul_isUnit`: two pure sections `a ⊗ e` and
`a' ⊗ e` with the same image agree in `L ⊗_{𝒪_F} 𝒦_F` over a covering sieve, over a member of
which the restricted generator is still free, so the restrictions of `a` and `a'` agree there,
and `𝒦_F` is separated. Surjectivity is the matching gluing argument: a section of the
sheafification is a meromorphic section over a covering sieve, over a member of which it is
`a ⊗ e` for a unique `a`; those coefficients are compatible, by injectivity, hence glue, `𝒦_F`
being a sheaf; and the product of the glued coefficient with `e` agrees with the given section
over the sieve, `𝒦_F(L)` being a sheaf too.

That bijection is then inverted: the meromorphic function it assigns to a meromorphic section is
the **ratio of that section against the generator** over the chart, and the whole of its theory
is that it is unique and that it changes by a unit of `𝒪_F(V)` when the generator does.

## Main results

* `AlgebraicGeometry.Space.injective_toMeromorphicSectionSheaf_tmul` and
  `AlgebraicGeometry.Space.surjective_toMeromorphicSectionSheaf_tmul`, assembled into
  `AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_tmul`.
* `AlgebraicGeometry.Space.exists_isUnit_smul_of_bijective_smul`: two free generators of `L` over
  a chart differ by a unit of the regular functions there.
* `AlgebraicGeometry.Space.chartRatio`, with
  `AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio` and
  `AlgebraicGeometry.Space.chartRatio_eq_of_eval_eq`: the ratio of a meromorphic section against
  the generator over the chart, its defining property and its uniqueness.
* `AlgebraicGeometry.Space.exists_isUnit_chartRatio_eq_mul_of_eval_eq`: a presentation of the
  section against *any* free generator over the chart computes the ratio up to a unit of
  `𝒪_F(V)`.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

variable (hF : IsAlgebraicSpace B S hS F) (L : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W))

/-- Restricting the pure meromorphic section `a ⊗ e` to a chart over `V` gives `a|_W ⊗ e|_W`,
with the generator read at that chart. -/
private theorem map_tmul_generator
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (W : SmallEtale B S hS F) (k : W ⟶ V)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V)) :
    ((meromorphicSectionModule B S hS F hF L).map k.op).hom
        (a ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS F hF L).obj (op V)) =
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.map k.op).hom a) ⊗ₜ[
          chartRing B S hS F hF W] e W k :
        (meromorphicSectionModule B S hS F hF L).obj (op W)) := by
  refine (meromorphicSectionModule_map_tmul B S hS F hF L V W k a (e V (𝟙 V))).trans ?_
  exact congrArg (fun z : L.val.obj (op W) ↦
    ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.map k.op).hom a) ⊗ₜ[
        chartRing B S hS F hF W] z :
      (meromorphicSectionModule B S hS F hF L).obj (op W)))
    ((hcompat V W (𝟙 V) k).trans (congrArg (e W) (Category.comp_id k)))

/-- **A free generator over a chart reads the sections of `𝒦_F(L)` there injectively.**  If the
restriction of `e` to every chart over `V` freely generates `L` there, then two meromorphic
functions over `V` with the same product against `e` in the sheaf `𝒦_F(L)` of Stacks 0EN5 are
equal.

The sheaf of meromorphic sections is a sheafification, so the two pure sections `a ⊗ e` and
`a' ⊗ e` agree in `𝒦_F ⊗_{𝒪_F} L` only over a covering sieve; over a member of it the
restricted generator is still free, so the restrictions of `a` and `a'` agree there, and `𝒦_F`
is separated. -/
theorem injective_toMeromorphicSectionSheaf_tmul
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k) :
    Function.Injective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      toMeromorphicSectionSheaf B S hS F hF L V
        (a ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS F hF L).obj (op V)) := by
  intro a a' h
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).property.isSeparated V _
    (equalizerSieve_toMeromorphicSectionSheaf_mem B S hS F hF L V _ _ h) a a' ?_
  intro Z g hg
  have hZ : ((meromorphicSectionModule B S hS F hF L).map g.op).hom
        (a ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS F hF L).obj (op V)) =
      ((meromorphicSectionModule B S hS F hF L).map g.op).hom
        (a' ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS F hF L).obj (op V)) :=
    congrArg ULift.down hg
  rw [map_tmul_generator B S hS F hF L V e hcompat Z g a,
    map_tmul_generator B S hS F hF L V e hcompat Z g a'] at hZ
  exact (bijective_meromorphicSectionModule_tmul B S hS F hF L Z (e Z g) (hfree Z g)).1 hZ

/-- The generator family `e` read at the arrows through `j : V' ⟶ V` is again compatible with
restriction. -/
private theorem compat_comp_right
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (V' : SmallEtale B S hS F) (j : V' ⟶ V) :
    ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V') (g : W' ⟶ W),
      (L.val.map g.op).hom (e W (k ≫ j)) = e W' ((g ≫ k) ≫ j) :=
  fun W W' k g ↦ (hcompat W W' (k ≫ j) g).trans
    (congrArg (e W') (Category.assoc g k j).symm)

/-- `AlgebraicGeometry.Space.injective_toMeromorphicSectionSheaf_tmul` at a chart over `V`, with
the generator read there. -/
private theorem injective_toMeromorphicSectionSheaf_tmul_hom
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (W : SmallEtale B S hS F) (h : W ⟶ V) :
    Function.Injective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op W) ↦
      toMeromorphicSectionSheaf B S hS F hF L W
        (a ⊗ₜ[chartRing B S hS F hF W] e W h :
          (meromorphicSectionModule B S hS F hF L).obj (op W)) := by
  have hid : e W (𝟙 W ≫ h) = e W h := congrArg (e W) (Category.id_comp h)
  have key := injective_toMeromorphicSectionSheaf_tmul B S hS F hF L W
    (fun W' k' ↦ e W' (k' ≫ h))
    (compat_comp_right B S hS F hF L V e hcompat W h)
    (fun W' k ↦ hfree W' (k ≫ h))
  rwa [hid] at key

/-- **A free generator over a chart reads every section of `𝒦_F(L)` there.**  If the restriction
of `e` to every chart over `V` freely generates `L` there, then every section of the sheaf
`𝒦_F(L)` of Stacks 0EN5 over `V` is the product of `e` with a meromorphic function over `V`.

A section of a sheafification is a meromorphic section only over a covering sieve
(`AlgebraicGeometry.Space.exists_eval_toMeromorphicSectionSheaf_sieve_mem`); over a member of
that sieve the restricted generator is free, so the meromorphic section there is `a ⊗ e` for a
unique meromorphic function `a`, and those functions are compatible because two of them with the
same product against `e` agree. They therefore glue, `𝒦_F` being a sheaf, and the product of
the glued function with `e` agrees with the given section over the sieve, `𝒦_F(L)` being a
sheaf too. -/
theorem surjective_toMeromorphicSectionSheaf_tmul
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k) :
    Function.Surjective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      toMeromorphicSectionSheaf B S hS F hF L V
        (a ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS F hF L).obj (op V)) := by
  classical
  intro t
  obtain ⟨T, hT, hpres⟩ :=
    exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS F hF L V t
  -- over a member of the sieve the section is `a ⊗ e`, for a unique `a`
  have hcoef : ∀ ⦃W : SmallEtale B S hS F⦄ (k : W ⟶ V), T k →
      ∃ a : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.obj (op W),
        toMeromorphicSectionSheaf B S hS F hF L W
            (a ⊗ₜ[chartRing B S hS F hF W] e W k :
              (meromorphicSectionModule B S hS F hF L).obj (op W)) =
          ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map k.op).hom t := by
    intro W k hk
    obtain ⟨y, hy⟩ := hpres k hk
    obtain ⟨a, ha⟩ := (bijective_meromorphicSectionModule_tmul B S hS F hF L W (e W k)
      (hfree W k)).2 y
    exact ⟨a, (congrArg (toMeromorphicSectionSheaf B S hS F hF L W) ha).trans hy⟩
  set KP := (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj ⋙
    CategoryTheory.forget RingCat.{u} with hKP
  have hKsheaf : Presheaf.IsSheaf (SmallEtale.topology B S hS F) KP :=
    GrothendieckTopology.HasSheafCompose.isSheaf _
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).property
  have hsh := (isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS F) KP).1 hKsheaf T hT
  set fam : Presieve.FamilyOfElements KP T.arrows := fun W k hk ↦ (hcoef k hk).choose with hfam
  have hfamspec : ∀ ⦃W : SmallEtale B S hS F⦄ (k : W ⟶ V) (hk : T.arrows k),
      toMeromorphicSectionSheaf B S hS F hF L W
          (fam k hk ⊗ₜ[chartRing B S hS F hF W] e W k :
            (meromorphicSectionModule B S hS F hF L).obj (op W)) =
        ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map k.op).hom t :=
    fun W k hk ↦ (hcoef k hk).choose_spec
  -- the restriction of the product of a coefficient with the generator is the section
  have hrestrict : ∀ ⦃W W' : SmallEtale B S hS F⦄ (k : W ⟶ V) (hk : T.arrows k) (g : W' ⟶ W),
      toMeromorphicSectionSheaf B S hS F hF L W'
          ((((Stacks.SheafOfModules.Tensor.ringSheaf
              (meromorphicRingedSite B S hS F hF).O).obj.map g.op).hom (fam k hk)) ⊗ₜ[
              chartRing B S hS F hF W'] e W' (g ≫ k) :
            (meromorphicSectionModule B S hS F hF L).obj (op W')) =
        ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map (g ≫ k).op).hom t := by
    intro W W' k hk g
    have h1 := map_tmul_generator B S hS F hF L W (fun Z j ↦ e Z (j ≫ k))
      (compat_comp_right B S hS F hF L V e hcompat W k) W' g (fam k hk)
    have h2 : e W (𝟙 W ≫ k) = e W k := congrArg (e W) (Category.id_comp k)
    rw [h2] at h1
    rw [← h1]
    refine Eq.trans (toMeromorphicSectionSheaf_map B S hS F hF L W W' g
      (fam k hk ⊗ₜ[chartRing B S hS F hF W] e W k :
        (meromorphicSectionModule B S hS F hF L).obj (op W))).symm ?_
    refine Eq.trans (congrArg ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map g.op).hom
      (hfamspec k hk)) ?_
    exact (PresheafOfModules.map_comp_apply
      (meromorphicSectionSheaf.{u, u} B S hS F hF L).val k.op g.op t).symm
  -- the same, at a factorization of a morphism of the sieve through the chart
  have key : ∀ ⦃W W' : SmallEtale B S hS F⦄ (k : W ⟶ V) (hk : T.arrows k) (g : W' ⟶ W)
      (j : W' ⟶ V), g ≫ k = j →
      toMeromorphicSectionSheaf B S hS F hF L W'
          ((((Stacks.SheafOfModules.Tensor.ringSheaf
              (meromorphicRingedSite B S hS F hF).O).obj.map g.op).hom (fam k hk)) ⊗ₜ[
              chartRing B S hS F hF W'] e W' j :
            (meromorphicSectionModule B S hS F hF L).obj (op W')) =
        ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map j.op).hom t := by
    intro W W' k hk g j hj
    subst hj
    exact hrestrict k hk g
  have hcomp : fam.Compatible := by
    intro W₁ W₂ W' g₁ g₂ k₁ k₂ h₁ h₂ hc
    refine injective_toMeromorphicSectionSheaf_tmul_hom B S hS F hF L V e hcompat hfree W'
      (g₁ ≫ k₁) ?_
    exact (key k₁ h₁ g₁ (g₁ ≫ k₁) rfl).trans (key k₂ h₂ g₂ (g₁ ≫ k₁) hc.symm).symm
  refine ⟨hsh.amalgamate fam hcomp, ?_⟩
  set LP := (meromorphicSectionSheaf.{u, u} B S hS F hF L).val.presheaf ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1} with hLP
  have hLsheaf : Presheaf.IsSheaf (SmallEtale.topology B S hS F) LP :=
    GrothendieckTopology.HasSheafCompose.isSheaf _
      (meromorphicSectionSheaf.{u, u} B S hS F hF L).isSheaf
  refine ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS F) LP).1 hLsheaf T
    hT).isSeparatedFor.ext fun W k hk ↦ ?_
  have hglue : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.map k.op).hom
      (hsh.amalgamate fam hcomp) = fam k hk := hsh.valid_glue hcomp k hk
  refine Eq.trans (toMeromorphicSectionSheaf_map B S hS F hF L V W k _) ?_
  refine Eq.trans (congrArg (toMeromorphicSectionSheaf B S hS F hF L W)
    (map_tmul_generator B S hS F hF L V e hcompat W k _)) ?_
  rw [hglue]
  exact hfamspec k hk

/-- **The sections of `𝒦_F(L)` over a chart carrying a free generator.**  If `e` restricts to a
free generator of `L` over every chart over `V`, then `a ↦ a ⊗ e` is a bijection of the
meromorphic functions `𝒦_F(V)` onto the sections of the sheaf `𝒦_F(L)` of Stacks 0EN5 over `V`:
every meromorphic section of `L` over `V` is `a · e` for exactly one meromorphic function `a`.

This is the module analogue of Stacks 0EN6, part (2), which computes the sections of `𝒦_F` over
an affine chart. It needs no affineness: the generator is what replaces it. -/
theorem bijective_toMeromorphicSectionSheaf_tmul
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k) :
    Function.Bijective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) ↦
      toMeromorphicSectionSheaf B S hS F hF L V
        (a ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS F hF L).obj (op V)) :=
  ⟨injective_toMeromorphicSectionSheaf_tmul B S hS F hF L V e hcompat hfree,
    surjective_toMeromorphicSectionSheaf_tmul B S hS F hF L V e hcompat hfree⟩

/-! ### The ratio of a meromorphic section against a free generator over a chart -/

/-- **Two free generators of an `𝒪_F`-module over a chart differ by a unit of the regular
functions there.**  Each generates the sections over the chart freely, so each is a multiple of
the other and the two factors multiply to `1`.

`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_smul_genericStalkGenerator` is this at the
chart `Spec(𝒪_{U, u})` of a prime divisor and the generator chosen there. -/
theorem exists_isUnit_smul_of_bijective_smul (m m' : L.val.obj (op V))
    (hm : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • m)
    (hm' : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • m') :
    ∃ v : (chartRing B S hS F hF V)ˣ, m' = (v : chartRing B S hS F hF V) • m := by
  obtain ⟨v, hv⟩ := hm.2 m'
  obtain ⟨w, hw⟩ := hm'.2 m
  have hv' : v • m = m' := hv
  have hw' : w • m' = m := hw
  have key : (w * v) • m = m := by rw [mul_smul, hv', hw']
  have h1 : w * v = 1 := hm.1 (key.trans (one_smul _ m).symm)
  exact ⟨⟨v, w, (mul_comm v w).trans h1, h1⟩, hv'.symm⟩

/-- **The ratio `t / e` of a meromorphic section against a free generator over a chart.**  If `e`
restricts to a free generator of `L` over every chart over `V`, a meromorphic section of `L` is
over `V` the product of exactly one meromorphic function with `e`
(`AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_tmul`), and this is that function.

This is the reading of a meromorphic section on a *prescribed* chart that the proof of Stacks
0EPX makes of the rational function `f` with `t|_U = f · s_U`;
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient` is the same construction at the
chart `Spec(𝒪_{U, u})` and the generator chosen there. -/
noncomputable def chartRatio
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS F hF L) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj (op V) :=
  (Equiv.ofBijective _
      (bijective_toMeromorphicSectionSheaf_tmul B S hS F hF L V e hcompat hfree)).symm
    (t.eval (op V))

/-- **The defining property of the chart ratio**: over `V` the section is the ratio times the
generator. -/
theorem eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS F hF L) :
    t.eval (op V) = toMeromorphicSectionSheaf B S hS F hF L V
      (chartRatio B S hS F hF L V e hcompat hfree t ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS F hF L).obj (op V)) :=
  ((Equiv.ofBijective _
      (bijective_toMeromorphicSectionSheaf_tmul B S hS F hF L V e hcompat hfree)).apply_symm_apply
    (t.eval (op V))).symm

/-- **The chart ratio is the unique meromorphic function with that property.**  Any presentation
of the section over `V` as a multiple of the generator `e` computes it. -/
theorem chartRatio_eq_of_eval_eq
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS F hF L)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS F hF).O).obj.obj (op V))
    (ha : t.eval (op V) = toMeromorphicSectionSheaf B S hS F hF L V
      (a ⊗ₜ[chartRing B S hS F hF V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS F hF L).obj (op V))) :
    chartRatio B S hS F hF L V e hcompat hfree t = a :=
  (bijective_toMeromorphicSectionSheaf_tmul B S hS F hF L V e hcompat hfree).1
    ((eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS F hF L V e hcompat hfree
      t).symm.trans ha)

/-- **A presentation against any free generator computes the chart ratio up to a unit.**  If the
section is over `V` the product of `a` with *some* free generator `g` of `L` there, then the
chart ratio against `e` is `v · a` for the unit `v` of `𝒪_F(V)` with `g = v · e`.

This is the independence of the chart ratio of the chosen generator, in the form the comparison
of two readings of one section needs: the ratio is not determined by the section alone, but two
readings of it differ by a unit of the regular functions, which is all an order of vanishing
sees.  `AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul` is
this at the chart `Spec(𝒪_{U, u})` of a prime divisor. -/
theorem exists_isUnit_chartRatio_eq_mul_of_eval_eq
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS F hF L) (g : L.val.obj (op V))
    (hg : Function.Bijective fun r : chartRing B S hS F hF V ↦ r • g)
    (a : (meromorphicChartSheaf B S hS F hF).obj.obj (op V))
    (ha : t.eval (op V) = toMeromorphicSectionSheaf B S hS F hF L V
      (a ⊗ₜ[chartRing B S hS F hF V] g :
        (meromorphicSectionModule B S hS F hF L).obj (op V))) :
    ∃ v : (chartRing B S hS F hF V)ˣ,
      chartRatio B S hS F hF L V e hcompat hfree t =
        algebraMap (chartRing B S hS F hF V)
            ((meromorphicChartSheaf B S hS F hF).obj.obj (op V))
            (v : chartRing B S hS F hF V) * a := by
  obtain ⟨v, hv⟩ := exists_isUnit_smul_of_bijective_smul B S hS F hF L V (e V (𝟙 V)) g
    (hfree V (𝟙 V)) hg
  refine ⟨v, chartRatio_eq_of_eval_eq B S hS F hF L V e hcompat hfree t _ (ha.trans ?_)⟩
  refine congrArg (toMeromorphicSectionSheaf B S hS F hF L V) ?_
  rw [hv]
  exact meromorphicSectionModule_tmul_smul B S hS F hF L V (v : _) a _

/-- **The chart ratio is natural in the chart.**  Restricting the ratio of `t` against the free
generator `e` over `V` along a morphism of charts `j : V' ⟶ V` gives the ratio of `t` against the
restricted generator family over `V'`.

The restricted family is `e` read at the arrows through `j`, which is again compatible with
restriction and again free, so the right-hand side is a chart ratio in the sense of
`AlgebraicGeometry.Space.chartRatio`; those two proofs are supplied inline, proof irrelevance
making the term independent of them.

This is what lets a comparison of two readings of one meromorphic section be made over a
*common refinement* of two charts: each reading is the restriction of the reading on its own
chart, so a comparison downstairs is a comparison of the original two.  Together with
`AlgebraicGeometry.Space.functionFieldToEtaleFractionRing_chartFunctionFieldMap_stalkMap`, which
says the reading of a rational function in `Q(𝒪_{X, x̄})` is likewise unchanged by refining the
chart, it is the chart-side half of the identification of the two ratios that the proof of
Stacks 0EPX makes.

Both sides are the unique meromorphic function presenting `t` over `V'` against `e V' j`, by
`AlgebraicGeometry.Space.chartRatio_eq_of_eval_eq`: the restriction of a presentation is a
presentation, which is
`AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionSheaf_tmul_restrict`. -/
theorem chartRatio_restrict
    (hcompat : ∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS F hF L)
    (V' : SmallEtale B S hS F) (j : V' ⟶ V) :
    chartRatio B S hS F hF L V' (fun W k ↦ e W (k ≫ j))
        (fun W W' k g ↦ (hcompat W W' (k ≫ j) g).trans
          (congrArg (e W') (Category.assoc g k j).symm))
        (fun W k ↦ hfree W (k ≫ j)) t =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.map j.op).hom
        (chartRatio B S hS F hF L V e hcompat hfree t) := by
  refine chartRatio_eq_of_eval_eq B S hS F hF L V' (fun W k ↦ e W (k ≫ j)) _ _ t _ ?_
  refine Eq.trans (eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS F hF L t V e hcompat
    (chartRatio B S hS F hF L V e hcompat hfree t)
    (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS F hF L V e hcompat hfree t)
    V' j) ?_
  exact congrArg (fun z : L.val.obj (op V') ↦ toMeromorphicSectionSheaf B S hS F hF L V'
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.map j.op).hom
          (chartRatio B S hS F hF L V e hcompat hfree t)) ⊗ₜ[chartRing B S hS F hF V'] z :
        (meromorphicSectionModule B S hS F hF L).obj (op V')))
    (congrArg (e V') (Category.id_comp j).symm)

end AlgebraicGeometry.Space

end
