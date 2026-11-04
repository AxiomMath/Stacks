module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSmul

/-!
# The canonical map from a module to its meromorphic sections

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B` and let `M` be a sheaf of
`𝒪_F`-modules.  The sheaf `𝒦_F(M)` of meromorphic sections of `M` of Stacks 0EN5 is the extension
of scalars of `M` along `𝒪_F ⟶ 𝒦_F`, sheafified, so there is a canonical map

`M ⟶ 𝒦_F(M)`,

the unit of that extension of scalars followed by the sheafification map, which over a chart `V`
sends a section `m` of `M` to the pure meromorphic section `1 ⊗ m`.  It is the map along which a
section of `M` *is* a meromorphic section of `M`, and it is what the phrase "`s` not in `ℒ_ξ`" of
Stacks 0EPS refers to: the sections of `ℒ` at a point sit inside the meromorphic ones along it,
and the first of the two collections of that lemma consists of the prime divisors at whose
generic point `s` fails to lie in the image.

## Main definitions

* `AlgebraicGeometry.Space.toMeromorphicSectionValue` is the canonical map
  `M(V) → 𝒦_F(M)(V)` over an étale chart `V`.

## Main results

* `AlgebraicGeometry.Space.toMeromorphicSectionValue_add` and
  `AlgebraicGeometry.Space.toMeromorphicSectionValue_zero`: the canonical map is additive.
* `AlgebraicGeometry.Space.toMeromorphicSectionValue_smul`: it is semilinear along the component
  `𝒪_F(V) ⟶ 𝒦_F(V)` of the canonical map into the meromorphic functions, which is the linearity
  it can have — the source of the map is a module over the regular functions and its target a
  module over the meromorphic ones.
* `AlgebraicGeometry.Space.toMeromorphicSectionValue_map`: it is natural in the chart, so the
  maps over all charts are the components of a single map of presheaves.
* `AlgebraicGeometry.Space.pureMeromorphicSection_smul_eq_algebraMap_tmul`: the pure meromorphic
  section of `r • m` is the pure tensor `(algebraMap r) ⊗ m`, which is what reads a meromorphic
  section whose coefficient happens to be regular as an honest section.
* `AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionValue_of_hom`: being an honest section is
  stable under refining the chart.

## Implementation notes

The map is given over each chart separately rather than as a morphism of presheaves of modules,
as `AlgebraicGeometry.Space.toMeromorphicSectionSheaf` is: the source `M` has its sections in the
universe `u` of the schemes while `𝒦_F(M)` has its sections in `u + 1`, so the two are not objects
of one category of presheaves of modules and a morphism between them cannot be written without
first lifting `M`.  Naturality is therefore stated as the explicit lemma
`AlgebraicGeometry.Space.toMeromorphicSectionValue_map`.

The module universe of `M` is the universe of the schemes throughout, as in the whole chartwise
theory of meromorphic sections: `AlgebraicGeometry.Space.meromorphicSectionModule` is stated for
`Modules.{u, u}`.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
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

/-- Moving a scalar of the base ring across a pure tensor whose left factor is `1`: this is
`TensorProduct.smul_tmul` at an algebra, stated abstractly so that the instance
`TensorProduct.CompatibleSMul` it rests on is discharged here rather than at the concrete types
of the meromorphic sections over a chart, where instance search does not find it. -/
private theorem one_tmul_smul {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K]
    {N : Type*} [AddCommGroup N] [Module R N] (r : R) (n : N) :
    (1 : K) ⊗ₜ[R] (r • n) = (r • (1 : K)) ⊗ₜ[R] n :=
  (smul_tmul r 1 n).symm

/-! ### The pure meromorphic section `1 ⊗ m` -/

/-- **The pure meromorphic section `1 ⊗ m` of a section `m` of `M` over a chart.**  The
meromorphic sections of `M` over a chart `V`, before sheafification, are the extension of scalars
`𝒦_F(V) ⊗_{𝒪_F(V)} M(V)` of Stacks 03CU; this is the image of `m` under the unit of that
extension of scalars. -/
noncomputable def pureMeromorphicSection (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (m : M.val.obj (op V)) :
    (meromorphicSectionModule B S hS F hF M).obj (op V) :=
  (1 : (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) ⊗ₜ[chartRing B S hS F hF V] m

/-- The pure meromorphic section of `0` is `0`. -/
@[simp]
theorem pureMeromorphicSection_zero (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) :
    pureMeromorphicSection B S hS F hF M V 0 = 0 :=
  tmul_zero _ _

/-- Taking the pure meromorphic section of a section of `M` is additive. -/
theorem pureMeromorphicSection_add (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (m m' : M.val.obj (op V)) :
    pureMeromorphicSection B S hS F hF M V (m + m') =
      pureMeromorphicSection B S hS F hF M V m + pureMeromorphicSection B S hS F hF M V m' :=
  tmul_add _ _ _

/-- A meromorphic function `c` times the pure meromorphic section of `m` is the pure tensor
`c ⊗ m`. -/
private theorem smul_pureMeromorphicSection_eq_tmul (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (c : meromorphicChartRing B S hS F hF V) (m : M.val.obj (op V)) :
    c • pureMeromorphicSection B S hS F hF M V m =
      (c ⊗ₜ[chartRing B S hS F hF V] m :
        (meromorphicSectionModule B S hS F hF M).obj (op V)) := by
  rw [meromorphicSectionModule_smul_tmul B S hS F hF M V
    (pureMeromorphicSection B S hS F hF M V m) c 1 m rfl, mul_one]

/-- **The pure meromorphic section of `r • m` is `r` times that of `m`.**  Multiplying a section
of `M` by a regular function `r` moves, in the extension of scalars, to multiplying by the image
`c` of `r` in the meromorphic functions.

The image `c` is a parameter with a defining hypothesis, as in
`AlgebraicGeometry.Space.meromorphicSectionModule_smul_tmul`: the sections of `𝒦_F` over a chart
carry two spellings, the one the tensor product is taken over and the one the meromorphic
sections are a module over, and scalar multiplication is found by instance search only at the
latter. -/
theorem pureMeromorphicSection_smul (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (r : chartRing B S hS F hF V) (m : M.val.obj (op V))
    (c : meromorphicChartRing B S hS F hF V)
    (hc : c = algebraMap (chartRing B S hS F hF V)
      ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) r) :
    pureMeromorphicSection B S hS F hF M V (r • m) =
      c • pureMeromorphicSection B S hS F hF M V m := by
  rw [smul_pureMeromorphicSection_eq_tmul, hc, Algebra.algebraMap_eq_smul_one]
  exact one_tmul_smul (K := (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) r m

/-- **The pure meromorphic section of `r • m` is the pure tensor whose coefficient is the image
of `r` in the meromorphic functions.**  Over a chart on which a section of `M` is written `r • m`
for a regular function `r`, its pure meromorphic section is `(algebraMap r) ⊗ m`.

This is `AlgebraicGeometry.Space.pureMeromorphicSection_smul` followed by
`AlgebraicGeometry.Space.meromorphicSectionModule_smul_tmul`, which moves the scalar into the
left factor of the extension of scalars where the coefficient `1` of the pure tensor absorbs
it. -/
theorem pureMeromorphicSection_smul_eq_algebraMap_tmul (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (r : chartRing B S hS F hF V) (m : M.val.obj (op V)) :
    pureMeromorphicSection B S hS F hF M V (r • m) =
      ((algebraMap (chartRing B S hS F hF V)
          ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) r) ⊗ₜ[
        chartRing B S hS F hF V] m :
          (meromorphicSectionModule B S hS F hF M).obj (op V)) := by
  rw [pureMeromorphicSection_smul B S hS F hF M V r m
    (algebraMap (chartRing B S hS F hF V)
      ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) r) rfl]
  exact smul_pureMeromorphicSection_eq_tmul B S hS F hF M V _ m

/-- **Taking the pure meromorphic section of a section of `M` is natural in the chart.**
Restricting `1 ⊗ m` restricts `m` and leaves the coefficient `1` alone. -/
theorem pureMeromorphicSection_map (M : Modules.{u, u} B S hS F hF)
    (V W : SmallEtale B S hS F) (g : W ⟶ V) (m : M.val.obj (op V)) :
    ((meromorphicSectionModule B S hS F hF M).map g.op).hom
        (pureMeromorphicSection B S hS F hF M V m) =
      pureMeromorphicSection B S hS F hF M W ((M.val.map g.op).hom m) := by
  refine Eq.trans (meromorphicSectionModule_map_tmul B S hS F hF M V W g
    (1 : (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) m) ?_
  congr 1
  exact map_one _

/-! ### The canonical map `M ⟶ 𝒦_F(M)` -/

/-- **The canonical map `M ⟶ 𝒦_F(M)` over an étale chart.**  A section `m` of a sheaf of
`𝒪_F`-modules `M` over a chart `V` is a meromorphic section of `M` over `V`, namely the pure
meromorphic section `1 ⊗ m` read in the sheafification `𝒦_F(M)` of Stacks 0EN5.

Its image is what "`ℒ_ξ` inside the meromorphic sections" denotes in Stacks 0EPS. -/
noncomputable def toMeromorphicSectionValue (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (m : M.val.obj (op V)) :
    (meromorphicSectionSheaf.{u, u} B S hS F hF M).val.obj (op V) :=
  toMeromorphicSectionSheaf B S hS F hF M V (pureMeromorphicSection B S hS F hF M V m)

/-- The canonical map `M ⟶ 𝒦_F(M)` over a chart, unfolded: it is the sheafification map of
Stacks 0EN5 applied to the pure meromorphic section `1 ⊗ m`. -/
theorem toMeromorphicSectionValue_eq (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (m : M.val.obj (op V)) :
    toMeromorphicSectionValue B S hS F hF M V m =
      toMeromorphicSectionSheaf B S hS F hF M V
        (pureMeromorphicSection B S hS F hF M V m) :=
  rfl

/-- The canonical map `M ⟶ 𝒦_F(M)` carries `0` to `0`. -/
@[simp]
theorem toMeromorphicSectionValue_zero (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) :
    toMeromorphicSectionValue B S hS F hF M V 0 = 0 := by
  rw [toMeromorphicSectionValue_eq, pureMeromorphicSection_zero]
  exact map_zero _

/-- The canonical map `M ⟶ 𝒦_F(M)` is additive. -/
theorem toMeromorphicSectionValue_add (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (m m' : M.val.obj (op V)) :
    toMeromorphicSectionValue B S hS F hF M V (m + m') =
      toMeromorphicSectionValue B S hS F hF M V m +
        toMeromorphicSectionValue B S hS F hF M V m' := by
  rw [toMeromorphicSectionValue_eq, pureMeromorphicSection_add,
    toMeromorphicSectionSheaf_add B S hS F hF M V
      (pureMeromorphicSection B S hS F hF M V m)
      (pureMeromorphicSection B S hS F hF M V m')]
  rfl

/-- **The canonical map `M ⟶ 𝒦_F(M)` is semilinear along `𝒪_F ⟶ 𝒦_F`.**  Multiplying a section
of `M` over a chart by a regular function `r` multiplies the meromorphic section it becomes by
`r` read as a meromorphic function: the coefficient of the pure meromorphic section `1 ⊗ m`
absorbs the scalar from the module factor.

As in `AlgebraicGeometry.Space.pureMeromorphicSection_smul`, the image `c` of `r` in the
meromorphic functions is a parameter with a defining hypothesis. -/
theorem toMeromorphicSectionValue_smul (M : Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (r : chartRing B S hS F hF V) (m : M.val.obj (op V))
    (c : meromorphicChartRing B S hS F hF V)
    (hc : c = algebraMap (chartRing B S hS F hF V)
      ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) r) :
    toMeromorphicSectionValue B S hS F hF M V (r • m) =
      c • toMeromorphicSectionValue B S hS F hF M V m := by
  rw [toMeromorphicSectionValue_eq, pureMeromorphicSection_smul B S hS F hF M V r m c hc,
    toMeromorphicSectionSheaf_smul B S hS F hF M V c
      (pureMeromorphicSection B S hS F hF M V m)]
  rfl

/-- **The canonical map `M ⟶ 𝒦_F(M)` is natural in the chart.**  Restricting a section of `M` and
then reading it as a meromorphic section is reading it as a meromorphic section and then
restricting, so the maps over all charts are the components of one map of presheaves. -/
theorem toMeromorphicSectionValue_map (M : Modules.{u, u} B S hS F hF)
    (V W : SmallEtale B S hS F) (g : W ⟶ V) (m : M.val.obj (op V)) :
    ((meromorphicSectionSheaf.{u, u} B S hS F hF M).val.map g.op).hom
        (toMeromorphicSectionValue B S hS F hF M V m) =
      toMeromorphicSectionValue B S hS F hF M W ((M.val.map g.op).hom m) := by
  rw [toMeromorphicSectionValue_eq, toMeromorphicSectionSheaf_map B S hS F hF M V W g
      (pureMeromorphicSection B S hS F hF M V m),
    pureMeromorphicSection_map]
  rfl

/-- **Being an honest section of `M` is stable under refining the chart.**  If a meromorphic
section `s` of `M` is over a chart `V` the image under the canonical map `M ⟶ 𝒦_F(M)` of a
section `m` of `M`, then over every chart `W` over `V` it is the image of the restriction of `m`.

This is naturality of the canonical map
(`AlgebraicGeometry.Space.toMeromorphicSectionValue_map`) together with the compatibility of the
values of a global section of `𝒦_F(M)` with restriction. -/
theorem eval_eq_toMeromorphicSectionValue_of_hom (M : Modules.{u, u} B S hS F hF)
    (s : MeromorphicSection.{u, u} B S hS F hF M) {V W : SmallEtale B S hS F} (g : W ⟶ V)
    (m : M.val.obj (op V))
    (hm : s.eval (op V) = toMeromorphicSectionValue B S hS F hF M V m) :
    s.eval (op W) = toMeromorphicSectionValue B S hS F hF M W ((M.val.map g.op).hom m) := by
  rw [← toMeromorphicSectionValue_map B S hS F hF M V W g m, ← hm]
  exact (PresheafOfModules.sections_property
    (M := (meromorphicSectionSheaf.{u, u} B S hS F hF M).val) s g.op).symm

end AlgebraicGeometry.Space

end
