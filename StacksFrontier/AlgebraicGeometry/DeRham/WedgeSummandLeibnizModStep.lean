module

public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeSummandLeibniz
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The Leibniz rule on a summand of the wedge map, modulo the next step of the filtration

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, let `Ω^•`
be the relative de Rham complex of `AlgebraicGeometry.SheafOfModules.deRhamComplex`, and let
`ι : P ⟶ Ω^•` be a morphism of complexes of sheaves of `A`-modules factoring through the exterior
powers of a sheaf `F ⟶ Ω^1` as `ι^i = c i ≫ (⋀^iF ⟶ Ω^i)|_A` — the hypothesis `hc` of
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep`. The `(i, j)` summand of the
wedge map cutting out the wedge filtration of `Ω^•` is

`P^i ⊗_A Ω^j ⟶ Ω^i ⊗_A Ω^j ⟶ Ω^{i+j}`,

and `AlgebraicGeometry.SheafOfModules.summandOfEq_d` computes the de Rham differential on it as a
sum of two terms: the `(i + 1, j)` summand precomposed with `d_P ⊗ 1`, and `(-1)^i` times the
`(i, j + 1)` summand precomposed with `1 ⊗ d`.

**This file kills the first of those two terms.** It factors through the degree `i + 1` of `P`, so
its image lies in the step at `i + 1` of the filtration of `Ω^{i+j+1}` by the images of
`⋀^•F ⊗_{𝒪_X} ⋀^•Ω^1`
(`AlgebraicGeometry.SheafOfModules.imageSubobject_summand_le_exteriorImageFiltration`), and that
step is the image of `SheafOfModules.prodWedgeHomOfEq` at `i + 1`
(`AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction_exteriorImageFiltration`); so
anything that kills that wedge map kills the term. Modulo the step at `i + 1` the de Rham
differential is therefore `(-1)^i(1 ⊗ d)` on the `(i, j)` summand, which is the sign
`Stacks.DeRhamSmooth.gradedTargetComplex_d` carries and the whole content of the two squares of
[Stacks, Section 0FMK] on the step of the filtration.

## Main results

* `Stacks.CategoryTheory.comp_eq_zero_of_imageSubobject_le_of_comp_eq_zero`: **a morphism
  dominated by one that is killed is killed** — if the image of `u` is below the image of `w` and
  `w ≫ v = 0` then `u ≫ v = 0`. Stated at generic objects of an abelian category.
* `AlgebraicGeometry.SheafOfModules.summandOfEq_comp_eq_zero_of_prodWedgeHomOfEq_comp_eq_zero`:
  **anything that kills the `(i, j)` wedge map of the exterior-power filtration kills the `(i, j)`
  summand of the wedge map.**
* `AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_of_comp_eq_zero`: **the Leibniz rule on the
  `(i, j)` summand, read after a morphism that kills the `(i + 1, j)` wedge map**: the de Rham
  differential becomes `(-1)^i` times the `(i, j + 1)` summand precomposed with `1 ⊗ d`, the first
  term of the rule having vanished.
* `AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_cokernelπ_prodWedgeHomOfEq`: the same read
  into the quotient of `Ω^{m+1}` by the step at `i + 1`, where the hypothesis is
  `CategoryTheory.Limits.cokernel.condition` and nothing is left to supply.

## Implementation notes

**Why the domination lemma is stated generically.** `CategoryTheory.Limits` has
`CategoryTheory.Limits.imageSubobject_arrow_comp_eq_zero`, which kills the arrow of the image of
`w`; passing from there to the image of `u` is one `CategoryTheory.Subobject.ofLE_arrow` and one
`CategoryTheory.Limits.imageSubobject_arrow_comp`, and all three are `rw`s. At the binders of the
de Rham complex no `rw` fires at all — the goals there are reported as not type-correct at
`implicit` transparency, the ring sheaf `A` being a `TopCat.Sheaf` while `Tensor.ringSheaf`
expects a sheaf on the site of opens — so the three steps are done once over an abstract abelian
category, where the objects are variables, and the result is applied as a term. This is the same
discipline as `Stacks.CategoryTheory.imageSubobject_le_imageSubobject_of_eq_comp` of
`StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece`, and for the same reason.

**The hypothesis is on the wedge map and not on the step.** `summandOfEq_d_comp_of_comp_eq_zero`
asks that `v` kill `SheafOfModules.prodWedgeHomOfEq` at `(i + 1, j)` rather than that it kill the
step of the filtration, because that is the form a consumer has: the projection onto a graded
piece is a cokernel of a wedge map, so the hypothesis is `cokernel.condition` and not a statement
about a subobject. The passage from the wedge map to the step is inside the proof, through the
containment of images, where it costs one `le_of_le_of_eq`.

**Nothing is assumed of `i` or `j`**, and in particular no cut is fixed: the vanishing is of the
term that moves one step *up* the filtration, which happens at every `i`.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (sheafTensor ringSheaf)

universe u

namespace Stacks.CategoryTheory

/-- **A morphism dominated by one that is killed is killed.** If the image of `u` lies below the
image of `w` and `w ≫ v = 0`, then `u ≫ v = 0`.

Stated at generic objects of an abelian category, which is what makes it usable at the binders of
the de Rham complex: all three rewrites it is made of —
`CategoryTheory.Limits.imageSubobject_arrow_comp_eq_zero`,
`CategoryTheory.Subobject.ofLE_arrow` and
`CategoryTheory.Limits.imageSubobject_arrow_comp` — happen here, where the objects are variables,
and none of them fires at those binders. See the implementation notes of this file.

Costs 432 heartbeats against the default budget of 200,000. -/
theorem comp_eq_zero_of_imageSubobject_le_of_comp_eq_zero {C₁ : Type*}
    [_root_.CategoryTheory.Category C₁] [_root_.CategoryTheory.Abelian C₁] {P Q R T : C₁}
    {u : P ⟶ R} {w : Q ⟶ R} (v : R ⟶ T)
    (hle : imageSubobject u ≤ imageSubobject w) (hw : w ≫ v = 0) :
    u ≫ v = 0 := by
  have h1 : (imageSubobject w).arrow ≫ v = 0 := imageSubobject_arrow_comp_eq_zero hw
  have h2 : (imageSubobject u).arrow ≫ v = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, h1, comp_zero]
  rw [← imageSubobject_arrow_comp u, Category.assoc, h2, comp_zero]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)
  {F : _root_.SheafOfModules.{u}
    (Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf)}
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)
  (iF : F ⟶ moduleOfDifferentials.{u, u, u} φ)
  (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
  (ι : P ⟶ deRhamComplex B D)
  (c : ∀ i : ℕ, P.X i ⟶
    (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).obj
      (AF.exteriorPower i))
  (hc : ∀ i : ℕ, ι.f i = c i ≫
    (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
      ((AF.exterior_isExteriorAlgebra.map B.exterior_isExteriorAlgebra iF).app (i : ℤ)))

/-! The abelian structures of the two categories of sheaves of modules, named rather than searched
for, exactly as in `StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep`: these are
the instances the subobject lattices of the two filtrations are elaborated against. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

include hc in
/-- **Anything that kills the `(i, j)` wedge map of the exterior-power filtration kills the
`(i, j)` summand of the wedge map.** The summand factors through that wedge map after an
epimorphism (`AlgebraicGeometry.SheafOfModules.summandOfEq_eq_laxComparison_comp`), so its image
is below the wedge map's; and a morphism dominated by one that is killed is killed
(`Stacks.CategoryTheory.comp_eq_zero_of_imageSubobject_le_of_comp_eq_zero`).

Costs 23,619 heartbeats against the default budget of 200,000. -/
theorem summandOfEq_comp_eq_zero_of_prodWedgeHomOfEq_comp_eq_zero (i j m : ℕ) (h : i + j = m)
    {T : _root_.SheafOfModules.{u} (ringSheaf A)}
    (v : (deRhamComplex B D).X m ⟶ T)
    (hv : (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
        (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) i j m h) ≫ v = 0) :
    (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≫ v = 0 :=
  Stacks.CategoryTheory.comp_eq_zero_of_imageSubobject_le_of_comp_eq_zero v
    (le_of_le_of_eq
      (imageSubobject_summand_le_exteriorImageFiltration B D AF iF P ι c hc i j m h)
      (exteriorPowerSubobjectRestriction_exteriorImageFiltration B AF iF i j m h))
    hv

include hc in
/-- **The Leibniz rule on the `(i, j)` summand of the wedge map, read after a morphism that kills
the `(i + 1, j)` wedge map of the exterior-power filtration.** The de Rham differential on the
summand is `dω ∧ η + (-1)^iω ∧ dη` with `ω` the image of a section of `P^i`
(`AlgebraicGeometry.SheafOfModules.summandOfEq_d`); the first term is the `(i + 1, j)` summand
precomposed with `d_P ⊗ 1`, so `v` kills it
(`AlgebraicGeometry.SheafOfModules.summandOfEq_comp_eq_zero_of_prodWedgeHomOfEq_comp_eq_zero`),
and what is left is `(-1)^i` times the `(i, j + 1)` summand precomposed with `1 ⊗ d`.

This is the computation the identification of the graded pieces of [Stacks, Section 0FMK] rests
on: the differential of the `i`-th graded piece is `(-1)^i(1 ⊗ d)`, which is the sign
`Stacks.DeRhamSmooth.gradedTargetComplex_d` carries.

Costs 30,782 heartbeats against the default budget of 200,000. -/
theorem summandOfEq_d_comp_of_comp_eq_zero (i j m : ℕ) (h : i + j = m)
    {T : _root_.SheafOfModules.{u} (ringSheaf A)}
    (v : (deRhamComplex B D).X (m + 1) ⟶ T)
    (hv : (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
        (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) (i + 1) j (m + 1)
          (show i + 1 + j = m + 1 by omega)) ≫ v = 0) :
    (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
          exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≫
        (deRhamComplex B D).d m (m + 1) ≫ v =
      (-1 : ℤ) ^ i • (((sheafTensor.{u,u,u,u,u} A).obj (P.X i)).map
            ((deRhamComplex B D).d j (j + 1)) ≫
        (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X (j + 1)) ≫
            exteriorProductComponent B i (j + 1) ≫
              ((deRhamComplex B D).XIsoOfEq (show i + (j + 1) = m + 1 by omega)).hom) ≫ v) := by
  have hT1 : (((sheafTensor.{u,u,u,u,u} A).map (P.d i (i + 1))).app ((deRhamComplex B D).X j) ≫
      ((sheafTensor.{u,u,u,u,u} A).map (ι.f (i + 1))).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B (i + 1) j ≫
          ((deRhamComplex B D).XIsoOfEq (show i + 1 + j = m + 1 by omega)).hom) ≫ v = 0 :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (((sheafTensor.{u,u,u,u,u} A).map (P.d i (i + 1))).app
            ((deRhamComplex B D).X j) ≫ ·)
          (summandOfEq_comp_eq_zero_of_prodWedgeHomOfEq_comp_eq_zero B D AF iF P ι c hc
            (i + 1) j (m + 1) (show i + 1 + j = m + 1 by omega) v hv))
        comp_zero)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ v) (summandOfEq_d B D P ι i j m h)) ?_
  refine Eq.trans (Preadditive.add_comp _ _ _ _ _ _) ?_
  refine Eq.trans (congrArg (· + _) hT1) ?_
  refine Eq.trans (zero_add _) ?_
  refine Eq.trans (Preadditive.zsmul_comp _ _ _) ?_
  exact congrArg (((-1 : ℤ) ^ i) • ·) (Category.assoc _ _ _)

include hc in
/-- **The Leibniz rule on the `(i, j)` summand of the wedge map, read in the quotient of `Ω^{m+1}`
by the step at `i + 1` of the exterior-power filtration.** This is
`AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_of_comp_eq_zero` at the projection onto that
quotient, where the hypothesis on `v` is `CategoryTheory.Limits.cokernel.condition` carried across
restriction of scalars and nothing is left for a consumer to supply: modulo the next step the de
Rham differential on the `(i, j)` summand is `(-1)^i` times the `(i, j + 1)` summand precomposed
with `1 ⊗ d`.

Costs 28,383 heartbeats against the default budget of 200,000. -/
theorem summandOfEq_d_comp_cokernelπ_prodWedgeHomOfEq (i j m : ℕ) (h : i + j = m) :
    (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
          exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≫
        (deRhamComplex B D).d m (m + 1) ≫
          (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
            (cokernel.π (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) (i + 1) j (m + 1)
              (show i + 1 + j = m + 1 by omega))) =
      (-1 : ℤ) ^ i • (((sheafTensor.{u,u,u,u,u} A).obj (P.X i)).map
            ((deRhamComplex B D).d j (j + 1)) ≫
        (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X (j + 1)) ≫
            exteriorProductComponent B i (j + 1) ≫
              ((deRhamComplex B D).XIsoOfEq (show i + (j + 1) = m + 1 by omega)).hom) ≫
          (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
            (cokernel.π (_root_.SheafOfModules.prodWedgeHomOfEq AF B B iF (𝟙 _) (i + 1) j (m + 1)
              (show i + 1 + j = m + 1 by omega)))) := by
  refine summandOfEq_d_comp_of_comp_eq_zero B D AF iF P ι c hc i j m h _ ?_
  refine Eq.trans
    ((_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map_comp _ _).symm ?_
  refine Eq.trans (congrArg
    (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map
    (cokernel.condition _)) ?_
  exact (_root_.SheafOfModules.restrictScalars.{u} (underlyingRingHom (φ := φ))).map_zero _ _

end AlgebraicGeometry.SheafOfModules

end
