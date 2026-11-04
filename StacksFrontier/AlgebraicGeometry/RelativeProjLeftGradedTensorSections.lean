module

public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensorQcoh
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.IsIso0FZE
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison on graded sections for property (6) of Tag 01O7

Let `s` be a relative `Proj` situation and let `ℳ`, `𝒩` be left graded modules over its graded
algebra `𝒜`. Property (6) of Tag 01O7 asserts a canonical morphism

`ℳ̃ ⊗_{𝒪} 𝒩̃ ⟶ (ℳ ⊗_𝒜 𝒩)~`

of sheaves of modules on the relative projective spectrum. Both sheaves are glued from the
charts `Proj 𝒜(W)` over the affine opens `W` of the base, and on the chart over `W` the first is
built from the graded `𝒜(W)`-modules of sections `Γ(W, ℳ)` and `Γ(W, 𝒩)` while the second is
built from `Γ(W, ℳ ⊗_𝒜 𝒩)`. The input the chart comparison needs, and what this file supplies,
is the comparison of those graded modules of sections:

`Γ(W, ℳ) ⊗_{𝒜(W)} Γ(W, 𝒩) ⟶ Γ(W, ℳ ⊗_𝒜 𝒩)`.

It is built from the local sections `x ⊗ y` of the relative tensor product. Over any open `U` of
the base a homogeneous section `x` of degree `p` of `ℳ` and a homogeneous section `y` of degree
`q` of `𝒩` have a product `x ⊗ y`, a section of degree `p + q` of `ℳ ⊗_𝒜 𝒩`, by
`SheafOfModules.RelativeTensor.tmul`. That family is biadditive summand by summand, so it
assembles over the direct sums into a biadditive map of the graded modules of sections; it is
linear over the section ring in the second variable because the action of `𝒜` on `ℳ ⊗_𝒜 𝒩` is
`a • (x ⊗ y) = x ⊗ (a • y)`, and in the first variable because the relative tensor product is
balanced, `(x • a) ⊗ y = x ⊗ (a • y)`. Hence it descends to the tensor product over the section
ring, and it carries the tensor grading into the grading of the sections of `ℳ ⊗_𝒜 𝒩`.

## Main definitions

* `Stacks.RelativeProj.Situation.sectionTmul` is the local section `x ⊗ y` of `ℳ ⊗_𝒜 𝒩` of a
  homogeneous section of `ℳ` and one of `𝒩`.
* `Stacks.RelativeProj.Situation.sectionTensorBilinear` is the comparison as a bilinear map of
  the graded modules of sections, and
  `Stacks.RelativeProj.Situation.sectionTensorMap` is **the comparison
  `Γ(U, ℳ) ⊗_{𝒜(U)} Γ(U, 𝒩) →ₗ Γ(U, ℳ ⊗_𝒜 𝒩)`** itself.
* `Stacks.RelativeProj.Situation.restrictTensorₛₗ` is restriction of the tensor products of the
  graded modules of sections along an inclusion of opens of the base, semilinear over
  restriction of the section rings.
* `Stacks.RelativeProj.Situation.sectionTensorGradedHom` packages it as a morphism of graded
  modules over the section ring, from the tensor product of the graded modules of sections with
  its tensor grading to the graded module of sections of `ℳ ⊗_𝒜 𝒩`.
* `Stacks.RelativeProj.Situation.moduleChartTensorMap` is **the comparison morphism of property
  (6) of Tag 01O7 on the chart over an affine open of the base**,
  `ℳ̃(W) ⊗ 𝒩̃(W) ⟶ (ℳ ⊗_𝒜 𝒩)~(W)` on `Proj 𝒜(W)`.
* `Stacks.RelativeProj.Situation.moduleSheafTensorChartMap` is **that morphism read as a
  morphism of the restrictions of the two sheaves of property (6) to the chart**,
  `(ℳ̃ ⊗ 𝒩̃)|_{chart W} ⟶ (ℳ ⊗_𝒜 𝒩)~|_{chart W}` — the family that gluing consumes.

## Main results

* `Stacks.RelativeProj.Situation.sectionTensorMap_tmul_of_of`: **the comparison sends
  `x ⊗ y` to `x ⊗ y`** — the pure tensor of two homogeneous sections to the local section of
  that name in the degree which is the sum of theirs.
* `Stacks.RelativeProj.Situation.sectionTensorMap_mem_grading`: **the comparison preserves
  degrees**, carrying the degree-`k` piece of the tensor grading into the degree-`k` sections of
  `ℳ ⊗_𝒜 𝒩`.
* `Stacks.RelativeProj.Situation.sectionModuleRestrict_sectionTensorMap`: **the comparison
  commutes with restriction to a smaller open of the base**, as an equality of maps on the whole
  tensor product, with `Stacks.RelativeProj.Situation.restrictTensorₛₗ` the restriction map of
  the tensor products. This is the module-level half of the compatibility that gluing the chart
  morphisms needs, and it is the hypothesis `huv` of
  `Stacks.ProjModuleComparison.fibreMap_localizedModuleMap` for the Tag 01M7 half of the chart
  comparison. `Stacks.RelativeProj.Situation.sectionTensorMap_restrict` and
  `Stacks.RelativeProj.Situation.sectionModuleRestrict_sectionTensorAddHom` are the same fact on
  pure tensors and on the biadditive map.
* `Stacks.RelativeProj.Situation.tensorSection_linearMap_ext`: **a linear map out of
  `Γ(U, ℳ) ⊗_{𝒜(U)} Γ(U, 𝒩)` is determined by its values on the pure tensors of homogeneous
  sections**, so the comparison is the only linear map with that formula.
* `SheafOfModules.RelativeTensor.tmul_heq_congr`: two local sections `x ⊗ y` of the relative
  tensor product whose indices agree, and whose factors agree heterogeneously, agree
  heterogeneously. This is what moves a product between the degrees `p + (q + i)` and
  `p + (i + q)`.

## Implementation notes

The degree bookkeeping is the whole difficulty. The action of `𝒜` on `ℳ ⊗_𝒜 𝒩` lands in degree
`i + n` while the local section it is equal to lands in degree `n + i`, so
`SheafOfModules.LeftGradedModule.relativeTensor_smul_tmul` is a heterogeneous equality, as is
`SheafOfModules.LeftGradedModule.relativeTensor_tmul_factor_heq`, which identifies the
exchanged action used there with the action of `𝒩`. Neither index can be substituted away: both
are compound expressions, so `subst` does not apply. `tmul_heq_congr` is therefore proved first,
by destructuring the two tensor indices — after which the total degrees *are* variables and can
be substituted — and the two linearity laws are assembled from it and
`Stacks.RelativeProj.Situation.of_eq_of_heq`, which turns a heterogeneous equality of
homogeneous sections of equal degrees into an equality of their images in the direct sum.

The biadditive map is assembled with `AddMonoidHom.mk'` over the summands rather than by
proving additivity of `SheafOfModules.RelativeTensor.tmul` by hand: the canonical balanced
family `SheafOfModules.RelativeTensor.tmulBalanced` already presents `x ⊗ y` as a value of an
`AddMonoidHom`-valued `AddMonoidHom`, so additivity in each variable is `map_add`.

The three linearity reductions are nested inductions over the direct sums, on the section ring,
then on the first variable, then on the second: every one of the two laws is additive in each
of its three arguments separately, so the homogeneous case is the only content.

The chart morphisms `Stacks.RelativeProj.Situation.moduleSheafTensorChartMap` are glued to the
morphism of property (6) on the relative projective spectrum in
`StacksFrontier/AlgebraicGeometry/RelativeProjLeftGradedTensorGlueHom.lean`, through
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`. The comparison is
a canonical map, not an isomorphism in general:
`Stacks.EvenWeightProj.not_isIso_associatedModuleSheafTensorMap`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite DirectSum TensorProduct
open Stacks.GradedModule
open scoped Stacks.GradedLocalization

universe v u t m

namespace SheafOfModules.RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A : GradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  (P : GradedModule.{t, m, m} A) (N : LeftGradedModule.{t, m, m} A)

/-- **The local section `x ⊗ y` of the relative tensor product, as a biadditive map on
sections.** This is the canonical balanced family read at one index and one object of the
site. -/
noncomputable abbrev tmulAddHom (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) :
    (P.piece p.1.1).val.obj X →+ (N.piece p.1.2).val.obj X →+ (gradedTensor P N n).val.obj X :=
  ((tmulBalanced P N n).app p).app X

/-- **Local sections `x ⊗ y` of the relative tensor product with the same tensor index agree
heterogeneously as soon as their factors do.** The total degrees are then equal as well, being
determined by the index, so the conclusion is an equality once the degrees are substituted; but
neither degree can be substituted before the indices are destructured, which is why the
statement is heterogeneous. -/
theorem tmul_heq_congr {n n' : ℤ} (p : TensorIndex n) (p' : TensorIndex n') (X : Cᵒᵖ)
    {x : (P.piece p.1.1).val.obj X} {x' : (P.piece p'.1.1).val.obj X}
    {y : (N.piece p.1.2).val.obj X} {y' : (N.piece p'.1.2).val.obj X}
    (h₁ : p.1.1 = p'.1.1) (h₂ : p.1.2 = p'.1.2) (hx : x ≍ x') (hy : y ≍ y') :
    tmul P N n p X x y ≍ tmul P N n' p' X x' y' := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨a', b'⟩, hab'⟩ := p'
  dsimp only at h₁ h₂ hx hy
  subst h₁
  subst h₂
  subst hab
  subst hab'
  rw [eq_of_heq hx, eq_of_heq hy]

end SheafOfModules.RelativeTensor

namespace Stacks.RelativeProj.Situation

open SheafOfModules.RelativeTensor

attribute [local instance] sectionModuleDecomposition

variable {s : Situation.{u}} (ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  (U : s.base.Opens)

/-- Homogeneous sections of equal degrees which agree heterogeneously have equal images in the
graded module of sections. -/
theorem of_eq_of_heq {n n' : ℤ} (h : n = n')
    (x : sectionModulePieces ℳ U n) (x' : sectionModulePieces ℳ U n') (hx : x ≍ x') :
    DirectSum.of (sectionModulePieces ℳ U) n x
      = DirectSum.of (sectionModulePieces ℳ U) n' x' := by
  subst h
  rw [eq_of_heq hx]

/-- **The product `x ⊗ y` of a homogeneous section of `ℳ` of degree `p` and a homogeneous
section of `𝒩` of degree `q`**: a homogeneous section of `ℳ ⊗_𝒜 𝒩` of degree `p + q`, as a
biadditive map. -/
noncomputable abbrev sectionTmulHom (p q : ℤ) :
    sectionModulePieces ℳ U p →+ sectionModulePieces 𝒩 U q →+
      sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U (p + q) :=
  tmulAddHom (ℳ.toGradedModule s.mul_comm) 𝒩 (p + q) ⟨(p, q), rfl⟩ (op U)

/-- **The product `x ⊗ y` of a homogeneous section of `ℳ` of degree `p` and a homogeneous
section of `𝒩` of degree `q`**, a homogeneous section of `ℳ ⊗_𝒜 𝒩` of degree `p + q`. -/
noncomputable abbrev sectionTmul (p q : ℤ) (x : sectionModulePieces ℳ U p)
    (y : sectionModulePieces 𝒩 U q) :
    sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U (p + q) :=
  sectionTmulHom ℳ 𝒩 U p q x y

/-- **The comparison of the graded modules of sections as a biadditive map**, assembled from the
products of homogeneous sections over the summands of the two direct sums. -/
noncomputable def sectionTensorAddHom :
    sectionModule ℳ U →+ sectionModule 𝒩 U →+ sectionModule (s.leftGradedTensor ℳ 𝒩) U :=
  DirectSum.toAddMonoid fun p =>
    AddMonoidHom.mk'
      (fun x => DirectSum.toAddMonoid fun q =>
        (DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) (p + q)).comp
          (sectionTmulHom ℳ 𝒩 U p q x))
      (fun x x' => DirectSum.addHom_ext fun q y => by
        simp only [DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp, Function.comp_apply,
          AddMonoidHom.add_apply, map_add])

/-- The comparison on a pure tensor of two homogeneous sections. -/
@[simp]
theorem sectionTensorAddHom_of_of (p q : ℤ) (x : sectionModulePieces ℳ U p)
    (y : sectionModulePieces 𝒩 U q) :
    sectionTensorAddHom ℳ 𝒩 U (DirectSum.of _ p x) (DirectSum.of _ q y)
      = DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) (p + q)
          (sectionTmul ℳ 𝒩 U p q x y) := by
  rw [sectionTensorAddHom, DirectSum.toAddMonoid_of]
  simp only [AddMonoidHom.mk'_apply, DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp,
    Function.comp_apply]

/-! ### Linearity over the section ring

Both laws reduce to the homogeneous case, where they are the two halves of the balancing of the
relative tensor product: `a • (x ⊗ y) = x ⊗ (a • y)` and `(x • a) ⊗ y = x ⊗ (a • y)`. -/

/-- **The action of a homogeneous section of `𝒜` on a product `x ⊗ y` of homogeneous sections is
`x ⊗ (a • y)`.** -/
theorem smul_of_sectionTmul (i : ℕ) (p q : ℤ) (a : s.sectionPieces U i)
    (x : sectionModulePieces ℳ U p) (y : sectionModulePieces 𝒩 U q) :
    DirectSum.of (s.sectionPieces U) i a
        • DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) (p + q)
            (sectionTmul ℳ 𝒩 U p q x y)
      = DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) (p + ((i : ℤ) + q))
          (sectionTmul ℳ 𝒩 U p ((i : ℤ) + q) x (𝒩.smul (i : ℤ) q (op U) a y)) := by
  rw [sectionModule_of_smul_of]
  refine of_eq_of_heq (s.leftGradedTensor ℳ 𝒩) U (by ring) _ _ ?_
  refine HEq.trans (ℳ.relativeTensor_smul_tmul 𝒩 s.mul_comm (p + q) (i : ℤ) ⟨(p, q), rfl⟩
    (op U) x y a) ?_
  exact tmul_heq_congr (ℳ.toGradedModule s.mul_comm) 𝒩 _ ⟨(p, (i : ℤ) + q), rfl⟩ (op U)
    rfl (add_comm q (i : ℤ)) HEq.rfl
    (𝒩.relativeTensor_tmul_factor_heq s.mul_comm q (i : ℤ) (op U) y a)

/-- **A product `(a • x) ⊗ y` of homogeneous sections is the action of `a` on `x ⊗ y`**: the
balancing of the relative tensor product identifies it with `x ⊗ (a • y)`, which is that
action. -/
theorem of_sectionTmul_smul_left (i : ℕ) (p q : ℤ) (a : s.sectionPieces U i)
    (x : sectionModulePieces ℳ U p) (y : sectionModulePieces 𝒩 U q) :
    DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) ((i : ℤ) + p + q)
        (sectionTmul ℳ 𝒩 U ((i : ℤ) + p) q (ℳ.smul (i : ℤ) p (op U) a x) y)
      = DirectSum.of (s.sectionPieces U) i a
          • DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) (p + q)
              (sectionTmul ℳ 𝒩 U p q x y) := by
  rw [smul_of_sectionTmul]
  refine of_eq_of_heq (s.leftGradedTensor ℳ 𝒩) U (by ring) _ _ ?_
  refine HEq.trans (tmul_heq_congr (ℳ.toGradedModule s.mul_comm) 𝒩 ⟨((i : ℤ) + p, q), rfl⟩
    (leftIndex (n := p + (i : ℤ) + q) ⟨(p, (i : ℤ), q), rfl⟩) (op U)
    (add_comm (i : ℤ) p) rfl
    (ℳ.toGradedModule_smul_heq s.mul_comm p (i : ℤ) (op U) x a).symm HEq.rfl) ?_
  refine HEq.trans (heq_of_eq ((tmulBalanced (ℳ.toGradedModule s.mul_comm) 𝒩
    (p + (i : ℤ) + q)).balanced ⟨(p, (i : ℤ), q), rfl⟩ (op U) x a y)) ?_
  exact tmul_heq_congr (ℳ.toGradedModule s.mul_comm) 𝒩
    (rightIndex (n := p + (i : ℤ) + q) ⟨(p, (i : ℤ), q), rfl⟩)
    ⟨(p, (i : ℤ) + q), rfl⟩ (op U) rfl rfl HEq.rfl HEq.rfl

/-- The comparison is linear over the section ring in both variables, by induction on the three
direct sums. -/
private theorem sectionTensorAddHom_smul_aux (r : s.sectionRing U) :
    ∀ (x : sectionModule ℳ U) (y : sectionModule 𝒩 U),
      sectionTensorAddHom ℳ 𝒩 U x (r • y) = r • sectionTensorAddHom ℳ 𝒩 U x y ∧
        sectionTensorAddHom ℳ 𝒩 U (r • x) y = r • sectionTensorAddHom ℳ 𝒩 U x y := by
  induction r using DirectSum.induction_on with
  | zero => intro x y; simp
  | of i a =>
      intro x
      induction x using DirectSum.induction_on with
      | zero => intro y; simp
      | of p x =>
          intro y
          induction y using DirectSum.induction_on with
          | zero => simp
          | of q y =>
              exact ⟨by rw [sectionModule_of_smul_of, sectionTensorAddHom_of_of,
                  sectionTensorAddHom_of_of, smul_of_sectionTmul],
                by rw [sectionModule_of_smul_of, sectionTensorAddHom_of_of,
                  sectionTensorAddHom_of_of, of_sectionTmul_smul_left]⟩
          | add y y' hy hy' => simp only [smul_add, map_add, hy, hy', and_self]
      | add x x' hx hx' =>
          intro y
          simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hx', and_self]
  | add r r' hr hr' =>
      intro x y
      simp only [add_smul, map_add, AddMonoidHom.add_apply, hr, hr', and_self]

/-- **The comparison is linear over the section ring in the second variable.** -/
theorem sectionTensorAddHom_smul_right (r : s.sectionRing U) :
    ∀ (x : sectionModule ℳ U) (y : sectionModule 𝒩 U),
      sectionTensorAddHom ℳ 𝒩 U x (r • y) = r • sectionTensorAddHom ℳ 𝒩 U x y :=
  fun x y => (sectionTensorAddHom_smul_aux ℳ 𝒩 U r x y).1

/-- **The comparison is linear over the section ring in the first variable.** -/
theorem sectionTensorAddHom_smul_left (r : s.sectionRing U) :
    ∀ (x : sectionModule ℳ U) (y : sectionModule 𝒩 U),
      sectionTensorAddHom ℳ 𝒩 U (r • x) y = r • sectionTensorAddHom ℳ 𝒩 U x y :=
  fun x y => (sectionTensorAddHom_smul_aux ℳ 𝒩 U r x y).2

/-! ### The comparison -/

/-- **The comparison of the graded modules of sections as a bilinear map over the section
ring.** -/
noncomputable def sectionTensorBilinear :
    sectionModule ℳ U →ₗ[s.sectionRing U] sectionModule 𝒩 U →ₗ[s.sectionRing U]
      sectionModule (s.leftGradedTensor ℳ 𝒩) U where
  toFun x :=
    { toFun := sectionTensorAddHom ℳ 𝒩 U x
      map_add' := map_add _
      map_smul' := fun r y => sectionTensorAddHom_smul_right ℳ 𝒩 U r x y }
  map_add' x x' := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add,
      AddMonoidHom.add_apply]
  map_smul' r x := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
    exact sectionTensorAddHom_smul_left ℳ 𝒩 U r x y

/-- **The comparison `Γ(U, ℳ) ⊗_{𝒜(U)} Γ(U, 𝒩) ⟶ Γ(U, ℳ ⊗_𝒜 𝒩)` of graded modules of
sections**, linear over the graded ring of sections of `𝒜` over `U`. -/
noncomputable def sectionTensorMap :
    sectionModule ℳ U ⊗[s.sectionRing U] sectionModule 𝒩 U →ₗ[s.sectionRing U]
      sectionModule (s.leftGradedTensor ℳ 𝒩) U :=
  TensorProduct.lift (sectionTensorBilinear ℳ 𝒩 U)

/-- **The comparison sends `x ⊗ y` to `x ⊗ y`**: the pure tensor of a homogeneous section of
degree `p` of `ℳ` and one of degree `q` of `𝒩` to the local section `x ⊗ y` of degree `p + q`
of `ℳ ⊗_𝒜 𝒩`. -/
theorem sectionTensorMap_tmul_of_of (p q : ℤ) (x : sectionModulePieces ℳ U p)
    (y : sectionModulePieces 𝒩 U q) :
    sectionTensorMap ℳ 𝒩 U (DirectSum.of _ p x ⊗ₜ[s.sectionRing U] DirectSum.of _ q y)
      = DirectSum.of (sectionModulePieces (s.leftGradedTensor ℳ 𝒩) U) (p + q)
          (sectionTmul ℳ 𝒩 U p q x y) := by
  rw [sectionTensorMap, TensorProduct.lift.tmul]
  exact sectionTensorAddHom_of_of ℳ 𝒩 U p q x y

/-- **The comparison preserves degrees**: it carries the degree-`k` piece of the tensor grading
of `Γ(U, ℳ) ⊗_{𝒜(U)} Γ(U, 𝒩)` into the degree-`k` homogeneous sections of `ℳ ⊗_𝒜 𝒩`. -/
theorem sectionTensorMap_mem_grading (k : ℤ)
    (z : sectionModule ℳ U ⊗[s.sectionRing U] sectionModule 𝒩 U)
    (hz : z ∈ tensorGrading (sectionModuleGrading ℳ U) (sectionModuleGrading 𝒩 U) k) :
    sectionTensorMap ℳ 𝒩 U z ∈ sectionModuleGrading (s.leftGradedTensor ℳ 𝒩) U k :=
  map_mem_of_mem_tensorGrading _ _ _ (sectionTensorMap ℳ 𝒩 U) k
    (fun i j hij m hm n hn => by
      obtain ⟨x, rfl⟩ := (mem_sectionModuleGrading_iff ℳ U m).mp hm
      obtain ⟨y, rfl⟩ := (mem_sectionModuleGrading_iff 𝒩 U n).mp hn
      rw [sectionTensorMap_tmul_of_of]
      exact hij ▸ mem_sectionModuleGrading_of (s.leftGradedTensor ℳ 𝒩) U _) hz

/-- **A linear map out of `Γ(U, ℳ) ⊗_{𝒜(U)} Γ(U, 𝒩)` is determined by its values on the pure
tensors of homogeneous sections.** Together with
`Stacks.RelativeProj.Situation.sectionTensorMap_tmul_of_of` this says that the comparison is the
only linear map sending `x ⊗ y` to the local section `x ⊗ y`. -/
theorem tensorSection_linearMap_ext {Q : Type u} [AddCommGroup Q]
    [Module (s.sectionRing U) Q]
    {f g : sectionModule ℳ U ⊗[s.sectionRing U] sectionModule 𝒩 U →ₗ[s.sectionRing U] Q}
    (h : ∀ (p q : ℤ) (x : sectionModulePieces ℳ U p) (y : sectionModulePieces 𝒩 U q),
      f (DirectSum.of _ p x ⊗ₜ[s.sectionRing U] DirectSum.of _ q y)
        = g (DirectSum.of _ p x ⊗ₜ[s.sectionRing U] DirectSum.of _ q y)) :
    f = g := by
  refine TensorProduct.ext' fun z => ?_
  induction z using DirectSum.induction_on with
  | zero => intro w; simp
  | of p x =>
      intro w
      induction w using DirectSum.induction_on with
      | zero => simp
      | of q y => exact h p q x y
      | add w w' hw hw' => rw [TensorProduct.tmul_add, map_add, map_add, hw, hw']
  | add z z' hz hz' =>
      intro w
      rw [TensorProduct.add_tmul, map_add, map_add, hz, hz']

/-! ### Compatibility with restriction to a smaller open of the base

This is the module-level half of the compatibility that gluing the chart morphisms of property
(6) of Tag 01O7 needs: the comparison commutes with the restriction maps of the graded modules
of sections, so the two readings of a product `x ⊗ y` over the smaller open agree. -/

section Restriction

variable {V W : s.base.Opens}

/-- **Restricting a product `x ⊗ y` of homogeneous sections to a smaller open of the base gives
the product of the restrictions.** This is the naturality of the canonical balanced family. -/
theorem sectionModuleRestrictPiece_sectionTmul (h : V ≤ W) (p q : ℤ)
    (x : sectionModulePieces ℳ W p) (y : sectionModulePieces 𝒩 W q) :
    sectionModuleRestrictPiece (s.leftGradedTensor ℳ 𝒩) h (p + q)
        (sectionTmul ℳ 𝒩 W p q x y)
      = sectionTmul ℳ 𝒩 V p q (sectionModuleRestrictPiece ℳ h p x)
          (sectionModuleRestrictPiece 𝒩 h q y) :=
  ((tmulBalanced (ℳ.toGradedModule s.mul_comm) 𝒩 (p + q)).app ⟨(p, q), rfl⟩).naturality
    (homOfLE h).op x y

/-- **The comparison of the graded modules of sections commutes with restriction to a smaller
open of the base.** -/
theorem sectionModuleRestrict_sectionTensorAddHom (h : V ≤ W) :
    ∀ (z : sectionModule ℳ W) (w : sectionModule 𝒩 W),
      sectionModuleRestrict (s.leftGradedTensor ℳ 𝒩) h (sectionTensorAddHom ℳ 𝒩 W z w)
        = sectionTensorAddHom ℳ 𝒩 V (sectionModuleRestrict ℳ h z)
            (sectionModuleRestrict 𝒩 h w) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => intro w; simp
  | of p x =>
      intro w
      induction w using DirectSum.induction_on with
      | zero => simp
      | of q y =>
          rw [sectionTensorAddHom_of_of, sectionModuleRestrict_of, sectionModuleRestrict_of,
            sectionModuleRestrict_of, sectionTensorAddHom_of_of,
            sectionModuleRestrictPiece_sectionTmul]
      | add w w' hw hw' => rw [map_add, map_add, hw, hw', map_add, map_add]
  | add z z' hz hz' =>
      intro w
      have e₁ : sectionTensorAddHom ℳ 𝒩 W (z + z') w
          = sectionTensorAddHom ℳ 𝒩 W z w + sectionTensorAddHom ℳ 𝒩 W z' w :=
        congrArg (fun f : sectionModule 𝒩 W →+ sectionModule (s.leftGradedTensor ℳ 𝒩) W => f w)
          ((sectionTensorAddHom ℳ 𝒩 W).map_add z z')
      have e₂ : sectionTensorAddHom ℳ 𝒩 V (sectionModuleRestrict ℳ h (z + z'))
            (sectionModuleRestrict 𝒩 h w)
          = sectionTensorAddHom ℳ 𝒩 V (sectionModuleRestrict ℳ h z)
              (sectionModuleRestrict 𝒩 h w)
            + sectionTensorAddHom ℳ 𝒩 V (sectionModuleRestrict ℳ h z')
              (sectionModuleRestrict 𝒩 h w) :=
        (congrArg (fun a => sectionTensorAddHom ℳ 𝒩 V a (sectionModuleRestrict 𝒩 h w))
            ((sectionModuleRestrict ℳ h).map_add z z')).trans
          (congrArg
            (fun f : sectionModule 𝒩 V →+ sectionModule (s.leftGradedTensor ℳ 𝒩) V =>
              f (sectionModuleRestrict 𝒩 h w))
            ((sectionTensorAddHom ℳ 𝒩 V).map_add (sectionModuleRestrict ℳ h z)
              (sectionModuleRestrict ℳ h z')))
      exact (congrArg (sectionModuleRestrict (s.leftGradedTensor ℳ 𝒩) h) e₁).trans
        (((sectionModuleRestrict (s.leftGradedTensor ℳ 𝒩) h).map_add _ _).trans
          ((congrArg₂ (· + ·) (hz w) (hz' w)).trans e₂.symm))

/-- **Restriction of the tensor products of the graded modules of sections**, semilinear over
restriction of the section rings: `z ⊗ w` restricts to the tensor of the restrictions. The
balancing needed to descend it to the tensor product is the semilinearity of restriction of the
graded modules of sections. -/
noncomputable def restrictTensorₛₗ (h : V ≤ W) :
    sectionModule ℳ W ⊗[s.sectionRing W] sectionModule 𝒩 W
      →ₛₗ[s.sectionRingRestrict V W h]
      sectionModule ℳ V ⊗[s.sectionRing V] sectionModule 𝒩 V where
  toFun := TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun z => AddMonoidHom.mk'
        (fun w => sectionModuleRestrict ℳ h z ⊗ₜ[s.sectionRing V] sectionModuleRestrict 𝒩 h w)
        (fun w w' => by rw [map_add, TensorProduct.tmul_add]))
      (fun z z' => AddMonoidHom.ext fun w => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        rw [map_add, TensorProduct.add_tmul]))
    (fun r z w => by
      simp only [AddMonoidHom.mk'_apply]
      rw [sectionModuleRestrict_smul, sectionModuleRestrict_smul, TensorProduct.smul_tmul])
  map_add' := map_add _
  map_smul' := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [TensorProduct.smul_tmul']
        change TensorProduct.liftAddHom _ _ ((r • a) ⊗ₜ[s.sectionRing W] b) = _
        rw [TensorProduct.liftAddHom_tmul]
        change sectionModuleRestrict ℳ h (r • a) ⊗ₜ[s.sectionRing V]
            sectionModuleRestrict 𝒩 h b = _
        rw [sectionModuleRestrict_smul, ← TensorProduct.smul_tmul']
        rfl
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- The restriction of a pure tensor of sections is the tensor of the restrictions. -/
@[simp]
theorem restrictTensorₛₗ_tmul (h : V ≤ W) (z : sectionModule ℳ W) (w : sectionModule 𝒩 W) :
    restrictTensorₛₗ ℳ 𝒩 h (z ⊗ₜ[s.sectionRing W] w)
      = sectionModuleRestrict ℳ h z ⊗ₜ[s.sectionRing V] sectionModuleRestrict 𝒩 h w := rfl

/-- **The comparison commutes with restriction to a smaller open of the base**, read on the
tensor product over the section ring: a pure tensor of homogeneous sections restricts to the
pure tensor of the restrictions, and the comparison of the smaller open sends it to the
restriction of the comparison over the larger. -/
theorem sectionTensorMap_restrict (h : V ≤ W) (z : sectionModule ℳ W)
    (w : sectionModule 𝒩 W) :
    sectionTensorMap ℳ 𝒩 V
        (sectionModuleRestrict ℳ h z ⊗ₜ[s.sectionRing V] sectionModuleRestrict 𝒩 h w)
      = sectionModuleRestrict (s.leftGradedTensor ℳ 𝒩) h
          (sectionTensorMap ℳ 𝒩 W (z ⊗ₜ[s.sectionRing W] w)) := by
  rw [sectionTensorMap, sectionTensorMap, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  exact (sectionModuleRestrict_sectionTensorAddHom ℳ 𝒩 h z w).symm

/-- **The comparison commutes with restriction to a smaller open of the base, as an equality of
maps on the whole tensor product.** This is the equation that the glue square of property (6) of
Tag 01O7 reads in the module fibres: it is the hypothesis `huv` of
`Stacks.ProjModuleComparison.fibreMap_localizedModuleMap` for the Tag 01M7 half of the chart
comparison. -/
theorem sectionModuleRestrict_sectionTensorMap (h : V ≤ W)
    (z : sectionModule ℳ W ⊗[s.sectionRing W] sectionModule 𝒩 W) :
    sectionTensorMap ℳ 𝒩 V (restrictTensorₛₗ ℳ 𝒩 h z)
      = sectionModuleRestrict (s.leftGradedTensor ℳ 𝒩) h (sectionTensorMap ℳ 𝒩 W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [restrictTensorₛₗ_tmul, sectionTensorMap_restrict]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', ← map_add, ← map_add]

end Restriction

/-! ### The comparison as a morphism of graded modules -/

/-- The tensor product of the graded modules of sections, as a graded module over the graded ring
of sections: the carrier is `Γ(U, ℳ) ⊗_{𝒜(U)} Γ(U, 𝒩)` and the grading is the tensor
grading. -/
noncomputable def sectionTensorGradedObj :
    Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.{u, u, u}
      (s.sectionRingGrading U) where
  carrier := sectionModule ℳ U ⊗[s.sectionRing U] sectionModule 𝒩 U
  grade := tensorGrading (sectionModuleGrading ℳ U) (sectionModuleGrading 𝒩 U)
  decomposition := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition
    (s.sectionRingGrading U) (sectionModuleGrading ℳ U) (sectionModuleGrading 𝒩 U)
  gradedSMul := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul
    (s.sectionRingGrading U) (sectionModuleGrading ℳ U) (sectionModuleGrading 𝒩 U)

/-- The graded module of sections of a left graded module, as a graded module over the graded
ring of sections. -/
noncomputable def sectionModuleGradedObj
    (𝒬 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra) :
    Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.{u, u, u}
      (s.sectionRingGrading U) where
  carrier := sectionModule 𝒬 U
  grade := sectionModuleGrading 𝒬 U
  decomposition := sectionModuleDecomposition 𝒬 U
  gradedSMul := sectionModuleGradedSMul 𝒬 U

/-- **The comparison of the graded modules of sections, as a morphism of graded modules over the
graded ring of sections of `𝒜` over `U`.** -/
noncomputable def sectionTensorGradedHom :
    sectionTensorGradedObj ℳ 𝒩 U ⟶ sectionModuleGradedObj U (s.leftGradedTensor ℳ 𝒩) where
  toLinearMap := sectionTensorMap ℳ 𝒩 U
  map_grade := sectionTensorMap_mem_grading ℳ 𝒩 U

/-! ### The comparison on a chart

The chart over an affine open `W` of the base carries `ℳ̃(W) = (Γ(W, ℳ))~` on `Proj 𝒜(W)`, so
the comparison of the graded modules of sections induces a comparison of the chart sheaves. -/

/-- **The comparison morphism of property (6) of Tag 01O7 on the chart over an affine open `W` of
the base**: `ℳ̃(W) ⊗ 𝒩̃(W) ⟶ (ℳ ⊗_𝒜 𝒩)~(W)` on `Proj 𝒜(W)`. It is the canonical morphism of
Tag 01MK out of the tensor product of the two chart sheaves, into the sheaf attached to the
tensor product of the graded modules of sections, followed by the morphism of Tag 01M7 induced
by `Stacks.RelativeProj.Situation.sectionTensorMap`. -/
@[ega "II 8.14.2" "special case"]
noncomputable def moduleChartTensorMap (W : s.base.affineOpens) :
    letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition
      (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul
      (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
      (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace)).presheaf,
          (((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).toRingedSpace)).IsSheaf⟩).obj
        ((moduleChart ℳ W))).obj ((moduleChart 𝒩 W))) ⟶
      moduleChart (s.leftGradedTensor ℳ 𝒩) W :=
  letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition
    (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul
    (S := s.sectionRing W.1) (s.sectionRingGrading W.1)
    (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1)
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTensorMap
      (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1) ≫
    Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap
      (s.sectionRingGrading W.1)
      (tensorGrading (sectionModuleGrading ℳ W.1) (sectionModuleGrading 𝒩 W.1))
      (sectionModuleGrading (s.leftGradedTensor ℳ 𝒩) W.1)
      (sectionTensorMap ℳ 𝒩 W.1) (sectionTensorMap_mem_grading ℳ 𝒩 W.1)

/-! ### The comparison restricted to a chart

The two sheaves of property (6) of Tag 01O7 restrict on the chart over `W` to the tensor
product of the chart sheaves and to `(ℳ ⊗_𝒜 𝒩)~(W)`, so the chart morphism transports to a
morphism of their restrictions. That family, one member per affine open of the base, is the
datum that `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`
consumes. -/

section Chart

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]

/-- **The comparison morphism of property (6) of Tag 01O7, restricted to the chart over an
affine open `W` of the base**: a morphism
`(ℳ̃ ⊗ 𝒩̃)|_{chart W} ⟶ (ℳ ⊗_𝒜 𝒩)~|_{chart W}` on `Proj 𝒜(W)`.

Restriction to an open subscheme commutes with the tensor product of sheaves of modules by
`Stacks.ProjectionFormula.restrictTensorIso`, and `ℳ̃` and `𝒩̃` restrict on the chart to the
chart sheaves by `Stacks.RelativeProj.Situation.moduleSheafChartIso`; so the restriction of
`ℳ̃ ⊗ 𝒩̃` is the tensor product of the chart sheaves, where
`Stacks.RelativeProj.Situation.moduleChartTensorMap` applies. -/
@[ega "II 8.14.2" "special case"]
noncomputable def moduleSheafTensorChartMap (W : s.base.affineOpens) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor (relativeProjChart s W)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((relativeProj s).toRingedSpace)).presheaf,
            (((relativeProj s).toRingedSpace)).IsSheaf⟩).obj ((moduleSheaf ℳ))).obj
          ((moduleSheaf 𝒩)))) ⟶
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (relativeProjChart s W)).obj
        (s.tensorModuleSheaf ℳ 𝒩) :=
  (Stacks.ProjectionFormula.restrictTensorIso (relativeProjChart s W)
        (moduleSheaf ℳ) (moduleSheaf 𝒩)).hom ≫
    (Stacks.ProjectionFormula.tensorSheafIsoMk (moduleSheafChartIso ℳ W)
        (moduleSheafChartIso 𝒩 W)).hom ≫
      moduleChartTensorMap ℳ 𝒩 W ≫ (moduleSheafChartIso (s.leftGradedTensor ℳ 𝒩) W).inv

end Chart

end Stacks.RelativeProj.Situation

end
