module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraEpiDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# A trivialization of a tensor product carries a product of generators to a local unit

Let `O` be a sheaf of commutative rings on a site, let `M` and `N` be sheaves of `O`-modules and
let `s ∈ M(U)`, `t ∈ N(U)` be sections over an object `U` which generate `M` and `N` over `U`:
every section of `M` over an object `W ⟶ U` is a multiple of the restriction of `s`, and likewise
for `N` and `t`.  If `μ : M ⊗ N ≅ O` is any isomorphism of sheaves of modules, then the image
`μ(s ⊗ t) ∈ O(U)` of the section determined by `s` and `t` becomes a unit on a covering sieve
of `U`.

The tensor product sheaf is a sheafification, so its sections over `U` are not in general sums
of pure tensors; but they are so locally.  Writing the section `μ⁻¹(1)` locally as a sum of pure
tensors and each factor as a multiple of the restricted generator exhibits it locally as
`r · (s ⊗ t)`, and applying `μ` gives `1 = r · μ(s ⊗ t)` there.

This is the input from which the Laurent algebra of an invertible module, over a chart
trivializing it, is identified as a ring with a ring of Laurent polynomials: the product of a
generator in degree one and a generator in degree minus one is a unit.

## Main definitions

* `Stacks.SheafOfModules.IsGeneratorOver`: a section generating a sheaf of modules over an
  object.

## Main results

* `Stacks.SheafOfModules.exists_mem_isUnit_map_tensorSectionsAt`: **`μ(s ⊗ t)` is a unit on a
  covering sieve.**

## References

* [Stacks Project, Tag 01CR](https://stacks.math.columbia.edu/tag/01CR)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf Tensor.sheafTensor
attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The restriction of a section of a sheaf of modules along an arrow, as an element of the
module of sections over the source (rather than of its restriction of scalars). -/
abbrev sectionMap (M : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {U W : C} (f : W ⟶ U) (x : M.val.obj (op U)) : M.val.obj (op W) :=
  M.val.map f.op x

/-- **A section `s` of `M` over `U` generates `M` over `U`**: every section of `M` over an object
`W` mapping to `U` is a multiple of the restriction of `s` to `W`. -/
def IsGeneratorOver (M : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {U : C} (s : M.val.obj (op U)) : Prop :=
  ∀ ⦃W : C⦄ (f : W ⟶ U) (x : M.val.obj (op W)),
    ∃ r : O.obj (op W), x = r • sectionMap O hO M f s

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **A trivialization of `M` over the slice of `U` makes the image of `1` a generator of `M`
over `U`.** -/
theorem isGeneratorOver_of_iso
    (M : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) {U : C}
    (e : M.over U ≅
      _root_.SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U)) :
    IsGeneratorOver O hO M (show M.val.obj (op U) from
      e.inv.val.app (op (Over.mk (𝟙 U))) (show O.obj (op U) from 1)) := by
  intro W f x
  let Y : Over U := Over.mk f
  let g : Y ⟶ Over.mk (𝟙 U) := Over.homMk f
  let r : O.obj (op W) := e.hom.val.app (op Y) x
  refine ⟨r, ?_⟩
  have hx : x = e.inv.val.app (op Y) (show O.obj (op W) from r * 1) := by
    rw [mul_one]
    show x = (e.hom ≫ e.inv).val.app (op Y) x
    rw [e.hom_inv_id]
    rfl
  have h1 : (show O.obj (op W) from 1) =
      (_root_.SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U)).val.map
        g.op (show O.obj (op U) from 1) :=
    ((O.map f.op).hom.map_one).symm
  have hnat := PresheafOfModules.naturality_apply e.inv.val g.op (show O.obj (op U) from 1)
  refine hx.trans ?_
  refine ((e.inv.val.app (op Y)).hom.map_smul r (show O.obj (op W) from 1)).trans ?_
  congr 1
  rw [h1]
  exact hnat

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **The inverse of a trivialization over a slice is multiplication by the restriction of the
generator.** -/
theorem iso_inv_app_eq_smul
    (M : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) {U W : C}
    (e : M.over U ≅
      _root_.SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U))
    (f : W ⟶ U) (r : O.obj (op W)) :
    e.inv.val.app (op (Over.mk f)) r = r • sectionMap O hO M f (show M.val.obj (op U) from
      e.inv.val.app (op (Over.mk (𝟙 U))) (show O.obj (op U) from 1)) := by
  let g : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  have h1 : (show O.obj (op W) from 1) =
      (_root_.SheafOfModules.unit ((TensorSheafification.structureSheaf O hO).over U)).val.map
        g.op (show O.obj (op U) from 1) :=
    ((O.map f.op).hom.map_one).symm
  have hnat := PresheafOfModules.naturality_apply e.inv.val g.op (show O.obj (op U) from 1)
  have hr : e.inv.val.app (op (Over.mk f)) r =
      e.inv.val.app (op (Over.mk f)) (show O.obj (op W) from r * 1) := by
    rw [mul_one]
  refine hr.trans (((e.inv.val.app (op (Over.mk f))).hom.map_smul r
    (show O.obj (op W) from 1)).trans ?_)
  congr 1
  rw [h1]
  exact hnat

/-- The section determined by a pair of sections is compatible with restriction. -/
theorem map_tensorSectionsAt
    (M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {U W : C} (f : W ⟶ U) (s : M.val.obj (op U)) (t : N.val.obj (op U)) :
    (((Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
        (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N).val.map f.op
        (tensorSectionsAt O hO (op U) M N s t) =
      tensorSectionsAt O hO (op W) M N (M.val.map f.op s) (N.val.map f.op t) := by
  exact (PresheafOfModules.naturality_apply
    (TensorSheafification.toSheafify O hO (M.val ⊗ N.val)) f.op (s ⊗ₜ[O.obj (op U)] t)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- A section of the objectwise tensor product of two modules each generated by one element is a
multiple of the pure tensor of the generators. -/
theorem exists_eq_smul_tmul_of_isGeneratorOver
    (M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {U W : C} (f : W ⟶ U) {s : M.val.obj (op U)} {t : N.val.obj (op U)}
    (hs : IsGeneratorOver O hO M s) (ht : IsGeneratorOver O hO N t)
    (y : M.val.obj (op W) ⊗[O.obj (op W)] N.val.obj (op W)) :
    ∃ r : O.obj (op W),
      y = r • (sectionMap O hO M f s ⊗ₜ[O.obj (op W)] sectionMap O hO N f t) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, (zero_smul _ _).symm⟩
  | tmul a b =>
    obtain ⟨r₁, rfl⟩ := hs f a
    obtain ⟨r₂, rfl⟩ := ht f b
    exact ⟨r₁ * r₂, by rw [TensorProduct.smul_tmul_smul]⟩
  | add a b ha hb =>
    obtain ⟨r₁, rfl⟩ := ha
    obtain ⟨r₂, rfl⟩ := hb
    exact ⟨r₁ + r₂, by rw [add_smul]⟩

/-- **A trivialization of a tensor product carries the product of two generators to a local
unit.**  If `s` generates `M` and `t` generates `N` over `U`, and `μ : M ⊗ N ≅ O`, then
`μ(s ⊗ t)` becomes a unit after restriction along every arrow of a covering sieve of `U`. -/
theorem exists_mem_isUnit_map_tensorSectionsAt
    (M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {U : C} {s : M.val.obj (op U)} {t : N.val.obj (op U)}
    (hs : IsGeneratorOver O hO M s) (ht : IsGeneratorOver O hO N t)
    (μ : ((Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
        (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N ≅
      _root_.SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) :
    ∃ S ∈ J U, ∀ ⦃W : C⦄ (f : W ⟶ U), S f →
      IsUnit (O.map f.op (μ.hom.val.app (op U) (tensorSectionsAt O hO (op U) M N s t))) := by
  let T : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) :=
    ((Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
        (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N
  let z : T.val.obj (op U) := μ.inv.val.app (op U) (1 : O.obj (op U))
  have hloc := isLocallySurjective_toSheafify (O := O) hO (M.val ⊗ N.val)
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map
    (TensorSheafification.toSheafify O hO (M.val ⊗ N.val))) z,
    Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map
      (TensorSheafification.toSheafify O hO (M.val ⊗ N.val))) (U := op U) z, ?_⟩
  rintro W f ⟨y, hy⟩
  obtain ⟨r, rfl⟩ := exists_eq_smul_tmul_of_isGeneratorOver O hO M N f hs ht y
  set c := tensorSectionsAt O hO (op U) M N s t with hc
  -- the restriction of `z` is `r` times the restriction of `s ⊗ t`
  have hz : sectionMap O hO T f z = r • sectionMap O hO T f c := by
    have e1 : sectionMap O hO T f c = tensorSectionsAt O hO (op W) M N
        (sectionMap O hO M f s) (sectionMap O hO N f t) :=
      map_tensorSectionsAt O hO M N f s t
    have e2 : (TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app (op W)
        (r • (sectionMap O hO M f s ⊗ₜ[O.obj (op W)] sectionMap O hO N f t)) =
          r • (show T.val.obj (op W) from
            tensorSectionsAt O hO (op W) M N (sectionMap O hO M f s) (sectionMap O hO N f t)) :=
      ((TensorSheafification.toSheafify O hO (M.val ⊗ N.val)).app (op W)).hom.map_smul r _
    rw [e1, ← e2]
    exact hy.symm
  -- apply `μ`
  have hnat : ∀ x : T.val.obj (op U),
      μ.hom.val.app (op W) (sectionMap O hO T f x) = O.map f.op (μ.hom.val.app (op U) x) :=
    PresheafOfModules.naturality_apply μ.hom.val f.op
  have hz1 : μ.hom.val.app (op U) z = (1 : O.obj (op U)) := by
    show (μ.inv ≫ μ.hom).val.app (op U) (1 : O.obj (op U)) = _
    rw [μ.inv_hom_id]
    rfl
  have hsmul : μ.hom.val.app (op W) (r • sectionMap O hO T f c) =
      r * (show O.obj (op W) from μ.hom.val.app (op W) (sectionMap O hO T f c)) :=
    (μ.hom.val.app (op W)).hom.map_smul r _
  have key : r * O.map f.op (show O.obj (op U) from μ.hom.val.app (op U) c) = 1 := by
    rw [← hnat, ← hsmul, ← hz, hnat, hz1]
    exact (O.map f.op).hom.map_one
  exact IsUnit.of_mul_eq_one_right r key

end Stacks.SheafOfModules

end
