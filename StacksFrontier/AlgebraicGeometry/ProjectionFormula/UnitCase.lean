module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.TwistedUnit

/-!
# The projection formula when the module on the target is the structure sheaf

For a morphism of ringed spaces `f : Z ⟶ X`,
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Basic.lean` builds the canonical map

`Stacks.AffineProjectionFormula.projectionFormulaMap f 𝒢 ℋ : f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`

and proves it invertible when `f` is a closed quotient morphism.  This file proves it invertible,
for an **arbitrary** morphism of ringed spaces and with no hypothesis on `𝒢`, when `ℋ` is the
structure sheaf `𝒪_X` — and hence whenever `ℋ` is isomorphic to `𝒪_X`.

This is the degree-zero, rank-one case of the projection formula of [Stacks, Tag 01E8], whose
own proof reads *"This is clear when `ℰ = 𝒪_Y^{⊕ n}`, and follows in general by working locally
on `Y`"*: the statement below is that sentence at `n = 1`.

## The argument

Write `η`, `ε` for the unit and counit of `f^* ⊣ f_*`, `c` for the pullback tensor comparison of
[Stacks, Tag 01CD], `ρ` for the right unit constraint `M ⊗ 𝒪 ≅ M` of the sheaf tensor product,
and `ε₀ : f^*𝒪_X ⟶ 𝒪_Z` for Mathlib's `SheafOfModules.pullbackObjUnitToUnit`.  The composite

`f_*𝒢 ⊗ 𝒪_X --projectionFormulaMap--> f_*(𝒢 ⊗ f^*𝒪_X) --f_*(𝟙 ⊗ ε₀)--> f_*(𝒢 ⊗ 𝒪_Z)
   --f_*ρ--> f_*𝒢`

is `ρ` on `f_*𝒢` (`projectionFormulaMap_comp_structureUnitorRight`), and each of its three later
factors is invertible — `ε₀` for any morphism of ringed spaces, because `Opens.map f` is final.
So the first factor is invertible too.

The identity itself is three moves.  Writing the projection-formula map through the adjunction,
its argument is `c ≫ (ε ⊗ 𝟙)`; naturality of `ρ` moves `ε` out past the unit constraint; what is
left is the coherence of the pullback tensor comparison with the **right** unit constraints
(`comparisonTranspose_comp_structureUnitorRight`, proved on sections exactly as
`Stacks.AffineProjectionFormula.comparisonTranspose_comp_structureUnitor` is for the left ones);
and that leaves `η_{f_*𝒢} ≫ f_*ε`, which is the triangle identity of the adjunction.  So the only
new mathematics is the right-hand coherence, and the invertibility is the triangle identity.

## Main definitions

* `Stacks.AffineProjectionFormula.structureUnitorRight`: the right unit constraint
  `M ⊗_{𝒪_W} 𝒪_W ≅ M`, with its type declared at the
  `Stacks.RingedSpace.structureRingSheaf` spelling.

## Main results

* `Stacks.SheafOfModules.Invertible.toSheafify_tensorProductRightUnitor`: the right unit
  constraint on the sheafification-unit image of a pure tensor, the companion of
  `toSheafify_tensorProductLeftUnitor`.
* `Stacks.AffineProjectionFormula.comparisonTranspose_comp_structureUnitorRight`: **the
  coherence** of the pullback tensor comparison with the right unit constraints.
* `Stacks.AffineProjectionFormula.projectionFormulaMap_comp_structureUnitorRight`: the
  projection-formula map at `ℋ = 𝒪_X`, followed by the two canonical isomorphisms, is the right
  unit constraint.
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_structureModule`: **the projection
  formula at `ℋ = 𝒪_X`, for an arbitrary morphism of ringed spaces.**
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_iso` and
  `isIso_projectionFormulaMap_of_iso_structureModule`: invertibility depends only on the
  isomorphism class of `ℋ`, so it holds whenever `ℋ ≅ 𝒪_X`.

## Implementation notes

**Place in Tag 01E8.** What is proved here is the degree-zero projection formula at the unit
`ℋ = 𝒪_X`, the starting point of the source's argument for [Stacks, Tag 01E8]. Additivity in `ℋ`
(`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_biproduct`, in
`ProjectionFormula/FiniteFree.lean`) passes to `𝒪_X^{⊕ n}`, and locality on the target
(`ProjectionFormula/LocalityRingedSpace.lean`) to a finite locally free module, which is
`isIso_projectionFormulaMap_of_isFiniteLocallyFree_class_ringedSpace` (in the namespace
`Stacks.AffineProjectionFormula`).
The tag itself, in every degree and in `D⁺`, for an arbitrary morphism of ringed spaces, is
`Stacks.ProjectionFormula.higherDirectImageProjectionFormulaRingedSpaceIso` and
`Stacks.ProjectionFormula.derivedPushforwardTensorRightRingedSpacePlusIso` in
`ProjectionFormula/HigherDirectImageRingedSpace.lean`.

**The right unit constraint is a declared return type, as the left one is.** The generic
`Stacks.SheafOfModules.Invertible.tensorProductRightUnitor` is stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`; `structureUnitorRight` re-declares it
  with its codomain at
`Stacks.RingedSpace.structureRingSheaf`, which is the reducible abbreviation carrying the
`CommRing` instance the `TensorProduct` lemmas need.  This is the same cure, for the same
reason, as `Stacks.AffineProjectionFormula.structureUnitor`.

**Naturality of the right unit constraint had to be proved, and it is proved on sections**
rather than from naturality of the presheaf-level constraint and of the sheafification counit.
The section-level route reuses `structureUnitorRight_tensorSheafUnit_tmul` and
`Stacks.RingedSpace.tensorSheaf_map_unit_tmul`, which are the two lemmas the coherence below
needs anyway; no new infrastructure is introduced for it.

**`IsIso` is supplied in argument position, never as an instance binder.**
`projectionFormulaMap` is a semireducible definition, so `IsIso (projectionFormulaMap …)` never
matches `IsIso (?f ≫ ?g)` during instance search; `CategoryTheory.IsIso.of_isIso_comp_right` and
`of_isIso_comp_left` are therefore applied with their arguments and both `IsIso` witnesses
written out.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf PresheafOfModules.tensorObj
  Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open PresheafOfModules (Hom)
open scoped TensorProduct
open scoped CategoryTheory.Prod

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-- **The right unit constraint of the sheaf tensor product, on sections**: it sends the product
of a section `m` with the unit section to `m`.  This is the companion of
`Stacks.SheafOfModules.Invertible.toSheafify_tensorProductLeftUnitor`, proved the same way: the
sheafification unit followed by the constraint is the presheaf-level constraint, and there the
right unitor of `ModuleCat` sends `m ⊗ₜ 1` to `1 • m`. -/
theorem toSheafify_tensorProductRightUnitor
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (U : Cᵒᵖ)
    (m : M.val.obj U) :
    Hom.app (tensorProductRightUnitor O hO M).hom.val U
        (Hom.app (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          ((PresheafOfModules.tensorObj (O := O) (M.val) ((_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO)).val)))) U
          (m ⊗ₜ unitOne U)) = m := by
  have rightUnitorApp : ∀ {R : CommRingCat.{w}} (N : ModuleCat.{w} R) (z : N),
      ConcreteCategory.hom (MonoidalCategory.rightUnitor N).hom (z ⊗ₜ[R] (1 : R)) = z :=
    fun N z => (ModuleCat.MonoidalCategory.rightUnitor_hom_apply z 1).trans (one_smul _ z)
  have key : Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        ((PresheafOfModules.tensorObj (O := O) (M.val) ((_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO)).val))) ≫
        (tensorProductRightUnitor O hO M).hom.val = (MonoidalCategory.rightUnitor M.val).hom :=
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit_comp_map_eq_iff
      (tensorProductRightUnitor O hO M).hom (MonoidalCategory.rightUnitor M.val).hom).mpr rfl
  exact (PresheafOfModules.hom_congr_apply key U (m ⊗ₜ unitOne U)).trans (rightUnitorApp _ m)

end Stacks.SheafOfModules.Invertible

namespace Stacks.AffineProjectionFormula

universe u'

/-- The right unit constraint `M ⊗_{𝒪_W} 𝒪_W ≅ M` of the sheaf tensor product, at the
`Stacks.RingedSpace.structureRingSheaf` spelling. -/
abbrev structureUnitorRight {W : RingedSpace.{u', u'}}
    (M : SheafOfModules.{u'} (structureRingSheaf W)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
      W.sheaf))).obj (M, structureModule W) ≅ M :=
  Stacks.SheafOfModules.Invertible.tensorProductRightUnitor W.presheaf
    (structureSheafRing W).property M

/-- **The right unit constraint on the sheafification-unit image of a pure tensor**: it carries
`m ⊗ a` to `a • m`.  The first tensor factor's partner is a free variable `a'` named by `ha`, as
in `Stacks.AffineProjectionFormula.structureUnitor_tensorSheafUnit_tmul`, so that the lemma
applies without a rewrite having to locate the closed term the computation produces. -/
theorem structureUnitorRight_tensorSheafUnit_tmul {W : RingedSpace.{u', u'}}
    (M : SheafOfModules.{u'} (structureRingSheaf W)) (U : (Opens W.carrier)ᵒᵖ)
    (a : ToType ((structureRingSheaf W).obj.obj U)) (m : ToType (M.val.obj U))
    (a' : ToType ((structureModule W).val.obj U))
    (ha : a' = Stacks.SheafOfModules.toUnit U a) :
    Hom.app (structureUnitorRight M).hom.val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (W)) (𝟙 (Stacks.RingedSpace.structureRingSheaf
          (W)).obj)).unit.app (PresheafOfModules.tensorObj (O := (W).presheaf) (M).val
          ((structureModule W)).val)) U (m ⊗ₜ a')) = a • m := by
  rw [ha]
  let : TensorProduct.CompatibleSMul (W.presheaf.obj U)
      ((structureRingSheaf W).obj.obj U) (M.val.obj U) ((structureModule W).val.obj U) := by
    change TensorProduct.CompatibleSMul (W.presheaf.obj U)
      (W.presheaf.obj U) (M.val.obj U) ((structureModule W).val.obj U)
    infer_instance
  have h1 : a • Stacks.SheafOfModules.unitOne (S := structureRingSheaf W) U
      = Stacks.SheafOfModules.toUnit (S := structureRingSheaf W) U a :=
    (Stacks.SheafOfModules.toUnit_smul U a 1).trans (by rw [mul_one])
  rw [← h1]
  refine (congrArg (fun tensorValue => Hom.app (structureUnitorRight M).hom.val U
    (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf W)
      (𝟙 (structureRingSheaf W).obj)).unit.app
        (PresheafOfModules.tensorObj (O := W.presheaf) M.val (structureModule W).val))
      U tensorValue))
    (TensorProduct.smul_tmul (R := W.presheaf.obj U) (a : W.presheaf.obj U) m
      (Stacks.SheafOfModules.unitOne (S := structureRingSheaf W) U)).symm).trans ?_
  exact Stacks.SheafOfModules.Invertible.toSheafify_tensorProductRightUnitor
    W.presheaf (structureSheafRing W).property M U (a • m)

/-- **Naturality of the right unit constraint** in the module argument.  On the unit image of
`m ⊗ a` both sides are `a • u m`, the right-hand one because `u` is linear on sections. -/
theorem structureUnitorRight_naturality {W : RingedSpace.{u', u'}}
    {M N : SheafOfModules.{u'} (structureRingSheaf W)} (u : M ⟶ N) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
      W.sheaf))).map (u ×ₘ 𝟙 (structureModule W)) ≫ (structureUnitorRight N).hom =
      (structureUnitorRight M).hom ≫ u := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U m a => ?_)
  have key : ∀ (m : ToType (M.val.obj U)) (a : ToType ((structureModule W).val.obj U)),
      Hom.app (structureUnitorRight N).hom.val U
          (Hom.app (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} W.sheaf))).map
            (u ×ₘ 𝟙 (structureModule W))).val U
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (W))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (W)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (W).presheaf) (M).val ((structureModule W)).val)) U
              (m ⊗ₜ a)))
        = Hom.app u.val U
            (Hom.app (structureUnitorRight M).hom.val U
              (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (W))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (W)).obj)).unit.app
                (PresheafOfModules.tensorObj (O := (W).presheaf) (M).val ((structureModule W)).val))
                U (m ⊗ₜ a))) := by
    intro m a
    have b1 : Hom.app (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} W.sheaf))).map
        (u ×ₘ 𝟙 (structureModule W))).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (W))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (W)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (W).presheaf) (M).val ((structureModule W)).val)) U
            (m ⊗ₜ a))
        = Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (W)) (𝟙 (Stacks.RingedSpace.structureRingSheaf
          (W)).obj)).unit.app (PresheafOfModules.tensorObj (O := (W).presheaf) (N).val
          ((structureModule W)).val)) U
            (Hom.app u.val U m ⊗ₜ a) :=
      tensorSheaf_map_unit_tmul W u (𝟙 (structureModule W)) U _ _
    have b2 := structureUnitorRight_tensorSheafUnit_tmul N U
      (a : ToType ((structureRingSheaf W).obj.obj U)) (Hom.app u.val U m) a rfl
    have b3 := structureUnitorRight_tensorSheafUnit_tmul M U
      (a : ToType ((structureRingSheaf W).obj.obj U)) m a rfl
    rw [b1, b2, b3]
    exact ((Hom.app u.val U).hom.map_smul a m).symm
  exact key m a

/-- The sheaf tensor product functor sends `𝟙 A ×ₘ g` to an isomorphism when `g` is one. -/
private theorem isIso_tensor_map_id_prod {W : RingedSpace.{u', u'}}
    (A : SheafOfModules.{u'} (structureRingSheaf W))
    {B B' : SheafOfModules.{u'} (structureRingSheaf W)} (g : B ⟶ B') [IsIso g] :
    IsIso (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} W.sheaf))).map (𝟙 A ×ₘ g)) :=
  have : IsIso (𝟙 A ×ₘ g) := ((Iso.refl A).prod (asIso g)).isIso_hom
  Functor.map_isIso _ _

section Coherence

variable {X Z : RingedSpace.{u', u'}} (f : Z ⟶ X)

/-- **The pullback tensor comparison is compatible with the right unit constraints.**  In
transposed form: the adjoint transpose of `c : f^*(A ⊗ 𝒪_X) ⟶ f^*A ⊗ f^*𝒪_X`, followed by
`f^*𝒪_X ⟶ 𝒪_Z` in the second factor and then the right unit constraint on `Z`, is the right unit
constraint on `X` followed by the unit of `f^* ⊣ f_*`.

A morphism out of a sheaf tensor product is determined by its effect on the sheafification-unit
images of pure tensors, and on `x ⊗ y` both sides are `f^♯y · η x`: on the left by
`Stacks.RingedSpace.comparisonTranspose_unit_tmul` and
`Stacks.AffineProjectionFormula.pullbackStructureComparison_pullbackUnit`, on the right by
`Stacks.RingedSpace.pullbackUnit_smul`.  This is the mirror of
`Stacks.AffineProjectionFormula.comparisonTranspose_comp_structureUnitor`. -/
theorem comparisonTranspose_comp_structureUnitorRight
    (A : SheafOfModules.{u'} (structureRingSheaf X)) :
    comparisonTranspose f A (structureModule X) ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
            Z.sheaf))).map
              (𝟙 ((pullbackFunctor f).obj A) ×ₘ pullbackStructureComparison f) ≫
            (structureUnitorRight ((pullbackFunctor f).obj A)).hom) =
      (structureUnitorRight A).hom ≫ (pullbackAdjunction f).unit.app A := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y => ?_)
  have key : ∀ (x : ToType (A.val.obj U)) (y : ToType ((structureModule X).val.obj U)),
      Hom.app (structureUnitorRight ((pullbackFunctor f).obj A)).hom.val
          ((opensMap f).op.obj U)
          (Hom.app (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} Z.sheaf))).map
              (𝟙 ((pullbackFunctor f).obj A) ×ₘ pullbackStructureComparison f)).val
            ((opensMap f).op.obj U)
            (Hom.app (comparisonTranspose f A (structureModule X)).val U
              (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (X))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
                (PresheafOfModules.tensorObj (O := (X).presheaf) (A).val ((structureModule X)).val))
                U (x ⊗ₜ y))))
        = Hom.app ((pullbackAdjunction f).unit.app A).val U
            (Hom.app (structureUnitorRight A).hom.val U
              (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (X))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
                (PresheafOfModules.tensorObj (O := (X).presheaf) (A).val ((structureModule X)).val))
                U (x ⊗ₜ y))) := by
    intro x y
    have a1 : Hom.app (comparisonTranspose f A (structureModule X)).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (X))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (X).presheaf) (A).val ((structureModule X)).val)) U
            (x ⊗ₜ y))
        = Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Z)) (𝟙 (Stacks.RingedSpace.structureRingSheaf
          (Z)).obj)).unit.app (PresheafOfModules.tensorObj (O := (Z).presheaf)
          (((pullbackFunctor f).obj A)).val (((pullbackFunctor f).obj (structureModule X))).val))
          ((opensMap f).op.obj U)
            (pullbackUnit f A U x ⊗ₜ pullbackUnit f (structureModule X) U y) :=
      comparisonTranspose_unit_tmul f A (structureModule X) U x y
    have a2 : Hom.app (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} Z.sheaf))).map
            (𝟙 ((pullbackFunctor f).obj A) ×ₘ pullbackStructureComparison f)).val
          ((opensMap f).op.obj U)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Z))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Z)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Z).presheaf) (((pullbackFunctor f).obj A)).val
            (((pullbackFunctor f).obj (structureModule X))).val)) ((opensMap f).op.obj U)
            (pullbackUnit f A U x ⊗ₜ pullbackUnit f (structureModule X) U y))
        = Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Z)) (𝟙 (Stacks.RingedSpace.structureRingSheaf
          (Z)).obj)).unit.app (PresheafOfModules.tensorObj (O := (Z).presheaf)
          (((pullbackFunctor f).obj A)).val ((structureModule Z)).val))
            ((opensMap f).op.obj U)
            (pullbackUnit f A U x ⊗ₜ
              Hom.app (pullbackStructureComparison f).val ((opensMap f).op.obj U)
                (pullbackUnit f (structureModule X) U y)) :=
      tensorSheaf_map_unit_tmul Z (𝟙 ((pullbackFunctor f).obj A))
        (pullbackStructureComparison f) ((opensMap f).op.obj U) _ _
    have a3 := structureUnitorRight_tensorSheafUnit_tmul ((pullbackFunctor f).obj A)
      ((opensMap f).op.obj U) (sharp f U y) (pullbackUnit f A U x)
      (Hom.app (pullbackStructureComparison f).val ((opensMap f).op.obj U)
        (pullbackUnit f (structureModule X) U y))
      (pullbackStructureComparison_pullbackUnit f U y)
    have a4 := structureUnitorRight_tensorSheafUnit_tmul A U
      (y : ToType ((structureRingSheaf X).obj.obj U)) x y rfl
    rw [a1, a2, a3, a4]
    exact (pullbackUnit_smul f A U y x).symm
  exact key x y

/-- The projection-formula map as the adjoint transpose of the pullback tensor comparison
followed by the counit of `f^* ⊣ f_*` in the first factor.  This is its definition, with the
component of the comparison bifunctor written out. -/
theorem projectionFormulaMap_eq_homEquiv (G : SheafOfModules.{u'} (structureRingSheaf Z))
    (H : SheafOfModules.{u'} (structureRingSheaf X)) :
    projectionFormulaMap f G H =
      (pullbackAdjunction f).homEquiv _ _
        (comparison f ((pushforwardFunctor f).obj G) H ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
            Z.sheaf))).map ((pullbackAdjunction f).counit.app G ×ₘ
            𝟙 ((pullbackFunctor f).obj H))) := rfl

/-- **The projection-formula map at `ℋ = 𝒪_X` is the right unit constraint**, after the two
canonical identifications `f^*𝒪_X ≅ 𝒪_Z` and `𝒢 ⊗ 𝒪_Z ≅ 𝒢` upstairs.

Naturality of the right unit constraint moves the counit of `f^* ⊣ f_*` out from under the
tensor product; the coherence of the comparison with the right unit constraints then leaves
`η_{f_*𝒢} ≫ f_*ε`, which is the triangle identity. -/
theorem projectionFormulaMap_comp_structureUnitorRight
    (G : SheafOfModules.{u'} (structureRingSheaf Z)) :
    projectionFormulaMap f G (structureModule X) ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
            Z.sheaf))).map (𝟙 G ×ₘ pullbackStructureComparison f) ≫
            (structureUnitorRight G).hom) =
      (structureUnitorRight ((pushforwardFunctor f).obj G)).hom := by
  have hprod :
      ((pullbackAdjunction f).counit.app G ×ₘ
          𝟙 ((pullbackFunctor f).obj (structureModule X))) ≫
        (𝟙 G ×ₘ pullbackStructureComparison f) =
      (𝟙 ((pullbackFunctor f).obj ((pushforwardFunctor f).obj G)) ×ₘ
          pullbackStructureComparison f) ≫
        ((pullbackAdjunction f).counit.app G ×ₘ 𝟙 (structureModule Z)) := by
    simp
  have step1 :
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
        Z.sheaf))).map ((pullbackAdjunction f).counit.app G ×ₘ
            𝟙 ((pullbackFunctor f).obj (structureModule X))) ≫
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
            Z.sheaf))).map (𝟙 G ×ₘ pullbackStructureComparison f) ≫
            (structureUnitorRight G).hom) =
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
          Z.sheaf))).map (𝟙 ((pullbackFunctor f).obj ((pushforwardFunctor f).obj G)) ×ₘ
              pullbackStructureComparison f) ≫
            (structureUnitorRight
              ((pullbackFunctor f).obj ((pushforwardFunctor f).obj G))).hom) ≫
          (pullbackAdjunction f).counit.app G := by
    rw [← Category.assoc, ← Functor.map_comp, hprod, Functor.map_comp, Category.assoc,
      structureUnitorRight_naturality, ← Category.assoc]
  rw [projectionFormulaMap_eq_homEquiv]
  refine ((pullbackAdjunction f).homEquiv_naturality_right
    (comparison f ((pushforwardFunctor f).obj G) (structureModule X) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
        Z.sheaf)).map ((pullbackAdjunction f).counit.app G ×ₘ
          𝟙 ((pullbackFunctor f).obj (structureModule X))))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
      Z.sheaf)).map (𝟙 G ×ₘ pullbackStructureComparison f) ≫
        (structureUnitorRight G).hom)).symm.trans ?_
  rw [Category.assoc, step1, ← Category.assoc, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, homEquiv_comparison,
    comparisonTranspose_comp_structureUnitorRight, Category.assoc,
    Adjunction.right_triangle_components, Category.comp_id]

/-- **`f^*𝒪_X ⟶ 𝒪_Z` is an isomorphism for an arbitrary morphism of ringed spaces**, because
`Opens.map f` is final, being representably flat. -/
instance isIso_pullbackStructureComparison : IsIso (pullbackStructureComparison f) := by
  have : (opensMap f).Final := CategoryTheory.final_of_representablyFlat _
  exact inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)))

/-- **The projection formula at `ℋ = 𝒪_X`, for an arbitrary morphism of ringed spaces and with
no hypothesis on `𝒢`**: the canonical map `f_*𝒢 ⊗_{𝒪_X} 𝒪_X ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*𝒪_X)` is an
isomorphism.

This is the `q = 0`, `ℰ = 𝒪_X` case of [Stacks, Tag 01E8]; it carries the hypothesis that the
module on the target be the structure sheaf, which that tag does not, so no attribute is
attached. -/
theorem isIso_projectionFormulaMap_structureModule
    (G : SheafOfModules.{u'} (structureRingSheaf Z)) :
    IsIso (projectionFormulaMap f G (structureModule X)) := by
  have h2 := isIso_tensor_map_id_prod G (pullbackStructureComparison f)
  have h3 : IsIso (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} Z.sheaf))).map
      (𝟙 G ×ₘ pullbackStructureComparison f) ≫
      (structureUnitorRight G).hom) := inferInstance
  have h4 : IsIso ((pushforwardFunctor f).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
        Z.sheaf))).map (𝟙 G ×ₘ pullbackStructureComparison f) ≫
        (structureUnitorRight G).hom)) := Functor.map_isIso _ _
  have h5 : IsIso (projectionFormulaMap f G (structureModule X) ≫
      (pushforwardFunctor f).map
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
          Z.sheaf))).map (𝟙 G ×ₘ pullbackStructureComparison f) ≫
          (structureUnitorRight G).hom)) := by
    rw [projectionFormulaMap_comp_structureUnitorRight]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (projectionFormulaMap f G (structureModule X))
    ((pushforwardFunctor f).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
        Z.sheaf))).map (𝟙 G ×ₘ pullbackStructureComparison f) ≫
        (structureUnitorRight G).hom)) h4 h5

/-- Invertibility of the projection-formula map depends only on the isomorphism class of the
module on the target: naturality in that argument conjugates the two maps by isomorphisms. -/
theorem isIso_projectionFormulaMap_of_iso
    (G : SheafOfModules.{u'} (structureRingSheaf Z))
    {H H' : SheafOfModules.{u'} (structureRingSheaf X)} (e : H ≅ H')
    (h : IsIso (projectionFormulaMap f G H)) :
    IsIso (projectionFormulaMap f G H') := by
  have hnat := projectionFormulaMap_natural f (𝟙 G) e.hom
  rw [CategoryTheory.Functor.map_id] at hnat
  have ha := isIso_tensor_map_id_prod ((pushforwardFunctor f).obj G) e.hom
  have hd : IsIso ((pushforwardFunctor f).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'}
        Z.sheaf))).map (𝟙 G ×ₘ (pullbackFunctor f).map e.hom))) := by
    have := isIso_tensor_map_id_prod G ((pullbackFunctor f).map e.hom)
    exact Functor.map_isIso _ _
  have hab : IsIso (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', u', u', u', u'} X.sheaf))).map
      (𝟙 ((pushforwardFunctor f).obj G) ×ₘ e.hom) ≫
      projectionFormulaMap f G H') := by
    rw [hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h hd
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ha hab

/-- **The projection formula whenever the module on the target is trivial**, `ℋ ≅ 𝒪_X`.  This is
the local situation a locality argument for the finite locally free case of
[Stacks, Tag 01E8] would reduce to. -/
theorem isIso_projectionFormulaMap_of_iso_structureModule
    (G : SheafOfModules.{u'} (structureRingSheaf Z))
    {H : SheafOfModules.{u'} (structureRingSheaf X)} (e : structureModule X ≅ H) :
    IsIso (projectionFormulaMap f G H) :=
  isIso_projectionFormulaMap_of_iso f G e (isIso_projectionFormulaMap_structureModule f G)

end Coherence

end Stacks.AffineProjectionFormula

end
