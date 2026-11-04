module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalSections

/-!
# The associator of total tensor complexes on local pure tensors

Let `(C, O)` be a ringed site and `A`, `F`, `B` complexes of `O`-modules. The associator
`Tot(Tot(A ⊗_O F) ⊗_O B) ≅ Tot(A ⊗_O Tot(F ⊗_O B))` of the monoidal structure on complexes
re-brackets local pure tensors with no sign: `(a ⊗ x) ⊗ b ↦ a ⊗ (x ⊗ b)`.

## Main results

* `AlgebraicGeometry.RingedSite.ι_tensorComplexAssociator_hom`: the associator on a summand
  `(A^t ⊗ F^p) ⊗ B^r`, as a morphism of sheaves of `O`-modules.
* `AlgebraicGeometry.RingedSite.tensorComplexAssociator_hom_tensorComplexSection`: the associator
  on a local pure tensor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  _root_.SheafOfModules.monoidalCategorySheafTensor

variable (A F B :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The associator of total tensor complexes on a summand.** On `(A^t ⊗_O F^p) ⊗_O B^r` it is
the associator of sheaves of `O`-modules followed by the inclusion of the summand
`A^t ⊗_O (F^p ⊗_O B^r)`. -/
theorem ι_tensorComplexAssociator_hom (t p r s q c : ℤ)
    (hs : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, p) = s)
    (hq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, r) = q)
    (hc : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (s, r) = c)
    (hc' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, q) = c) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        (HomologicalComplex.ιMapBifunctor A F (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t p s hs)).app (B.X r) ≫
      HomologicalComplex.ιMapBifunctor
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj F) B
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) s r c hc ≫
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom.f c =
    (α_ (A.X t) (F.X p) (B.X r)).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (A.X t)).map
        (HomologicalComplex.ιMapBifunctor F B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) p r q hq) ≫
      HomologicalComplex.ιMapBifunctor A
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).obj B)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t q c hc' := by
  have h1 := HomologicalComplex.mapBifunctor₁₂.ι_eq (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A F B (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    t p r s c hs hc
  have h2 := HomologicalComplex.mapBifunctor₂₃.ι_eq (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A F B (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) t p r q c hq hc'
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun φ => φ ≫ (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
    A F B).hom.f c) h1.symm).trans ?_
  refine (HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (F₁₂ := Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (G := Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (F := Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (G₂₃ := Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (curriedAssociatorNatIso _) A F B (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    t p r c _).trans ?_
  exact congrArg (fun φ => (α_ (A.X t) (F.X p) (B.X r)).hom ≫ φ) h2

variable {A F B}

/-- The sheafification unit carries the presheaf pure tensor of a local pure tensor of
`Tot(A ⊗_O F)` with a section of `B^r` to the image, under `ι ⊗_O B^r`, of the iterated local
pure tensor. -/
private lemma unit_tensorComplexSection_tmul (t p s r : ℤ) (hs : t + p = s) {W : X.C}
    (a : (A.X t).val.obj (op W)) (x : (F.X p).val.obj (op W)) (b : (B.X r).val.obj (op W)) :
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj F).X s).val ⊗
          (B.X r).val)).app (op W)
      (tensorComplexSection X t p s hs a x
        ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b) =
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
        (HomologicalComplex.ιMapBifunctor A F (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t p s (by simpa using hs))).app (B.X r)).val.app (op W)
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (A.X t)).obj (F.X p)).val ⊗
          (B.X r).val)).app (op W)
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((A.X t).val ⊗ (F.X p).val)).app (op W)
            (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] x)
          ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b)) :=
  (sheafification_map_unit_apply X ((HomologicalComplex.ιMapBifunctor A F
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t p s
      (by simpa using hs)).val ▷ (B.X r).val) (op W)
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((A.X t).val ⊗ (F.X p).val)).app (op W)
            (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] x)
          ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b)).symm

/-- The associator of sheaves of `O`-modules on an iterated sheafified pure tensor. -/
private lemma associator_hom_unit_tmul
    (M N P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {W : X.C}
    (m : M.val.obj (op W)) (n : N.val.obj (op W)) (p : P.val.obj (op W)) :
    (α_ M N P).hom.val.app (op W)
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).obj N).val ⊗ P.val)).app (op W)
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (M.val ⊗ N.val)).app (op W)
            (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n)
          ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] p)) =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (M.val ⊗ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj N).obj P).val)).app (op W)
        (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)]
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            (N.val ⊗ P.val)).app (op W)
              (n ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] p)) :=
  Stacks.SheafOfModules.associator_hom_val_app_tmul X.O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) M N P (op W) m n p

/-- **The associator of total tensor complexes on local pure tensors**:
`(a ⊗ x) ⊗ b ↦ a ⊗ (x ⊗ b)`, with no sign. -/
theorem tensorComplexAssociator_hom_tensorComplexSection (t p r s q c : ℤ) (hs : t + p = s)
    (hq : p + r = q) (hc : s + r = c) (hc' : t + q = c) {W : X.C}
    (a : (A.X t).val.obj (op W)) (x : (F.X p).val.obj (op W)) (b : (B.X r).val.obj (op W)) :
    ((Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom.f c).val.app
        (op W) (tensorComplexSection X s r c hc (tensorComplexSection X t p s hs a x) b) =
      tensorComplexSection X t q c hc' a (tensorComplexSection X p r q hq x b) := by
  have hA := ι_tensorComplexAssociator_hom X A F B t p r s q c (by simpa using hs)
    (by simpa using hq) (by simpa using hc) (by simpa using hc')
  refine (congrArg (fun y => ((Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
      A F B).hom.f c).val.app (op W)
    ((HomologicalComplex.ιMapBifunctor
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj F) B
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) s r c
        (by simpa using hc)).val.app (op W) y))
    (unit_tensorComplexSection_tmul X t p s r hs a x b)).trans ?_
  refine (congrArg (fun φ => φ.val.app (op W)
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (A.X t)).obj (F.X p)).val ⊗
          (B.X r).val)).app (op W)
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((A.X t).val ⊗ (F.X p).val)).app (op W)
            (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] x)
          ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b))) hA).trans ?_
  refine (congrArg (fun y => (HomologicalComplex.ιMapBifunctor A
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).obj B)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t q c
        (by simpa using hc')).val.app (op W)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (A.X t)).map
        (HomologicalComplex.ιMapBifunctor F B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) p r q (by simpa using hq))).val.app (op W) y))
    (associator_hom_unit_tmul X (A.X t) (F.X p) (B.X r) a x b)).trans ?_
  exact congrArg (fun y => (HomologicalComplex.ιMapBifunctor A
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).obj B)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t q c
        (by simpa using hc')).val.app (op W) y)
    (sheafification_map_unit_apply X ((A.X t).val ◁ (HomologicalComplex.ιMapBifunctor F B
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p r q
        (by simpa using hq)).val) (op W)
      (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)]
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((F.X p).val ⊗ (B.X r).val)).app (op W)
            (x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b)))

end AlgebraicGeometry.RingedSite

end
