module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
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

## Implementation notes

The computation on local pure tensors is carried out with the unit of
`Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction`, whose values are sections of the
underlying presheaf `((Stacks.SheafOfModules.Tensor.sheafification R).obj P).val`, the spelling in
which `⊗_O` and its maps act on sections; the local pure tensors themselves are built from the
unit of `Stacks.SheafOfModules.Tensor.sheafificationAdjunction`, and the two agree on sections
(`Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction_unit_app_app_apply`). The
associator of `SheafOfModules.monoidalCategorySheafTensor` is evaluated through its agreement
`SheafOfModules.associator_eq_strict` with the associator of
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose section formula is
`Stacks.SheafOfModules.associator_hom_val_app_tmul`.
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

/-- Naturality, on sections, of the unit of
`Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction`, the sealed sheafification with
the plain forgetful functor as right adjoint. -/
private lemma forgetUnit_naturality_apply
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj} (φ : P ⟶ Q)
    (U : X.Cᵒᵖ) (x : P.obj U) :
    ((Stacks.SheafOfModules.Tensor.sheafification X.O).map φ).val.app U
        (((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app P).app U x) =
      ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app Q).app U
        (φ.app U x) :=
  congrArg (fun z ↦ z.app U x)
    ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.naturality φ).symm

/-- The local pure tensor is the inclusion of the summand applied to the image of the pure tensor
under the unit of `Stacks.SheafOfModules.Tensor.sheafificationAdjunction`: this is its
definition. -/
private lemma tensorComplexSection_eq_unit {K L :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    tensorComplexSection X t r c htr k l =
      (HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t r c (by simpa using htr)).val.app (op W)
        (((Stacks.SheafOfModules.Tensor.sheafificationAdjunction X.O).unit.app
          ((K.X t).val ⊗ (L.X r).val)).app (op W)
            (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)) := rfl

/-- The local pure tensor is the inclusion of the summand applied to the image of the pure tensor
under the unit of `Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction`. -/
private lemma tensorComplexSection_eq_forgetUnit {K L :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    tensorComplexSection X t r c htr k l =
      (HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t r c (by simpa using htr)).val.app (op W)
        (((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
          ((K.X t).val ⊗ (L.X r).val)).app (op W)
            (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)) :=
  (tensorComplexSection_eq_unit X t r c htr k l).trans
    (congrArg ((HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ) t r c (by simpa using htr)).val.app (op W))
      (Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction_unit_app_app_apply X.O
        ((K.X t).val ⊗ (L.X r).val) (op W)
          (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l))).symm

section Units

variable {M M' N N' P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {W : X.C}

/-- The unit of the sheafification carries a pure tensor `f(m) ⊗ n` to the image of the class of
`m ⊗ n` under `f ⊗_O N`. -/
private lemma forgetUnit_map_tmul (f : M ⟶ M') (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
        (M'.val ⊗ N.val)).app (op W)
        (f.val.app (op W) m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map f).app N).val.app (op W)
        (((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
          (M.val ⊗ N.val)).app (op W)
            (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n)) :=
  (forgetUnit_naturality_apply X (f.val ▷ N.val) (op W)
    (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n)).symm

/-- The unit of the sheafification carries a pure tensor `m ⊗ g(n)` to the image of the class of
`m ⊗ n` under `M ⊗_O g`. -/
private lemma forgetUnit_tmul_map (g : N ⟶ N') (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
        (M.val ⊗ N'.val)).app (op W)
        (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] g.val.app (op W) n) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).map g).val.app (op W)
        (((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
          (M.val ⊗ N.val)).app (op W)
            (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n)) :=
  (forgetUnit_naturality_apply X (M.val ◁ g.val) (op W)
    (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n)).symm

/-- The associator of sheaves of `O`-modules on an iterated sheafified pure tensor. -/
private lemma associator_hom_forgetUnit_tmul
    (m : M.val.obj (op W)) (n : N.val.obj (op W)) (p : P.val.obj (op W)) :
    (α_ M N P).hom.val.app (op W)
      (((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).obj N).val ⊗ P.val)).app (op W)
        (((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
          (M.val ⊗ N.val)).app (op W)
            (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] n)
          ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] p)) =
      ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
        (M.val ⊗ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj N).obj P).val)).app (op W)
        (m ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)]
          ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction X.O).unit.app
            (N.val ⊗ P.val)).app (op W)
              (n ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] p)) := by
  rw [_root_.SheafOfModules.associator_eq_strict]
  exact Stacks.SheafOfModules.associator_hom_val_app_tmul X.O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) M N P (op W) m n p

end Units

/-- **The associator of total tensor complexes on local pure tensors**:
`(a ⊗ x) ⊗ b ↦ a ⊗ (x ⊗ b)`, with no sign. -/
theorem tensorComplexAssociator_hom_tensorComplexSection (t p r s q c : ℤ) (hs : t + p = s)
    (hq : p + r = q) (hc : s + r = c) (hc' : t + q = c) {W : X.C}
    (a : (A.X t).val.obj (op W)) (x : (F.X p).val.obj (op W)) (b : (B.X r).val.obj (op W)) :
    ((Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom.f c).val.app
        (op W) (tensorComplexSection X s r c hc (tensorComplexSection X t p s hs a x) b) =
      tensorComplexSection X t q c hc' a (tensorComplexSection X p r q hq x b) := by
  rw [tensorComplexSection_eq_forgetUnit X s r c hc, tensorComplexSection_eq_forgetUnit X t p s hs,
    tensorComplexSection_eq_forgetUnit X t q c hc', tensorComplexSection_eq_forgetUnit X p r q hq]
  refine (congrArg (fun y ↦
    ((Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom.f c).val.app
      (op W) ((HomologicalComplex.ιMapBifunctor
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj F) B
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) s r c
        (by simpa using hc)).val.app (op W) y))
    (forgetUnit_map_tmul X (HomologicalComplex.ιMapBifunctor A F
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t p s
        (by simpa using hs)) _ b)).trans
    (Eq.trans ?_ (congrArg (fun y ↦ (HomologicalComplex.ιMapBifunctor A
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).obj B)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t q c
        (by simpa using hc')).val.app (op W) y)
      (forgetUnit_tmul_map X (HomologicalComplex.ιMapBifunctor F B
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p r q
          (by simpa using hq)) a _)).symm)
  rw [← associator_hom_forgetUnit_tmul]
  exact PresheafOfModules.hom_congr_apply' (congrArg SheafOfModules.Hom.val
    (ι_tensorComplexAssociator_hom X A F B t p r s q c (by simpa using hs) (by simpa using hq)
      (by simpa using hc) (by simpa using hc'))) (op W) _

end AlgebraicGeometry.RingedSite

end
