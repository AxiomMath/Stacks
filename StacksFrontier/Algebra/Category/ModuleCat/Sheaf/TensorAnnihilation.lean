module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Annihilating a tensor product of sheaves of modules on a site

Let `(C, J)` be a site, `Osharp` a sheaf of commutative rings on it and `M`, `N` two sheaves of
`Osharp`-modules. If a section `a` of the structure sheaf over `U` annihilates the sections of
`N` over every object mapping to `U`, then it annihilates every section of `M ⊗_{Osharp} N`
over `U`.

## Main results

* `Stacks.SheafOfModules.smul_tensorProduct_eq_zero`: a ring element killing the right factor
  kills the whole tensor product of two modules.
* `Stacks.SheafOfModules.smul_presheafTensorObj_eq_zero`: the same statement for the objectwise
  tensor product of two presheaves of modules.
* `Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero`: the statement for the tensor
  product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor`.

## Implementation notes

There are no stalks on a general site, so the argument is the one of
`Stacks.Sites.smul_adicGradedPiece_eq_zero` rather than the stalkwise argument of
`Stacks.AffineProjectionFormula.smul_tensorSheaf_eq_zero`: the tensor product sheaf is the
sheafification of the objectwise tensor product, so its unit is locally surjective and a section
`s` over `U` is, after restriction along the arrows of a covering sieve, the image of a genuine
element of a tensor product of modules of sections. There the restriction of `a` kills every pure
tensor, because it already kills the right-hand factor. Vanishing of a section is a local
condition, a sheaf being separated, so `a • s` vanishes outright.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules

universe v u w

namespace Stacks.SheafOfModules

/-- **A ring element killing the right factor kills the whole tensor product.** On a pure tensor
`m ⊗ n` the scalar can be moved onto `n`, where it already acts by zero. -/
theorem smul_tensorProduct_eq_zero {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (b : A)
    (hN : ∀ y : N, b • y = 0) (z : TensorProduct A M N) : b • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => rw [← TensorProduct.tmul_smul, hN n, TensorProduct.tmul_zero]
  | add z₁ z₂ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]

section PresheafLevel

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **A section of a presheaf of rings killing the sections of `N` over an object kills the
objectwise tensor product there.** The sections of `M ⊗ N` over an object are the tensor product
of the modules of sections. -/
theorem smul_presheafTensorObj_eq_zero
    (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat.{w} RingCat.{w})) (V : Cᵒᵖ)
    (b : (R ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj V)
    (hN : ∀ y : N.obj V, b • y = 0) (z : (M ⊗ N).obj V) : b • z = 0 :=
  smul_tensorProduct_eq_zero b hN z

end PresheafLevel

section LocalVanishing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Membership in the image sieve of a morphism of presheaves of modules, read on sections. -/
private lemma mem_imageSieve_toPresheaf_map_iff {R : Cᵒᵖ ⥤ RingCat.{w}}
    {P Q : PresheafOfModules.{w} R} (φ : P ⟶ Q) {U : C} (s : Q.obj (op U)) {V : C} (g : V ⟶ U) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R).map φ) s g ↔
      ∃ z : P.obj (op V), φ.app (op V) z = Q.map g.op s :=
  Iff.rfl

/-- **A section killed by a scalar on a locally surjective source.** If `φ : P ⟶ M` is locally
surjective and the restrictions of `a` kill the sections of `P`, then `a` kills the sections of the
sheaf `M`. -/
private theorem smul_eq_zero_of_isLocallySurjective {R : Sheaf J RingCat.{w}}
    {P : PresheafOfModules.{w} R.obj} {M : _root_.SheafOfModules.{w} R} (φ : P ⟶ M.val)
    [hφ : PresheafOfModules.IsLocallySurjective J φ] {U : Cᵒᵖ} (a : R.obj.obj U)
    (h : ∀ {V : C} (g : V ⟶ U.unop) (z : P.obj (op V)), R.obj.map g.op a • z = 0)
    (s : M.val.obj U) : a • s = 0 := by
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (J := J) _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map φ) s) fun V g hg => ?_
  obtain ⟨z, hz⟩ := (mem_imageSieve_toPresheaf_map_iff φ s g).1 hg
  rw [PresheafOfModules.map_smul, ← hz]
  exact ((φ.app (op V)).hom.map_smul _ z).symm.trans (by rw [h]; exact map_zero _)

end LocalVanishing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  {Osharp : Sheaf J CommRingCat.{w}}

/-- **The unit of Mathlib's sheafification of the objectwise tensor product is locally
surjective.** Instance search cannot see through the sheafification functor, so the instance for
`CategoryTheory.toSheafify` is transported by hand. (The tensor product sheaf itself is the sealed
`Stacks.SheafOfModules.Tensor.sheafification`, whose unit carries its own instance.) -/
instance isLocallySurjective_tensorSheafificationUnit
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj).map
        ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
            Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj M.val N.val))) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J
    ((_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).obj M ⊗
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).obj
          N).presheaf))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The unit of the sealed sheafification, with the plain forgetful functor as right adjoint, is
locally surjective. -/
private lemma isLocallySurjective_sheafificationForgetAdjunction_unit_app
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj) :
    PresheafOfModules.IsLocallySurjective J
      ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction Osharp).unit.app P) := by
  rw [Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction_unit_app,
    PresheafOfModules.IsLocallySurjective, Functor.map_comp]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A section of the structure sheaf annihilating the right factor annihilates the tensor
product sheaf.** If `a` over `U` kills the sections of `N` over every object mapping to `U`, then
it kills every section of `M ⊗_{Osharp} N` over `U`.

A section of the tensor product sheaf is locally the image under the sheafification unit of an
element of a tensor product of modules of sections, where the restriction of `a` acts by zero
because it does so on the right-hand factor; a sheaf is separated, so the product vanishes. -/
theorem smul_tensorSheafBifunctor_eq_zero
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) (U : Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
    (hN : ∀ {V : Cᵒᵖ} (g : U ⟶ V) (y : N.val.obj V),
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map g a • y = 0)
    (s : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M).obj N).val.obj
        U) :
    a • s = 0 := by
  exact smul_eq_zero_of_isLocallySurjective J
    ((Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction Osharp).unit.app
      (PresheafOfModules.tensorObj M.val N.val))
    (hφ := isLocallySurjective_sheafificationForgetAdjunction_unit_app J _) a
    (fun g z => smul_presheafTensorObj_eq_zero (R := Osharp.obj) _ _ _ _ (fun y => hN g.op y) z) s

end Stacks.SheafOfModules

end
