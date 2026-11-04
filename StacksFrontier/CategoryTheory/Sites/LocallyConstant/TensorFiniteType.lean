module

public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of locally constant sheaves of modules of finite type

Let `(C, J)` be a site and let `Λ` be a commutative ring. The tensor product of two locally
constant sheaves of `Λ`-modules *of finite type* is again locally constant of finite type: the
finite type refinement of Tag 093V.

## Main definitions

* `Stacks.ConstantSheaf.constantSheafTensorIso`: the constant sheaf functor is monoidal,
  `M̲ ⊗ N̲ ≅ (M ⊗ N)̲`.

## Main results

* `Stacks.ConstantSheaf.IsConstantFGOver.tensor`: if `F` and `G` both become, over `V`, the
  constant sheaf on a finitely generated module, then so does `F ⊗ G`.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_tensor`: the tensor product of
  two locally constant sheaves of `Λ`-modules of finite type is locally constant of finite type.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 093V](https://stacks.math.columbia.edu/tag/093V)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Stacks.ConstantSheaf

universe w v u u' v'

attribute [local instance] Sheaf.monoidalCategory

/-! ### Monoidality of the constant sheaf functor -/

section Constant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

/-- The constant sheaf functor is monoidal: the constant sheaf on `M ⊗ N` is the tensor product
of the constant sheaves on `M` and on `N`. -/
def constantSheafTensorIso (M N : A) :
    (constantSheaf J A).obj M ⊗ (constantSheaf J A).obj N ≅ (constantSheaf J A).obj (M ⊗ N) :=
  letI c : A ⥤ Cᵒᵖ ⥤ A := Functor.const Cᵒᵖ
  Functor.Monoidal.μIso (presheafToSheaf J A) (c.obj M) (c.obj N) ≪≫
    (presheafToSheaf J A).mapIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [c]) :
        c.obj M ⊗ c.obj N ≅ c.obj (M ⊗ N))

end Constant

/-! ### Finite type local constancy and the tensor product -/

/-- The tensor product of two finitely generated modules is finitely generated. -/
theorem isFG_tensor {Λ : Type u'} [CommRing Λ] {E E' : ModuleCat.{u'} Λ}
    (hE : ModuleCat.isFG Λ E) (hE' : ModuleCat.isFG Λ E') : ModuleCat.isFG Λ (E ⊗ E') := by
  rw [ModuleCat.isFG_iff] at hE hE' ⊢
  exact Module.Finite.tensorProduct Λ E E'

section Module

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type (max u v w)} [CommRing Λ]

/-- The tensor product of two sheaves which are constant on a finitely generated module over `V`
is constant on a finitely generated module over `V`, namely on the tensor product of the two
modules. -/
theorem IsConstantFGOver.tensor {V : C} {F G : Sheaf J (ModuleCat.{max u v w} Λ)}
    (hF : IsConstantFGOver.{v, u, w} J Λ V F) (hG : IsConstantFGOver.{v, u, w} J Λ V G) :
    IsConstantFGOver.{v, u, w} J Λ V (F ⊗ G) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hF
  obtain ⟨E', hE', ⟨e'⟩⟩ := hG
  let _ := overPullbackMonoidal J (ModuleCat.{max u v w} Λ) V
  exact ⟨E ⊗ E', isFG_tensor hE hE',
    ⟨(constantSheafTensorIso (J.over V) (ModuleCat.{max u v w} Λ) E E').symm ≪≫
      tensorIso e e' ≪≫ Functor.Monoidal.μIso (J.overPullback (ModuleCat.{max u v w} Λ) V) F G⟩⟩

variable (J Λ) in
/-- The tensor product of two locally constant sheaves of `Λ`-modules of finite type is locally
constant of finite type. This is the finite type refinement of Tag 093V. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_tensor
    (F G : Sheaf J (ModuleCat.{max u v w} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ F)
    (hG : IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ G) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ (F ⊗ G) := by
  rw [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem] at hF hG ⊢
  intro U
  refine J.superset_covering ?_ (J.intersection_covering (hF U) (hG U))
  intro Y g hg
  exact hg.1.tensor hg.2

end Module

end Stacks.ConstantSheaf

end
