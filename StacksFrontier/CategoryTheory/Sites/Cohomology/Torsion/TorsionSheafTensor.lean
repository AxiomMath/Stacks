module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionModules

/-!
# The tensor product with a torsion sheaf of modules is torsion

Let `O` be a sheaf of commutative rings on a site. If `M` is a torsion sheaf of `O`-modules (its
sections are locally annihilated by positive integers, `Stacks.Torsion.torsionModules`), then
so is `M ⊗_O N` for every sheaf of `O`-modules `N`: a pure tensor `x ⊗ y` is killed wherever `x`
is, the locally torsion sections of the presheaf tensor product form a submodule, and
sheafification preserves local torsion.

## Main results

* `Stacks.Torsion.torsionModules_sheafTensor_obj_obj`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

namespace Stacks.Torsion

universe u

open Stacks.SheafOfModules.Tensor

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The objectwise tensor product of presheaves of modules with a locally torsion left factor
is locally torsion**: a pure tensor `x ⊗ y` is killed wherever `x` is, and the locally torsion
sections form a submodule. -/
theorem mem_torsionSections_tensorObj {O : Cᵒᵖ ⥤ CommRingCat.{u}}
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat))
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj U), x ∈ torsionSections J F U) (U : Cᵒᵖ)
    (z : (PresheafOfModules.tensorObj F G).obj U) :
    z ∈ torsionSections J (PresheafOfModules.tensorObj F G) U := by
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul x y =>
    have hx := hF U x
    rw [mem_torsionSections_iff] at hx
    refine (mem_torsionSections_iff J _ U _).2 (J.superset_covering ?_ hx)
    rintro V f ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    show n • (PresheafOfModules.tensorObj F G).restrictₛₗ f.op (x ⊗ₜ y) = 0
    change n • F.restrictₛₗ f.op x = 0 at h
    rw [PresheafOfModules.tensorObj_restrictₛₗ_tmul]
    show n • (F.restrictₛₗ f.op x ⊗ₜ[(O ⋙ forget₂ CommRingCat RingCat).obj (op V)]
      G.restrictₛₗ f.op y : F.obj (op V) ⊗[(O ⋙ forget₂ CommRingCat RingCat).obj (op V)]
        G.obj (op V)) = 0
    rw [TensorProduct.smul_tmul', h, TensorProduct.zero_tmul]

/-- **The tensor product of a torsion sheaf of modules with any sheaf of modules is torsion.** -/
theorem torsionModules_sheafTensor_obj_obj
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (hM : torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R) M) :
    torsionModules (Stacks.SheafOfModules.Tensor.ringSheaf R)
      (((sheafTensor.{u, u, u, u, u} R).obj M).obj N) := by
  rw [sheafTensor_obj_obj]
  exact torsionSheafProperty_sheafify J _
    ((isLocallyTorsion_toPresheaf_iff J (PresheafOfModules.tensorObj M.val N.val)).2
      (mem_torsionSections_tensorObj M.val N.val
        ((isLocallyTorsion_toPresheaf_iff J M.val).1 hM)))

end Stacks.Torsion
