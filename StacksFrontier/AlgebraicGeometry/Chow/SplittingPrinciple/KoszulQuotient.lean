module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.SymTwistChart.Basic

/-!
# The Koszul quotient of the kernel of a map onto an invertible module

Let `X` be a scheme, `q : 𝒜 ⟶ ℒ` an epimorphism of `𝒪_X`-modules onto an invertible module and
`𝒦 = Ker(q)`. The Koszul map `𝒜 ⊗ 𝒜 ⟶ 𝒜 ⊗ ℒ`, `a ⊗ b ↦ a ⊗ q(b) - b ⊗ q(a)`, lands in
`𝒦 ⊗ ℒ` and is onto it: on `𝒦 ⊗ 𝒜` it is `𝒦 ⊗ q`, which is onto `𝒦 ⊗ ℒ`. So `𝒦 ⊗ ℒ` is a
quotient of `𝒜 ⊗ 𝒜`.

That the Koszul map lands in `𝒦 ⊗ ℒ` uses that the symmetry of `ℒ ⊗ ℒ` is the identity, which
holds because `ℒ` is invertible, and that `- ⊗ ℒ` is exact, which holds because it is an
equivalence. The tensor product is the tensor product sheaf of Stacks 01CA, with the symmetric
monoidal structure `Stacks.SheafOfModules.Strict.monoidalCategory`.

## Main results

* `Stacks.KoszulQuotient.exists_epi_tensorObj_kernel`: **`Ker(q) ⊗ ℒ` is a quotient of
  `𝒜 ⊗ 𝒜`.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.KoszulQuotient

variable {X : Scheme.{u}}

/-- **The kernel of an epimorphism onto an invertible module, twisted by that module, is a
quotient of the tensor square of the source.** For `q : 𝒜 ⟶ ℒ` an epimorphism of `𝒪_X`-modules
with `ℒ` invertible (Stacks 01CS), the Koszul map `a ⊗ b ↦ a ⊗ q(b) - b ⊗ q(a)` is an
epimorphism `𝒜 ⊗ 𝒜 ⟶ Ker(q) ⊗ ℒ`. -/
theorem exists_epi_tensorObj_kernel (A L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) L]
    (q : A ⟶ L) [Epi q] :
    ∃ κ : Stacks.SymTwistChart.tensorObj A A ⟶ Stacks.SymTwistChart.tensorObj (kernel q) L,
      Epi κ := by
  let : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf)
  let : BraidedCategory X.Modules := Stacks.SheafOfModules.Strict.braidedCategory X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf)
  have : MonoidalPreadditive X.Modules :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.sheaf
  -- the symmetry of `ℒ ⊗ ℒ` is the identity
  have hβL : (β_ L L).hom = 𝟙 _ := congrArg Iso.hom
    ((Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding X.sheaf.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) L L).trans
      (Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl X.sheaf.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) L))
  -- the Koszul map `𝒜 ⊗ 𝒜 ⟶ 𝒜 ⊗ ℒ` composes to zero with `q ⊗ ℒ`
  have e : (β_ A A).hom ≫ A ◁ q ≫ q ▷ L = A ◁ q ≫ q ▷ L :=
    calc (β_ A A).hom ≫ A ◁ q ≫ q ▷ L = (q ▷ A ≫ (β_ L A).hom) ≫ q ▷ L := by
          rw [BraidedCategory.braiding_naturality_left q A, Category.assoc]
      _ = q ▷ A ≫ L ◁ q ≫ (β_ L L).hom := by
          rw [BraidedCategory.braiding_naturality_right L q, Category.assoc]
      _ = A ◁ q ≫ q ▷ L := by rw [hβL, Category.comp_id, whisker_exchange]
  let κ' : A ⊗ A ⟶ A ⊗ L := A ◁ q - (β_ A A).hom ≫ A ◁ q
  have hκ' : κ' ≫ q ▷ L = 0 := by
    change (A ◁ q - (β_ A A).hom ≫ A ◁ q) ≫ q ▷ L = 0
    rw [Preadditive.sub_comp, Category.assoc, e, sub_self]
  -- tensoring with `ℒ` is an equivalence, so it carries the kernel of `q` to that of `q ⊗ ℒ`
  let G : X.Modules ⥤ X.Modules := (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf)⟩).flip.obj L
  have : G.IsEquivalence := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    X.sheaf.obj (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) L
  have hG : ∀ {B C : X.Modules} (f : B ⟶ C), G.map f = f ▷ L := fun f ↦
    (Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor X.sheaf f L).symm
  have hlim := isLimitOfHasKernelOfPreservesLimit G q
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hlim κ' (by rwa [hG])
  have hl' : l ≫ kernel.ι q ▷ L = κ' := by rw [← hG]; exact hl
  -- on `𝒦 ⊗ 𝒜` the Koszul map is `𝒦 ⊗ q`
  have hK : kernel.ι q ▷ A ≫ κ' = kernel q ◁ q ≫ kernel.ι q ▷ L := by
    change kernel.ι q ▷ A ≫ (A ◁ q - (β_ A A).hom ≫ A ◁ q) = _
    rw [Preadditive.comp_sub, ← Category.assoc,
      BraidedCategory.braiding_naturality_left (kernel.ι q) A, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, kernel.condition, MonoidalPreadditive.whiskerLeft_zero,
      Limits.comp_zero, sub_zero, whisker_exchange]
  have : Mono (kernel.ι q ▷ L) := by rw [← hG]; infer_instance
  have hKl : kernel.ι q ▷ A ≫ l = kernel q ◁ q := by
    rw [← cancel_mono (kernel.ι q ▷ L), Category.assoc, hl', hK]
  -- `𝒦 ⊗ -` preserves epimorphisms
  have hpres : PreservesColimit (span q q)
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (kernel q)) :=
    _root_.SheafOfModules.preservesColimitsOfSize_sheafTensor_obj X.sheaf (kernel q) _
  have : Epi (kernel q ◁ q) := by
    rw [show kernel q ◁ q = ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
      (kernel q)).map q from Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor X.sheaf _ q]
    exact @preserves_epi_of_preservesColimit _ _ _ _ _ _ _ q hpres _
  have : Epi (kernel.ι q ▷ A ≫ l) := by rw [hKl]; infer_instance
  exact ⟨l, epi_of_epi (kernel.ι q ▷ A) l⟩

end Stacks.KoszulQuotient

end
