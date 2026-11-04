module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# The braiding of the tensor product sheaf on local pure tensors

Let `O` be a sheaf of commutative rings on a site `(C, J)`. The symmetry constraint of the
monoidal structure of [Stacks, Tag 01CA] on sheaves of `O`-modules exchanges the two factors of
a local pure tensor: on the sheafification-unit image of `s ⊗ₜ t` it is the
sheafification-unit image of `t ⊗ₜ s`.

This is the computation rule a consumer needs in order to recognise the braiding, in the same
way that `Stacks.RingedSpace.comparison_homEquiv_unit_tmul` is what lets one recognise the
pullback tensor comparison of Tag 01CD. It is used to show that a functor commuting with the
tensor product also commutes with the braiding, i.e. is lax braided, by the uniqueness clause
`Stacks.RingedSpace.comparison_unique`.

## Main results

* `Stacks.SheafOfModules.braiding_tensorSectionsAt`: **the braiding `β_ M N` of the strict
  monoidal structure carries the local pure tensor `s ⊗ₜ t` to `t ⊗ₜ s`.**
* `Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt`: the same at the
  `Stacks.SheafOfModules.tensorSheafBraiding` spelling of the symmetry constraint.
* `Stacks.SheafOfModules.tensorSheafificationUnit_app_eq_tensorSectionsAt`: the two spellings of
  the sheafification unit of a tensor product agree on local pure tensors —
  `PresheafOfModules.sheafificationAdjunction`, which the pullback tensor comparison of Tag 01CD
  is stated with, and `Stacks.SheafOfModules.tensorSectionsAt`, which the section formulas use.
  Both are the unit of the sheafification adjunction at the objectwise tensor product, so this
  is `rfl`; it is recorded because neither name is usable against a goal stated with the other.

## Implementation notes

Nothing is reproved. `Stacks.SheafOfModules.tensorSections_braidingAt` is this statement for
`Stacks.SheafOfModules.Invertible.tensorProductBraiding`, which is
`Stacks.SheafOfModules.tensorSheafBraiding` by `rfl` — both are the sheafification of the
braiding of the underlying presheaves of modules — and
`Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding` identifies that with `β_`. What this
file adds is the statement at the `β_` spelling, which is the one the monoidal-functor classes
are phrased in; neither of the two existing names is usable against a goal mentioning `β_`
without it.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

noncomputable section

namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The symmetry constraint of the tensor product sheaf exchanges the two factors of a local
pure tensor. -/
theorem tensorSheafBraiding_tensorSectionsAt (U : Cᵒᵖ)
    (M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : M.val.obj U) (t : N.val.obj U) :
    ((tensorSheafBraiding O hO M N).hom.val.app U) (tensorSectionsAt O hO U M N s t)
      = tensorSectionsAt O hO U N M t s :=
  tensorSections_braidingAt O hO U M N s t

section Braided

attribute [local instance] Strict.monoidalCategory Strict.braidedCategory

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The braiding of the strict monoidal structure of Tag 01CA exchanges the two factors of a
local pure tensor.** -/
theorem braiding_tensorSectionsAt (U : Cᵒᵖ)
    (M N : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : M.val.obj U) (t : N.val.obj U) :
    ((β_ M N).hom.val.app U) (tensorSectionsAt O hO U M N s t)
      = tensorSectionsAt O hO U N M t s := by
  rw [braiding_eq_tensorSheafBraiding]
  exact tensorSheafBraiding_tensorSectionsAt O hO U M N s t

end Braided

section UnitSpellings

open scoped TensorProduct

variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J' CommRingCat.{w})
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J' AddCommGrpCat.{w}]

/-- The two spellings of the sheafification unit of a tensor product of sheaves of modules
agree on local pure tensors: `PresheafOfModules.sheafificationAdjunction`, which the pullback
tensor comparison of Tag 01CD is stated with, and `Stacks.SheafOfModules.tensorSectionsAt`,
which the section formulas are stated with. Both are the unit of the sheafification adjunction
at the objectwise tensor product. -/
theorem tensorSheafificationUnit_app_eq_tensorSectionsAt (U : C'ᵒᵖ)
    (M N : _root_.SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J' Osharp))
    (s : M.val.obj U) (t : N.val.obj U) :
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
        Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj M.val N.val)).app U
        (s ⊗ₜ[Osharp.obj.obj U] t)
      = tensorSectionsAt Osharp.obj (CategoryTheory.Sheaf.toRingCat J' Osharp).property U M N
          s t :=
  rfl

end UnitSpellings

end Stacks.SheafOfModules
