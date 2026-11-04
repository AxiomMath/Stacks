module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualLocalDualBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackPowerSystem

/-!
# The tensor product of two morphisms of modules on a ringed space, on a local pure tensor

Let `Z` be a ringed space. `Stacks.PullbackSheafTensor.monoidalModules Z` is the monoidal
structure of [Stacks, Tag 01CA] on `Mod(𝒪_Z)`, named at the `structureSheafRing` spelling of the
structure sheaf of rings. A section of a tensor product `M ⊗ N` over an open `V` need not be a
pure tensor, but the *local pure tensors* `Stacks.SheafOfModules.tensorPt` — the images under the
Tag 05NA sheafification unit of the pure tensors of local sections — generate it locally, and
every morphism out of a tensor product is pinned down by its values on them.

This file records the one such value that was missing: the action of `f ⊗ₘ g`.

## Main results

* `Stacks.RingedSpace.tensorHom_val_app_tensorPt` — **the tensor product of two morphisms of
  sheaves of modules carries a local pure tensor to the local pure tensor of the images**:
  `(f ⊗ₘ g)(m ⊗ n) = f m ⊗ g n`.

## Implementation notes

**Why the detour through the whiskerings.** `Mod(𝒪_Z)` carries the tensor product of Tag 01CA in
several mutually definitional spellings, and the section formulas live at different ones: the
whiskerings of `Stacks.PullbackSheafTensor.monoidalModules` are identified with those of
`Stacks.PullbackGradedAlgebra.monoidalCategory` by
`Stacks.RingedSpace.whiskerRight_eq_strict` and `whiskerLeft_eq_strict`, and the latter structure
*is* `Stacks.SheafOfModules.Strict.monoidalCategory` of the structure presheaf
(`Stacks.PullbackGradedAlgebra.monoidalCategory_eq`), which is where the section formulas
`Stacks.SheafOfModules.tensorPt_whiskerRight` and `tensorPt_whiskerLeft` are stated. There is no
section formula for `⊗ₘ` at any of them, so `CategoryTheory.MonoidalCategory.tensorHom_def`
splits it into the two whiskerings first; that detour is not avoidable.

**Why the statement is at `Stacks.SheafOfModules.tensorPt`.** The same section of `M ⊗ N` is also
`PresheafOfModules.tensorSheafUnit M N` applied to `m ⊗ₜ n`. That spelling takes the sheaf of
rings as an argument and so fixes a second name for it in the statement, whereas `tensorPt` takes
the structure *presheaf* and its sheaf condition; stating the result at `tensorPt` is what lets
`structureSheafRing Z` be the only name for the ring sheaf that the statement mentions.

**Where `Stacks.SheafOfModules.OnSpace.monoidal` is, and is not, usable.** That is a third
monoidal structure on the very same category, `CategoryTheory.Monoidal.transport`ed along a
`ULift` equivalence, and `Stacks.SheafOfModules.OnSpace.tensorHom_tmul` is already the formula
below for it. It is not interchangeable with the structure used here: the two agree on
`tensorObj` definitionally but **not** on `tensorHom`, and no lemma relates them, so neither
result follows from the other.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — the tensor product
  sheaf as a sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.RingedSpace

attribute [local instance] Stacks.PullbackSheafTensor.monoidalModules

variable {Z : RingedSpace.{u, u}}

/-- Equal morphisms of sheaves of modules have equal components on every section. -/
private theorem val_app_congr {M M' : _root_.SheafOfModules.{u} (structureSheafRing Z)}
    {φ ψ : M ⟶ M'} (h : φ = ψ) (V : (Opens Z)ᵒᵖ) (x : M.val.obj V) :
    φ.val.app V x = ψ.val.app V x := by
  rw [h]

/-- Right whiskering carries a local pure tensor to the local pure tensor of the image of its
first factor. This is `Stacks.SheafOfModules.tensorPt_whiskerRight` read at
`Stacks.PullbackSheafTensor.monoidalModules`. -/
private theorem whiskerRight_val_app_tensorPt
    {M M' : _root_.SheafOfModules.{u} (structureSheafRing Z)}
    (f : M ⟶ M') (N : _root_.SheafOfModules.{u} (structureSheafRing Z)) (V : (Opens Z)ᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) :
    (f ▷ N).val.app V
        (Stacks.SheafOfModules.tensorPt Z.presheaf (structureSheafRing Z).property M N V m n) =
      Stacks.SheafOfModules.tensorPt Z.presheaf (structureSheafRing Z).property M' N V
        (f.val.app V m) n :=
  (val_app_congr (whiskerRight_eq_strict (Z := Z) f N) V _).trans
    (Stacks.SheafOfModules.tensorPt_whiskerRight Z.presheaf (structureSheafRing Z).property
      f V m n)

/-- Left whiskering carries a local pure tensor to the local pure tensor of the image of its
second factor. This is `Stacks.SheafOfModules.tensorPt_whiskerLeft` read at
`Stacks.PullbackSheafTensor.monoidalModules`. -/
private theorem whiskerLeft_val_app_tensorPt
    (M : _root_.SheafOfModules.{u} (structureSheafRing Z))
    {N N' : _root_.SheafOfModules.{u} (structureSheafRing Z)}
    (g : N ⟶ N') (V : (Opens Z)ᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) :
    (M ◁ g).val.app V
        (Stacks.SheafOfModules.tensorPt Z.presheaf (structureSheafRing Z).property M N V m n) =
      Stacks.SheafOfModules.tensorPt Z.presheaf (structureSheafRing Z).property M N' V
        m (g.val.app V n) :=
  (val_app_congr (whiskerLeft_eq_strict (Z := Z) M g) V _).trans
    (Stacks.SheafOfModules.tensorPt_whiskerLeft Z.presheaf (structureSheafRing Z).property
      g V m n)

/-- **The tensor product of two morphisms of sheaves of modules on a ringed space, on a local
pure tensor.** `f ⊗ₘ g` carries the local pure tensor of `m` and `n` to the local pure tensor of
`f m` and `g n`.

This is the two whiskering formulas of [Stacks, Tag 01CA] composed along
`CategoryTheory.MonoidalCategory.tensorHom_def`. -/
public theorem tensorHom_val_app_tensorPt
    {M M' N N' : _root_.SheafOfModules.{u} (structureSheafRing Z)}
    (f : M ⟶ M') (g : N ⟶ N') (V : (Opens Z)ᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) :
    (f ⊗ₘ g).val.app V
        (Stacks.SheafOfModules.tensorPt Z.presheaf (structureSheafRing Z).property M N V m n) =
      Stacks.SheafOfModules.tensorPt Z.presheaf (structureSheafRing Z).property M' N' V
        (f.val.app V m) (g.val.app V n) :=
  (val_app_congr (tensorHom_def f g) V _).trans
    ((congrArg ((M' ◁ g).val.app V) (whiskerRight_val_app_tensorPt f N V m n)).trans
      (whiskerLeft_val_app_tensorPt M' g V (f.val.app V m) n))

end Stacks.RingedSpace

end
