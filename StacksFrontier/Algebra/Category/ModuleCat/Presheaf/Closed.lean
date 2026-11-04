module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection

/-!
# Presheaves of modules are monoidal closed

`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/MonoidalClosed.lean` constructs the internal
hom `PresheafOfModules.ihom M N` and the adjunction bijection
`PresheafOfModules.ihomHomEquiv : (M ⊗ L ⟶ N) ≃ (L ⟶ ihom M N)` together with its naturality
in `L`.  That is exactly the data `CategoryTheory.Adjunction.rightAdjointOfEquiv` asks for, so
it packages into an adjunction `(M ⊗ -) ⊣ ihom M` and hence into
`CategoryTheory.MonoidalClosed`.

The point of having the instance, rather than just the bijection, is that it feeds Day's
reflection theorem `CategoryTheory.Monoidal.Reflective.monoidalClosed`, which then makes
sheaves of modules monoidal closed, and therefore makes the tensor product of sheaves of
modules commute with colimits -- which is what the total complex of a tensor double complex
needs.

## Main results

* `PresheafOfModules.monoidalClosed`: `Mod_{pre}(O)` is monoidal closed.
-/

@[expose] public section

universe v u w

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R₀ : Cᵒᵖ ⥤ CommRingCat.{max u v w}}

/-- **Presheaves of modules are monoidal closed**: the internal hom `ihom M` is right adjoint
to `M ⊗ -`, by `ihomHomEquiv` and its naturality in the second variable. -/
instance monoidalClosed :
    MonoidalClosed (PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat)) where
  closed M :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (F := tensorLeft M)
        (fun _ N ↦ ihomHomEquiv (M := M) (N := N)) (fun _ _ _ f g ↦ curry_naturality_left f g)
      adj := Adjunction.adjunctionOfEquivRight _ _ }

end PresheafOfModules

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]

/-- Presheaves of modules over the ring sheaf `ringSheaf R` are monoidal closed, as an instance
for this spelling of the ring. -/
instance ringSheafPresheafMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{max u v} (ringSheaf R).obj) :=
  PresheafOfModules.monoidalClosed (R₀ := R.obj)

end Stacks.SheafOfModules.Tensor

end

end
