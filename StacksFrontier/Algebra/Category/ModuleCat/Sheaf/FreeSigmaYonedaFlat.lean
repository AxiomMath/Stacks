module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSigmaYoneda
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize

/-!
# Free sheaves of modules on coproducts of representables are flat

The free sheaf of `O`-modules on a coproduct of representable presheaves,
`Stacks.SheafOfModules.SigmaYoneda.freeSigmaYoneda`, is flat: its underlying presheaf is
objectwise free, hence flat (Stacks 03ES), and sheafification preserves flatness (Stacks 03ET).
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules.SigmaYoneda

universe u u₁

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u₁} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The free sheaf of modules on a coproduct of representables is flat.** -/
theorem isFlat_freeSigmaYoneda (O : Sheaf J CommRingCat.{u}) {ι : Type u} (V : ι → C) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u₁, u, u} (O := O)
      (freeSigmaYoneda (Stacks.SheafOfModules.Tensor.ringSheaf O) V) := by
  let a : O.obj ⋙ forget₂ CommRingCat RingCat ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
    𝟙 _
  have : Presheaf.IsLocallyInjective J a :=
    Presheaf.isLocallyInjective_of_injective J a fun _ _ _ h ↦ h
  have : Presheaf.IsLocallySurjective J a :=
    Presheaf.isLocallySurjective_of_surjective J a fun _ x ↦ ⟨x, rfl⟩
  exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification J (O := O.obj)
    (Osharp := O) a ((PresheafOfModules.free _).obj (sigmaYoneda V))
    (AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat _ fun U ↦
      inferInstanceAs (Module.Flat (O.obj.obj U) ((sigmaYoneda V).obj U →₀ O.obj.obj U)))

end Stacks.SheafOfModules.SigmaYoneda
