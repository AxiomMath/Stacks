module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroSubcomplex
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatCover
public import StacksFrontier.Topology.Sheaves.Modules.ExtensionByZero.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualBoundedAbove

/-!
# Resolutions by sums of extensions by zero

For a ringed space `X`, we consider sheaves of `O_X`-modules that are direct sums of extensions by
zero `j_{U!} O_U` of structure sheaves of opens `U`. Every sheaf of `O_X`-modules is a quotient of
such a sum, and every such sum is flat.

## Main definitions

* `Stacks.Cohomology.LeftDualPerfect.IsSumExt`: the property of a sheaf of `O_X`-modules of being
  a direct sum of extensions by zero of structure sheaves of opens.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.exists_epi_isSumExt`: every sheaf of `O_X`-modules admits an
  epimorphism from a direct sum of extensions by zero of structure sheaves of opens.
* `Stacks.Cohomology.LeftDualPerfect.isFlat_of_isSumExt`: a direct sum of extensions by zero of
  structure sheaves of opens is a flat sheaf of `O_X`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ExtensionByZeroModules Stacks.SheafOfModules.DerivedMonoidal ZeroObject

universe u

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u})

/-- The structure sheaf of a ringed space `X`, as a sheaf of rings on the site of opens of `X`. -/
abbrev ringO : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf

/-- A sheaf of `O_X`-modules is a sum of extensions by zero of structure sheaves of opens. -/
def IsSumExt : ObjectProperty (Mod X.sheaf) := fun F =>
  ∃ (I : Type u) (U : I → Opens X.carrier) (ι : ∀ α, extUnit (ringO X) (U α) ⟶ F),
    Nonempty (IsColimit (Cofan.mk F ι))

/-- The category of sheaves of `O_X`-modules has a zero object. -/
instance : HasZeroObject (Mod X.sheaf) := inferInstance

/-- The zero sheaf of `O_X`-modules is a sum of extensions by zero, indexed by the empty type. -/
instance : (IsSumExt X).ContainsZero where
  exists_zero := ⟨(0 : Mod X.sheaf), isZero_zero _, PEmpty.{u + 1}, fun α => α.elim,
    fun α => α.elim, ⟨Cofan.IsColimit.mk _ (fun _ => 0) (fun _ α => α.elim)
      (fun _ _ _ => (isZero_zero _).eq_of_src _ _)⟩⟩

/-- Every sheaf of `O_X`-modules is a quotient of a direct sum of extensions by zero of structure
sheaves of opens. -/
theorem exists_epi_isSumExt (F : Mod X.sheaf) :
    ∃ (G : Mod X.sheaf) (_ : IsSumExt X G) (p : G ⟶ F), Epi p := by
  obtain ⟨I, U, f, hf⟩ := Stacks.SheafOfModules.exists_epi_from_coproduct_jShriek_unit (ringO X) F
  exact ⟨_, ⟨I, U, Sigma.ι _, ⟨coproductIsCoproduct _⟩⟩, f, hf⟩

/-- A direct sum of extensions by zero of structure sheaves of opens is a flat sheaf of
`O_X`-modules. -/
theorem isFlat_of_isSumExt {F : Mod X.sheaf} (h : IsSumExt X F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F := by
  obtain ⟨I, U, ι, ⟨hc⟩⟩ := h
  exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
    (hc.coconePointUniqueUpToIso (coproductIsCoproduct _)).symm
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct.{u, u, u, u} (O := X.sheaf)
      (fun α => extUnit (ringO X) (U α))
      fun α => AlgebraicGeometry.SheafOfModules.isFlat_jShriek_unit (U α) X.sheaf)

end Stacks.Cohomology.LeftDualPerfect
