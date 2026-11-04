module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Modules over the constant sheaf of rings `𝐙_X` are the abelian sheaves

Let `X` be a topological space and let `𝐙_X` be the constant sheaf of commutative rings with
value `𝐙` on the opens of `X`. A sheaf of `𝐙_X`-modules is the same thing as a sheaf of abelian
groups: the forgetful functor from sheaves of modules over the underlying sheaf of rings of
`𝐙_X` to abelian sheaves is an equivalence. This is the identification through which statements
about sheaves of modules over a sheaf of commutative rings `𝒪_X` specialize to statements about
abelian sheaves, by taking `𝒪_X = 𝐙_X`.

## Main definitions

* `Stacks.Cech.Hypercohomology.integerRingSheaf`: the constant sheaf of commutative rings `𝐙_X`.

## Main results

* `Stacks.Cech.Hypercohomology.isEquivalence_toSheaf_integerRingSheaf`: sheaves of
  `𝐙_X`-modules are the abelian sheaves.

## Implementation notes

The value is `ULift 𝐙`, so that the sheaf of rings takes values in the universe of the space.
The proof is `Stacks.Cohomology.full_toSheaf_of_constant_int` and
`Stacks.Cohomology.essSurj_toSheaf_of_constant_int` applied to the sheafification map of the
constant presheaf, read in rings: it is locally bijective because the sheafification map of the
constant presheaf of commutative rings is, and forgetting to sets does not see the difference
between rings and commutative rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cech.Hypercohomology

variable (X : TopCat.{u})

/-- **The constant sheaf of commutative rings `𝐙_X`** on the opens of a topological space: the
sheafification of the constant presheaf with value `𝐙`. -/
@[ega "IV 21.10.9" "partial", sga "4 IV 11.1.5" "special case"]
abbrev integerRingSheaf : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    (CommRingCat.of (ULift.{u} ℤ))

/-- **Sheaves of `𝐙_X`-modules are the abelian sheaves.** The forgetful functor from sheaves of
modules over the underlying sheaf of rings of `𝐙_X` to abelian sheaves on `X` is an
equivalence. -/
@[ega "IV 5.9.12" "(iii)", sga "4 IV 11.1.5" "special case"]
theorem isEquivalence_toSheaf_integerRingSheaf :
    (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (integerRingSheaf X))).IsEquivalence := by
  let J := Opens.grothendieckTopology X
  let P := (Functor.const (Opens X)ᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))
  let α : (Functor.const (Opens X)ᵒᵖ).obj (RingCat.of (ULift.{u} ℤ)) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (integerRingSheaf X)).obj :=
    Functor.whiskerRight (toSheafify J P) (forget₂ CommRingCat RingCat.{u})
  have hinj : Presheaf.IsLocallyInjective J α := by
    apply (Presheaf.isLocallyInjective_forget_iff J _).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J P) (forget CommRingCat.{u}))
    infer_instance
  have hsurj : Presheaf.IsLocallySurjective J α := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J P) (forget CommRingCat.{u}))
    infer_instance
  have _ := Stacks.Cohomology.full_toSheaf_of_constant_int α
  have _ := Stacks.Cohomology.essSurj_toSheaf_of_constant_int α
  exact {}

end Stacks.Cech.Hypercohomology

end
