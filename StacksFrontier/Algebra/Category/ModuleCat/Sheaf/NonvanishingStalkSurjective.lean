module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.VanishingSectionNakayama

/-!
# The nonvanishing locus is where a section generates the stalks

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings, `𝓛` an invertible
`𝒪_X`-module and `s` a global section of `𝓛`.  A point `x` lies in the nonvanishing locus `X_s`
of Stacks 01CY exactly when the stalk map of `s : 𝒪_X ⟶ 𝓛` at `x` is surjective, that is when
the germ of `s` generates `𝓛_x`.  One direction is clause 2 of Stacks 01CY
(`Stacks.SheafOfModules.bijective_stalkMapL_of_mem_nonvanishingLocus`); the other is Nakayama's
lemma, the stalk `𝓛_x` being free of rank one and hence finite and nonzero.

## Main results

* `Stacks.SheafOfModules.mem_nonvanishingLocus_iff_surjective_stalkMapL`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **The nonvanishing locus of a section of an invertible module is the locus where the
section generates the stalk.** -/
theorem mem_nonvanishingLocus_iff_surjective_stalkMapL
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections)
    (x : X.carrier) :
    x ∈ nonvanishingLocus L s ↔
      Function.Surjective (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val
        L.val (L.unitHomEquiv.symm s).val x) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  refine ⟨fun hx => (bijective_stalkMapL_of_mem_nonvanishingLocus ψ s x hx).2,
    fun hsurj => ?_⟩
  by_contra hx
  obtain ⟨e⟩ := nonempty_grpStalk_linearEquiv X L x
  have : Module.Finite (ringStalk X x) (grpStalk X L.val x) := Module.Finite.equiv e.symm
  have h0 := eq_zero_of_surjective_stalkMapL_of_mem_maximalSmul (L.unitHomEquiv.symm s)
    inferInstance hsurj (stalkMapL_unitHomEquiv_symm_mem_maximalSmul L s hx) (e.symm 1)
  have h1 : (1 : ringStalk X x) = 0 := by
    simpa using congrArg e h0
  exact one_ne_zero h1

end Stacks.SheafOfModules
