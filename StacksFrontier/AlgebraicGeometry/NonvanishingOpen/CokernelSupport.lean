module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingStalkSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The support of the cokernel of a section of an invertible module

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings, `𝓛` an invertible
`𝒪_X`-module and `s` a global section of `𝓛`, the map `φ_s : 𝒪_X ⟶ 𝓛`, `1 ↦ s`.  The support of
the cokernel of `φ_s` is the complement of the nonvanishing locus `X_s` of Stacks 01CY: the
stalk functor preserves cokernels, so `x` is outside the support exactly when the stalk map of
`φ_s` at `x` is surjective, which is membership in `X_s` by
`Stacks.SheafOfModules.mem_nonvanishingLocus_iff_surjective_stalkMapL`.

## Main results

* `Stacks.SheafOfModules.supp_cokernel_unitHomEquiv_symm`: `Supp(coker φ_s) = X \ X_s`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- **The support of the cokernel of a section of an invertible module is the complement of its
nonvanishing locus.** -/
theorem supp_cokernel_unitHomEquiv_symm
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections) :
    _root_.SheafOfModules.supp (cokernel (L.unitHomEquiv.symm s)) =
      (nonvanishingLocus L s)ᶜ := by
  ext x
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x
  set φ := L.unitHomEquiv.symm s
  have key : x ∉ _root_.SheafOfModules.supp (cokernel φ) ↔ Epi (T.map φ) := by
    rw [Preadditive.epi_iff_isZero_cokernel, ← (PreservesCokernel.iso T φ).isZero_iff,
      ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun hx => ⟨fun a b => by_contra fun hab => hx ⟨a - b, sub_ne_zero.mpr hab⟩⟩,
      fun ⟨h⟩ ⟨a, ha⟩ => ha (h a 0)⟩
  have hsurj : Epi (T.map φ) ↔ Function.Surjective
      (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val φ.val x) :=
    ModuleCat.epi_iff_surjective _
  rw [Set.mem_compl_iff, mem_nonvanishingLocus_iff_surjective_stalkMapL, ← hsurj, ← key,
    not_not]

end Stacks.SheafOfModules
