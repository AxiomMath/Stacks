module

public import Mathlib.RingTheory.Localization.Defs

/-!
# The universal property of localization

Let `M` be a submonoid of a commutative ring `R` and `S` a localization of `R` at `M`. A ring
map `f : R →+* P` sending every element of `M` to a unit factors uniquely through the localization
map `R → S` (`Stacks.Localization.existsUnique_ringHom_comp_algebraMap_eq`).
-/

@[expose] public section

namespace Stacks.Localization

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization M S] {P : Type*} [CommRing P]

/-- The universal property of localization: if a ring map `f : R →+* P` sends every element of
`M` to a unit of `P`, there is a unique ring map `g : S →+* P` out of the localization
`S = M⁻¹R` with `g ∘ (R → S) = f`. -/
@[stacks 00CP "Stated for any localization `S` of `R` at `M`, in particular `Localization M`."]
theorem existsUnique_ringHom_comp_algebraMap_eq {f : R →+* P} (hf : ∀ y : M, IsUnit (f y)) :
    ∃! g : S →+* P, g.comp (algebraMap R S) = f :=
  ⟨IsLocalization.lift hf, IsLocalization.lift_comp hf, fun _ hg =>
    IsLocalization.ringHom_ext M (hg.trans (IsLocalization.lift_comp hf).symm)⟩

end Stacks.Localization
