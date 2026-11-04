module

public import StacksFrontier.RingTheory.Nilpotent.Lifting

/-!
# Units and `n`th roots of `1` modulo a locally nilpotent ideal

Let `I` be an ideal of a commutative ring `R` all of whose elements are nilpotent. An element of
`R` is a unit exactly when its image in `R ⧸ I` is, so the quotient map induces a surjection on
unit groups. When moreover `n` is invertible in `R ⧸ I`, the `n`th power map is injective on
`1 + I`, so `1` is the only `n`th root of `1` lying in `1 + I`.

## Main results

* `Stacks.NilpotentIdeal.PowerMap.units_map_surjective`: units lift along `R → R ⧸ I`.
* `Stacks.NilpotentIdeal.PowerMap.eq_one_of_sub_one_mem_of_pow_eq_one`: an element of `1 + I`
  whose `n`th power is `1` equals `1`.
-/

@[expose] public section

namespace Stacks.NilpotentIdeal.PowerMap

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Units lift along the quotient by a locally nilpotent ideal: every unit of `R ⧸ I` is the
image of a unit of `R`. -/
theorem units_map_surjective (hI : ∀ x ∈ I, IsNilpotent x) :
    Function.Surjective (Units.map (Ideal.Quotient.mk I).toMonoidHom) := by
  intro u
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : R ⧸ I)
  have hxu : IsUnit ((Ideal.Quotient.mk I) x) := hx ▸ u.isUnit
  obtain ⟨v, rfl⟩ := isUnit_of_mk_isUnit I hI hxu
  exact ⟨v, Units.ext (by simpa using hx)⟩

/-- Uniqueness of `n`th roots of `1` in `1 + I`: if every element of `I` is nilpotent, `n` is
invertible in `R ⧸ I`, `a - 1 ∈ I` and `a ^ n = 1`, then `a = 1`. -/
theorem eq_one_of_sub_one_mem_of_pow_eq_one (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hnu : IsUnit ((n : R ⧸ I))) {a : R} (ha : a - 1 ∈ I) (han : a ^ n = 1) :
    a = 1 := by
  have h1 : (1 : R) - 1 ∈ I := by simp
  have hkey : powMap I n ⟨a, ha⟩ = powMap I n ⟨1, h1⟩ :=
    Subtype.ext (by simpa [powMap] using han)
  exact congrArg Subtype.val (powMap_injective I hI hnu hkey)

end Stacks.NilpotentIdeal.PowerMap

end
