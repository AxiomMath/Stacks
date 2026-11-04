module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# The cardinality of a ring extension with a given kernel

A surjective ring homomorphism `f : R → S` presents `R` as a union of cosets of
`RingHom.ker f`, one for each element of `S`, so `#R ≤ #S * #(Ker f)`. Together with the
closure of a cardinal bound under products this is what makes an extension of a ring by a
small ideal small again.

## Main results

* `Cardinal.mk_le_mul_mk_ker` — the bound `#R ≤ #S * #(Ker f)` for a surjective ring
  homomorphism `f : R → S`.
* `Cardinal.mk_le_max_of_surjective_of_mk_ker_le_max` — the same bound in the shape the size
  estimates for schemes consume: if `#(Ker f) ≤ max ℵ₀ #S`, then `#R ≤ max ℵ₀ #S`.

## Implementation notes

The estimate on a single fibre is an injection, not a bijection: a chosen preimage `r` of `s`
turns the fibre over `s` into the coset `r + Ker f`, and subtracting `r` embeds that fibre into
the kernel. Only `Cardinal.mk_le_mk_mul_of_mk_preimage_le` is then needed, which sums the fibre
estimates. Surjectivity is used only to produce the chosen preimage; without it the fibres over
elements outside the image are empty and the bound holds a fortiori, but the statement is used
only for surjections and is left in that form.
-/

@[expose] public section

open Cardinal

universe u

namespace Cardinal

/-- A surjective ring homomorphism `f : R → S` exhibits every fibre as a coset of `Ker f`,
whence `#R ≤ #S * #(Ker f)`. -/
public theorem mk_le_mul_mk_ker {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) : #R ≤ #S * #(RingHom.ker f) := by
  refine mk_le_mk_mul_of_mk_preimage_le (f := f) fun s => ?_
  obtain ⟨r, hr⟩ := hf s
  have hmem : ∀ b : (f ⁻¹' {s} : Set R), (b : R) - r ∈ RingHom.ker f := fun b => by
    have hb : f (b : R) = s := b.2
    simp [RingHom.mem_ker, hb, hr]
  refine mk_le_of_injective
    (f := fun b : (f ⁻¹' {s} : Set R) => (⟨(b : R) - r, hmem b⟩ : RingHom.ker f))
    fun b₁ b₂ hb => ?_
  have h : (b₁ : R) - r = (b₂ : R) - r := congrArg Subtype.val hb
  exact Subtype.ext (sub_left_inj.mp h)

/-- `Cardinal.mk_le_mul_mk_ker` in the shape the size estimates for schemes consume: a ring
surjecting onto `S` with kernel of cardinality at most `max ℵ₀ #S` has cardinality at most
`max ℵ₀ #S`. -/
public theorem mk_le_max_of_surjective_of_mk_ker_le_max {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : #(RingHom.ker f) ≤ max ℵ₀ #S) : #R ≤ max ℵ₀ #S :=
  (mk_le_mul_mk_ker f hf).trans <|
    (mul_le_max _ _).trans <|
      max_le (max_le (le_max_right _ _) hker) (le_max_left _ _)

end Cardinal
