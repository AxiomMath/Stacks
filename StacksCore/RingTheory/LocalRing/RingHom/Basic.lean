module

public import Mathlib.RingTheory.Ideal.Cotangent

/-! # Surjectivity of a local homomorphism from its cotangent map

Stacks tag 0E8M: a local homomorphism `A → B` of local rings is surjective as soon as `B` is
finite over `A`, `m_B` is finitely generated, the residue fields agree, and
`m_A/m_A² → m_B/m_B²` is surjective.

The proof splits in two, and the first half is the substance:
`IsLocalRing.map_maximalIdeal_eq_of_surjective_mapCotangent` upgrades surjectivity on cotangent
spaces to the ideal equality `m_A B = m_B`. Given that, the tag is one application of Nakayama —
Stacks 00DV (6), `LinearMap.surjective_of_surjective_comp_mkQ` — with the residue hypothesis
supplying its input.

That first half is where this diverges from the Stacks proof, which applies 00DV (6) twice:
once to `A → B` over `A`, and again to `m_A B → m_B` over `B`. Going through 00DV **(4)**
(`Submodule.le_of_le_smul_of_le_jacobson_bot`) instead gets the ideal equality directly, since
`m_B ≤ m_A B ⊔ m_B²` is exactly what the cotangent hypothesis says. The same substitution
shortened Stacks 0GLX, in `StacksCore.RingTheory.Support`.

Two points where the statement is not the tag's wording, both deliberate. The tag asks for an
*isomorphism* on residue fields; only **surjectivity** of `IsLocalRing.ResidueField.map` is ever
used, and injectivity is automatic for a local homomorphism, so the weaker hypothesis is taken.
And `Ideal.mapCotangent` is stated for an `AlgHom`, so `B` is presented as an `A`-algebra with
`[IsLocalHom (algebraMap A B)]` rather than as a bare ring map; this is how Mathlib states the
converse, `Ideal.mapCotangent_surjective_of_comap_eq`.
-/

@[expose] public section

open IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- If `m_A/m_A² → m_B/m_B²` is surjective and `m_B` is finitely generated, then `m_A B = m_B`.

This is Nakayama for the maximal ideal: the cotangent hypothesis says precisely that
`m_B ≤ m_A B ⊔ m_B • m_B`, and `Submodule.le_of_le_smul_of_le_jacobson_bot` — Stacks 00DV (4) —
converts that into `m_B ≤ m_A B`, the containment that is not automatic. Finiteness of `B` over
`A` is not needed here; only finite generation of `m_B`. -/
theorem IsLocalRing.map_maximalIdeal_eq_of_surjective_mapCotangent
    (hmB : (maximalIdeal B).FG)
    (hcot : Function.Surjective (Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B)
      (Algebra.ofId A B) (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm))) :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  refine le_antisymm (map_maximalIdeal_le _) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hmB
    (le_of_eq (Ideal.jacobson_bot (R := B) ▸ (ringJacobson_eq_maximalIdeal B).symm)) ?_
  intro y hy
  obtain ⟨z, hz⟩ := hcot (Ideal.toCotangent _ ⟨y, hy⟩)
  obtain ⟨⟨a, ha⟩, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
  rw [Ideal.mapCotangent_toCotangent] at hz
  have hsub : y - algebraMap A B a ∈ maximalIdeal B ^ 2 := by
    have h0 := sub_eq_zero.2 hz.symm
    rw [← map_sub] at h0
    simpa using (Ideal.toCotangent_eq_zero _ _).1 h0
  have hy' : y = algebraMap A B a + (y - algebraMap A B a) := by ring
  rw [hy']
  refine Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ ha))
    (Submodule.mem_sup_right ?_)
  rwa [Ideal.smul_eq_mul, ← sq]

/-- **Stacks 0E8M**: a local homomorphism `A → B` with `B` finite over `A`, `m_B` finitely
generated, surjective on residue fields, and surjective on cotangent spaces, is surjective.

The cotangent hypothesis gives `m_A B = m_B`, so `B ⧸ m_A B` is the residue field of `B`, and the
residue hypothesis says `A` already surjects onto it. Nakayama (00DV (6)) promotes that to
surjectivity of `A → B`.

The tag asks for an isomorphism on residue fields; surjectivity is all that is used. -/
@[stacks 0E8M]
theorem IsLocalRing.surjective_of_surjective_mapCotangent [Module.Finite A B]
    (hmB : (maximalIdeal B).FG)
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hcot : Function.Surjective (Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B)
      (Algebra.ofId A B) (le_of_eq (maximalIdeal_comap (algebraMap A B)).symm))) :
    Function.Surjective (algebraMap A B) := by
  have hmap := IsLocalRing.map_maximalIdeal_eq_of_surjective_mapCotangent hmB hcot
  refine LinearMap.surjective_of_surjective_comp_mkQ (Algebra.linearMap A B) (maximalIdeal A)
    (le_of_eq (Ideal.jacobson_bot (R := A) ▸ (ringJacobson_eq_maximalIdeal A).symm)) ?_
  intro q
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨x, hx⟩ := hres (residue B b)
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [ResidueField.map_residue] at hx
  exact ⟨a, by rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, hmap]; exact Ideal.Quotient.eq.1 hx⟩
