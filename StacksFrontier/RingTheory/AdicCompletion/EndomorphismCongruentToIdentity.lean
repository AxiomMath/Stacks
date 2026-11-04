module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.RingTheory.Noetherian.Endomorphism

/-!
# Endomorphisms of a complete local ring that are the identity to first order

Let `P` be a Noetherian local ring, complete for the `𝔪`-adic topology. An endomorphism of `P`
which moves every element only by an amount in `𝔪 ^ 2` is an automorphism. The reason is that
such an endomorphism is the identity on the cotangent space `𝔪 / 𝔪 ^ 2` and on the residue
field, and for a complete ring those two first-order statements already force surjectivity;
surjectivity then upgrades to bijectivity because `P` is Noetherian.

This is the first-order rigidity used to recognise an isomorphism of complete local rings from a
congruence: a map which agrees with a known isomorphism modulo `𝔪 ^ 2` differs from it by such
an endomorphism, and is therefore an isomorphism itself.

## Main results

* `surjective_of_residue_surjective_of_cotangent_span`: an endomorphism of a complete Noetherian
  local ring whose image spans the cotangent space and which is surjective on the residue field
  is surjective.
* `surjective_of_sub_id_mem_maximalIdeal_sq` and `bijective_of_sub_id_mem_maximalIdeal_sq`: an
  endomorphism with `f x - x ∈ 𝔪 ^ 2` for every `x` is surjective, hence bijective.

## Implementation notes

The spanning hypothesis is transported from the residue field to `P` by
`IsLocalRing.CotangentSpace.span_image_eq_top_iff`, which turns it into `Ideal.map f 𝔪 = 𝔪`.
That equality is what makes `P` Hausdorff for the ideal `Ideal.map f 𝔪`, and so lets
`surjective_of_mk_map_comp_surjective` — the successive-approximation argument for a complete
ring — conclude surjectivity from surjectivity modulo `𝔪`. Bijectivity is then Stacks 06RN,
`surjective_endomorphism_noetherian_bijective`.
-/

@[expose] public noncomputable section

open IsLocalRing

/-- An endomorphism of a complete Noetherian local ring is surjective as soon as its image spans
the cotangent space `𝔪 / 𝔪 ^ 2` over the residue field and it is surjective modulo `𝔪`. -/
theorem surjective_of_residue_surjective_of_cotangent_span
    (P : Type*) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (maximalIdeal P) P] (f : P →+* P)
    (hfm : ∀ x : P, x ∈ maximalIdeal P → f x ∈ maximalIdeal P)
    (hcot : Submodule.span (ResidueField P)
      ((maximalIdeal P).toCotangent ''
        Set.range (fun x : maximalIdeal P => (⟨f x, hfm x x.2⟩ : maximalIdeal P))) = ⊤)
    (hquot : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal P)).comp f)) :
    Function.Surjective f := by
  let m := maximalIdeal P
  let s : Set m := Set.range (fun x : m => (⟨f x, hfm x x.2⟩ : m))
  have hspan : Submodule.span P s = ⊤ :=
    IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hcot
  have hmap_le : Ideal.map f m ≤ m :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => hfm x hx
  have hmap_ge : m ≤ Ideal.map f m := by
    intro x hx
    let M : Submodule P m :=
      Submodule.comap m.subtype ((Ideal.map f m : Ideal P) : Submodule P P)
    have hs_le : Submodule.span P s ≤ M :=
      Submodule.span_le.mpr (by
        rintro y ⟨z, rfl⟩
        exact Ideal.mem_map_of_mem f z.2)
    have htop : M = ⊤ := top_unique (hspan ▸ hs_le)
    exact (htop.symm ▸ Submodule.mem_top : (⟨x, hx⟩ : m) ∈ M)
  have hmap : Ideal.map f m = m := le_antisymm hmap_le hmap_ge
  have hqmap : Function.Surjective ((Ideal.Quotient.mk (Ideal.map f m)).comp f) := by
    rwa [hmap]
  have : IsHausdorff (Ideal.map f m) P := hmap.symm ▸ inferInstance
  exact surjective_of_mk_map_comp_surjective (I := m) f hqmap

/-- An endomorphism of a complete Noetherian local ring which is the identity modulo `𝔪 ^ 2` is
surjective. -/
theorem surjective_of_sub_id_mem_maximalIdeal_sq
    (P : Type*) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (maximalIdeal P) P] (f : P →+* P)
    (hf : ∀ x : P, f x - x ∈ maximalIdeal P ^ 2) :
    Function.Surjective f := by
  let m := maximalIdeal P
  have hp : m ^ 2 ≤ m := Ideal.pow_le_self two_ne_zero
  have hfm : ∀ x : P, x ∈ m → f x ∈ m := fun x hx => by
    simpa using m.add_mem (hp (hf x)) hx
  refine surjective_of_residue_surjective_of_cotangent_span P f hfm ?_ ?_
  · refine top_unique fun z _ => ?_
    obtain ⟨x, rfl⟩ := m.toCotangent_surjective z
    have heq : m.toCotangent (⟨f x, hfm x x.2⟩ : m) = m.toCotangent x :=
      (Ideal.toCotangent_eq m).mpr (hf x)
    rw [← heq]
    exact Submodule.subset_span ⟨⟨f x, hfm x x.2⟩, ⟨x, rfl⟩, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, Ideal.Quotient.eq.mpr (hp (hf x))⟩

/-- An endomorphism of a complete Noetherian local ring which is the identity modulo `𝔪 ^ 2` is
bijective: it is surjective by `surjective_of_sub_id_mem_maximalIdeal_sq`, and a surjective
endomorphism of a Noetherian ring is injective. -/
theorem bijective_of_sub_id_mem_maximalIdeal_sq
    (P : Type*) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    [IsAdicComplete (maximalIdeal P) P] (f : P →+* P)
    (hf : ∀ x : P, f x - x ∈ maximalIdeal P ^ 2) :
    Function.Bijective f :=
  surjective_endomorphism_noetherian_bijective P f
    (surjective_of_sub_id_mem_maximalIdeal_sq P f hf)

end
