module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization

/-!
# Completion at a maximal ideal is completion of the local ring there

Let `C` be a commutative ring and `𝔮` a maximal ideal. The localization map `C → C_𝔮` is flat and
is an isomorphism modulo `𝔮` — both sides are the residue field — so it induces an isomorphism of
the `𝔮`-adic completion of `C` with the `𝔮 C_𝔮`-adic completion of `C_𝔮`, compatibly with the
maps from `C`. Since `𝔮 C_𝔮` is the maximal ideal of `C_𝔮`, this says that completing a ring at a
maximal ideal computes the completion of the local ring at the corresponding point, which is what
makes a computation of `AdicCompletion 𝔮 C` a computation of a completed local ring of
`Spec C`.

## Main results

* `Stacks.MaximalLocalization.bijective_quotientMap_localizationAtPrime` — the localization map is
  an isomorphism modulo a maximal ideal.
* `Stacks.MaximalLocalization.exists_adicCompletionAlgEquiv_localizationAtPrime` — **the `𝔮`-adic
  completion of `C` is the completion of `C_𝔮`**, compatibly with the maps from `C`.

## Implementation notes

Surjectivity modulo `𝔮` is the one computation: an element of `C_𝔮` is `a/s` with `s ∉ 𝔮`, and
maximality of `𝔮` provides `c` with `cs ≡ 1` mod `𝔮`, so `a/s` and `ac` agree modulo `𝔮 C_𝔮`.
Injectivity is free because `C ⧸ 𝔮` is a field and the target is nontrivial. The passage from the
single congruence to all the powers, and from there to the completions, is
`exists_adicCompletionAlgEquiv_of_flat`, which needs exactly flatness of the localization.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.MaximalLocalization

variable {C : Type u} [CommRing C] (q : Ideal C) [hq : q.IsMaximal]

/-- **The localization at a maximal ideal is an isomorphism modulo that ideal.** Both sides are
the residue field at `𝔮`. -/
public theorem bijective_quotientMap_localizationAtPrime :
    Function.Bijective (Ideal.quotientMap
      (Ideal.map (algebraMap C (Localization.AtPrime q)) q)
      (algebraMap C (Localization.AtPrime q)) Ideal.le_comap_map) := by
  have hne : Ideal.map (algebraMap C (Localization.AtPrime q)) q ≠ ⊤ := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact (maximalIdeal.isMaximal (Localization.AtPrime q)).ne_top
  let : Field (C ⧸ q) := Ideal.Quotient.field q
  have : Nontrivial (Localization.AtPrime q ⧸
      Ideal.map (algebraMap C (Localization.AtPrime q)) q) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
  obtain ⟨c, i, hi, hci⟩ := hq.exists_inv s.2
  refine ⟨Ideal.Quotient.mk _ (a * c), ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime q) a s
  have hci' := congrArg (algebraMap C (Localization.AtPrime q)) hci
  rw [map_add, map_mul, map_one] at hci'
  have hkey : algebraMap C (Localization.AtPrime q) (a * c) -
        IsLocalization.mk' (Localization.AtPrime q) a s =
      -(IsLocalization.mk' (Localization.AtPrime q) a s *
        algebraMap C (Localization.AtPrime q) i) := by
    rw [map_mul]
    linear_combination IsLocalization.mk' (Localization.AtPrime q) a s * hci' -
      algebraMap C (Localization.AtPrime q) c * hspec
  rw [hkey]
  exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hi))

/-- **The `𝔮`-adic completion of `C` is the completion of the local ring `C_𝔮`**, compatibly with
the canonical maps from `C`. -/
public theorem exists_adicCompletionAlgEquiv_localizationAtPrime :
    ∃ E : AdicCompletion q C ≃ₐ[C]
        AdicCompletion (Ideal.map (algebraMap C (Localization.AtPrime q)) q)
          (Localization.AtPrime q),
      ∀ c : C, E (algebraMap C (AdicCompletion q C) c) =
        algebraMap (Localization.AtPrime q)
          (AdicCompletion (Ideal.map (algebraMap C (Localization.AtPrime q)) q)
            (Localization.AtPrime q))
          (algebraMap C (Localization.AtPrime q) c) :=
  exists_adicCompletionAlgEquiv_of_flat q (bijective_quotientMap_localizationAtPrime q)

end Stacks.MaximalLocalization

end
