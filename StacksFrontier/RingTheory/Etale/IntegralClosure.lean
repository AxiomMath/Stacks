module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Integral closure commutes with étale base change

Let `R → S` be an étale ring map, let `R → B` be an arbitrary ring map, let
`A = integralClosure R B` be the integral closure of `R` in `B` and let
`A' = integralClosure S (S ⊗[R] B)` be the integral closure of `S` in `S ⊗[R] B`. Every element
of `A` stays integral over `S` after base change, so there is a canonical `S`-algebra map
```
S ⊗[R] A → A' ,   s ⊗ a ↦ s ⊗ a ,
```
namely `TensorProduct.toIntegralClosure R S B`. This map is an isomorphism.

The proof is the one of the Stacks project. Injectivity holds because `S` is flat over `R`.
Bijectivity can be checked on a Zariski cover of `Spec S` by principal opens: integral closure
commutes with localization (Stacks 0307) and bijectivity of a module map is local (Stacks 00EO),
which is Mathlib's `TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway`. An étale
algebra is Zariski-locally standard étale (Stacks 00UE, Mathlib's
`Algebra.IsEtaleAt.exists_isStandardEtale`), and in the standard étale case surjectivity is
Mathlib's `mem_adjoin_map_integralClosure_of_isStandardEtale`.

## Main results

* `TensorProduct.toIntegralClosure_bijective_of_etale`: for `S` étale over `R`, the canonical map
  `S ⊗[R] integralClosure R B → integralClosure S (S ⊗[R] B)` is bijective.

## References

* [Stacks 03GE](https://stacks.math.columbia.edu/tag/03GE)

## Tags

integral closure, base change, étale ring map, tensor product
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]

/-- Let `R → S` be an étale ring map, let `R → B` be any ring map, let
`A = integralClosure R B` be the integral closure of `R` in `B` and let
`A' = integralClosure S (S ⊗[R] B)` be the integral closure of `S` in `S ⊗[R] B`. Then the
canonical map `S ⊗[R] A → A'`, `s ⊗ a ↦ s ⊗ a`, is an isomorphism. -/
@[stacks 03GE "The isomorphism of the tag is bijectivity of Mathlib's canonical map
`TensorProduct.toIntegralClosure`. The proof follows the tag: injectivity by flatness, then
bijectivity is checked on principal opens of `Spec S` on which `S` is standard étale (00UE,
Mathlib's `Algebra.IsEtaleAt.exists_isStandardEtale`), using that integral closure commutes with
localization (0307) and the local criterion 00EO (Mathlib's
`TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway`); the standard étale case is
Mathlib's `mem_adjoin_map_integralClosure_of_isStandardEtale`."]
theorem toIntegralClosure_bijective_of_etale [Algebra.Etale R S] :
    Function.Bijective (toIntegralClosure R S B) := by
  have (m : PrimeSpectrum S) : ∃ f ∉ m.asIdeal,
      Function.Bijective (toIntegralClosure R (Localization.Away f) B) := by
    obtain ⟨f, hfm, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) m.asIdeal
    refine ⟨f, hfm, toIntegralClosure_injective_of_flat, ?_⟩
    rintro ⟨x, hx⟩
    simp only [toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict, ← AlgHom.mem_range]
    refine Algebra.adjoin_le ?_ (mem_adjoin_map_integralClosure_of_isStandardEtale x hx)
    rintro _ ⟨y, hy : IsIntegral _ _, rfl⟩
    exact ⟨1 ⊗ₜ ⟨y, hy⟩, by simp⟩
  choose f hfm hf using this
  refine toIntegralClosure_bijective_of_isLocalizationAway (R := R)
    (s := Set.range f) (B := B) ?_ (Localization.Away ·.1) (Set.forall_subtype_range_iff.mpr hf)
  by_contra H
  obtain ⟨m, hm, e⟩ := Ideal.exists_le_maximal _ H
  exact hfm ⟨m, inferInstance⟩ (e (Ideal.subset_span (Set.mem_range_self ⟨m, inferInstance⟩)) :)

end TensorProduct

end
