module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite morphisms are the proper morphisms with finite fibres

A morphism of schemes is finite exactly when it is proper with finite fibres, exactly when it is
proper and locally quasi-finite, and exactly when it is universally closed, separated, locally of
finite type and has finite fibres. This is the first application of Zariski's main theorem in
the chapter *More on Morphisms* of the Stacks project.

## Main results

* `AlgebraicGeometry.IsFinite.tfae_isProper_finite_preimage_singleton`: the four conditions are
  equivalent. This is **Stacks Project, Tag 02LS**, and its first two conditions are
  **Stacks Project, Tag 02OG**, without that tag's hypothesis that the base is locally Noetherian.

## Implementation notes

"Finite fibres" is read set-theoretically, as finiteness of `f ⁻¹' {s}` for every point `s` of
the base: the scheme-theoretic fibre `X_s` is homeomorphic to `f ⁻¹' {s}`
(`AlgebraicGeometry.Scheme.Hom.fiberHomeo`), so the two readings agree.

The substantial implication, proper and locally quasi-finite implies finite, is Mathlib's
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, proved there by Zariski's main
theorem in Grothendieck's form rather than by the étale-local decomposition of the source. The
remaining implications are bookkeeping: a morphism locally of finite type with finite fibres is
locally quasi-finite (`AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton`), a
quasi-compact locally quasi-finite morphism has finite fibres
(`AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`), and a universally closed morphism is
quasi-compact, so universally closed, separated and locally of finite type is proper.

Tag 02OG, in *Cohomology of Schemes*, is the equivalence of the first two conditions over a
locally Noetherian base, proved there through the theorem on formal functions. The equivalence
holds over any base, so 02OG is registered on the same declaration rather than restated with a
hypothesis that does nothing.

## References

* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
* [Stacks Project, Tag 02OG](https://stacks.math.columbia.edu/tag/02OG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02LS.** For a morphism of schemes `f : X ⟶ S` the following are
equivalent:
1. `f` is finite;
2. `f` is proper with finite fibres;
3. `f` is proper and locally quasi-finite;
4. `f` is universally closed, separated, locally of finite type and has finite fibres.

The equivalence of the first two conditions is **Stacks Project, Tag 02OG**, stated there over a
locally Noetherian base; no hypothesis on the base is needed. -/
theorem IsFinite.tfae_isProper_finite_preimage_singleton {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [IsFinite f,
      IsProper f ∧ ∀ s, (f ⁻¹' {s}).Finite,
      IsProper f ∧ LocallyQuasiFinite f,
      UniversallyClosed f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ ∀ s, (f ⁻¹' {s}).Finite] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, f.finite_preimage_singleton⟩
  tfae_have 2 → 3 := fun ⟨_, h⟩ ↦ ⟨inferInstance, .of_finite_preimage_singleton f h⟩
  tfae_have 3 → 1 := (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr
  tfae_have 2 → 4 := fun ⟨_, h⟩ ↦ ⟨inferInstance, inferInstance, inferInstance, h⟩
  tfae_have 4 → 2 := fun ⟨_, _, _, h⟩ ↦ ⟨⟨⟩, h⟩
  tfae_finish

end AlgebraicGeometry

end
