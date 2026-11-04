module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# A projective variety is a closed subvariety of the projective space of a vector space

A projective variety over a field `k` is isomorphic over `k` to a closed subscheme of `ℙᴺ_k`
(Tag 04L1 with Tag 01WB). The projections and the moving lemma of the intersection chapter are
stated for closed subvarieties of `𝐏(V) = AlgebraicGeometry.projectiveSpaceOfModule k V`; this file
records the embedding in that form, with `V = kᴺ⁺¹`.

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOfModule_of_isProjectiveVariety`:
  a projective variety admits a closed immersion over `k` into `𝐏(kᴺ⁺¹)` for some `N`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A projective variety embeds in `𝐏(kᴺ⁺¹)` over `k`.** The structure morphism of a projective
variety is H-projective: it factors as a closed immersion into `ℙᴺ_k` followed by the structure
morphism of `ℙᴺ_k`, and the standard basis of `kᴺ⁺¹` identifies `ℙᴺ_k` with `𝐏(kᴺ⁺¹)` over `k`
(`AlgebraicGeometry.basisProjectiveSpaceIso`). -/
public theorem exists_isClosedImmersion_projectiveSpaceOfModule_of_isProjectiveVariety
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjectiveVariety k p] :
    ∃ (N : ℕ) (iX : X ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k)),
      IsClosedImmersion iX ∧ iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = p ∧
        Module.finrank k (Fin (N + 1) → k) = N + 1 := by
  obtain ⟨N, i, hi, hip⟩ : IsProjectiveMorphism p := IsProjectiveVariety.isProjective
  refine ⟨N, i ≫ (basisProjectiveSpaceIso (Pi.basisFun k (Fin (N + 1)))).hom, ?_, ?_,
    Module.finrank_fin_fun k⟩
  · have := hi
    infer_instance
  · rw [Category.assoc, basisProjectiveSpaceIso_hom_comp_toSpec, ← hip]
    rfl

end AlgebraicGeometry
