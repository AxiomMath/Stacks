module

public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# An open and closed piece of a closed subscheme is a closed subscheme of an open

Let `Z` be a closed subscheme of a scheme `Y` and `c : P ⟶ Z` an open and closed immersion. Then
`P` is the closed subscheme cut out by `Z` on the open `N ⊆ Y` complementary to the other piece:
`N` is the complement of the image in `Y` of the closed set `Z \ c(P)`, it contains `c(P)`, and
`Z ∩ N` is `P`. If moreover `Z` is an effective Cartier divisor on an open `V` of `Y` containing
`c(P)`, then `N` may be taken inside `V`, and `Z ∩ N` is an effective Cartier divisor on `N`
(Stacks 01WR).

This is how an open and closed piece of a relative effective Cartier divisor, produced by the
étale localization of quasi-finite morphisms (Stacks 02LN), is again an effective Cartier divisor
on an open of the ambient scheme, in the proof that families of curves are étale locally schemes
(Stacks 0E6F).

## Main results

* `Stacks.Divisors.exists_opens_iso_comap_subscheme_of_isOpenImmersion`: the open `N` and the
  isomorphism of `P` with `Z ∩ N`.

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- **An open and closed piece of a closed subscheme is a closed subscheme of an open.** Let `Z`
be a closed subscheme of `Y`, `V` an open of `Y` on which `Z` is an effective Cartier divisor,
and `c : P ⟶ Z` an open and closed immersion whose image lies over `V`. Then there are an open
`N ⊆ V` of `Y` containing the image of `P` such that `Z ∩ N` is an effective Cartier divisor on
`N`, and an isomorphism of `P` with `Z ∩ N` over `Y`. -/
theorem exists_opens_iso_comap_subscheme_of_isOpenImmersion {Y P : Scheme.{u}}
    (Z : Y.IdealSheafData) (V : Y.Opens) (hV : IsEffectiveCartierDivisor (Z.comap V.ι))
    (c : P ⟶ Z.subscheme) [IsOpenImmersion c] [IsClosedImmersion c]
    (hcV : Set.range (c ≫ Z.subschemeι) ⊆ V) :
    ∃ (N : Y.Opens) (_ : N ≤ V), Set.range (c ≫ Z.subschemeι) ⊆ N ∧
      IsEffectiveCartierDivisor (Z.comap N.ι) ∧
      ∃ e : P ≅ (Z.comap N.ι).subscheme,
        e.hom ≫ (Z.comap N.ι).subschemeι ≫ N.ι = c ≫ Z.subschemeι := by
  -- the image in `Y` of the other piece is closed
  set C : Set Z.subscheme := (Set.range c)ᶜ
  have hCc : IsClosed C := isClosed_compl_iff.2 c.isOpenEmbedding.isOpen_range
  have hιC : IsClosed (Z.subschemeι '' C) := Z.subschemeι.isClosedEmbedding.isClosedMap _ hCc
  let N : Y.Opens := V ⊓ ⟨(Z.subschemeι '' C)ᶜ, hιC.isOpen_compl⟩
  have hNV : N ≤ V := inf_le_left
  -- the points of `Z` over `N` are those of the piece
  have hpre : ∀ q : Z.subscheme, Z.subschemeι q ∈ N ↔ q ∈ Set.range c := by
    intro q
    constructor
    · rintro ⟨-, hq⟩
      by_contra h
      exact hq ⟨q, h, rfl⟩
    · rintro ⟨p, rfl⟩
      refine ⟨hcV ⟨p, rfl⟩, ?_⟩
      rintro ⟨q', hq', he⟩
      exact hq' ⟨p, (Z.subschemeι.isEmbedding.injective he).symm⟩
  have hrange : Set.range (c ≫ Z.subschemeι) ⊆ N :=
    Set.range_subset_iff.2 fun p => (hpre (c p)).2 ⟨p, rfl⟩
  -- `Z ∩ N` is the restriction of the Cartier divisor `Z ∩ V`
  have hcart : IsEffectiveCartierDivisor (Z.comap N.ι) := by
    have h := isPullbackDefined_of_flat (Y.homOfLE hNV) (Z.comap V.ι) hV
    change IsEffectiveCartierDivisor ((Z.comap V.ι).comap (Y.homOfLE hNV)) at h
    rwa [← Scheme.IdealSheafData.comap_comp, Y.homOfLE_ι] at h
  refine ⟨N, hNV, hrange, hcart, ?_⟩
  -- the isomorphism, through the open subscheme `Z.subschemeι ⁻¹ᵁ N` of `Z`
  have hopens : Set.range c = Set.range (Z.subschemeι ⁻¹ᵁ N).ι := by
    rw [Scheme.Opens.range_ι]
    ext q
    exact (hpre q).symm
  let e₁ : P ≅ (Z.subschemeι ⁻¹ᵁ N).toScheme :=
    IsOpenImmersion.isoOfRangeEq c (Z.subschemeι ⁻¹ᵁ N).ι hopens
  let e₂ : (Z.subschemeι ⁻¹ᵁ N).toScheme ≅ (Z.comap N.ι).subscheme :=
    (pullbackRestrictIsoRestrict Z.subschemeι N).symm ≪≫ pullbackSymmetry _ _ ≪≫
      (Z.comapIso N.ι).symm
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  simp only [e₁, e₂, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Scheme.IdealSheafData.comapIso_hom_fst Z N.ι, Category.assoc, Iso.inv_hom_id_assoc,
    pullback.condition,
    pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]

end Stacks.Divisors

end
