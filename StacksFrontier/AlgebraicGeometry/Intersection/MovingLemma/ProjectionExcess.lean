module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ChainInduction
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints

/-!
# The excess of a moved subvariety drops along a general finite projection

Let `X ⊆ 𝐏(V)` be a nonsingular closed subvariety of dimension `n < N = dim 𝐏(V)`, let `Z ⊆ X`
be a closed subvariety of dimension `d < n` and let `T i ⊆ X` be finitely many closed
subvarieties of dimensions `d' i < n`. The proof of Tag 0B0E produces a finite projection
`π : X ⟶ 𝐏^n` from a general linear centre such that every closed subvariety `W ⊆ π^{-1}(π(Z))`
of dimension `d` other than `Z` itself meets each `T i` in less excess than `Z` does:

* `dim (W ∩ T i) ≤ dim (Z ∩ T i)` or `dim (W ∩ T i) + n ≤ d + d' i`, and
* `dim (W ∩ T i) < dim (Z ∩ T i)` whenever `Z` does not intersect `T i` properly.

The source states this for the components `Z_j` of `C · X`, where `C` is the cone over `π(Z)`;
those components are the components of `π^{-1}(π(Z))` other than `Z`, and the argument is about
them as subsets only, so it is stated here for every such `W`. The projection is moreover étale
at the generic point of `Z`, which is what makes `Z` occur with multiplicity one in the flat
pullback `π^*[π(Z)]` used by the moving lemma.

## Main results

* `exists_isFinite_excess_clauses_of_le_of_isOpenImmersion` of
  `AlgebraicGeometry.ProjectiveSpaceOfModule`: a finite morphism to `𝐏^n` with the two clauses,
  for `n ≤ N`, read in an open subset of the nonsingular locus. Its case `n < N` is
  `exists_isFinite_projection_excess_clauses_of_isOpenImmersion`, which lives in
  `StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma` because the proofs of Remark
  0B61 and of Tag 0B0E there use it.

## Implementation notes

The projection and conditions (1)–(4) of the proof of Tag 0B0E are
`exists_submodule_finrank_eq_isFinite_etaleAt_projection_family`, with the dimension bound of the
error term of condition (4) taken separately for each `T i`; that is what lets the `T i` have
different dimensions. The two clauses are then read off condition (4) exactly as in the proof of
Tag 0B0E (`exists_intersectProperly_torFormulaCycleIntersectionProduct_eq`): a component of
`W ∩ T i` lies either in the error term, of dimension at most `d + d' i - n`, or in `Z ∩ T i`,
and in the latter case it misses the chosen point of each component of `Z ∩ T i` by condition (3),
so it is a proper closed subset of such a component.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
* [Stacks Project, Tag 0AZP](https://stacks.math.columbia.edu/tag/0AZP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **A finite morphism to `𝐏^n` along which the excess drops, for `n ≤ N`, read in an open
subset of the nonsingular locus.** Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension
`n ≤ N = dim 𝐏(V)`, let `j₀ : U ⟶ X` be an open immersion whose image lies in the nonsingular
locus, let `ζ` be a point of `U` whose closure `Z` in `X` has dimension `d < n`, and let `T i ⊆ X`
be finitely many closed subsets of dimensions at most `d' i < n`. Then there is a finite morphism
`π : X ⟶ 𝐏(W)` over `k` to the projective space of a subspace `W ≤ V` of dimension `n + 1`, such
that the maximal ideal of `𝒪_{𝐏(W), π ζ}` generates that of `𝒪_{U, ζ}` along `j₀ ≫ π`, and such
that the two excess clauses of `exists_isFinite_projection_excess_clauses_of_isOpenImmersion`,
read in `U`, hold for every closed subvariety of `π^{-1}(π(Z))` of dimension `d` other than `Z`.

For `n < N` the morphism is the projection of
`exists_isFinite_projection_excess_clauses_of_isOpenImmersion`, étale at `ζ`. For `n = N` it is the
closed immersion of `X` itself, read in `𝐏(⊤)`; then `π^{-1}(π(Z)) = Z` and the clauses are
vacuous. -/
public theorem exists_isFinite_excess_clauses_of_le_of_isOpenImmersion [IsAlgClosed k]
    [FiniteDimensional k V] {N n d : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hnN : n ≤ N) (hd : d < n)
    {Y : Scheme.{u}} (j₀ : Y ⟶ X) [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus X)
    (ζ : Y) (hZd : topologicalKrullDim ↥(closure ({j₀.base ζ} : Set X)) = (d : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (T : ι → Set X) (hTcl : ∀ i, IsClosed (T i)) {d' : ι → ℕ}
    (hd' : ∀ i, d' i < n) (hTd : ∀ i, topologicalKrullDim ↥(T i) ≤ (d' i : WithBot ℕ∞)) :
    ∃ W : Submodule k V, Module.finrank k ↥W = n + 1 ∧
      ∃ π : X ⟶ projectiveSpaceOfModule k ↥W, IsFinite π ∧
        π ≫ projectiveSpaceOfModuleToSpec k ↥W = iX ≫ projectiveSpaceOfModuleToSpec k V ∧
        Ideal.map ((j₀ ≫ π).stalkMap ζ).hom
            (IsLocalRing.maximalIdeal ((projectiveSpaceOfModule k ↥W).presheaf.stalk
              ((j₀ ≫ π).base ζ))) =
          IsLocalRing.maximalIdeal (Y.presheaf.stalk ζ) ∧
        ∀ W' : Set X, IsClosed W' → IsIrreducible W' →
          W' ⊆ π.base ⁻¹' (π.base '' closure ({j₀.base ζ} : Set X)) →
          topologicalKrullDim ↥W' = (d : WithBot ℕ∞) → W' ≠ closure ({j₀.base ζ} : Set X) →
          ∀ i,
            (topologicalKrullDim ↥(j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i) ≤
                topologicalKrullDim ↥(j₀.base ⁻¹' closure ({j₀.base ζ} : Set X) ∩
                  j₀.base ⁻¹' T i) ∨
              topologicalKrullDim ↥(j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i) + (n : WithBot ℕ∞) ≤
                (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞)) ∧
            (¬ topologicalKrullDim ↥(j₀.base ⁻¹' closure ({j₀.base ζ} : Set X) ∩
                  j₀.base ⁻¹' T i) + (n : WithBot ℕ∞) ≤
                (d : WithBot ℕ∞) + (d' i : WithBot ℕ∞) →
              topologicalKrullDim ↥(j₀.base ⁻¹' W' ∩ j₀.base ⁻¹' T i) <
                topologicalKrullDim ↥(j₀.base ⁻¹' closure ({j₀.base ζ} : Set X) ∩
                  j₀.base ⁻¹' T i)) := by
  have hZirr : IsIrreducible (closure ({j₀.base ζ} : Set X)) := isIrreducible_singleton.closure
  have hgen : hZirr.genericPoint = j₀.base ζ :=
    (hZirr.isGenericPoint_genericPoint isClosed_closure).eq isGenericPoint_closure
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (iX ≫ projectiveSpaceOfModuleToSpec k V)
  rcases lt_or_eq_of_le hnN with hlt | heq
  · obtain ⟨W, hWrank, j, hj, hfin, het, hcl⟩ :=
      exists_isFinite_projection_excess_clauses_of_isOpenImmersion k V hV iX hdimX hlt hd j₀ hU
        (closure ({j₀.base ζ} : Set X)) isClosed_closure hZirr
        ⟨ζ, subset_closure (Set.mem_singleton _)⟩ hZd T hTcl hd' hTd
    rw [hgen] at het
    have := hfin
    have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hWrank]; omega)
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
      (j₀ ≫ iX ≫ projectiveSpaceOfModuleToSpec k V)
    have : LocallyOfFinitePresentation (j₀ ≫ j ≫ projection k V W) :=
      instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
    have het' : EtaleAt (j₀ ≫ j ≫ projection k V W) ζ :=
      etaleAt_comp j₀ _ ((etale_iff_forall_etaleAt j₀).mp inferInstance ζ) het
    refine ⟨W, hWrank, j ≫ projection k V W, hfin, ?_,
      TorFormula.map_maximalIdeal_stalkMap_eq_of_etaleAt _ ζ het', hcl⟩
    rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]
  · subst heq
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hV]; omega)
    set e : projectiveSpaceOfModule k V ≅ projectiveSpaceOfModule k ↥(⊤ : Submodule k V) :=
      mapOfLinearEquiv (Submodule.topEquiv : ↥(⊤ : Submodule k V) ≃ₗ[k] V) with he
    have hrank : Module.finrank k ↥(⊤ : Submodule k V) = n + 1 := by
      rw [finrank_top]; exact hV
    have hinj : Function.Injective (iX ≫ e.hom).base := by
      have h1 : Function.Injective iX.base := iX.isClosedEmbedding.injective
      have h2 : Function.Injective e.hom.base :=
        (Scheme.homeoOfIso e).injective
      exact h2.comp h1
    refine ⟨⊤, hrank, iX ≫ e.hom, inferInstance, ?_, ?_, ?_⟩
    · rw [Category.assoc, he, mapOfLinearEquiv_hom_comp_toSpec]
    · exact IsLocalRing.map_maximalIdeal_of_surjective _
        ((j₀ ≫ iX ≫ e.hom).stalkMap_surjective ζ)
    · intro W' hW'cl hW'irr hW'sub hW'dim hW'ne
      exfalso
      have hW'Z : W' ⊆ closure ({j₀.base ζ} : Set X) := by
        rw [Set.preimage_image_eq _ hinj] at hW'sub
        exact hW'sub
      have : IrreducibleSpace ↥(closure ({j₀.base ζ} : Set X)) := Subtype.irreducibleSpace hZirr
      have hAne : ((Subtype.val : ↥(closure ({j₀.base ζ} : Set X)) → X) ⁻¹' W') ≠
          Set.univ := by
        intro hcon2
        exact hW'ne (Set.Subset.antisymm hW'Z fun z hz =>
          (hcon2 ▸ Set.mem_univ (⟨z, hz⟩ : ↥(closure ({j₀.base ζ} : Set X))) :
            (⟨z, hz⟩ : ↥(closure ({j₀.base ζ} : Set X))) ∈ _))
      have hlt2 := topologicalKrullDim_lt_of_isClosed_ne_univ
        (hW'cl.preimage continuous_subtype_val) hAne
        (by rw [hZd]; exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top d))
      rw [topologicalKrullDim_preimage_val _ W' hW'Z, hW'dim, hZd] at hlt2
      exact absurd hlt2 (lt_irrefl _)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
