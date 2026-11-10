module

public import StacksFrontier.AlgebraicGeometry.GenericFlatness.NoetherianFlatStratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhCoveringRefinement

/-!
# The closed subschemes of a flat stratification form a ph covering

The proofs of Stacks 0ETR and Stacks 0ETT both begin by stratifying the base by generic flatness
and then *covering* the base by the closed subschemes of that stratification, so that the problem
may be solved one stratum at a time. This file supplies the covering half of that step.

The family of closed subschemes `S_0 ⊇ S_1 ⊇ ⋯ ⊇ S_{t-1}` of a flat stratification — the members
of the chain except the empty last one — is a ph covering of `S`. It is jointly surjective
because `S_0 ⊆ S` is a thickening and `S_t = ∅`, so every point of `S` lies in some stratum
`S_i ∖ S_{i+1}` and in particular in `S_i`; and a jointly surjective finite family of proper
morphisms is a ph covering.

## Main results

* `AlgebraicGeometry.isPHCovering_of_isProper_of_exists_mem_range`: a finite, jointly surjective
  family of proper morphisms with a common target is a ph covering. This is the family form of
  Stacks 0DES.
* `AlgebraicGeometry.Scheme.IdealSheafData.isPHCovering_subschemeι_castSucc`: the closed
  subschemes of a flat stratification form a ph covering of the base.
* `AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_flat_stratum`: the step of the
  proofs of Stacks 0ETR and Stacks 0ETT this is for — a morphism with a flat stratification admits
  a finite ph covering of its base by closed subschemes, each carrying an open over which the
  morphism base changes flat.

## Implementation notes

Joint surjectivity is turned into a ph covering through
`AlgebraicGeometry.isPHCovering_tfae`, Stacks 0ET9: the family is a ph covering as soon as the
single morphism from the coproduct of its sources is one, that morphism is proper by
`AlgebraicGeometry.isProper_sigmaDesc` and surjective because every point of the target is hit by
some member, and a proper surjection is a ph covering by Stacks 0DES. Finiteness of the index type
enters only through `AlgebraicGeometry.isProper_sigmaDesc`, where it is what makes the coproduct
morphism closed.

The family is indexed by `Fin t` and its `i`-th member is `S_{i}` written as
`I i.castSucc`, matching the indexing of the flatness clauses of
`AlgebraicGeometry.HasFlatStratification`: the `i`-th clause is about the stratum
`S_i ∖ S_{i+1}`, an open of `S_i`, and the `i`-th member of the covering is the `S_i` that stratum
is an open of. The last member `S_t = ∅` of the chain is not in the family — it would contribute
nothing, being empty — and no clause of the stratification is about it.

## References

* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
* [Stacks Project, Tag 0DES](https://stacks.math.columbia.edu/tag/0DES)
* [Stacks Project, Tag 0ET9](https://stacks.math.columbia.edu/tag/0ET9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **The family form of Stacks 0DES.** A finite family of proper morphisms with a common target
which is jointly surjective is a ph covering.

The morphism from the coproduct of the sources is proper by
`AlgebraicGeometry.isProper_sigmaDesc` and surjective because every point of the target lies in
the image of some member; a proper surjection is a ph covering by Stacks 0DES, and a family whose
coproduct morphism is a ph covering is one by Stacks 0ET9. -/
theorem isPHCovering_of_isProper_of_exists_mem_range {T : Scheme.{u}} {I : Type v} [Finite I]
    [Small.{u} I] (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) [∀ i, IsProper (f i)]
    (hsurj : ∀ t : T, ∃ i, t ∈ Set.range (f i).base) :
    IsPHCovering X f := by
  have _ : IsProper (Sigma.desc f) := isProper_sigmaDesc f
  have _ : Surjective (Sigma.desc f) := by
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨i, x, hx⟩ := hsurj t
    refine ⟨(Sigma.ι X i).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    simpa using hx
  exact ((isPHCovering_tfae X f fun i ↦ inferInstance).out 3 1).1
    (surjective_proper_isPHCovering (Sigma.desc f))

/-- **The closed subschemes of a flat stratification form a ph covering of the base.** If `I` is
an ascending chain of quasi-coherent ideal sheaves on `S` whose first member cuts out a thickening
of `S` and whose last member is the unit ideal — the two clauses of
`AlgebraicGeometry.HasFlatStratification` that control the ends of the chain — then the closed
subschemes `S_0, …, S_{t-1}` cut out by `I 0, …, I (t-1)` form a ph covering of `S`.

Every point of `S` lies in one of the strata `S_i ∖ S_{i+1}` by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_mem_stratum_of_isThickening`, hence in `S_i`, so
the family is jointly surjective; its members are closed immersions, hence proper. -/
theorem Scheme.IdealSheafData.isPHCovering_subschemeι_castSucc {S : Scheme.{u}} {t : ℕ}
    (I : Fin (t + 1) → S.IdealSheafData)
    (h0 : Stacks.Thickenings.IsThickening (I 0).subschemeι) (hlast : I (Fin.last t) = ⊤) :
    IsPHCovering (fun i : Fin t ↦ (I i.castSucc).subscheme)
      (fun i : Fin t ↦ (I i.castSucc).subschemeι) := by
  refine isPHCovering_of_isProper_of_exists_mem_range _ _ fun s ↦ ?_
  obtain ⟨i, hi, -⟩ := Scheme.IdealSheafData.exists_mem_stratum_of_isThickening I h0 hlast s
  exact ⟨i, by rw [Scheme.IdealSheafData.range_subschemeι]; exact hi⟩

/-- **The covering step of the proofs of Stacks 0ETR and Stacks 0ETT.** A morphism `f : X ⟶ S`
with a flat stratification of its base admits a finite ph covering `{Z k ⟶ S}` of that base by
closed subschemes, together with, for each `k`, an open `U k` of `Z k` such that `f` base changes
to a flat morphism over `U k`, and such that every point of `S` is in the image of the open `U k`
of some member.

This is the reduction both proofs perform before flattening: by transitivity of ph coverings
(Stacks 0DBI part (2)) and stability of the covering conditions under base change, the problem over
`S` is replaced by the problem over each `Z k`, where the family has become flat over an open.

What the Stacks proofs use and this does not provide is that `U k` may be taken **dense** in
`Z k`: there one replaces `Z k` by the scheme-theoretic closure of the stratum `U k` inside it,
which is possible because the stratum is a quasi-compact open. Density is what the flattening
blowup of Stacks 0815 needs in order to be made dense (Stacks 080Y), and what the valuative
lifting at the end of both proofs needs in order to see the generic point of a valuation ring
inside the flat locus. That replacement is
`AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_dense_flat_stratum` in
`StacksFrontier/AlgebraicGeometry/GenericFlatness/StratificationDensePhCovering.lean`, which is this
statement with the density clause added, over a Noetherian base. -/
theorem HasFlatStratification.exists_isPHCovering_flat_stratum {X S : Scheme.{u}} {f : X ⟶ S}
    (h : HasFlatStratification f) :
    ∃ (K : Type) (_ : Finite K) (Z : K → Scheme.{u}) (z : ∀ k, Z k ⟶ S)
      (U : ∀ k, (Z k).Opens),
      IsPHCovering Z z ∧ (∀ k, IsClosedImmersion (z k)) ∧
        (∀ k, Flat (pullback.snd f ((U k).ι ≫ z k))) ∧
        ∀ s : S, ∃ (k : K) (x : Z k), x ∈ U k ∧ (z k).base x = s := by
  obtain ⟨t, I, h0, -, -, hlast, hflat⟩ := h
  refine ⟨Fin t, inferInstance, fun i ↦ (I i.castSucc).subscheme,
    fun i ↦ (I i.castSucc).subschemeι,
    fun i ↦ (I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl,
    Scheme.IdealSheafData.isPHCovering_subschemeι_castSucc I h0 hlast, fun _ ↦ inferInstance,
    fun i ↦ hflat i, fun s ↦ ?_⟩
  obtain ⟨i, hi, hi'⟩ := Scheme.IdealSheafData.exists_mem_stratum_of_isThickening I h0 hlast s
  obtain ⟨x, hx⟩ := (Scheme.IdealSheafData.range_subschemeι (I i.castSucc)).ge hi
  have hxmem : x ∈ (I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl := by
    change (I i.castSucc).subschemeι x ∈ (I i.succ).support.compl
    rw [hx]
    exact hi'
  exact ⟨i, x, hxmem, hx⟩

end AlgebraicGeometry

end
