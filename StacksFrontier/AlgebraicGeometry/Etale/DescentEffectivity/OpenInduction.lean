module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.ChangeTransitivity
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Local

/-!
# The largest open over which a descent datum is effective

Let `f : X ⟶ S` be a surjective integral morphism and `(V, φ)` a quasi-compact separated étale
descent datum relative to `X / S`. The opens of `S` over which `(V, φ)` is effective are closed
under arbitrary suprema, by [Stacks, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM) and the
transitivity of base change, so there is a *largest* such open. The proof of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) therefore reduces to showing that
this largest open is everything, and for that it is enough to produce, whenever it is not
everything, one effective open which it does not contain.

No Noetherian hypothesis is needed for this: the supremum of *all* effective opens is effective,
so an effective open not contained in it is already a contradiction, and no maximality argument
or two-member glueing step is required.

## Main results

* `AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_iSup`: **the supremum of a family
  of opens over which an étale descent datum is effective is again such an open.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_of_le`: étale effectivity over an
  open of the base passes to smaller opens.
* `AlgebraicGeometry.qcSepEtaleEffective_of_exists_not_le`: **effectivity of quasi-compact
  separated étale descent data follows from being able to enlarge any proper effective open.**

## References

* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe v u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}}

namespace DescentDatum

variable {f : X ⟶ S} [Surjective f] [IsIntegralHom f] (D : DescentDatum f) [Etale D.over.hom]

/-- **The supremum of a family of opens over which an étale descent datum is effective is again
such an open.** The restriction of the datum to the supremum is effective over the preimages of
the members, which cover the supremum, so Tag 0BTM applies to it; the full faithfulness
hypotheses hold because the projection of the restricted datum is again surjective and
integral. -/
theorem isEtaleEffective_baseDatum_iSup {ι : Type v} (U : ι → S.Opens)
    (h : ∀ i, (D.baseDatum (U i)).IsEtaleEffective) :
    (D.baseDatum (⨆ i, U i)).IsEtaleEffective := by
  set W : S.Opens := ⨆ i, U i with hW
  refine isEtaleEffective_of_isOpenCover (D.baseDatum W) (fun i ↦ W.ι ⁻¹ᵁ U i) ?_
    (fun i ↦ (isEtaleEffective_baseDatum_of_le_iff D (le_iSup U i)).mpr (h i))
    (fun i j ↦ fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom
      (pullback.snd f W.ι) (W.ι ⁻¹ᵁ U i ⊓ W.ι ⁻¹ᵁ U j).ι)
    (fun i j k ↦ (fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom
      (pullback.snd f W.ι) (W.ι ⁻¹ᵁ U i ⊓ W.ι ⁻¹ᵁ U j ⊓ W.ι ⁻¹ᵁ U k).ι).faithful)
  rw [← Scheme.Hom.preimage_iSup, ← hW]
  exact W.ι_preimage_self

omit [Surjective f] [IsIntegralHom f] in
/-- **Étale effectivity over an open of the base passes to smaller opens.** -/
theorem isEtaleEffective_baseDatum_of_le {U W : S.Opens} (hUW : U ≤ W)
    (h : (D.baseDatum W).IsEtaleEffective) : (D.baseDatum U).IsEtaleEffective :=
  (isEtaleEffective_baseDatum_of_le_iff D hUW).mp
    (isEtaleEffective_pullbackSquare (basePullbackFunctor (pullback.snd f W.ι) (W.ι ⁻¹ᵁ U)) h)

end DescentDatum

/-- **Effectivity of quasi-compact separated étale descent data follows from being able to
enlarge any proper effective open.** Given a quasi-compact separated étale datum and an open
`U₀ ≠ ⊤` of the base over which it is effective, it is enough to produce one effective open not
contained in `U₀`: applying this to the supremum of all effective opens, which is itself
effective, shows that supremum to be everything, and the family of all effective opens is then
an open cover to which Tag 0BTM applies. -/
theorem qcSepEtaleEffective_of_exists_not_le (f : X ⟶ S) [Surjective f] [IsIntegralHom f]
    (H : ∀ (D : DescentDatum f) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
      IsSeparated D.over.hom → ∀ U₀ : S.Opens, (D.baseDatum U₀).IsEtaleEffective → U₀ ≠ ⊤ →
        ∃ T : S.Opens, (D.baseDatum T).IsEtaleEffective ∧ ¬ T ≤ U₀) :
    QcSepEtaleEffective f := by
  refine qcSepEtaleEffective_of_isEtaleEffective fun D hD hqc hsep ↦ ?_
  set G : Type u := {U : S.Opens // (D.baseDatum U).IsEtaleEffective}
  set c : G → S.Opens := fun U ↦ U.1
  have hiSup : (D.baseDatum (⨆ U, c U)).IsEtaleEffective :=
    D.isEtaleEffective_baseDatum_iSup c fun U ↦ U.2
  have htop : (⨆ U, c U) = ⊤ := by
    by_contra hne
    obtain ⟨T, hT, hTle⟩ := H D hD hqc hsep _ hiSup hne
    exact hTle (le_iSup c (⟨T, hT⟩ : G))
  exact DescentDatum.isEtaleEffective_of_isOpenCover D c htop (fun U ↦ U.2)
    (fun U U' ↦ fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom f (c U ⊓ c U').ι)
    (fun U U' U'' ↦ (fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom f
      (c U ⊓ c U' ⊓ c U'').ι).faithful)

end AlgebraicGeometry

end
