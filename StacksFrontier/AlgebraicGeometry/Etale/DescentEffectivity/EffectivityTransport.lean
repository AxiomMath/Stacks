module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.ChangeTransitivity
public import StacksFrontier.Topology.Noetherian.IrreduciblePieceGenericPoint

/-!
# Transporting effectivity out of an open of the base, and choosing an irreducible component

Two small ingredients of the Noetherian induction step of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP). That step works inside an affine
open `W` of the base and produces there an open over which the descent datum is effective; what
the induction consumes is an open *of the base* with the same property. The first half of this
file performs that transport, in the only form it is ever needed: the open of the base is the
image of the open of `W`, and the transport is the already available comparison
`AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_of_le_iff` together with the fact that
an open immersion recovers an open from its image.

The second half chooses the irreducible piece the step shrinks to. On a Noetherian quasi-sober
space a nonempty closed set has an irreducible closed subset maximal among all irreducible
subsets, and that subset has a generic point. This is not a new decomposition argument: the
lemma `Topology.exists_isOpen_isIrreducible_genericPoint` already produces an open set `V` with
`V ∩ Z` irreducible and dominated by the closure of one of its points, and maximality of that
closure among the irreducible subsets of `Z` is a three-line consequence — an irreducible
`D ⊆ Z` containing the closure meets `V`, hence is dense in `D ∩ V`, which lies inside the
closure.

## Main results

* `Topology.exists_genericPoint_maximal_isIrreducible_subset`: **a nonempty closed subset of a
  Noetherian quasi-sober space has an irreducible closed subset, maximal among its irreducible
  subsets, with a generic point.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_baseDatum_iff`: the datum restricted
  to an open `W` of the base is étale effective over an open `V` of `W` exactly when the datum
  itself is étale effective over an open of the base cutting `V` out of `W`.
* `AlgebraicGeometry.DescentDatum.exists_isEtaleEffective_baseDatum_of_baseDatum`: **étale
  effectivity over an open of an open of the base is étale effectivity over an open of the
  base**, namely over its image.

## Implementation notes

The identification of `V` with `W.ι ⁻¹ᵁ U` is a non-definitional transport appearing in the type
of `AlgebraicGeometry.DescentDatum.baseDatum`, so it is taken as a hypothesis alongside the open
it names and discharged by `subst` in its own declaration; stating and proving the two in one
step costs an order of magnitude in elaboration time.

Affineness of `W` plays no part in the transport and is not assumed, although the open `W` is
affine where the induction uses this.

## References

* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

open Set TopologicalSpace

namespace Topology

/-- **A nonempty closed subset of a Noetherian quasi-sober space has an irreducible closed
subset, maximal among its irreducible subsets, with a generic point.** Such a subset is an
irreducible component of the closed set, presented by a point generating it.

The open set `V` of `Topology.exists_isOpen_isIrreducible_genericPoint` cuts out of the closed
set a piece contained in the closure `C` of a single point `ξ ∈ V`. That closure is the subset
wanted: an irreducible `D ⊆ Z` containing `C` contains `ξ`, so the open set `V` meets `D` and `D`
is therefore dense in `D ∩ V`; but `D ∩ V ⊆ V ∩ Z ⊆ C`, and `C` is closed, so `D ⊆ C`. -/
theorem exists_genericPoint_maximal_isIrreducible_subset {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] (Z : Set α) (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ (C : Set α) (x : α), IsIrreducible C ∧ IsClosed C ∧ C ⊆ Z ∧
      (∀ D : Set α, IsIrreducible D → D ⊆ Z → C ⊆ D → D = C) ∧ IsGenericPoint x C := by
  obtain ⟨V, hVopen, -, -, ξ, hξmem, hsub⟩ :=
    exists_isOpen_isIrreducible_genericPoint (α := α) isOpen_univ Z hZ (by simpa using hne)
  have hξV : ξ ∈ V := hξmem.1.1
  have hξZ : ξ ∈ Z := hξmem.2
  have hVZ : V ∩ Z ⊆ closure {ξ} := by simpa using hsub
  refine ⟨closure {ξ}, ξ, isIrreducible_singleton.closure, isClosed_closure,
    hZ.closure_subset_iff.mpr (singleton_subset_iff.mpr hξZ), ?_, isGenericPoint_closure⟩
  intro D hD hDZ hCD
  refine Subset.antisymm ?_ hCD
  have hDV : (D ∩ V).Nonempty := ⟨ξ, hCD (subset_closure rfl), hξV⟩
  have hDVC : D ∩ V ⊆ closure {ξ} := fun _ hy ↦ hVZ ⟨hy.2, hDZ hy.1⟩
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen hD.2 hVopen hDV).trans
    ((closure_mono hDVC).trans_eq closure_closure)

end Topology

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- **The datum restricted to an open `W` of the base is étale effective over an open `V` of `W`
exactly when the datum itself is étale effective over an open `U` of the base cutting `V` out of
`W`.** This is `AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_of_le_iff` with the
preimage of `U` in `W` replaced by a name for it. -/
theorem isEtaleEffective_baseDatum_baseDatum_iff (D : DescentDatum f) [Etale D.over.hom]
    {U W : S.Opens} (hUW : U ≤ W) {V : W.toScheme.Opens} (hV : W.ι ⁻¹ᵁ U = V) :
    ((D.baseDatum W).baseDatum V).IsEtaleEffective ↔ (D.baseDatum U).IsEtaleEffective := by
  subst hV
  exact isEtaleEffective_baseDatum_of_le_iff D hUW

/-- **Étale effectivity over an open of an open of the base is étale effectivity over an open of
the base.** If the datum restricted to an open `W` of the base is étale effective over an open
`V` of `W`, then the datum itself is étale effective over the image of `V` in the base, an open
contained in `W` which cuts `V` out of `W` again. -/
theorem exists_isEtaleEffective_baseDatum_of_baseDatum (D : DescentDatum f) [Etale D.over.hom]
    {W : S.Opens} {V : W.toScheme.Opens}
    (hV : ((D.baseDatum W).baseDatum V).IsEtaleEffective) :
    ∃ U : S.Opens, U ≤ W ∧ W.ι ⁻¹ᵁ U = V ∧ (D.baseDatum U).IsEtaleEffective :=
  have hle : W.ι ''ᵁ V ≤ W := (W.ι.image_le_opensRange V).trans_eq W.opensRange_ι
  ⟨W.ι ''ᵁ V, hle, W.ι.preimage_image_eq V,
    (D.isEtaleEffective_baseDatum_baseDatum_iff hle (W.ι.preimage_image_eq V)).mp hV⟩

end DescentDatum

end AlgebraicGeometry

end
