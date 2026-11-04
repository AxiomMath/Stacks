module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeComp09UT

/-!
# Relative pseudo-coherence is local on the source

Let `f : X ⟶ S` be locally of finite type and let `E` be an object of `D(𝒪_X)`. If every point
of `X` has an open neighbourhood `U` such that the restriction `E|_U` is relatively
`m`-pseudo-coherent for `U ⟶ X ⟶ S`, then `E` is relatively `m`-pseudo-coherent for `f`. This is
the locality on the source built into Stacks Definition 09UI ("there exist affine open
coverings"), and it is the form in which the conclusion of Stacks 0CSL, which is proved one point
of `X` at a time, is assembled.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_exists_opens`: relative
  `m`-pseudo-coherence from relative `m`-pseudo-coherence on an open neighbourhood of every point.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_of_forall_exists_opens`: the same for relative
  pseudo-coherence.

## Implementation notes

By Stacks 09UJ (`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair`) it is
enough to prove the pair condition at a compatible pair of affine opens `W ⊆ f ⁻¹ᵁ V`, and by its
locality on `W`
(`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_forall_mem_basicOpen`) enough
to prove it on a standard open `X_r ⊆ W ⊓ U` around each point. There the hypothesis on `U`
supplies the pair condition for `U ⟶ S` at the affine open `ι_U⁻¹(X_r)` of `U`, and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE_iff` moves it to
`X_r` along `ι_U⁻¹(X_r) ≅ X_r`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, as
in the definition of relative pseudo-coherence.

## References

* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-- **Relative `m`-pseudo-coherence is local on the source.** If every point of `X` has an open
neighbourhood `U` on which the restriction of `E` is relatively `m`-pseudo-coherent for the
composite `U ⟶ X ⟶ S`, then `E` is relatively `m`-pseudo-coherent for `f`. -/
public theorem isPseudoCoherentFrom_of_forall_exists_opens (E : DerivedCategory X.Modules)
    (m : ℤ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (U.ι ≫ f).IsPseudoCoherentFrom
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) m) :
    f.IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f E m fun W V hWV => ?_
  refine isPseudoCoherentFromOnAffinePair_of_forall_mem_basicOpen f W V hWV fun x => ?_
  obtain ⟨U, hxU, hU⟩ := h x.1
  obtain ⟨r, hrle, hxr⟩ := W.2.exists_basicOpen_le (V := (W.1 : X.Opens) ⊓ U) ⟨x.1, x.2, hxU⟩ x.2
  have hrU : X.basicOpen r ≤ U := fun _ hz => (hrle hz).2
  have hrW : X.basicOpen r ≤ (W.1 : X.Opens) := Scheme.basicOpen_le X r
  have hrV : X.basicOpen r ≤ f ⁻¹ᵁ V.1 := hrW.trans hWV
  refine ⟨r, hxr, hrV, ?_⟩
  -- the affine open `ι_U⁻¹(X_r)` of `U`
  have hraff : IsAffineOpen (X.basicOpen r) := W.2.basicOpen r
  have : IsAffine (X.basicOpen r) := hraff
  have hpreaff : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen r) :=
    IsAffine.of_isIso (Scheme.Opens.isoOfLE hrU).hom
  have hpreV : U.ι ⁻¹ᵁ X.basicOpen r ≤ (U.ι ≫ f) ⁻¹ᵁ V.1 := fun z hz => hrV hz
  obtain ⟨n, i, hi, hio, hpc⟩ :=
    isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom (U.ι ≫ f) hU
      ⟨U.ι ⁻¹ᵁ X.basicOpen r, hpreaff⟩ V hpreV
  have := hi
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  refine ⟨n, (Scheme.Opens.isoOfLE hrU).inv ≫ i, inferInstance, ?_,
    (Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE_iff hrU
      ((Scheme.Opens.isoOfLE hrU).inv ≫ i) E m).mp ?_⟩
  · have key : (Scheme.Opens.isoOfLE hrU).inv ≫ (U.ι ⁻¹ᵁ X.basicOpen r).ι ≫ U.ι =
        (X.basicOpen r).ι := by
      rw [← Scheme.Opens.isoOfLE_hom_ι hrU, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc i, hio, Scheme.Hom.resLE_comp_ι]
    exact (reassoc_of% key) f
  · rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact hpc

/-- **Relative pseudo-coherence is local on the source.** If every point of `X` has an open
neighbourhood `U` on which the restriction of `E` is pseudo-coherent relative to `S` for the
composite `U ⟶ X ⟶ S`, then `E` is pseudo-coherent relative to `S`. -/
public theorem isPseudoCoherent_of_forall_exists_opens (E : DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (U.ι ≫ f).IsPseudoCoherent
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)) :
    f.IsPseudoCoherent E := fun m =>
  isPseudoCoherentFrom_of_forall_exists_opens f E m fun x =>
    let ⟨U, hxU, hU⟩ := h x
    ⟨U, hxU, hU m⟩

end Scheme.Hom

end AlgebraicGeometry

end
