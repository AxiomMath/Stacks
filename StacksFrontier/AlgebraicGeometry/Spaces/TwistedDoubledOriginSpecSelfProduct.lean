module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSpecBase

/-!
# The self-product of the covering `Spec k' ⟶ Spec k` splits

The closing claim of Stacks 03FN concerns the one-member covering `{Spec k' ⟶ Spec k}`, whose
self-product is `Spec(k' ⊗_k k')`.  For a degree two Galois extension that ring is `k' × k'`,
so on spectra

    `Spec k' ×_{Spec k} Spec k' ≅ Spec k' ⨿ Spec k'`,

the first summand being the diagonal and the second the graph `(1, σ)` of the nonidentity
Galois automorphism.  This is the same splitting as
`AlgebraicGeometry.TwistedDoubledOrigin.coverFiberProductSplitIso`, read over `Spec k` instead
of over `S = Spec k[x]`, and it is what a gluing isomorphism relative to the covering
`{Spec k' ⟶ Spec k}` is assembled from: an isomorphism over the self-product is a pair of
isomorphisms, one over each summand.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.specGaloisAction` is a Galois automorphism of the
  extension, read on spectra.
* `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionTensorSplitSpecIso` is the splitting of
  `Spec(k' ⊗_k k')` as `Spec(k' × k')`.
* `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionFiberProductSplitIso` is the resulting
  isomorphism `Spec k' ×_{Spec k} Spec k' ≅ Spec k' ⨿ Spec k'`.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionFiberProductSplitIso_inl`: the first
  summand is the diagonal.
* `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionFiberProductSplitIso_inr_fst` and
  `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionFiberProductSplitIso_inr_snd`: the
  second summand is the graph of the Galois automorphism.
* `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionFiberProductSplitIso_first_factor` and
  `AlgebraicGeometry.TwistedDoubledOrigin.specExtensionFiberProductSplitIso_second_factor`
  read the two projections of the self-product on both summands at once: the first projection
  is the identity on each, and the second is the identity on the diagonal summand and the
  Galois automorphism on the twisted one.

## Implementation notes

Unlike the splitting over `S = Spec k[x]`, which has to be obtained from the splitting of
`k' ⊗_k k'` by base change along `k ⟶ k[x]`, this one *is* the splitting of `k' ⊗_k k'`:
`AlgebraicGeometry.TwistedDoubledOrigin.quadraticTensorProductSplit` is already the required
algebra isomorphism, and
`AlgebraicGeometry.TwistedDoubledOrigin.quadraticTensorProductSplit_tmul` computes it on
elementary tensors, so the four ring-level identities below — what the splitting does to the
two inclusions, read in each coordinate — are each a one-line computation.

Everything is phrased with `AlgebraicGeometry.TwistedDoubledOrigin.specExtension`, which is
the morphism `Spec k' ⟶ Spec k` of the covering; the proofs restate the goal with that
definition unfolded, because the Mathlib isomorphisms
`AlgebraicGeometry.pullbackSpecIso` and `AlgebraicGeometry.coprodSpec` are stated for the
literal `Spec.map` of an `algebraMap`.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A Galois automorphism of the extension, read on spectra. -/
def specGaloisAction (σ : K ≃ₐ[k] K) : Spec (.of K) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (σ : K →+* K))

/-- The Galois automorphism, read on spectra, lies over `Spec k`. -/
@[reassoc]
theorem specGaloisAction_comp_specExtension (σ : K ≃ₐ[k] K) :
    specGaloisAction k K σ ≫ specExtension k K = specExtension k K := by
  dsimp [specGaloisAction, specExtension]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (σ : K →+* K).comp (algebraMap k K) = algebraMap k K from
      RingHom.ext fun x => σ.commutes x]

variable [FiniteDimensional k K] [IsGalois k K]

section RingLevel

variable (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)

/-- The first coordinate of the splitting restricts to the identity on the left factor. -/
theorem quadraticTensorSplitFirst_includeLeft :
    (RingHom.fst K K).comp
      ((quadraticTensorProductSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] K)) = RingHom.id K := by
  refine RingHom.ext fun a => ?_
  simp

/-- The second coordinate of the splitting restricts to the identity on the left factor. -/
theorem quadraticTensorSplitSecond_includeLeft :
    (RingHom.snd K K).comp
      ((quadraticTensorProductSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] K)) = RingHom.id K := by
  refine RingHom.ext fun a => ?_
  simp

/-- The first coordinate of the splitting restricts to the identity on the right factor. -/
theorem quadraticTensorSplitFirst_includeRight :
    (RingHom.fst K K).comp
      ((quadraticTensorProductSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K).toRingHom) = RingHom.id K := by
  refine RingHom.ext fun b => ?_
  simp

/-- The second coordinate of the splitting restricts to the Galois automorphism on the right
factor. -/
theorem quadraticTensorSplitSecond_includeRight :
    (RingHom.snd K K).comp
      ((quadraticTensorProductSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K).toRingHom) =
      (σ : K →+* K) := by
  refine RingHom.ext fun b => ?_
  simp

end RingLevel

variable (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)

/-- The splitting of `k' ⊗_k k'` as `k' × k'`, on spectra. -/
def specExtensionTensorSplitSpecIso :
    Spec (.of (K ⊗[k] K)) ≅ Spec (.of (K × K)) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (quadraticTensorProductSplit k K hdegree σ hσ).symm.toRingEquiv).op

/-- **Stacks 03FN.** The self-product of the covering `Spec k' ⟶ Spec k` is the disjoint
union of two copies of `Spec k'`, the diagonal and the graph of the Galois automorphism. -/
def specExtensionFiberProductSplitIso :
    pullback (specExtension k K) (specExtension k K) ≅ Spec (.of K) ⨿ Spec (.of K) :=
  (AlgebraicGeometry.pullbackSpecIso k K K).trans
    ((specExtensionTensorSplitSpecIso k K hdegree σ hσ).trans
      (asIso (AlgebraicGeometry.coprodSpec K K)).symm)

/-- A map into the split self-product, read through the first projection. -/
private theorem coprod_comp_splitIso_inv_fst (c : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of K))
    (p : K × K →+* K)
    (hc : c ≫ AlgebraicGeometry.coprodSpec K K = Spec.map (CommRingCat.ofHom p)) :
    c ≫ (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (specExtension k K) (specExtension k K) =
      Spec.map (CommRingCat.ofHom (p.comp
        ((quadraticTensorProductSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
          Algebra.TensorProduct.includeLeftRingHom))) := by
  change (c ≫ AlgebraicGeometry.coprodSpec K K ≫
      (specExtensionTensorSplitSpecIso k K hdegree σ hσ).inv ≫
      (AlgebraicGeometry.pullbackSpecIso k K K).inv) ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) = _
  rw [← Category.assoc c, hc]
  simp only [Category.assoc, specExtensionTensorSplitSpecIso, Scheme.Spec.mapIso_inv,
    AlgebraicGeometry.pullbackSpecIso_inv_fst]
  rw [Scheme.Spec_map (f := (RingEquiv.toCommRingCatIso
    (quadraticTensorProductSplit k K hdegree σ hσ).symm.toRingEquiv).op.inv),
    ← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- A map into the split self-product, read through the second projection. -/
private theorem coprod_comp_splitIso_inv_snd (c : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of K))
    (p : K × K →+* K)
    (hc : c ≫ AlgebraicGeometry.coprodSpec K K = Spec.map (CommRingCat.ofHom p)) :
    c ≫ (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (specExtension k K) (specExtension k K) =
      Spec.map (CommRingCat.ofHom (p.comp
        ((quadraticTensorProductSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
          Algebra.TensorProduct.includeRight.toRingHom))) := by
  change (c ≫ AlgebraicGeometry.coprodSpec K K ≫
      (specExtensionTensorSplitSpecIso k K hdegree σ hσ).inv ≫
      (AlgebraicGeometry.pullbackSpecIso k K K).inv) ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) = _
  rw [← Category.assoc c, hc]
  simp only [Category.assoc, specExtensionTensorSplitSpecIso, Scheme.Spec.mapIso_inv,
    AlgebraicGeometry.pullbackSpecIso_inv_snd]
  rw [Scheme.Spec_map (f := (RingEquiv.toCommRingCatIso
    (quadraticTensorProductSplit k K hdegree σ hσ).symm.toRingEquiv).op.inv),
    ← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The first summand of the split self-product is the diagonal. -/
theorem specExtensionFiberProductSplitIso_inl :
    (coprod.inl : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of K)) ≫
      (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv =
        pullback.diagonal (specExtension k K) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coprod_comp_splitIso_inv_fst k K hdegree σ hσ _ _
      (AlgebraicGeometry.coprodSpec_inl K K), quadraticTensorSplitFirst_includeLeft,
      pullback.diagonal_fst, ← Spec.map_id]
    rfl
  · rw [Category.assoc, coprod_comp_splitIso_inv_snd k K hdegree σ hσ _ _
      (AlgebraicGeometry.coprodSpec_inl K K), quadraticTensorSplitFirst_includeRight,
      pullback.diagonal_snd, ← Spec.map_id]
    rfl

/-- The second summand of the split self-product projects to `Spec k'` by the identity in the
first coordinate. -/
theorem specExtensionFiberProductSplitIso_inr_fst :
    (coprod.inr : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of K)) ≫
      (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (specExtension k K) (specExtension k K) = 𝟙 (Spec (.of K)) := by
  rw [coprod_comp_splitIso_inv_fst k K hdegree σ hσ _ _ (AlgebraicGeometry.coprodSpec_inr K K),
    quadraticTensorSplitSecond_includeLeft, ← Spec.map_id]
  rfl

/-- The second summand of the split self-product is the graph of the Galois automorphism: its
second coordinate is that automorphism. -/
theorem specExtensionFiberProductSplitIso_inr_snd :
    (coprod.inr : Spec (.of K) ⟶ Spec (.of K) ⨿ Spec (.of K)) ≫
      (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (specExtension k K) (specExtension k K) = specGaloisAction k K σ := by
  rw [coprod_comp_splitIso_inv_snd k K hdegree σ hσ _ _ (AlgebraicGeometry.coprodSpec_inr K K),
    quadraticTensorSplitSecond_includeRight]
  rfl

/-- The first projection of the self-product of the covering, read through the splitting: it
is the identity on both summands. -/
theorem specExtensionFiberProductSplitIso_first_factor :
    (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (specExtension k K) (specExtension k K) =
      coprod.desc (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) := by
  apply coprod.hom_ext
  · calc
      coprod.inl ≫ (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
          pullback.fst (specExtension k K) (specExtension k K) =
          pullback.diagonal (specExtension k K) ≫
            pullback.fst (specExtension k K) (specExtension k K) := by
            rw [← Category.assoc, specExtensionFiberProductSplitIso_inl]
      _ = 𝟙 (Spec (.of K)) := pullback.diagonal_fst (specExtension k K)
      _ = coprod.inl ≫ coprod.desc (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) :=
          (coprod.inl_desc _ _).symm
  · calc
      coprod.inr ≫ (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
          pullback.fst (specExtension k K) (specExtension k K) = 𝟙 (Spec (.of K)) :=
            specExtensionFiberProductSplitIso_inr_fst k K hdegree σ hσ
      _ = coprod.inr ≫ coprod.desc (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) :=
          (coprod.inr_desc _ _).symm

/-- The second projection of the self-product of the covering, read through the splitting: it
is the identity on the diagonal summand and the Galois automorphism on the twisted one. -/
theorem specExtensionFiberProductSplitIso_second_factor :
    (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (specExtension k K) (specExtension k K) =
      coprod.desc (𝟙 (Spec (.of K))) (specGaloisAction k K σ) := by
  apply coprod.hom_ext
  · calc
      coprod.inl ≫ (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
          pullback.snd (specExtension k K) (specExtension k K) =
          pullback.diagonal (specExtension k K) ≫
            pullback.snd (specExtension k K) (specExtension k K) := by
            rw [← Category.assoc, specExtensionFiberProductSplitIso_inl]
      _ = 𝟙 (Spec (.of K)) := pullback.diagonal_snd (specExtension k K)
      _ = coprod.inl ≫ coprod.desc (𝟙 (Spec (.of K))) (specGaloisAction k K σ) :=
          (coprod.inl_desc _ _).symm
  · calc
      coprod.inr ≫ (specExtensionFiberProductSplitIso k K hdegree σ hσ).inv ≫
          pullback.snd (specExtension k K) (specExtension k K) = specGaloisAction k K σ :=
            specExtensionFiberProductSplitIso_inr_snd k K hdegree σ hσ
      _ = coprod.inr ≫ coprod.desc (𝟙 (Spec (.of K))) (specGaloisAction k K σ) :=
          (coprod.inr_desc _ _).symm

end AlgebraicGeometry.TwistedDoubledOrigin

end
