module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Galois.Basic
public import StacksFrontier.FieldTheory.SeparableTensorSplitting

/-!
# The self-product of the spectrum of a Galois extension

Let `k'/k` be a finite Galois extension with group `G = Gal(k'/k)`. Then

`Spec(k') ×_k Spec(k') = ∐_{σ ∈ G} (Spec(σ) × id)^{-1} Δ`:

the self-product is the disjoint union of `|G|` copies of `Spec(k')`, the `σ`-th copy embedded
by `(id, Spec(σ))`, and that copy is the base change of the diagonal along the automorphism
`Spec(σ) × id` of the self-product. This is the decomposition of the self-product with which the
proof of Stacks Tag 0FVR opens.

On rings it is the isomorphism `k' ⊗_k k' ≅ ∏_{σ ∈ G} k'`, `η ⊗ ζ ↦ (η · σ(ζ))_σ`, the case
`K = k'` of `Stacks.FieldTheory.bijective_tensorPi`, reindexed from the `k`-embeddings of `k'`
into itself to its `k`-automorphisms.

## Main definitions

* `Stacks.WeilCohomology.galoisTensorPi`: the `k'`-algebra map
  `k' ⊗_k k' → ∏_{σ ∈ Gal(k'/k)} k'`, `η ⊗ ζ ↦ (η · σ(ζ))_σ`.
* `Stacks.WeilCohomology.galoisTensorPiEquiv`: the same map, as an isomorphism.
* `Stacks.WeilCohomology.specGaloisCoprojection`: the morphism
  `(id, Spec(σ)) : Spec(k') → Spec(k') ×_k Spec(k')`.
* `Stacks.WeilCohomology.specGaloisCofan`: the cofan of these morphisms.

## Main results

* `Stacks.WeilCohomology.isColimit_specGaloisCofan`: the self-product is the coproduct of the
  copies `(id, Spec(σ)) : Spec(k') → Spec(k') ×_k Spec(k')`, `σ ∈ Gal(k'/k)`.
* `Stacks.WeilCohomology.isPullback_specGaloisCoprojection_diagonal`: the `σ`-th copy is
  `(Spec(σ) × id)^{-1} Δ`, the base change of the diagonal along `Spec(σ) × id`.
* `Stacks.WeilCohomology.isOpenImmersion_specGaloisCoprojection`,
  `Stacks.WeilCohomology.disjoint_opensRange_specGaloisCoprojection`,
  `Stacks.WeilCohomology.iSup_opensRange_specGaloisCoprojection`: the copies are open
  immersions with pairwise disjoint images covering the self-product, the form in which axiom
  `(A1)` of Section 45.14 consumes a finite decomposition.

## References

* [Stacks Project, Tag 0FVR](https://stacks.math.columbia.edu/tag/0FVR)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.WeilCohomology

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-! ### The splitting of `k' ⊗_k k'` -/

/-- The `k'`-algebra map `k' ⊗_k k' → ∏_{σ ∈ Gal(k'/k)} k'`, `η ⊗ ζ ↦ (η · σ(ζ))_σ`. -/
def galoisTensorPi : k' ⊗[k] k' →ₐ[k'] ((k' ≃ₐ[k] k') → k') :=
  AlgHom.pi fun σ ↦ Stacks.FieldTheory.tensorEvalAlgHom (σ : k' →ₐ[k] k')

/-- The `σ`-component of `galoisTensorPi` sends `η ⊗ ζ` to `η · σ(ζ)`. -/
@[simp]
lemma galoisTensorPi_tmul (η ζ : k') (σ : k' ≃ₐ[k] k') :
    galoisTensorPi k k' (η ⊗ₜ[k] ζ) σ = η * σ ζ := by
  simp [galoisTensorPi]

/-- **`k' ⊗_k k' ≅ ∏_{σ ∈ Gal(k'/k)} k'`** for a finite Galois extension `k'/k`: the case
`K = k'` of `Stacks.FieldTheory.bijective_tensorPi`, reindexed along
`Gal(k'/k) ≃ (k' →ₐ[k] k')`. -/
theorem bijective_galoisTensorPi [FiniteDimensional k k'] [IsGalois k k'] :
    Function.Bijective (galoisTensorPi k k') := by
  let e : (k' ≃ₐ[k] k') ≃ (k' →ₐ[k] k') := (algEquivEquivAlgHom k k').toEquiv
  have h : ⇑(galoisTensorPi k k') =
      (fun f : (k' →ₐ[k] k') → k' ↦ f ∘ e) ∘ Stacks.FieldTheory.tensorPi k k' k' := rfl
  rw [h]
  exact (e.arrowCongr (Equiv.refl k')).symm.bijective.comp
    (Stacks.FieldTheory.bijective_tensorPi k k' k' (AlgHom.id k k'))

/-- The splitting `k' ⊗_k k' ≅ ∏_{σ ∈ Gal(k'/k)} k'`, `η ⊗ ζ ↦ (η · σ(ζ))_σ`, as an isomorphism
of `k'`-algebras. -/
def galoisTensorPiEquiv [FiniteDimensional k k'] [IsGalois k k'] :
    k' ⊗[k] k' ≃ₐ[k'] ((k' ≃ₐ[k] k') → k') :=
  AlgEquiv.ofBijective (galoisTensorPi k k') (bijective_galoisTensorPi k k')

/-- `galoisTensorPiEquiv` agrees with `galoisTensorPi` as a function. -/
@[simp]
lemma galoisTensorPiEquiv_apply [FiniteDimensional k k'] [IsGalois k k'] (x : k' ⊗[k] k') :
    galoisTensorPiEquiv k k' x = galoisTensorPi k k' x := rfl

/-! ### The self-product of `Spec(k')` -/

/-- The structure morphism `Spec(k') → Spec(k)`. -/
abbrev specStructure : Spec (.of k') ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

variable {k k'}

/-- `Spec(σ) : Spec(k') → Spec(k')` for a `k`-automorphism `σ` of `k'`. -/
abbrev specAut (σ : k' ≃ₐ[k] k') : Spec (.of k') ⟶ Spec (.of k') :=
  Spec.map (CommRingCat.ofHom (σ : k' →+* k'))

/-- `Spec(σ)` is a morphism over `Spec(k)`. -/
@[reassoc (attr := simp)]
lemma specAut_comp_specStructure (σ : k' ≃ₐ[k] k') :
    specAut σ ≫ specStructure k k' = specStructure k k' := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- `Spec` of the identity automorphism is the identity. -/
lemma specAut_one : specAut (1 : k' ≃ₐ[k] k') = 𝟙 _ := by
  rw [← Spec.map_id]
  rfl

/-- `Spec(σ τ) = Spec(σ) ≫ Spec(τ)`. -/
lemma specAut_mul (σ τ : k' ≃ₐ[k] k') : specAut (σ * τ) = specAut σ ≫ specAut τ := by
  rw [← Spec.map_comp]
  rfl

/-- `Spec(σ)` is an isomorphism, with inverse `Spec(σ⁻¹)`. -/
instance (σ : k' ≃ₐ[k] k') : IsIso (specAut σ) :=
  ⟨⟨specAut σ⁻¹, by rw [← specAut_mul, mul_inv_cancel, specAut_one],
    by rw [← specAut_mul, inv_mul_cancel, specAut_one]⟩⟩

variable (k k') in
/-- The self-product `Spec(k') ×_k Spec(k')`. -/
abbrev specSelfProduct : Scheme.{u} := pullback (specStructure k k') (specStructure k k')

/-- **The `σ`-th copy `(id, Spec(σ)) : Spec(k') → Spec(k') ×_k Spec(k')`.** -/
def specGaloisCoprojection (σ : k' ≃ₐ[k] k') : Spec (.of k') ⟶ specSelfProduct k k' :=
  pullback.lift (𝟙 _) (specAut σ) (by simp)

/-- The first component of `(id, Spec(σ))` is the identity. -/
@[reassoc (attr := simp)]
lemma specGaloisCoprojection_fst (σ : k' ≃ₐ[k] k') :
    specGaloisCoprojection σ ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second component of `(id, Spec(σ))` is `Spec(σ)`. -/
@[reassoc (attr := simp)]
lemma specGaloisCoprojection_snd (σ : k' ≃ₐ[k] k') :
    specGaloisCoprojection σ ≫ pullback.snd _ _ = specAut σ :=
  pullback.lift_snd _ _ _

/-- The automorphism `Spec(σ) × id` of `Spec(k') ×_k Spec(k')`. -/
def specAutProdId (σ : k' ≃ₐ[k] k') : specSelfProduct k k' ⟶ specSelfProduct k k' :=
  pullback.map _ _ _ _ (specAut σ) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- `Spec(σ) × id` is an isomorphism. -/
instance (σ : k' ≃ₐ[k] k') : IsIso (specAutProdId σ) := by
  unfold specAutProdId
  infer_instance

/-- **The `σ`-th copy is `(Spec(σ) × id)^{-1} Δ`**: the square
```
Spec(k') --(id, Spec(σ))--> Spec(k') ×_k Spec(k')
   |Spec(σ)                     | Spec(σ) × id
Spec(k') --------Δ--------> Spec(k') ×_k Spec(k')
```
is cartesian, so `(id, Spec(σ))` is the base change of the diagonal along `Spec(σ) × id`. -/
theorem isPullback_specGaloisCoprojection_diagonal (σ : k' ≃ₐ[k] k') :
    IsPullback (specGaloisCoprojection σ) (specAut σ) (specAutProdId σ)
      (pullback.diagonal (specStructure k k')) := by
  refine IsPullback.of_vert_isIso ⟨?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, specAutProdId, pullback.lift_fst, ← Category.assoc,
      specGaloisCoprojection_fst, Category.id_comp, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc, specAutProdId, pullback.lift_snd, ← Category.assoc,
      specGaloisCoprojection_snd, Category.comp_id, pullback.diagonal_snd, Category.comp_id]

variable (k k') in
/-- The cofan of the copies `(id, Spec(σ))`, `σ ∈ Gal(k'/k)`, of `Spec(k')` in the self-product. -/
abbrev specGaloisCofan : Cofan (fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')) :=
  Cofan.mk (specSelfProduct k k') specGaloisCoprojection

variable [FiniteDimensional k k'] [IsGalois k k']

variable (k k') in
/-- `Spec(∏_{σ ∈ Gal(k'/k)} k') ≅ Spec(k') ×_k Spec(k')`, from the splitting of `k' ⊗_k k'`. -/
def specPiIsoSelfProduct :
    Spec (.of ((k' ≃ₐ[k] k') → k')) ≅ specSelfProduct k k' :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (galoisTensorPiEquiv k k').toRingEquiv).op ≪≫ (pullbackSpecIso k k' k').symm

/-- The `σ`-component of `galoisTensorPiEquiv`, restricted to the left factor `k'`, is the
identity. -/
lemma eval_comp_galoisTensorPi_includeLeft (σ : k' ≃ₐ[k] k') :
    (Pi.evalRingHom (fun _ : k' ≃ₐ[k] k' ↦ k') σ).comp
        ((galoisTensorPiEquiv k k').toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := k') (B := k'))) =
      RingHom.id k' := by
  ext x
  simp

/-- The `σ`-component of `galoisTensorPiEquiv`, restricted to the right factor `k'`, is `σ`. -/
lemma eval_comp_galoisTensorPi_includeRight (σ : k' ≃ₐ[k] k') :
    (Pi.evalRingHom (fun _ : k' ≃ₐ[k] k' ↦ k') σ).comp
        ((galoisTensorPiEquiv k k').toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := k')).toRingHom) =
      (σ : k' →+* k') := by
  ext x
  simp

/-- `specPiIsoSelfProduct` carries the `σ`-th point `Spec(k') → Spec(∏_σ k')` to
`(id, Spec(σ))`. -/
lemma spec_eval_comp_specPiIsoSelfProduct (σ : k' ≃ₐ[k] k') :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : k' ≃ₐ[k] k' ↦ k') σ)) ≫
        (specPiIsoSelfProduct k k').hom = specGaloisCoprojection σ := by
  apply pullback.hom_ext <;>
  · simp only [specPiIsoSelfProduct, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom,
      Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
      specGaloisCoprojection_fst, specGaloisCoprojection_snd]
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    first
    | rw [← Spec.map_id]; congr 1; ext x
      exact DFunLike.congr_fun (eval_comp_galoisTensorPi_includeLeft σ) x
    | congr 1; ext x
      exact DFunLike.congr_fun (eval_comp_galoisTensorPi_includeRight σ) x

variable (k k') in
/-- `∐_{σ ∈ Gal(k'/k)} Spec(k') ≅ Spec(k') ×_k Spec(k')`, carrying the `σ`-th coprojection to
`(id, Spec(σ))`. -/
def sigmaIsoSelfProduct : (∐ fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')) ≅ specSelfProduct k k' :=
  asIso (sigmaSpec fun _ : k' ≃ₐ[k] k' ↦ CommRingCat.of k') ≪≫ specPiIsoSelfProduct k k'

/-- `sigmaIsoSelfProduct` carries the `σ`-th coprojection to `(id, Spec(σ))`. -/
@[reassoc (attr := simp)]
lemma ι_sigmaIsoSelfProduct_hom (σ : k' ≃ₐ[k] k') :
    Sigma.ι (fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')) σ ≫ (sigmaIsoSelfProduct k k').hom =
      specGaloisCoprojection σ := by
  simpa only [sigmaIsoSelfProduct, Iso.trans_hom, asIso_hom, ι_sigmaSpec_assoc] using
    spec_eval_comp_specPiIsoSelfProduct σ

variable (k k') in
/-- **`Spec(k') ×_k Spec(k') = ∐_{σ ∈ Gal(k'/k)} Spec(k')`**: for a finite Galois extension
`k'/k` the self-product of `Spec(k')` over `k` is the coproduct of copies of `Spec(k')`, the
`σ`-th one embedded by `(id, Spec(σ))`, which is `(Spec(σ) × id)^{-1} Δ` by
`Stacks.WeilCohomology.isPullback_specGaloisCoprojection_diagonal`. -/
def isColimitSpecGaloisCofan : IsColimit (specGaloisCofan k k') :=
  (coproductIsCoproduct fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')).ofIsoColimit
    (Cofan.ext (sigmaIsoSelfProduct k k') fun σ ↦ ι_sigmaIsoSelfProduct_hom σ)

/-- The self-product `Spec(k') ×_k Spec(k')` is the coproduct of the copies `(id, Spec(σ))`,
`σ ∈ Gal(k'/k)`, of `Spec(k')`. -/
theorem isColimit_specGaloisCofan : Nonempty (IsColimit (specGaloisCofan k k')) :=
  ⟨isColimitSpecGaloisCofan k k'⟩

/-- Each copy `(id, Spec(σ)) : Spec(k') → Spec(k') ×_k Spec(k')` is an open immersion. -/
instance isOpenImmersion_specGaloisCoprojection (σ : k' ≃ₐ[k] k') :
    IsOpenImmersion (specGaloisCoprojection σ) := by
  rw [← ι_sigmaIsoSelfProduct_hom]
  infer_instance

/-- The image of `(id, Spec(σ))` is the image under `sigmaIsoSelfProduct` of the `σ`-th summand
of `∐_σ Spec(k')`. -/
lemma range_specGaloisCoprojection (σ : k' ≃ₐ[k] k') :
    Set.range (specGaloisCoprojection σ) =
      (sigmaIsoSelfProduct k k').hom '' Set.range
        (Sigma.ι (fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')) σ) := by
  rw [← ι_sigmaIsoSelfProduct_hom, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- The copies of `Spec(k')` in the self-product are pairwise disjoint. -/
theorem disjoint_opensRange_specGaloisCoprojection {σ τ : k' ≃ₐ[k] k'} (h : σ ≠ τ) :
    Disjoint (specGaloisCoprojection σ).opensRange (specGaloisCoprojection τ).opensRange := by
  rw [← TopologicalSpace.Opens.coe_disjoint, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange, range_specGaloisCoprojection, range_specGaloisCoprojection]
  have hd := disjoint_opensRange_sigmaι (fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')) σ τ h
  rw [← TopologicalSpace.Opens.coe_disjoint, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange] at hd
  exact (Set.disjoint_image_iff
    (sigmaIsoSelfProduct k k').hom.isOpenEmbedding.injective).mpr hd

/-- The copies of `Spec(k')` cover the self-product. -/
theorem iSup_opensRange_specGaloisCoprojection :
    ⨆ σ : k' ≃ₐ[k] k', (specGaloisCoprojection σ).opensRange = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨⟨σ, y⟩, hy⟩ := (sigmaMk fun _ : k' ≃ₐ[k] k' ↦ Spec (.of k')).surjective
    ((sigmaIsoSelfProduct k k').inv x)
  rw [sigmaMk_mk] at hy
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨σ, y, ?_⟩
  rw [← ι_sigmaIsoSelfProduct_hom, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply,
    Iso.inv_hom_id]
  rfl

end Stacks.WeilCohomology

end

end
