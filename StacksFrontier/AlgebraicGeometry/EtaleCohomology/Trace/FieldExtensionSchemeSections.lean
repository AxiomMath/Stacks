module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful

/-!
# The sections of `X ×_k k' ⟶ X` given by a `k'`-structure of `X`

Let `k ⊆ k'` be a finite extension of finite fields and `X` a scheme over `k` whose structure
morphism factors as `X ⟶ Spec k' ⟶ Spec k` through `g : X ⟶ Spec k'`.  Every `k`-automorphism `τ`
of `k'` gives a section `s_τ = (id, Spec(τ) ∘ g) : X ⟶ X ×_k k'` of the projection.  It is an open
immersion (the projection is étale) and a closed immersion (the projection is separated), and
every point of `X ×_k k'` lies on one of them: at a point `y`, the two `k`-embeddings of `k'` in
`κ(y)` through `X` and through `Spec k'` have the same image, `k'` being normal over `k`, so they
differ by an automorphism `τ`, and `y` lies on `s_τ`.

This is the decomposition `X_k̄ = ⊔_σ X ×_{k', σ} k̄` used in the proof of purity in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) when `X_k̄` is disconnected, read over `k'`
on `X ×_k k'`.

## Main definitions

* `Stacks.EtaleCohomology.fieldExtensionSection`: the section `s_τ`.

## Main results

* `Stacks.EtaleCohomology.isOpenImmersion_fieldExtensionSection`,
  `Stacks.EtaleCohomology.isClosedImmersion_fieldExtensionSection`.
* `Stacks.EtaleCohomology.exists_mem_range_fieldExtensionSection`: the sections cover.
* `Stacks.EtaleCohomology.connectedSpace_pullback_comp_of_inverse`: base change of a morphism
  followed by an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- The structure morphism of a finite extension of finite fields is étale. -/
theorem etale_specAlgebraMap_of_finite (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [Finite k] [Module.Finite k k'] : Etale (specAlgebraMap k k') := by
  rw [specAlgebraMap, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.2
    ⟨Algebra.FormallyEtale.of_isSeparable k k',
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- `Spec(τ) : Spec k' ⟶ Spec k'` is a morphism over `Spec k` for a `k`-algebra map `τ`. -/
theorem specMap_algHom_comp_specAlgebraMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (τ : k' →ₐ[k] k') :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ specAlgebraMap k k' = specAlgebraMap k k' := by
  rw [specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact τ.comp_algebraMap

section Sections

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : X ⟶ Spec (.of k')) (hg : g ≫ specAlgebraMap k k' = f)

/-- **The section `s_τ = (id, Spec(τ) ∘ g)` of `X ×_k k' ⟶ X`.** -/
def fieldExtensionSection (τ : k' →ₐ[k] k') : X ⟶ pullback f (specAlgebraMap k k') :=
  pullback.lift (𝟙 X) (g ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) (by
    rw [Category.id_comp, Category.assoc, specMap_algHom_comp_specAlgebraMap, hg])

/-- The section `s_τ` composed with the projection `X ×_k k' ⟶ X` is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem fieldExtensionSection_fst (τ : k' →ₐ[k] k') :
    fieldExtensionSection f g hg τ ≫ pullback.fst f (specAlgebraMap k k') = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The section `s_τ` composed with the projection `X ×_k k' ⟶ Spec k'` is `Spec(τ) ∘ g`. -/
@[reassoc (attr := simp)]
theorem fieldExtensionSection_snd (τ : k' →ₐ[k] k') :
    fieldExtensionSection f g hg τ ≫ pullback.snd f (specAlgebraMap k k') =
      g ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) :=
  pullback.lift_snd _ _ _

/-- **`s_τ` is an open immersion**, being a section of the étale projection. -/
theorem isOpenImmersion_fieldExtensionSection [Finite k] [Module.Finite k k']
    (τ : k' →ₐ[k] k') : IsOpenImmersion (fieldExtensionSection f g hg τ) := by
  have := etale_specAlgebraMap_of_finite k k'
  exact isOpenImmersion_of_section_of_etale (pullback.fst f (specAlgebraMap k k')) _
    (fieldExtensionSection_fst f g hg τ)

/-- **`s_τ` is a closed immersion**, being a section of the separated projection. -/
theorem isClosedImmersion_fieldExtensionSection (τ : k' →ₐ[k] k') :
    IsClosedImmersion (fieldExtensionSection f g hg τ) := by
  have : IsClosedImmersion (fieldExtensionSection f g hg τ ≫
      pullback.fst f (specAlgebraMap k k')) := by
    rw [fieldExtensionSection_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst f (specAlgebraMap k k'))

/-- **Two `k`-embeddings of a finite extension `k'` of a finite field `k` in a field differ by a
`k`-endomorphism of `k'`**: `k'` is normal over `k`, so both have the same image. -/
theorem exists_algHom_comp_eq_of_finite [Finite k'] {K : Type u} [Field K] [Algebra k K]
    (α β : k' →ₐ[k] K) : ∃ τ : k' →ₐ[k] k', α.comp τ = β := by
  have : Finite k := Finite.of_injective _ (algebraMap k k').injective
  let e : k' ≃ₐ[k] α.fieldRange := AlgEquiv.ofInjectiveField α
  have : Normal k α.fieldRange := Normal.of_algEquiv e
  have hβ : ∀ x, β x ∈ α.fieldRange := fun x => by
    have hmem : β x ∈ (β.comp e.symm.toAlgHom).fieldRange := ⟨e x, by simp⟩
    rwa [AlgHom.fieldRange_of_normal (E := α.fieldRange) (β.comp e.symm.toAlgHom)] at hmem
  refine ⟨e.symm.toAlgHom.comp (β.codRestrict α.fieldRange.toSubalgebra hβ), ?_⟩
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply ⟨β x, hβ x⟩)

/-- **The sections `s_τ` cover `X ×_k k'`.** -/
theorem exists_mem_range_fieldExtensionSection [Finite k']
    (y : ↥(pullback f (specAlgebraMap k k'))) :
    ∃ τ : k' →ₐ[k] k', y ∈ Set.range (fieldExtensionSection f g hg τ) := by
  let ι := (pullback f (specAlgebraMap k k')).fromSpecResidueField y
  let a := ι ≫ pullback.fst f (specAlgebraMap k k')
  let b := ι ≫ pullback.snd f (specAlgebraMap k k')
  let K := (pullback f (specAlgebraMap k k')).residueField y
  let αc : CommRingCat.of k' ⟶ K := Spec.preimage (a ≫ g)
  let βc : CommRingCat.of k' ⟶ K := Spec.preimage b
  have hab : CommRingCat.ofHom (algebraMap k k') ≫ αc =
      CommRingCat.ofHom (algebraMap k k') ≫ βc := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc, hg]
    exact (Category.assoc _ _ _).trans
      ((congrArg (ι ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  let : Algebra k K := (βc.hom.comp (algebraMap k k')).toAlgebra
  let α : k' →ₐ[k] K := { αc.hom with
    commutes' := fun c => congrArg (fun φ => φ.hom c) hab }
  let β : k' →ₐ[k] K := { βc.hom with commutes' := fun c => rfl }
  obtain ⟨τ, hτ⟩ := exists_algHom_comp_eq_of_finite α β
  refine ⟨τ, a (IsLocalRing.closedPoint K), ?_⟩
  have hb : b = (a ≫ g) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) := by
    rw [← Spec.map_preimage (a ≫ g), ← Spec.map_comp, ← Spec.map_preimage b]
    congr 1
    ext x
    exact (congrArg (fun φ : k' →ₐ[k] K => φ x) hτ).symm
  have hι : a ≫ fieldExtensionSection f g hg τ = ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, fieldExtensionSection_fst, Category.comp_id]
    · rw [Category.assoc, fieldExtensionSection_snd, ← Category.assoc, ← hb]
  have hc : (a ≫ fieldExtensionSection f g hg τ) (IsLocalRing.closedPoint K) =
      fieldExtensionSection f g hg τ (a (IsLocalRing.closedPoint K)) := Scheme.Hom.comp_apply _ _ _
  rw [← hc, hι]
  exact Scheme.fromSpecResidueField_apply y _

end Sections

/-- **Connectedness of a base change along a morphism followed by an isomorphism**: the base change
of `g ≫ h` along `S` is that of `g` along `S ≫ h⁻¹`. -/
theorem connectedSpace_pullback_comp_of_inverse {X Y Y' T : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Y')
    (h' : Y' ⟶ Y) (hh : h' ≫ h = 𝟙 Y') (hh' : h ≫ h' = 𝟙 Y)
    (S : T ⟶ Y') [ConnectedSpace ↥(pullback g (S ≫ h'))] :
    ConnectedSpace ↥(pullback (g ≫ h) S) := by
  let φ : pullback g (S ≫ h') ⟶ pullback (g ≫ h) S :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
      rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hh,
        Category.comp_id])
  have hcond : pullback.fst (g ≫ h) S ≫ g = pullback.snd (g ≫ h) S ≫ S ≫ h' := by
    simpa only [Category.assoc, hh', Category.comp_id] using
      congrArg (· ≫ h') (pullback.condition (f := g ≫ h) (g := S))
  let ψ : pullback (g ≫ h) S ⟶ pullback g (S ≫ h') :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) hcond
  have hψ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp only [φ, ψ, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  have hsurj : Function.Surjective φ := fun z => ⟨ψ z, by
    rw [← Scheme.Hom.comp_apply, hψ]
    rfl⟩
  exact hsurj.connectedSpace φ.continuous

end Stacks.EtaleCohomology

end
