module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingProjective
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence

/-!
# The twisted inverse image of a dualizing module along an H-projective morphism

Let `A` be a Noetherian ring with a dualizing module `ω_A` and let `f : X ⟶ Spec(A)` be proper
and H-projective, i.e. a closed immersion `i : X ⟶ ℙⁿ_A` followed by the structure morphism
`p : ℙⁿ_A ⟶ Spec(A)`. Then `f^×(ω̃_A[0])` is a dualizing complex on `X`, where `f^×` is the
twisted inverse image of [Stacks, Tag 0A9E], the right adjoint of `Rf_*` on `D_QCoh`. This is
[Stacks, Tag 0AA3] for H-projective morphisms to an affine Noetherian base, `f^× = f^!` for
proper `f`.

The proof is the source's: `f^× ≅ i^× ∘ p^×`; `p^×(ω̃_A[0]) ≅ (p^*ω̃_A ⊗ 𝒪(-n-1))[n]` by
[Stacks, Tag 0A9U] and [Stacks, Tag 0A9W], a dualizing complex on `ℙⁿ_A` by
`RationalSingularitySituation.isDualizingComplex_twistedInverseImage_projectiveSpaceOver_of_isos`;
and `i^×` carries dualizing complexes to dualizing complexes by
`ClosedImmersionRestriction.isDualizingComplex_twistedInverseImage_comp_of_isClosedImmersion`. For
`n = 0` the structure morphism is an isomorphism, so `f` is itself a closed immersion.

Over a field `k`, the field is a dualizing module over itself, and [Stacks, Tag 0A26] says that
every proper scheme over `k` of dimension at most one is H-projective. This gives that the
dualizing complex `ω_X^• = f^×(𝒪_{Spec k})` of [Stacks, Tag 0BS2] is a dualizing complex in the
sense of [Stacks, Tag 0A87] for `X` proper over `k` of dimension at most one, and for every
H-projective `X` over `k`.

## Main results

* `Stacks.Duality.isDualizingComplex_twistedInverseImage_of_isProjectiveMorphism`
* `Stacks.Duality.isDualizingComplex_dualizingComplexOverField_of_isProjectiveMorphism`
* `Stacks.Duality.isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one`

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Duality.ClosedImmersionRestriction

universe u

namespace Stacks.Duality

/-- **A field is a dualizing module over itself.** The field in degree zero is a (normalized)
dualizing complex: a field is a regular, hence Gorenstein, local ring. -/
theorem isDualizingRingModule_self_of_field (k : Type u) [Field k] :
    IsDualizingRingModule k k :=
  ⟨inferInstance, 0, Dualizing.IsRegularLocalRing.isGorensteinLocalRing k⟩

/-- **[Stacks, Tag 0AA3] for an H-projective morphism to an affine Noetherian base.** Let `A` be
a Noetherian ring with a dualizing module `ω_A`, and `f : X ⟶ Spec(A)` proper and H-projective.
For `K ∈ D_QCoh(𝒪_{Spec A})` isomorphic to `ω̃_A[0]`, the twisted inverse image `f^×(K)` is a
dualizing complex on `X`. -/
theorem isDualizingComplex_twistedInverseImage_of_isProjectiveMorphism {A : CommRingCat.{u}}
    [IsNoetherianRing A] (ωA : ModuleCat.{u} A) (hωA : IsDualizingRingModule A ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f] (hf : IsProjectiveMorphism f)
    (K : quasiCoherentDerivedCategory (Spec A))
    (e : K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj ((tilde.functor A).obj ωA)) :
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingComplex ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K).obj := by
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- reduce to `K = ω̃_A[0]` on the nose
  let K' : quasiCoherentDerivedCategory (Spec A) :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj ((tilde.functor A).obj ωA),
      ObjectProperty.prop_of_iso _ e K.property⟩
  let eK : K' ≅ K := (ObjectProperty.fullyFaithfulι _).preimageIso e.symm
  refine isDualizingComplex_of_iso
    ((ObjectProperty.ι _).mapIso ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).mapIso eK)) ?_
  have hK' : IsDualizingComplex K'.obj :=
    (isDualizingComplex_singleFunctor_model_iff (HasDerivedCategory.standard (Spec A).Modules)
      inferInstance 0 ((tilde.functor A).obj ωA)).2
      (isDualizingComplex_singleFunctor_tilde A ωA 0 (hωA.isDualizingComplex_singleFunctor 0))
  obtain ⟨n, i, hi, hip⟩ := hf
  have := hi
  subst hip
  rcases n with _ | m
  · -- `ℙ⁰_A ⟶ Spec(A)` is an isomorphism, so `f` is a closed immersion
    have : IsClosedImmersion (i ≫ (projectiveSpaceOver 0 (Spec A) ↘ Spec A)) := inferInstance
    exact isDualizingComplex_rightAdjoint_of_isClosedImmersion _
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) _
      (twistedInverseImageAdjunction _ (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
      K' (isBoundedBelow_of_isDualizingComplex _ hK') hK'
  · set p := projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A
    have : IsProper p := isProper_projectiveSpaceOver _ _
    have : IsLocallyNoetherian (projectiveSpaceOver (m + 1) (Spec A)) :=
      LocallyOfFiniteType.isLocallyNoetherian p
    have : CompactSpace (projectiveSpaceOver (m + 1) (Spec A)) :=
      QuasiCompact.compactSpace_of_compactSpace p
    let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward p
    obtain ⟨e₁⟩ :=
      RationalSingularitySituation.nonempty_twistedInverseImage_iso_tensor_of_hasRightDual
        A m (fun L hL => nonempty_hasRightDual_of_isCompactObject (Spec A) L hL) K'
    obtain ⟨E₀, hE₀, ⟨e₂⟩⟩ :=
      RationalSingularitySituation.exists_twistedInverseImage_derivedStructureSheaf_iso_shift A m
    open RationalSingularitySituation in
    have hP := isDualizingComplex_twistedInverseImage_projectiveSpaceOver_of_isos
      m ωA hωA K' rfl E₀ hE₀ e₁ e₂
    exact isDualizingComplex_twistedInverseImage_comp_of_isClosedImmersion i p K'
      (isBoundedBelow_of_isDualizingComplex _ hP) hP

/-- **The dualizing complex `ω_X^• = f^×(𝒪_{Spec k})` of an H-projective scheme over a field is a
dualizing complex** ([Stacks, Tag 0A87]). -/
theorem isDualizingComplex_dualizingComplexOverField_of_isProjectiveMorphism {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hf : IsProjectiveMorphism f) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingComplex (dualizingComplexOverField f).obj :=
  isDualizingComplex_twistedInverseImage_of_isProjectiveMorphism
    (ModuleCat.of (CommRingCat.of k) k) (isDualizingRingModule_self_of_field k) f hf _
    (Iso.refl _)

/-- **For `X` proper over a field `k` with `dim(X) ≤ 1`, the dualizing complex
`ω_X^• = f^×(𝒪_{Spec k})` of [Stacks, Tag 0BS2] is a dualizing complex** ([Stacks, Tag 0A87]):
such an `X` is H-projective over `k` by [Stacks, Tag 0A26]. -/
theorem isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsDualizingComplex (dualizingComplexOverField f).obj :=
  isDualizingComplex_dualizingComplexOverField_of_isProjectiveMorphism f
    (HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
      f hdim)

end Stacks.Duality

end
