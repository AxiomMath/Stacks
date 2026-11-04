module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChartDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties

/-!
# `M ↦ 𝒪_X ⊗_A M` is exact on the model for a flat `X → Spec A`

The functor `M ↦ 𝒪_X ⊗_A M` on the `Type u` model of the small étale site of `X`
(`AlgebraicGeometry.Space.modelTensorFunctor`) is exact for every flat `g : X → Spec A`: it is a
left adjoint, and its affine étale charts have rings of sections flat over `A`. At the identity of
`Spec A` this is the exactness of `M ↦ M~`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.shortExact_map_modelTensorFunctor_of_isFlat_algebraOver`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Stacks.Cohomology.SiteModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- **`M ↦ 𝒪_X ⊗_A M` is exact on the model for a flat `g : X → Spec A`**: it is a left adjoint,
hence right exact, and it preserves injections because the rings of the affine étale charts of
`X` are flat over `Γ(Spec A)`, hence over `A`. This is
`AlgebraicGeometry.Space.ProperFlatLift.shortExact_map_modelTensorFunctor_chartBaseRingHom` for an
arbitrary flat `g`. -/
theorem shortExact_map_modelTensorFunctor_of_isFlat_algebraOver {X : AlgebraicSpaces B S hS}
    (g : X ⟶ schemeSpace (algebraOver A B S hS toS hA)) (hg : IsFlat B S hS g.hom)
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) :
    (Sq.map (modelTensorFunctor ((baseRingHomOfMap g).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))).ShortExact := by
  have adj := baseRingTensorAdjunction.{u, u, u, u, u} ((baseRingHomOfMap g).comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  have : (modelTensorFunctor ((baseRingHomOfMap g).comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).IsLeftAdjoint := adj.isLeftAdjoint
  have := hSq.mono_f
  have := hSq.epi_g
  have hcov : ∀ W, ∃ (I : Type u) (Vi : I → SmallModel.{u} (SmallEtale B S hS X.1))
      (g' : ∀ i, Vi i ⟶ W), Sieve.ofArrows Vi g' ∈ smallEtaleModelTopology B S hS X.1 W ∧
        ∀ i, let _ := baseRingSectionAlgebra ((baseRingHomOfMap g).comp
          (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) (Opposite.op (Vi i))
          Module.Flat A
            ((smallEtaleModelStructureSheaf B S hS X).obj.obj (Opposite.op (Vi i))) := by
    intro W
    obtain ⟨I, Vi, g', hS', hfl⟩ := exists_ofArrows_mem_modelTopology_flat g hg
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))) W
    refine ⟨I, Vi, g', hS', fun i => ?_⟩
    have h := RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)) (hfl i)
    exact h
  have : Mono (Sq.map (modelTensorFunctor ((baseRingHomOfMap g).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))).f :=
    Stacks.Cohomology.SiteModules.mono_baseRingTensorFunctor_map ((baseRingHomOfMap g).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) hcov Sq.f
      ((ModuleCat.mono_iff_injective Sq.f).1 inferInstance)
  have : Epi (Sq.map (modelTensorFunctor ((baseRingHomOfMap g).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))).g :=
    inferInstanceAs (Epi ((modelTensorFunctor ((baseRingHomOfMap g).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).map Sq.g))
  exact ShortComplex.ShortExact.mk' (hSq.exact.map_of_epi_of_preservesCokernel _ inferInstance
    inferInstance) inferInstance inferInstance

end AlgebraicGeometry.Space.ProperFlatLift

end
