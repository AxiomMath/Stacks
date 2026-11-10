module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.IntegralTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.UnibranchConstantModuleFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# Inverse images of étale-locally free sheaves

An étale-locally free sheaf of finite rank `N` on `Y` stays étale-locally free under the inverse
image along any morphism `a : X ⟶ Y`: for an étale `V ⟶ X`, base change a trivializing covering
`{Vᵢ ⟶ Y}` of `N` to `V`; on `V ×_Y Vᵢ` the inverse image of `a⁻¹ N` is the inverse image of
`N|_{Vᵢ}`, a constant sheaf, hence constant with the same value.

This is the local freeness of the kernels `m⁻¹ L_ψ` of the Fourier transform and of their
pullbacks to the triple product, which the composition of integral transforms needs
(`Stacks.EtaleCohomology.integralTransformCompIso`).

## Main results

* `Stacks.EtaleCohomology.isLocallyFreeEtaleModule_inverseImage`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **The inverse image of an étale-locally free sheaf of finite rank is étale-locally free of
finite rank**, with the same local values. -/
theorem isLocallyFreeEtaleModule_inverseImage {X Y : Scheme.{u}} (a : X ⟶ Y)
    {N : EtaleModules.{u, 0} Λ Y} (hN : IsLocallyFreeEtaleModule Λ N) :
    IsLocallyFreeEtaleModule Λ ((etaleModuleInverseImage.{u, 0} Λ a).obj N) := by
  intro V
  obtain ⟨I, Vs, f, hcov, htriv⟩ := hN (Scheme.Etale.mk (𝟙 Y))
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov
  -- the base change of the covering to `V`
  have : Etale V.hom := V.prop
  have : ∀ i, Etale (Vs i).hom := fun i => (Vs i).prop
  let W : I → X.Etale := fun i =>
    Scheme.Etale.mk (pullback.fst (V.hom ≫ a) (Vs i).hom ≫ V.hom)
  let g : ∀ i, W i ⟶ V := fun i =>
    MorphismProperty.Over.homMk (pullback.fst (V.hom ≫ a) (Vs i).hom) rfl
  refine ⟨I, W, g, ?_, fun i => ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ ((V.hom ≫ a) v))
    obtain ⟨w, hw⟩ := hi
    have hw' : (Vs i).hom w = (V.hom ≫ a) v := by
      rw [← hw]
      have := (f i).w
      exact congrArg (fun φ : (Vs i).left ⟶ Y => φ w) (this.symm.trans (Category.comp_id _))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback v w hw'.symm
    exact Set.mem_iUnion.2 ⟨i, z, hz⟩
  · obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
    refine ⟨E, hE, ⟨overPullbackIsoConstantOfEtaleModuleInverseImage Λ (W i) _ E ?_⟩⟩
    have hsq : (W i).hom ≫ a = pullback.snd (V.hom ≫ a) (Vs i).hom ≫ (Vs i).hom := by
      change (pullback.fst (V.hom ≫ a) (Vs i).hom ≫ V.hom) ≫ a = _
      rw [Category.assoc]
      exact pullback.condition
    exact (etaleModuleInverseImageCompIso.{u, 0} Λ (W i).hom a).symm.app N ≪≫
      eqToIso (congrArg (fun φ => (etaleModuleInverseImage.{u, 0} Λ φ).obj N) hsq) ≪≫
      (etaleModuleInverseImageCompIso.{u, 0} Λ (pullback.snd (V.hom ≫ a) (Vs i).hom)
        (Vs i).hom).app N ≪≫
      (etaleModuleInverseImage.{u, 0} Λ (pullback.snd (V.hom ≫ a) (Vs i).hom)).mapIso
        (etaleModuleInverseImageIsoConstantOfOverPullback (Vs i) Λ N E e) ≪≫
      (etaleModuleInverseImageConstantIso.{u, 0} Λ (pullback.snd (V.hom ≫ a) (Vs i).hom)).app E

end Stacks.EtaleCohomology

end
