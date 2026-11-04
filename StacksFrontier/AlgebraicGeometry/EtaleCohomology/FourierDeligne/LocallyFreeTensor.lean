module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyFreeInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal

/-!
# Tensor products of étale-locally free sheaves

The tensor product of two étale-locally free sheaves of finite rank `A`, `B` of `Λ`-modules on
`X_étale` is étale-locally free of finite rank. Over an étale `U ⟶ X`, take a trivializing
covering `{Vᵢ ⟶ U}` of `A` and, for each `i`, one `{W_{ij} ⟶ Vᵢ}` of `B`; the composites cover `U`.
On `W = W_{ij}` the inverse image `w⁻¹ A` is constant (it is the inverse image of the constant
sheaf `A|_{Vᵢ}`), `w⁻¹ B` is constant, the inverse image is monoidal, and the tensor product of two
constant sheaves is the constant sheaf on the tensor product of the values, a free module of
finite rank.

This is the local freeness of `pr₁⁻¹ F ⊗ μ⁻¹ L_ψ`, the integrand of the Fourier transform of a
lisse sheaf `F`, used in Laumon's argument for
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.etaleModuleConstantTensorIso`: `E̲ ⊗ E̲' ≅ (E ⊗ E')̲`.
* `Stacks.EtaleCohomology.isLocallyFreeEtaleModule_tensor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

variable (Λ : Type) [CommRing Λ]

/-- **`E̲ ⊗ E̲' ≅ (E ⊗ E')̲` on `X_étale`**: the constant presheaf functor and sheafification are
monoidal. -/
def etaleModuleConstantTensorIso (X : Scheme.{u}) (E E' : ModuleCat.{u + 1} Λ) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E ⊗
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E' ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (E ⊗ E') :=
  let c : ModuleCat.{u + 1} Λ ⥤ X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ := Functor.const _
  let e : c.obj E ⊗ c.obj E' ≅ c.obj (E ⊗ E') :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [c])
  Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (c.obj E) (c.obj E') ≪≫
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso e

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **The tensor product of two étale-locally free sheaves of finite rank is étale-locally free of
finite rank.** -/
theorem isLocallyFreeEtaleModule_tensor {X : Scheme.{u}} {A B : EtaleModules.{u, 0} Λ X}
    (hA : IsLocallyFreeEtaleModule Λ A) (hB : IsLocallyFreeEtaleModule Λ B) :
    IsLocallyFreeEtaleModule Λ (A ⊗ B) := by
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ := hA U
  choose I' W g hcov' htriv' using fun i => hB (V i)
  refine ⟨Σ i, I' i, fun p => W p.1 p.2, fun p => g p.1 p.2 ≫ f p.1, ?_, fun p => ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov ⊢
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, v, hv⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ x)
    have hi := hcov' i
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hi
    obtain ⟨j, w, hw⟩ := Set.mem_iUnion.1 (hi ▸ Set.mem_univ v)
    refine Set.mem_iUnion.2 ⟨⟨i, j⟩, w, ?_⟩
    show ((g i j).left ≫ (f i).left) w = x
    rw [Scheme.Hom.comp_apply, hw, hv]
  · obtain ⟨i, j⟩ := p
    obtain ⟨E, ⟨hEf, hEn⟩, ⟨eA⟩⟩ := htriv i
    obtain ⟨E', ⟨hE'f, hE'n⟩, ⟨eB⟩⟩ := htriv' i j
    have := hEf; have := hEn; have := hE'f; have := hE'n
    let w := (W i j).hom
    let a := (g i j).left
    have hw : a ≫ (V i).hom = w := MorphismProperty.Over.w (g i j)
    let iA : (etaleModuleInverseImage.{u, 0} Λ w).obj A ≅
        (constantSheaf (W i j).left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E :=
      eqToIso (congrArg (fun φ => (etaleModuleInverseImage.{u, 0} Λ φ).obj A) hw.symm) ≪≫
        (etaleModuleInverseImageCompIso.{u, 0} Λ a (V i).hom).app A ≪≫
        (etaleModuleInverseImage.{u, 0} Λ a).mapIso
          (etaleModuleInverseImageIsoConstantOfOverPullback (V i) Λ A E eA) ≪≫
        (etaleModuleInverseImageConstantIso.{u, 0} Λ a).app E
    let iB := etaleModuleInverseImageIsoConstantOfOverPullback (W i j) Λ B E' eB
    refine ⟨E ⊗ E', ⟨?_, ?_⟩, ⟨overPullbackIsoConstantOfEtaleModuleInverseImage Λ (W i j)
      (A ⊗ B) (E ⊗ E') ?_⟩⟩
    · exact inferInstanceAs (Module.Free Λ (TensorProduct Λ E E'))
    · exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ E E'))
    · exact (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ w) A B).symm ≪≫
        tensorIso iA iB ≪≫ etaleModuleConstantTensorIso Λ (W i j).left E E'

end Stacks.EtaleCohomology

end
