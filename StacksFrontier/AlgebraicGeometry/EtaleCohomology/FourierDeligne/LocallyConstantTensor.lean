module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyFreeTensor

/-!
# Inverse images and tensor products of locally constant sheaves

The two stability properties of étale-locally constant sheaves of `Λ`-modules
(`Stacks.ConstantSheaf.IsLocallyConstantWith`) with arbitrary constraints on the local values,
by the arguments of `Stacks.EtaleCohomology.isLocallyFreeEtaleModule_inverseImage` and
`Stacks.EtaleCohomology.isLocallyFreeEtaleModule_tensor`:

* the inverse image along any morphism of a locally constant sheaf is locally constant with the
  same local values;
* the tensor product of two locally constant sheaves is locally constant, with values the tensor
  products of the values.

They give the local constancy of the integrand `g⁻¹ H ⊗ L` of the Fourier transform over the open
where `H` is locally constant, in Laumon's argument for
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isLocallyConstantWith_inverseImage`.
* `Stacks.EtaleCohomology.isLocallyConstantWith_tensor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

variable (Λ : Type) [CommRing Λ]

/-- If `w = a ≫ V.hom` for an étale `Y`-scheme `V` on which `N` is trivialized by `e`, then
`w⁻¹ N` is constant. -/
private def etaleModuleInverseImageIsoConstantOfComp {X Y : Scheme.{u}} (V : Y.Etale)
    (N : EtaleModules.{u, 0} Λ Y) (E : ModuleCat.{u + 1} Λ)
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback _ V).obj N)
    (a : X ⟶ V.left) (w : X ⟶ Y) (hw : w = a ≫ V.hom) :
    (etaleModuleInverseImage.{u, 0} Λ w).obj N ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E :=
  eqToIso (congrArg (fun φ => (etaleModuleInverseImage.{u, 0} Λ φ).obj N) hw) ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} Λ a V.hom).app N ≪≫
    (etaleModuleInverseImage.{u, 0} Λ a).mapIso
      (etaleModuleInverseImageIsoConstantOfOverPullback V Λ N E e) ≪≫
    (etaleModuleInverseImageConstantIso.{u, 0} Λ a).app E

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **The inverse image of a locally constant sheaf is locally constant**, with the same local
values. -/
theorem isLocallyConstantWith_inverseImage (Q : ModuleCat.{u + 1} Λ → Prop) {X Y : Scheme.{u}}
    (a : X ⟶ Y) {N : EtaleModules.{u, 0} Λ Y}
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology Q N) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ a).obj N) := by
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
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ ((V.hom ≫ a) v))
    have hw' : (Vs i).hom w = (V.hom ≫ a) v := by
      rw [← hw]
      exact congrArg (fun φ : (Vs i).left ⟶ Y => φ w) ((f i).w.symm.trans (Category.comp_id _))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback v w hw'.symm
    exact Set.mem_iUnion.2 ⟨i, z, hz⟩
  · obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
    refine ⟨E, hE, ⟨overPullbackIsoConstantOfEtaleModuleInverseImage Λ (W i) _ E ?_⟩⟩
    have hsq : (W i).hom ≫ a = pullback.snd (V.hom ≫ a) (Vs i).hom ≫ (Vs i).hom := by
      show (pullback.fst (V.hom ≫ a) (Vs i).hom ≫ V.hom) ≫ a = _
      rw [Category.assoc]
      exact pullback.condition
    exact (etaleModuleInverseImageCompIso.{u, 0} Λ (W i).hom a).symm.app N ≪≫
      etaleModuleInverseImageIsoConstantOfComp Λ (Vs i) N E e _ _ hsq

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **The tensor product of two locally constant sheaves is locally constant**, its local values
being the tensor products of local values of the factors. -/
theorem isLocallyConstantWith_tensor (Q₁ Q₂ : ModuleCat.{u + 1} Λ → Prop) {X : Scheme.{u}}
    {A B : EtaleModules.{u, 0} Λ X}
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q₁ A)
    (hB : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q₂ B) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology
      (fun E => ∃ E₁ E₂, Q₁ E₁ ∧ Q₂ E₂ ∧ E = E₁ ⊗ E₂) (A ⊗ B) := by
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
    obtain ⟨E, hE, ⟨eA⟩⟩ := htriv i
    obtain ⟨E', hE', ⟨eB⟩⟩ := htriv' i j
    let iA := etaleModuleInverseImageIsoConstantOfComp Λ (V i) A E eA (g i j).left (W i j).hom
      (MorphismProperty.Over.w (g i j)).symm
    refine ⟨E ⊗ E', ⟨E, E', hE, hE', rfl⟩, ⟨overPullbackIsoConstantOfEtaleModuleInverseImage Λ
      (W i j) (A ⊗ B) (E ⊗ E') ?_⟩⟩
    exact (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ (W i j).hom) A B).symm ≪≫
      tensorIso iA (etaleModuleInverseImageIsoConstantOfOverPullback (W i j) Λ B E' eB) ≪≫
      etaleModuleConstantTensorIso Λ (W i j).left E E'

end Stacks.EtaleCohomology

end
