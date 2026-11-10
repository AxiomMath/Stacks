module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula

/-!
# Sheaves without sections supported off an open, and invertible twists

For an open immersion `i : V ⟶ X`, a sheaf `G` of `Λ`-modules on `X_étale` has no sections
supported off `V` (the unit `G ⟶ i_* i⁻¹ G` is a monomorphism) if and only if every morphism to
`G` from a sheaf `P` with `i⁻¹ P = 0` vanishes: the kernel `K` of the unit has `i⁻¹ K = 0`
because `i⁻¹` is exact and `i⁻¹` of the unit is a split monomorphism.

The property passes along an invertible twist: if `L, L'` are étale-locally free with
`L' ⊗ L ≅ 𝟙` and `G ⊗ L'` has no sections supported off `V`, neither has `G`. A morphism
`φ : P ⟶ G` with `i⁻¹ P = 0` gives `φ ▷ L' : P ⊗ L' ⟶ G ⊗ L'` with
`i⁻¹(P ⊗ L') = i⁻¹ P ⊗ i⁻¹ L' = 0`, so `φ ▷ L' = 0`, and then `φ ▷ (L' ⊗ L) = 0`, that is `φ = 0`.

This handles the Fourier kernel `L_ψ(xt)` in the vanishing of `H⁰` of the Fourier transform of a
sheaf without punctual sections in Laumon's argument for
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.mono_etaleModuleInverseImageAdj_unit_app_of_forall`.
* `Stacks.EtaleCohomology.eq_zero_of_mono_etaleModuleInverseImageAdj_unit_app`.
* `Stacks.EtaleCohomology.mono_etaleModuleInverseImageAdj_unit_app_of_tensor_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

variable (Λ : Type) [CommRing Λ]

/-- **Morphisms from sheaves vanishing on `V` kill a sheaf without sections supported off `V`.** -/
theorem eq_zero_of_mono_etaleModuleInverseImageAdj_unit_app {X V : Scheme.{u}} (i : V ⟶ X)
    {G : EtaleModules.{u, 0} Λ X} (hη : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G))
    {P : EtaleModules.{u, 0} Λ X} (φ : P ⟶ G)
    (hP : IsZero ((etaleModuleInverseImage.{u, 0} Λ i).obj P)) : φ = 0 := by
  have hn := (etaleModuleInverseImageAdj.{u, 0} Λ i).unit.naturality φ
  have h0 : (etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app P = 0 :=
    (Functor.map_isZero (etaleModuleDirectImage.{u, 0} Λ i) hP).eq_of_tgt _ _
  have hφ : φ ≫ (etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G = 0 ≫
      (etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G := by
    rw [Functor.id_map] at hn
    rw [zero_comp, hn, h0, zero_comp]
  exact (cancel_mono _).1 hφ

/-- **A sheaf has no sections supported off `V` if morphisms from sheaves vanishing on `V` to it
vanish.** -/
theorem mono_etaleModuleInverseImageAdj_unit_app_of_forall {X V : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i] (G : EtaleModules.{u, 0} Λ X)
    (h : ∀ (P : EtaleModules.{u, 0} Λ X) (φ : P ⟶ G),
      IsZero ((etaleModuleInverseImage.{u, 0} Λ i).obj P) → φ = 0) :
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G) := by
  let adj := etaleModuleInverseImageAdj.{u, 0} Λ i
  let I := etaleModuleInverseImage.{u, 0} Λ i
  -- `i⁻¹` of the unit is a split monomorphism
  have hm : Mono (I.map (adj.unit.app G)) := @IsSplitMono.mono _ _ _ _ _
    (IsSplitMono.mk' ⟨adj.counit.app (I.obj G), adj.left_triangle_components G⟩)
  have : PreservesFiniteLimits I := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ i
  -- so `i⁻¹` of the kernel of the unit vanishes
  exact Abelian.mono_of_kernel_ι_eq_zero _ (h _ _ ((@isZero_kernel_of_mono _ _ _ _ _ _ hm _).of_iso
    (PreservesKernel.iso I (adj.unit.app G))))

/-- **No sections supported off `V` descends along an invertible twist.** Let `L, L'` be
étale-locally free with `L' ⊗ L ≅ 𝟙`. If `G ⊗ L'` is isomorphic to a sheaf without sections
supported off `V`, then so is `G`. -/
theorem mono_etaleModuleInverseImageAdj_unit_app_of_tensor_iso {X V : Scheme.{u}} (i : V ⟶ X)
    [IsOpenImmersion i] {G A L L' : EtaleModules.{u, 0} Λ X}
    (hL : IsLocallyFreeEtaleModule Λ L) (hL' : IsLocallyFreeEtaleModule Λ L')
    (e : L' ⊗ L ≅ 𝟙_ (EtaleModules.{u, 0} Λ X)) (a : G ⊗ L' ≅ A)
    (hA : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app A)) :
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app G) := by
  refine mono_etaleModuleInverseImageAdj_unit_app_of_forall Λ i G fun P φ hP => ?_
  let I := etaleModuleInverseImage.{u, 0} Λ i
  have :=
    (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      L hL).1
  have :=
    (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      (I.obj L') (isLocallyFreeEtaleModule_inverseImage Λ i hL')).1
  -- `i⁻¹ (P ⊗ L') = 0`
  have hPL : IsZero (I.obj (P ⊗ L')) :=
    IsZero.of_iso (Functor.map_isZero (MonoidalCategory.tensorRight (I.obj L')) hP)
      (Functor.Monoidal.μIso I P L').symm
  have h1 : φ ▷ L' = 0 := by
    rw [← cancel_mono a.hom, zero_comp]
    exact eq_zero_of_mono_etaleModuleInverseImageAdj_unit_app Λ i hA _ hPL
  have h2 : φ ▷ (L' ⊗ L) = 0 := by
    rw [whiskerRight_tensor, h1]
    change (α_ _ _ _).inv ≫ (MonoidalCategory.tensorRight L).map 0 ≫ (α_ _ _ _).hom = 0
    rw [Functor.map_zero, zero_comp, comp_zero]
  have h3 : φ ▷ 𝟙_ _ = 0 := by
    rw [← cancel_epi (P ◁ e.hom), comp_zero, whisker_exchange, h2, zero_comp]
  rw [whiskerRight_id] at h3
  simpa using congrArg (fun k => (ρ_ P).inv ≫ k ≫ (ρ_ G).hom) h3

end Stacks.EtaleCohomology

end
