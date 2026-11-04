module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformFiniteStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.AffineLineNagata
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant

/-!
# The tensor product of a constructible sheaf and a locally free sheaf is constructible

Let `Λ` be a Noetherian commutative ring, `S` a Noetherian scheme, `A` a constructible sheaf of
`Λ`-modules on `S_étale` and `N` an étale-locally free sheaf of finite rank. Then `A ⊗ N` is
constructible. By Noetherian induction over the reduced closed subschemes `T` of `S`
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_exists_opens_of_isReduced`) it is
enough to find a nonempty open `U ⊆ T` on which `(A ⊗ N)|_U` is constructible: `A|_T` is
constructible ([Stacks, Tag 095G]), hence locally constant of finite type near a generic point of
`T`, and there `(A ⊗ N)|_U = A|_U ⊗ N|_U` is locally constant of finite type, since the tensor
product of two constant sheaves is the constant sheaf on the tensor product of the values
(`Stacks.EtaleCohomology.isLocallyConstantWith_tensor`).

This is the special case of [Stacks, Tag 095I] needed for the integrand `pr₁⁻¹ A ⊗ μ⁻¹ L_ψ` of the
Fourier transform; it holds for coefficients `Λ : Type` with the tensor product of
`Stacks.EtaleCohomology.EtaleModules`, where the library's statement of Tag 095I
(`Stacks.EtaleCohomology.isConstructibleModuleSheaf_tensor`, on the site of Tag 021B with
coefficients in the universe of the site) does not apply. It is used in Laumon's argument for
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_forall_exists_opens_of_isReduced`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_tensor_of_isLocallyFreeEtaleModule`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

section Induction

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- If `f` is a closed embedding with image `C` and `U` is a nonempty open of the source, then
the image of the complement of `U` is a closed subset strictly smaller than `C`. -/
theorem closeds_image_compl_lt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) {C : TopologicalSpace.Closeds Y}
    (hC : Set.range f = C) {U : TopologicalSpace.Opens X} (hU : (U : Set X).Nonempty) :
    (⟨f '' (U : Set X)ᶜ, hf.isClosedMap _ U.isOpen.isClosed_compl⟩ :
      TopologicalSpace.Closeds Y) < C := by
  have hmem : ∀ y, f y ∈ (C : Set Y) := fun y ↦ hC ▸ Set.mem_range_self y
  refine lt_of_le_of_ne (fun x hx ↦ ?_) fun he ↦ ?_
  · obtain ⟨y, -, rfl⟩ := hx
    exact hmem y
  · obtain ⟨y, hy⟩ := hU
    have h := hmem y
    rw [← he] at h
    obtain ⟨y', hy', hyy'⟩ := h
    exact hy' (hf.injective hyy' ▸ hy)

/-- **Noetherian induction for constructibility over reduced closed subschemes.** Let `S` be a
Noetherian scheme and `ℱ` a sheaf of `Λ`-modules on `S_étale`. If for every closed immersion
`i : T ⟶ S` with `T` nonempty and reduced there is a nonempty open `U ⊆ T` on which `i⁻¹ ℱ` is
constructible, then `ℱ` is constructible: the closed complement of `U` carries its reduced
subscheme structure, and `S` is covered by the closed immersion of `S_red`. -/
theorem isConstructibleEtaleModule_of_forall_exists_opens_of_isReduced {S : Scheme.{u}}
    [IsNoetherian S] (F : EtaleModules.{u, r} Λ S)
    (h : ∀ (T : Scheme.{u}) (i : T ⟶ S) [IsClosedImmersion i] [IsReduced T], Nonempty T →
      ∃ U : T.Opens, (U : Set T).Nonempty ∧
        IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ (U.ι ≫ i)).obj F)) :
    IsConstructibleEtaleModule Λ F := by
  suffices H : ∀ C : TopologicalSpace.Closeds S, ∀ (T : Scheme.{u}) (i : T ⟶ S)
      [IsClosedImmersion i] [IsReduced T], Set.range i.base = (C : Set S) →
      IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ i).obj F) by
    have : IsLocallyNoetherian S := IsNoetherian.toIsLocallyNoetherian
    have : QuasiSeparatedSpace S := IsLocallyNoetherian.quasiSeparatedSpace
    let Sr := (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds S)).subscheme
    let ι := (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds S)).subschemeι
    have : IsReduced Sr := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    have hι : Set.range ι.base = Set.univ := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    refine isConstructibleEtaleModule_of_constructible_immersion_cover Λ F (I := PUnit.{1})
      (fun _ ↦ Sr) (fun _ ↦ ι) (fun _ ↦ ?_) ?_ fun _ ↦ H ⊤ Sr ι hι
    · rw [hι]
      exact Topology.IsConstructible.univ
    · rw [Set.iUnion_const, hι]
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
  intro T i _ _ hC
  have : IsNoetherian T := isNoetherian_of_isClosedImmersion i
  have : IsLocallyNoetherian T := IsNoetherian.toIsLocallyNoetherian
  have : QuasiSeparatedSpace T := IsLocallyNoetherian.quasiSeparatedSpace
  rcases isEmpty_or_nonempty T with hT | hT
  · refine isConstructibleEtaleModule_of_constructible_immersion_cover Λ _ (I := PEmpty.{1})
      (fun _ ↦ T) (fun e ↦ e.elim) (fun e ↦ e.elim) ?_ (fun e ↦ e.elim)
    exact Set.eq_univ_of_forall fun x ↦ (hT.false x).elim
  obtain ⟨U, hU, hFU⟩ := h T i hT
  let Zc : TopologicalSpace.Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
  let Z := (Scheme.IdealSheafData.vanishingIdeal Zc).subscheme
  let ι : Z ⟶ T := (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  have : IsReduced Z := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hι : Set.range ι.base = (U : Set T)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  let C' : TopologicalSpace.Closeds S :=
    ⟨i.base '' (U : Set T)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hC' : C' < C := closeds_image_compl_lt i.isClosedEmbedding hC hU
  have hZ := ih C' hC' Z (ι ≫ i) (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hι]
    rfl)
  refine isConstructibleEtaleModule_of_isOpen_isClosed Λ _ U
    (TopologicalSpace.NoetherianSpace.isCompact _) ι hι ?_
    ((isConstructibleEtaleModule_inverseImage_comp_iff Λ ι i F).1 hZ)
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleInverseImageCompObjIso Λ U.ι i F ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, r} Λ U.ι).app _) hFU

end Induction

section Main

variable (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- **The tensor product of a constructible sheaf and an étale-locally free sheaf of finite rank
is constructible**, on a Noetherian scheme (a case of [Stacks, Tag 095I]): by Noetherian induction,
on a reduced closed subscheme `T` the constructible sheaf `A|_T` is locally constant of finite type
on an open neighbourhood `U` of a generic point, and so is `(A ⊗ N)|_U = A|_U ⊗ N|_U`. -/
theorem isConstructibleEtaleModule_tensor_of_isLocallyFreeEtaleModule {S : Scheme.{u}}
    [IsNoetherian S] {A N : EtaleModules.{u, 0} Λ S} (hA : IsConstructibleEtaleModule Λ A)
    (hN : IsLocallyFreeEtaleModule Λ N) : IsConstructibleEtaleModule Λ (A ⊗ N) := by
  refine isConstructibleEtaleModule_of_forall_exists_opens_of_isReduced Λ _ fun T i _ _ hT => ?_
  have : IsNoetherian T := isNoetherian_of_isClosedImmersion i
  let B := BigEtaleSite.containing T
  have hTB : B.Contains T := BigEtaleSite.contains_containing T
  have hc : IsBigSiteConstructibleEtaleModule B (B.obj T hTB) Λ
      ((etaleModuleInverseImage.{u, 0} Λ i).obj A) :=
    (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hTB _).1
      (isConstructibleEtaleModule_etaleModuleInverseImage Λ i A hA)
  have : IsReduced (B.obj T hTB).obj := ‹IsReduced T›
  obtain ⟨η, hη⟩ : (genericPoints T).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    have h' := genericPoints.closure (α := T)
    rw [he, closure_empty] at h'
    exact Set.empty_ne_univ h'
  obtain ⟨O, o, ho, ⟨z, -⟩, hFO⟩ :=
    exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule B
      (B.obj T hTB) _ hc hη
  let o' : O.obj ⟶ T := B.inclusion.map o
  have : IsOpenImmersion o' := ho
  refine ⟨o'.opensRange, ⟨o'.base z, z, rfl⟩, ?_⟩
  have hA' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ O.obj.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ (o' ≫ i)).obj A) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (etaleModuleInverseImageCompObjIso Λ o' i A).symm hFO
  have hM : IsConstructibleEtaleModule Λ
      ((etaleModuleInverseImage.{u, 0} Λ (o' ≫ i)).obj (A ⊗ N)) :=
    (IsConstructibleEtaleModule Λ).prop_of_iso
      (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ (o' ≫ i)) A N)
      (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant Λ fun U' => by
        obtain ⟨I, V, f, hcov, ht⟩ := isLocallyConstantWith_tensor Λ (fun E => ModuleCat.isFG Λ E)
          (fun E => Module.Free Λ E ∧ Module.Finite Λ E) hA'
          (isLocallyFreeEtaleModule_inverseImage Λ (o' ≫ i) hN) U'
        refine ⟨I, V, f, hcov, fun i' => ?_⟩
        obtain ⟨E, ⟨E₁, E₂, hE₁, hE₂, rfl⟩, e⟩ := ht i'
        refine ⟨E₁ ⊗ E₂, (ModuleCat.isFG_iff _).2 ?_, e⟩
        have := (ModuleCat.isFG_iff E₁).1 hE₁
        have := hE₂.2
        exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂)))
  rw [show o'.opensRange.ι ≫ i = o'.isoOpensRange.inv ≫ (o' ≫ i) by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]]
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleInverseImageCompObjIso Λ o'.isoOpensRange.inv (o' ≫ i) (A ⊗ N)).symm
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ _ _ hM)

end Main

end Stacks.EtaleCohomology

end
