module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ConstructibleLocallyFreeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass

/-!
# Kernels and cokernels of constructible sheaves, small coefficient rings

Let `S` be a Noetherian scheme and `Λ` a finite commutative ring (in `Type`). The kernel and the
cokernel of a morphism `f : A ⟶ A'` of constructible sheaves of `Λ`-modules on `S_étale` are
constructible. By Noetherian induction over the reduced closed subschemes `T` of `S` it suffices
that their restrictions be constructible on a nonempty open of `T`; on a common open of the
generic points of `T` where `A` and `A'` are locally constant of finite type, the restrictions
are the kernel and the cokernel of a morphism of locally constant sheaves of finite type, which
are locally constant of finite type.

The statements in the library for subsheaves and quotients
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_mono`) ask for `Λ : Type (u + 1)`; the
form here, for the coefficient rings `Λ : Type` of the Fourier transform, is used for the
images of morphisms between the Fourier transforms in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_opens_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_kernel_of_isConstructible`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_cokernel_of_isConstructible`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ] [Finite Λ]

/-- Local constancy of finite type passes to an open contained in the image of an open
immersion along which it holds. -/
theorem isFiniteTypeLocallyConstant_inverseImage_opensι_of_subset {T W : Scheme.{u}}
    (a : W ⟶ T) [IsOpenImmersion a] {F : EtaleModules.{u, 0} Λ T}
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ W.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ a).obj F))
    (U : T.Opens) (hU : Set.range U.ι.base ⊆ Set.range a.base) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj F) :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    ((etaleModuleInverseImageCompObjIso Λ (IsOpenImmersion.lift a U.ι hU) a F).symm ≪≫
      eqToIso (congrArg (fun m => (etaleModuleInverseImage.{u, 0} Λ m).obj F)
        (IsOpenImmersion.lift_fac a U.ι hU)))
    (isLocallyConstantWith_inverseImage Λ (ModuleCat.isFG Λ) (IsOpenImmersion.lift a U.ι hU) hF)

/-- **Two constructible sheaves on a nonempty reduced Noetherian scheme are locally constant of
finite type on a common nonempty open**: a neighbourhood of a generic point. -/
theorem exists_opens_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule {T : Scheme.{u}}
    [IsNoetherian T] [IsReduced T] [Nonempty T] {A A' : EtaleModules.{u, 0} Λ T}
    (hA : IsConstructibleEtaleModule Λ A) (hA' : IsConstructibleEtaleModule Λ A') :
    ∃ U : T.Opens, (U : Set T).Nonempty ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
        ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj A) ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
        ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj A') := by
  have : IsNoetherianRing Λ := inferInstance
  let B := BigEtaleSite.containing T
  have hTB : B.Contains T := BigEtaleSite.contains_containing T
  have : IsReduced (B.obj T hTB).obj := ‹IsReduced T›
  obtain ⟨η, hη⟩ : (genericPoints T).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    have h' := genericPoints.closure (α := T)
    rw [he, closure_empty] at h'
    exact Set.empty_ne_univ h'
  have key : ∀ {A : EtaleModules.{u, 0} Λ T}, IsConstructibleEtaleModule Λ A →
      ∃ V : T.Opens, η ∈ V ∧ ∀ U : T.Opens, U ≤ V →
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
          ((etaleModuleInverseImage.{u, 0} Λ U.ι).obj A) := fun {A} hA => by
    obtain ⟨O, o, ho, hz, hFO⟩ :=
      exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule B
        (B.obj T hTB) _ ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hTB _).1
          hA) hη
    have : IsOpenImmersion (B.inclusion.map o) := ho
    exact ⟨(B.inclusion.map o).opensRange, hz, fun U hU =>
      isFiniteTypeLocallyConstant_inverseImage_opensι_of_subset Λ _ hFO U
        (by rwa [Scheme.Opens.range_ι])⟩
  obtain ⟨V, hV, hFV⟩ := key hA
  obtain ⟨V', hV', hFV'⟩ := key hA'
  exact ⟨V ⊓ V', ⟨η, hV, hV'⟩, hFV _ inf_le_left, hFV' _ inf_le_right⟩

/-- The two constructible sheaves of a morphism, restricted to a common open of local constancy
of a reduced closed subscheme: the restriction along `U.ι ≫ i` of `A` and of `A'` is locally
constant of finite type. -/
theorem exists_opens_isFiniteTypeLocallyConstant_comp_of_isConstructibleEtaleModule
    {S T : Scheme.{u}} [IsNoetherian S] (i : T ⟶ S) [IsClosedImmersion i] [IsReduced T]
    [Nonempty T] {A A' : EtaleModules.{u, 0} Λ S}
    (hA : IsConstructibleEtaleModule Λ A) (hA' : IsConstructibleEtaleModule Λ A') :
    ∃ U : T.Opens, (U : Set T).Nonempty ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
        ((etaleModuleInverseImage.{u, 0} Λ (U.ι ≫ i)).obj A) ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.toScheme.smallEtaleTopology
        ((etaleModuleInverseImage.{u, 0} Λ (U.ι ≫ i)).obj A') := by
  have : IsNoetherian T := isNoetherian_of_isClosedImmersion i
  obtain ⟨U, hU, h₁, h₂⟩ :=
    exists_opens_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule Λ
      (isConstructibleEtaleModule_etaleModuleInverseImage Λ i A hA)
      (isConstructibleEtaleModule_etaleModuleInverseImage Λ i A' hA')
  exact ⟨U, hU,
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (etaleModuleInverseImageCompObjIso Λ U.ι i A).symm h₁,
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (etaleModuleInverseImageCompObjIso Λ U.ι i A').symm h₂⟩

/-- **The kernel of a morphism of constructible sheaves is constructible**, on a Noetherian
scheme, for a finite coefficient ring `Λ : Type`. -/
theorem isConstructibleEtaleModule_kernel_of_isConstructible {S : Scheme.{u}} [IsNoetherian S]
    {A A' : EtaleModules.{u, 0} Λ S} (f : A ⟶ A') (hA : IsConstructibleEtaleModule Λ A)
    (hA' : IsConstructibleEtaleModule Λ A') : IsConstructibleEtaleModule Λ (kernel f) := by
  have : IsNoetherianRing Λ := inferInstance
  refine isConstructibleEtaleModule_of_forall_exists_opens_of_isReduced Λ _ fun T i _ _ hT => ?_
  have := hT
  obtain ⟨U, hU, h₁, h₂⟩ :=
    exists_opens_isFiniteTypeLocallyConstant_comp_of_isConstructibleEtaleModule Λ i hA hA'
  refine ⟨U, hU, ?_⟩
  let L := etaleModuleInverseImage.{u, 0} Λ (U.ι ≫ i)
  exact (IsConstructibleEtaleModule Λ).prop_of_iso (PreservesKernel.iso L f).symm
    (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant Λ
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0} _ Λ
        (L.map f) h₁ h₂))

/-- **The cokernel of a morphism of constructible sheaves is constructible**, on a Noetherian
scheme, for a finite coefficient ring `Λ : Type`. -/
theorem isConstructibleEtaleModule_cokernel_of_isConstructible {S : Scheme.{u}} [IsNoetherian S]
    {A A' : EtaleModules.{u, 0} Λ S} (f : A ⟶ A') (hA : IsConstructibleEtaleModule Λ A)
    (hA' : IsConstructibleEtaleModule Λ A') : IsConstructibleEtaleModule Λ (cokernel f) := by
  have : IsNoetherianRing Λ := inferInstance
  refine isConstructibleEtaleModule_of_forall_exists_opens_of_isReduced Λ _ fun T i _ _ hT => ?_
  have := hT
  obtain ⟨U, hU, h₁, h₂⟩ :=
    exists_opens_isFiniteTypeLocallyConstant_comp_of_isConstructibleEtaleModule Λ i hA hA'
  refine ⟨U, hU, ?_⟩
  let L := etaleModuleInverseImage.{u, 0} Λ (U.ι ≫ i)
  exact (IsConstructibleEtaleModule Λ).prop_of_iso (PreservesCokernel.iso L f).symm
    (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant Λ
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_cokernel.{u, u + 1, 0, 0} _ Λ
        (L.map f) h₁ h₂))

end Stacks.EtaleCohomology

end
