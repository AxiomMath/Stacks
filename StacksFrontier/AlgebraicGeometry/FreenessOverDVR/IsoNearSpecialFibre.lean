module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SectionMultiplicationExtension
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.AdicMultiplication
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.NakayamaPower
public import StacksFrontier.AlgebraicGeometry.Modules.FreeMapIsoLocus
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# A morphism of vector bundles which is an isomorphism modulo `π` over a local base

Let `A` be a local ring, `π` an element of its maximal ideal and `f : X ⟶ Spec A` a universally
closed morphism with `X` locally Noetherian. A morphism `α : F ⟶ E` of finite locally free
modules which becomes an isomorphism modulo `πʲ` for some `j ≥ 1` is an isomorphism.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `supp_eq_empty_of_supp_subset_basicOpen`: a coherent module whose support avoids the zero
  locus of `π` is zero.
* `isIso_of_comp_adicProj`: **the isomorphism criterion.**

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.BaseAdicFiltration Stacks.Algebraization Stacks.ModuleSkyscraper

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {π : A}

/-- **A coherent module supported where `π` is invertible is zero**, for `f` universally closed
over a local ring and `π` in the maximal ideal. -/
theorem supp_eq_empty_of_supp_subset_basicOpen [UniversallyClosed f]
    (hπ : π ∈ IsLocalRing.maximalIdeal A) (G : X.Modules) (hG : G.IsCoherent)
    (hsupp : ∀ x : X, ¬ IsUnit ((X.presheaf.Γgerm x).hom (baseScalarMap f π)) →
      x ∉ SheafOfModules.supp G) :
    SheafOfModules.supp G = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have hclosed := f.isClosedMap _
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent G hG)
  obtain ⟨z, hz, hzc⟩ : IsLocalRing.closedPoint A ∈ f '' SheafOfModules.supp G :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hclosed ⟨x, hx, rfl⟩
  have hunit : IsUnit ((X.presheaf.Γgerm z).hom (baseScalarMap f π)) :=
    not_not.1 fun h => hsupp z h hz
  have hz' : z ∈ X.basicOpen (baseScalarMap f π) := (X.mem_basicOpen_top _ z).2 hunit
  have hpre : X.basicOpen (baseScalarMap f π) =
      f ⁻¹ᵁ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv π) := by
    rw [Scheme.preimage_basicOpen_top]
    rfl
  rw [hpre] at hz'
  change f z ∈ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv π) at hz'
  rw [basicOpen_eq_of_affine, hzc] at hz'
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hz' hπ

/-- **The isomorphism criterion.** Let `f : X ⟶ Spec A` be universally closed over a local ring,
with `X` locally Noetherian, and `π` in the maximal ideal of `A`. A morphism `α : F ⟶ E` of
finite locally free modules for which there is an isomorphism `ψ : F / πʲ F ≅ E / πʲ E`, `j ≥ 1`,
compatible with `α` and the two quotient projections, is an isomorphism. -/
theorem isIso_of_comp_adicProj [UniversallyClosed f] [IsLocallyNoetherian X]
    (hπ : π ∈ IsLocalRing.maximalIdeal A) {F E : X.Modules} (hF : F.IsFiniteLocallyFree)
    (hE : E.IsFiniteLocallyFree) (α : F ⟶ E) {j : ℕ} (hj : 1 ≤ j)
    (ψ : adicQuotient f (Ideal.span {π}) j F ≅ adicQuotient f (Ideal.span {π}) j E)
    (hα : α ≫ adicProj f (Ideal.span {π}) j E = adicProj f (Ideal.span {π}) j F ≫ ψ.hom) :
    IsIso α := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators F).mp hF
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).mp hE
  have hFc : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree _ F
  have hEc : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree _ E
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  have hstalk : ∀ x : X, ¬ IsUnit ((X.presheaf.Γgerm x).hom (baseScalarMap f π)) →
      Function.Bijective ((modulesStalkFunctor X x).map α).hom := by
    intro x hx
    have : Module.Finite (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj F) :=
      (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree F x).2
    have : Module.Free (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj E) :=
      (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree E x).1
    have : Module.Finite (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj E) :=
      (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree E x).2
    have hψ : Function.Bijective ((modulesStalkFunctor X x).map ψ.hom).hom :=
      (ConcreteCategory.isIso_iff_bijective _).1 (inferInstance : IsIso
        ((modulesStalkFunctor X x).map ψ.hom))
    have hcomm : ∀ m, ((modulesStalkFunctor X x).map (adicProj f (Ideal.span {π}) j E)).hom
        (((modulesStalkFunctor X x).map α).hom m) =
        ((modulesStalkFunctor X x).map ψ.hom).hom
          (((modulesStalkFunctor X x).map (adicProj f (Ideal.span {π}) j F)).hom m) := fun m => by
      simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using
        congrArg (fun φ => ((modulesStalkFunctor X x).map φ).hom m) hα
    exact bijective_of_bijective_reduction (IsLocalRing.mem_maximalIdeal _ |>.2 hx) hj _ _ _
      (surjective_stalk_adicProj f F x (Ideal.span {π}) j)
      (mem_ker_stalk_adicProj_iff f π F x j) (mem_ker_stalk_adicProj_iff f π E x j) _ hψ hcomm
  have hK := supp_eq_empty_of_supp_subset_basicOpen f hπ (kernel α)
    (isCoherent_kernel_of_isCoherent hFc hEc α) fun x hx =>
      notMem_supp_kernel_of_injective_mapFun α x (hstalk x hx).1
  have hC := supp_eq_empty_of_supp_subset_basicOpen f hπ (cokernel α)
    (isCoherent_cokernel_of_isCoherent hFc hEc α) fun x hx =>
      notMem_supp_cokernel_of_surjective_mapFun α x (hstalk x hx).2
  have hmono : Mono α := (Preadditive.mono_iff_isZero_kernel α).2
    ((Scheme.Modules.isZero_iff_supp_eq_empty _).2 hK)
  have hepi : Epi α := (Preadditive.epi_iff_isZero_cokernel α).2
    ((Scheme.Modules.isZero_iff_supp_eq_empty _).2 hC)
  exact isIso_of_mono_of_epi α

end Stacks.AlgebraicGeometry.FreenessOverDVR
