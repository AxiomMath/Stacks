module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.Statements
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.IdealKernelImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteAlgebra

/-!
# Completion is bijective on morphisms over the site base `Spec A`

`AlgebraicGeometry.Space.CompletionBijectiveOnHoms` (Stacks 08B9) holds over the base object
`Spec A` of the big fppf site over `Spec A`, for every Noetherian ring `A`, every ideal `J` of
`Γ(Spec A, 𝒪)` and every algebraic space over `Spec A`.

## Main results

* `AlgebraicGeometry.Space.C1573.idealKernel_comp_ringEquiv`: the kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X`
  does not change when the ring of scalars is replaced along a ring isomorphism.
* `AlgebraicGeometry.Space.C1573.completionBijectiveOnHoms_baseObject`: the proposition
  `CompletionBijectiveOnHoms (baseObject A B hA) J f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] pointTopology

section IdealKernel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- If every function `φ₁ a`, `a ∈ J₁`, is a function `φ₂ b` with `b ∈ J₂`, then
`J₁ 𝒪_X ⊆ J₂ 𝒪_X`. -/
theorem idealKernel_le_idealKernel {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (φ₁ : A₁ →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (φ₂ : A₂ →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (J₁ : Ideal A₁) (J₂ : Ideal A₂) (h : ∀ a ∈ J₁, ∃ b ∈ J₂, φ₁ a = φ₂ b) :
    idealKernel φ₁ J₁ ≤ idealKernel φ₂ J₂ := by
  have h0 : idealMultipleι φ₁ (structureSheafModule B S hS X) J₁ ≫
      idealQuotientπ φ₂ (structureSheafModule B S hS X) J₂ = 0 := by
    refine idealMultiple_hom_ext φ₁ _ J₁ fun a ha => ?_
    obtain ⟨b, hb, hab⟩ := h a ha
    rw [comp_zero, ← Category.assoc, idealMultipleFactor_ι, hab,
      ← idealMultipleFactor_ι φ₂ _ J₂ hb, Category.assoc]
    simp only [idealQuotientπ, cokernel.condition, comp_zero]
  let q := cokernel.desc _ (idealQuotientπ φ₂ (structureSheafModule B S hS X) J₂) h0
  have hq : idealQuotientπ φ₁ (structureSheafModule B S hS X) J₁ ≫ q =
      idealQuotientπ φ₂ (structureSheafModule B S hS X) J₂ :=
    cokernel.π_desc _ _ _
  intro U x hx
  have hx' := (SheafOfModules.Submodule.mem_ker _ U _).1 hx
  refine (SheafOfModules.Submodule.mem_ker _ U _).2 ?_
  rw [← hq]
  change (q.val.app U) ((idealQuotientπ φ₁ (structureSheafModule B S hS X) J₁).val.app U x) = 0
  rw [hx', map_zero]

/-- **`J 𝒪_X` along a ring isomorphism.**  Replacing the ring of scalars `A` by `A'` along a
ring isomorphism `e : A' ≃+* A`, the ideal `J ⊆ A` by its preimage and `φ` by `φ ∘ e`, does not
change the sheaf of ideals `J 𝒪_X`. -/
theorem idealKernel_comp_ringEquiv {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))))
    (e : A' ≃+* A) (J : Ideal A) :
    idealKernel (φ.comp e.toRingHom) (J.comap e.toRingHom) = idealKernel φ J :=
  le_antisymm (idealKernel_le_idealKernel _ _ _ _ fun a ha => ⟨e a, ha, rfl⟩)
    (idealKernel_le_idealKernel _ _ _ _ fun b hb =>
      ⟨e.symm b, by change e (e.symm b) ∈ J; rwa [e.apply_symm_apply], by simp⟩)

end IdealKernel

section Completion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- Completion functors along equal sheaves of ideals are bijective on the same morphisms. -/
theorem bijective_completionFunctor_map_congr
    [Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))]
    {𝓘 𝓙 : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule} (h : 𝓘 = 𝓙)
    (h𝓘 : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (h𝓙 : 𝓙.toSheafOfModules.IsQuasicoherentOnSite) (M N : CoherentModules.{u, u} B S hS X.1 X.2) :
    Function.Bijective ((completionFunctor B S hS X.1 X.2 𝓘 h𝓘).map (X := M) (Y := N)) ↔
      Function.Bijective ((completionFunctor B S hS X.1 X.2 𝓙 h𝓙).map (X := M) (Y := N)) := by
  subst h
  rfl

end Completion

section BaseObject

variable {B : BigFppfSite.{u}}

/-- **Stacks 08B9 in the form `AlgebraicGeometry.Space.CompletionBijectiveOnHoms`, over the base
object of the big fppf site over `Spec A`.**  For a Noetherian ring `A`, an ideal `J` of
`Γ(Spec A, 𝒪)` and a morphism `f : X ⟶ Spec A` of algebraic spaces, if `A` is `J`-adically
complete, `f` is separated of finite type, and `M`, `N` are coherent `𝒪_X`-modules with
`Supp M ∩ Supp N` closed and proper over `Spec A`, then completion along `J 𝒪_X` is a bijection
`Hom(M, N) ≃ Hom(M^∧, N^∧)`. -/
theorem completionBijectiveOnHoms_baseObject (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hA : B.Contains (Spec (.of A)))
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA))]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA))]
    (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA), ⊤))
    {X : AlgebraicSpaces B (Spec (.of A)) hA} (f : X ⟶ schemeSpace (baseObject A B hA)) :
    CompletionBijectiveOnHoms (baseObject A B hA) J f := by
  intro hJ _ hft M N hT hP
  let e : A ≃+* Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA), ⊤) :=
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  have : IsAdicComplete (J.comap e.toRingHom) A := by
    refine (IsAdicComplete.congr_ringEquiv (J.comap e.toRingHom) e).1 ?_
    convert hJ using 1
    exact Ideal.map_comap_of_surjective e.toRingHom e.surjective J
  have hφ : baseRingHom A B hA X.1 X.2 =
      (pullbackRingHom B (baseObject A B hA) f).comp e.toRingHom :=
    RingHom.ext fun a => (pullbackToGlobalFunctions_baseObject B A hA f a).symm
  have hid : baseIdealSubmodule X.1 X.2 (J.comap e.toRingHom) =
      idealKernel (pullbackRingHom B (baseObject A B hA) f) J := by
    change Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
      (idealMultipleι (baseRingHom A B hA X.1 X.2) (structureSheafModule B _ hA X)
        (J.comap e.toRingHom)) = _
    rw [imageSubmodule_idealMultipleι_eq_idealKernel, hφ]
    exact idealKernel_comp_ringEquiv _ e J
  have := fact_isLocallyNoetherian_of_baseObject X f hft.1
  exact (bijective_completionFunctor_map_congr hid _ _ M N).1
    (bijective_completionFunctor_map_of_isProperOver X (J.comap e.toRingHom) f hft.1 M N hT hP)

end BaseObject

end AlgebraicGeometry.Space.C1573

end
