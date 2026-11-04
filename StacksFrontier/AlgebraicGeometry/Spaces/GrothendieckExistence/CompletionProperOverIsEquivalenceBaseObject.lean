module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.GrothendieckExistenceSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionBijectiveOnHomsBaseObject

/-!
# Grothendieck's existence theorem over the site base `Spec A`

`AlgebraicGeometry.Space.CompletionProperOverIsEquivalence` (Stacks 08BE in the form of
`StacksFrontier/AlgebraicGeometry/Spaces/GrothendieckExistence/Statements.lean`) holds over the base
object `Spec A` of the big fppf site over `Spec A`, for every Noetherian ring `A`, every ideal `J`
of `Γ(Spec A, 𝒪)` and every algebraic space over `Spec A`.

The proof is the equivalence
`AlgebraicGeometry.Space.C1573.isEquivalence_completionFunctorProperOver`, which is stated for an
ideal `I ⊆ A` and the sheaf of ideals `AlgebraicGeometry.Space.C1573.baseIdealSubmodule`; here
`I` is the pullback of `J` along `A ≃ Γ(Spec A, 𝒪)`, and the two sheaves of ideals `I 𝒪_X` agree
(`AlgebraicGeometry.Space.C1573.idealKernel_comp_ringEquiv`).

## Main results

* `AlgebraicGeometry.Space.C1573.completionProperOverIsEquivalence_baseObject`: the proposition
  `CompletionProperOverIsEquivalence (baseObject A B hA) J f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] pointTopology

section Completion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- Completion functors on modules with support proper over `Y`, along equal sheaves of ideals,
are equivalences together. -/
theorem isEquivalence_completionFunctorProperOver_congr
    [Fact (HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))]
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    {𝓘 𝓙 : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule} (h : 𝓘 = 𝓙)
    (h𝓘 : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (h𝓙 : 𝓙.toSheafOfModules.IsQuasicoherentOnSite) :
    (completionFunctorProperOver B S hS X.1 Y.1 X.2 Y.2 f.hom hf 𝓘 h𝓘).IsEquivalence ↔
      (completionFunctorProperOver B S hS X.1 Y.1 X.2 Y.2 f.hom hf 𝓙 h𝓙).IsEquivalence := by
  subst h
  rfl

end Completion

section BaseObject

variable {B : BigFppfSite.{u}}

/-- **Stacks 08BE in the form `AlgebraicGeometry.Space.CompletionProperOverIsEquivalence`, over
the base object of the big fppf site over `Spec A`.**  For a Noetherian ring `A`, an ideal `J` of
`Γ(Spec A, 𝒪)` and a morphism `f : X ⟶ Spec A` of algebraic spaces, if `A` is `J`-adically
complete and `f` is separated of finite type, then completion along `J 𝒪_X` is an equivalence
`Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, J 𝒪_X)`. -/
theorem completionProperOverIsEquivalence_baseObject (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hA : B.Contains (Spec (.of A)))
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA))]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA))]
    (J : Ideal Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA), ⊤))
    {X : AlgebraicSpaces B (Spec (.of A)) hA} (f : X ⟶ schemeSpace (baseObject A B hA)) :
    CompletionProperOverIsEquivalence (baseObject A B hA) J f := by
  intro hJ hsep hft
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
  exact (isEquivalence_completionFunctorProperOver_congr f hft.1 hid _ _).1
    (isEquivalence_completionFunctorProperOver (J.comap e.toRingHom) X f hft hsep)

end BaseObject

end AlgebraicGeometry.Space.C1573

end
