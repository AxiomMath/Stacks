module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.SheafTensorColimits
import StacksCore.Tactic.StacksAttribute

/-!
# `D_QCoh` of an algebraic space is closed under the derived tensor product

Let `X` be an algebraic space over a scheme `S`. For `K, L` in `D_QCoh(𝒪_X)` the derived tensor
product `K ⊗^L_{𝒪_X} L` lies in `D_QCoh(𝒪_X)` (Stacks 08F5).

Membership in `D_QCoh` is checked on the affine étale charts (Stacks 08F2), and derived pullback
along a chart commutes with the derived tensor product (Stacks 07A4) and preserves `D_QCoh`
(Stacks 08F4); so one reduces to an affine represented algebraic space `U` with ring `R`. There
`D_QCoh(𝒪_U)` is the essential image of `D(R)` under the derived associated module `Φ`, and the
objects `M` of `D(R)` with `K ⊗^L Φ(M)` in `D_QCoh` are closed under direct sums (both functors
commute with them) and under triangles, and contain the shifts of `R`, where
`K ⊗^L 𝒪[k] ≅ K[k]`; so they are all of `D(R)` (Stacks 09PB).

## Main results

* `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedTensor`: **Stacks 08F5**.

## Implementation notes

The partial forms of Stacks 08F5 in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedTensor.lean` (two quasi-coherent
modules in degree zero, for an arbitrary derived tensor product) are covered by the statement
here; they are kept in their own module because the imports needed here change instance
resolution in that file's generic sections.

## References

* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- On an affine represented algebraic space, `K ⊗^L Φ(M)` has quasi-coherent cohomology for
every `K` in `D_QCoh` and every `M` in `D(R)`, `Φ` the derived associated module. The property
of `M` is closed under direct sums and triangles and holds on the shifts of `R`, where
`K ⊗^L 𝒪[k] ≅ K[k]`; so it holds everywhere (Stacks 09PB). -/
private theorem qcohDerived_smallEtaleDerivedTensor_representedAffineDerivedAssociated
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (K : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
        K).obj ((representedAffineDerivedAssociated B S hS U).obj M)) := by
  set X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  set T := smallEtaleDerivedTensorProduct B S hS X
  set Φ := representedAffineDerivedAssociated B S hS U
  set G : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤ _ :=
    Φ ⋙ T.tensor.obj K
  have : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) G := fun I =>
    have := (representedAffineDerivedAdjunction B S hS U).leftAdjoint_preservesColimits
    inferInstance
  refine (CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts.{u, u}
    (R := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))).2
    (fun M => QcohDerived B S hS X (G.obj M)) ?_ ?_ ?_ M
  · intro I Kf _ hKf
    have := isClosedUnderCoproducts_quasicoherentDerivedCategory B S hS X.1 X.2 I
      (fun Mf hMf => isQuasicoherentOnSite_sigma_of_h03DX B S hS X.1 X.2
        (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2) Mf hMf)
    exact (QcohDerived B S hS X).prop_of_isColimit
      (isColimitOfPreserves G (colimit.isColimit (Discrete.functor Kf))) (fun j => hKf j.as)
  · intro Δ hΔ
    have hGΔ := G.map_distinguished Δ hΔ
    exact ⟨fun h₁ h₂ => (QcohDerived B S hS X).ext_of_isTriangulatedClosed₃ _ hGΔ h₁ h₂,
      fun h₁ h₃ => (QcohDerived B S hS X).ext_of_isTriangulatedClosed₂ _ hGΔ h₁ h₃,
      fun h₂ h₃ => (QcohDerived B S hS X).ext_of_isTriangulatedClosed₁ _ hGΔ h₂ h₃⟩
  · intro k
    let eR : ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        (Shrink.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≅
        ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
      (Shrink.linearEquiv Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).toModuleIso
    have e : G.obj (((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          (Shrink.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))⟦k⟧) ≅ K⟦k⟧ :=
      G.mapIso ((shiftFunctor _ k).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eR)) ≪≫
        (G.commShiftIso k).app _ ≪≫
        (shiftFunctor _ k).mapIso ((T.tensor.obj K).mapIso
          (representedAffineDerivedAssociatedSingleUnitIso B S hS U 0) ≪≫ T.unitIso K)
    exact (QcohDerived B S hS X).prop_of_iso e.symm ((QcohDerived B S hS X).le_shift k K hK)

/-- Stacks 08F5 on an affine represented algebraic space: every object of `D_QCoh` is the derived
associated module of an object of `D(R)`. -/
private theorem qcohDerived_smallEtaleDerivedTensor_represented
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (K L : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (hL : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ L) :
    QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      (((smallEtaleDerivedTensor B S hS
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)).obj
        K).obj L) := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := representedAffineDerivedAssociatedQcoh B S hS U)
    (⟨L, hL⟩ : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
  have e' : (representedAffineDerivedAssociated B S hS U).obj M ≅ L :=
    (ObjectProperty.ι _).mapIso e
  exact (QcohDerived B S hS _).prop_of_iso
    (((smallEtaleDerivedTensor B S hS
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)).obj K).mapIso e')
    (qcohDerived_smallEtaleDerivedTensor_representedAffineDerivedAssociated U K hK M)

/-- **Stacks 08F5.** Let `X` be an algebraic space over a scheme `S`. For objects `K`, `L` of
`D_QCoh(𝒪_X)` the derived tensor product `K ⊗^L_{𝒪_X} L` is in `D_QCoh(𝒪_X)`. -/
@[stacks 08F5]
theorem qcohDerived_smallEtaleDerivedTensor (X : AlgebraicSpaces B S hS)
    (K L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : QcohDerived B S hS X K) (hL : QcohDerived B S hS X L) :
    QcohDerived B S hS X (((smallEtaleDerivedTensor B S hS X).obj K).obj L) := by
  suffices h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      DerivedQuasicoherentPullback B S hS (chartToSpace B S hS X A)
        (isEtale_chartToSpace B S hS X A) (((smallEtaleDerivedTensor B S hS X).obj K).obj L) from
    fun n => isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun A hA =>
      (derivedQuasicoherentPullback_iff B S hS _ _ _).1 (h A hA) n
  intro A hA
  set φ := chartToSpace B S hS X A
  have e := (smallEtaleDerivedModulePullbackIsoEtale B S hS φ
      (isEtale_chartToSpace B S hS X A)).symm.app
      (((smallEtaleDerivedTensor B S hS X).obj K).obj L) ≪≫
    (smallEtaleDerivedPullbackTensorIso φ).app (K, L)
  exact (QcohDerived B S hS (chartSpace B S hS X A)).prop_of_iso e.symm
    (qcohDerived_smallEtaleDerivedTensor_represented ((SmallEtale.toOver B S hS X.1).obj A) _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ φ K hK)
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ φ L hL))

end AlgebraicGeometry.Space

end
