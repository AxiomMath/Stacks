/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.C1746Private.EulerCharacteristicOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# The open immersion of Stacks 0DP3 on `Quot^P`

Let `j : X ⟶ Y` be an open immersion of algebraic spaces separated and of finite presentation
over `B`, `G` a quasi-coherent `𝒪_Y`-module, `F = j^*G`, and `M` an invertible `𝒪_Y`-module. The
open immersion `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` of Stacks 0DP3 sends a quotient `F_T ⟶ 𝒬` to
`G_T ⟶ j_{T,*}𝒬`, and

`χ(Y_t, (j_{T,*}𝒬)_t ⊗ M_t^{⊗ n}) = χ(X_t, 𝒬_t ⊗ (j^*M)_t^{⊗ n})`:

the restriction of `j_{T,*}𝒬` to `X_T` is `𝒬`, the restriction to `X_t` of its fibre is the fibre
of `𝒬`, and the support of the fibre lies in `X_t`, so
`AlgebraicGeometry.Space.eulerCharacteristicAlong_tensor_modulePullback_of_isOpenImmersion`
applies. Hence `Quot^{P, j^*M}_{F/X/B}` is the inverse image of `Quot^{P, M}_{G/Y/B}`: this is
the step "clearly this open immersion sends `Quot^P_{F/X/B}` into `Quot^P_{G/X'/B}`" of the
proof of Stacks 0DPD, in its sharp form.

## Main results

* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.twistedEuler_extendQuotient`.
* `AlgebraicGeometry.Space.QuotOpenSubspaceSituation.hasHilbertPolynomial_extendQuotient_iff`.

## References

* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotOpenSubspaceSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotOpenSubspaceSituation B S hS)

/-- **The twisted Euler characteristics of a direct image quotient along the open immersion of
Stacks 0DP3.** For an invertible `𝒪_Y`-module `M` and a quotient `F_T ⟶ 𝒬` in `Quot_{F/X/B}(T)`,
the object of `Coh_{Y/B}` given by `G_T ⟶ j_{T,*}𝒬` has, at every point `t` of `T`, the twisted
Euler characteristics with respect to `M` of the object `(T, 𝒬)` of `Coh_{X/B}` with respect to
`j^*M`. -/
theorem twistedEuler_extendQuotient (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
    (T : SchemesOver D.base) (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T)
    (t : (D.sourceSituation.cohObject T K hK).testScheme) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS D.targetSituation.toCoherentSituation M hM
        (D.targetSituation.cohObject T (D.extendQuotient T K) (D.extendQuotient_mem T hK)) t n =
      @CoherentObject.twistedEuler B S hS D.sourceSituation.toCoherentSituation
        ((modulePullback B S hS D.j).obj M) (isInvertible_modulePullback B S hS D.j M)
        (D.sourceSituation.cohObject T K hK) t n := by
  let AX := D.sourceSituation.cohObject T K hK
  let Tt := AX.pointTest t
  let h := AX.pointTestHom t
  let jt := D.baseChangeOfMap Tt
  have hjt : IsOpenImmersion B S hS jt.hom := D.isOpenImmersion_baseChangeOfMap
  let L := D.extendQuotient T K
  have hL := D.extendQuotient_mem T hK
  let QY := D.targetSituation.quotientModule T L
  have hQYqc : QY.IsQuasicoherentOnSite := hL.1.1.1
  have hQYft : SheafOfModules.IsFiniteTypeOnSite QY :=
    @SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ hL.1.2
  -- the fibre `N` of the direct image quotient on `Y_t`
  let N := (modulePullback B S hS (D.targetSituation.relativeMap h)).obj QY
  have hNqc : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ QY hQYqc
  have hNft : SheafOfModules.IsFiniteTypeOnSite N :=
    isFiniteTypeOnSite_modulePullback B S hS _ QY hQYft
  have hsupp : supportOfSheaf B S hS (D.targetSituation.space Tt).1
      ((SheafOfModules.toSheaf _).obj N) ⊆
      Set.range (pointsMap B S hS (D.sourceSituation.space Tt).1 jt.hom) := by
    refine (supportOfSheaf_modulePullback_eq B S hS (D.targetSituation.relativeMap h) QY hQYqc
      hQYft).le.trans ?_
    refine (Set.preimage_mono (D.support_extendQuotient_subset T hK)).trans ?_
    exact (D.range_pointsMap_baseChangeOfMap h).symm.le
  -- the twist `M_t^{⊗ n}` on `Y_t` and its pullback to `X_t`
  let Lt := (modulePullback B S hS (baseChangeProjection D.structureY Tt)).obj
    (invertibleTensorPower B S hS D.Y.1 D.Y.2 M n)
  have hinv := isInvertible_modulePullback B S hS (baseChangeProjection D.structureY Tt)
    (invertibleTensorPower B S hS D.Y.1 D.Y.2 M n)
  have hLtqc : Lt.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isInvertible _ _
      (isInvertible_invertibleTensorPower B S hS D.Y.1 D.Y.2 M n)
  have hk : jt ≫ baseChangeProjection D.structureY Tt =
      baseChangeProjection D.structureX Tt ≫ D.j := D.baseChangeOfMap_comp_projection Tt
  let e4 : (modulePullback B S hS jt).obj Lt ≅
      (modulePullback B S hS (baseChangeProjection D.structureX Tt)).obj
        (@invertibleTensorPower B S hS D.X.1 D.X.2 ((modulePullback B S hS D.j).obj M)
          (isInvertible_modulePullback B S hS D.j M) n) :=
    (modulePullbackTriangle B S hS hk).symm.app _ ≪≫
      (modulePullbackTriangle B S hS
        (rfl : baseChangeProjection D.structureX Tt ≫ D.j = _)).app _ ≪≫
      (modulePullback B S hS (baseChangeProjection D.structureX Tt)).mapIso
        (modulePullbackInvertibleTensorPowerIso B S hS D.j M n)
  -- the restriction to `X_t` of the fibre of the direct image is the fibre of `𝒬`
  let e1 : (modulePullback B S hS jt).obj N ≅ AX.fibreModule t :=
    ((modulePullbackSquare B S hS (D.relativeMap_comp_baseChangeOfMap h) rfl).app QY).symm ≪≫
      (modulePullback B S hS (D.sourceSituation.relativeMap h)).mapIso
        ((D.restrictQuotientCokernelIso T L).symm ≪≫
          eqToIso (congrArg (D.sourceSituation.quotientModule T)
            (D.restrictQuotient_extendQuotient T K (D.isClosed_image_support_of_mem T hK))))
  have hφ : jt.hom ≫ (D.targetSituation.projection Tt).hom =
      (D.sourceSituation.projection Tt).hom :=
    congrArg (fun k => k.hom) (D.baseChangeOfMap_comp_inclusion Tt)
  have key := eulerCharacteristicAlong_tensor_modulePullback_of_isOpenImmersion B S hS jt hjt
    (D.targetSituation.projection Tt).hom (AX.testScheme.residueField t)
    (Scheme.ΓSpecIso (.of (AX.testScheme.residueField t))).inv.hom N hNqc hNft hsupp Lt hLtqc
    _ hφ
  exact key.trans <| eulerCharacteristicAlong_congr _ _ _ _ _ _ _
    ((((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e1).app _) ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj (AX.fibreModule t)).mapIso e4)

/-- **The open immersion of Stacks 0DP3 carries `Quot^{P, j^*M}` onto the quotients of
`Quot^{P, M}` it reaches**: a quotient of `F_T` has Hilbert polynomial `P` with respect to `j^*M`
exactly when its direct image has Hilbert polynomial `P` with respect to `M`. -/
theorem hasHilbertPolynomial_extendQuotient_iff
    (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
    (P : ℤ → ℤ) (T : SchemesOver D.base) (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    @CoherentObject.HasHilbertPolynomial B S hS D.targetSituation.toCoherentSituation M hM P
        (D.targetSituation.cohObject T (D.extendQuotient T K) (D.extendQuotient_mem T hK)) ↔
      @CoherentObject.HasHilbertPolynomial B S hS D.sourceSituation.toCoherentSituation
        ((modulePullback B S hS D.j).obj M) (isInvertible_modulePullback B S hS D.j M) P
        (D.sourceSituation.cohObject T K hK) :=
  forall_congr' fun t => forall_congr' fun n => by
    rw [D.twistedEuler_extendQuotient M T K hK t n]

end AlgebraicGeometry.Space.QuotOpenSubspaceSituation

end
