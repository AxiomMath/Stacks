/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorClosedImmersionDirectImageIso
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerSchemeTheoreticSupport

/-!
# The direct image along a closed immersion on `Quot^P`

Let `π : X ⟶ Y` be a closed immersion of algebraic spaces separated and of finite presentation
over `B`, `F` a quasi-coherent `𝒪_X`-module and `M` an invertible `𝒪_Y`-module.  The direct image
`Quot_{F/X/B} ≅ Quot_{π_*F/Y/B}` of Stacks 0DP4 sends a quotient `F_T ⟶ 𝒬` to
`(π_*F)_T ⟶ π_{T,*}𝒬`, and

`χ(Y_t, (π_{T,*}𝒬)_t ⊗ M_t^{⊗ n}) = χ(X_t, 𝒬_t ⊗ (π^*M)_t^{⊗ n})`:

the pullback of `π_{T,*}𝒬` to the fibre is `π_{t,*}(𝒬_t)` (Stacks 07U8), the projection formula
moves the twist inside `π_{t,*}`, and the cohomology of a quasi-coherent module along the affine
`π_t` is unchanged (Stacks 0D2U).  So the isomorphism of Stacks 0DP4 restricts to
`Quot^{P, π^*M}_{F/X/B} ≅ Quot^{P, M}_{π_*F/Y/B}`, the step of the proof of Stacks 0DPC which
reduces it to Stacks 0DPB.

## Main definitions

* `QuotPushforwardSituation.directImageQuotSitePresheafIso`: Stacks 0DP4 on the Quot presheaves
  of the site.
* `QuotPushforwardSituation.directImageHilbertPolynomialQuotIso`: its restriction
  `Quot^{P, π^*M}_{F/X/B} ≅ Quot^{P, M}_{π_*F/Y/B}`.

## Main results

* `QuotPushforwardSituation.twistedEuler_directImageQuotient`: the twisted Euler characteristics
  of a direct image quotient.
* `QuotPushforwardSituation.directImageQuotFamily_mem_hilbertPolynomialQuot_iff`: the
  isomorphism of Stacks 0DP4 carries `Quot^{P, π^*M}` onto `Quot^{P, M}`.
* `QuotPushforwardSituation.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_directImage`:
  if `Quot^{P, M}_{π_*F/Y/B}` is an algebraic space proper over `B`, so is
  `Quot^{P, π^*M}_{F/X/B}`.

## References

* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

namespace QuotPushforwardSituation

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotPushforwardSituation B S hS)

/-- **The twisted Euler characteristics of a direct image quotient.**  For a closed immersion
`π`, an invertible `𝒪_Y`-module `M` and a quotient `F_T ⟶ 𝒬` in `Quot_{F/X/B}(T)`, the object
of `Coh_{Y/B}` given by the direct image quotient `(π_*F)_T ⟶ π_{T,*}𝒬` has, at every point `t`
of `T`, the twisted Euler characteristics with respect to `M` of the object `(T, 𝒬)` of
`Coh_{X/B}` with respect to `π^*M`. -/
theorem twistedEuler_directImageQuotient (hπ : IsClosedImmersion B S hS D.π.hom)
    (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
    (T : SchemesOver D.base) (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T)
    (t : (D.sourceSituation.cohObject T K hK).testScheme) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS D.directImageSituation.toCoherentSituation M hM
        (D.directImageSituation.cohObject T (D.directImageQuotient T K)
          (D.directImageQuotient_mem D.pushforwardIsCoherent T K hK)) t n =
      @CoherentObject.twistedEuler B S hS D.sourceSituation.toCoherentSituation
        ((modulePullback B S hS D.π).obj M) (isInvertible_modulePullback B S hS D.π M)
        (D.sourceSituation.cohObject T K hK) t n := by
  let A := D.sourceSituation.cohObject T K hK
  let Tt := A.pointTest t
  let h := A.pointTestHom t
  let πt := D.baseChangeOfMap Tt
  have hπt : IsClosedImmersion B S hS πt.hom := D.isClosedImmersion_baseChangeOfMap hπ Tt
  have haff : IsAffineHom B S hS πt.hom := isAffineHom_of_isClosedImmersion B S hS πt.hom hπt
  have hrep := relativelyRepresentable_of_isAffineHom B S hS πt haff
  have sq := D.isPullback_baseChangeMap_baseChangeOfMap h
  have hQ : (D.sourceSituation.quotientModule T K).IsQuasicoherentOnSite := hK.1.1.1
  have hiso := isIso_moduleBaseChangeMap_app_of_isAffineHom sq (D.isAffineHom_baseChangeOfMap T)
    (D.sourceSituation.quotientModule T K) hQ
  let Lt := (modulePullback B S hS (baseChangeProjection D.structureY Tt)).obj
    (invertibleTensorPower B S hS D.Y.1 D.Y.2 M n)
  let N := (modulePullback B S hS (baseChangeMap D.structureX h)).obj
    (D.sourceSituation.quotientModule T K)
  have hN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hQ
  have hinv := isInvertible_modulePullback B S hS (baseChangeProjection D.structureY Tt)
    (invertibleTensorPower B S hS D.Y.1 D.Y.2 M n)
  have hLqc : ((modulePullback B S hS πt).obj Lt).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isInvertible πt _ hinv
  have hW : (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (baseChangeSpace D.structureX Tt).1
        (baseChangeSpace D.structureX Tt).2).O).obj N).obj
      ((modulePullback B S hS πt).obj Lt)).IsQuasicoherentOnSite :=
    @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite.{u + 1, u, u}
      _ _ (smallEtaleRingedSite B S hS (baseChangeSpace D.structureX Tt).1
        (baseChangeSpace D.structureX Tt).2).J _ _ _
      (smallEtaleRingedSite B S hS (baseChangeSpace D.structureX Tt).1
        (baseChangeSpace D.structureX Tt).2).O N ((modulePullback B S hS πt).obj Lt) hN hLqc
  have hk : πt ≫ baseChangeProjection D.structureY Tt =
      baseChangeProjection D.structureX Tt ≫ D.π := D.baseChangeOfMap_comp_projection Tt
  let e4 : (modulePullback B S hS πt).obj Lt ≅
      (modulePullback B S hS (baseChangeProjection D.structureX Tt)).obj
        (@invertibleTensorPower B S hS D.X.1 D.X.2 ((modulePullback B S hS D.π).obj M)
          (isInvertible_modulePullback B S hS D.π M) n) :=
    (modulePullbackTriangle B S hS hk).symm.app _ ≪≫
      (modulePullbackTriangle B S hS
        (rfl : baseChangeProjection D.structureX Tt ≫ D.π = _)).app _ ≪≫
      (modulePullback B S hS (baseChangeProjection D.structureX Tt)).mapIso
        (modulePullbackInvertibleTensorPowerIso B S hS D.π M n)
  let e1a := (modulePullback B S hS (baseChangeMap D.structureY h)).mapIso
        (D.directImageQuotientCokernelIso T K hQ)
  let e1b := @asIso _ _ _ _ _ hiso
  let e1 : (modulePullback B S hS (baseChangeMap D.structureY h)).obj
        (D.directImageSituation.quotientModule T (D.directImageQuotient T K)) ≅
      (modulePushforward B S hS πt).obj N := e1a ≪≫ e1b
  have hproj : πt.hom ≫ (D.directImageSituation.projection Tt).hom =
      (D.sourceSituation.projection Tt).hom :=
    congrArg (fun k => k.hom) (D.baseChangeOfMap_comp_inclusion Tt)
  have hψ : (globalSectionsRingHom B S hS (baseChangeSpace D.structureX Tt).1
        (baseChangeSpace D.structureX Tt).2
        (πt.hom ≫ (D.directImageSituation.projection Tt).hom)).comp
          (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom = A.fibreFieldHom t :=
    congrArg (fun φ => (globalSectionsRingHom B S hS _ _ φ).comp
      (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom) hproj
  have hc : GlobalSectionRingHomsCompatible B S hS πt hrep
      ((globalSectionsRingHom B S hS (baseChangeSpace D.structureY Tt).1
        (baseChangeSpace D.structureY Tt).2 (D.directImageSituation.projection Tt).hom).comp
          (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom)
      (A.fibreFieldHom t) := by
    rw [← hψ]
    exact globalSectionRingHomsCompatible_globalSectionsRingHom B S hS πt hrep
      (D.directImageSituation.projection Tt).hom
      (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom
  refine (eulerCharacteristicAlong_congr _ _ _ _ _ (A.testScheme.residueField t) _
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS (baseChangeSpace D.structureY Tt).1
          (baseChangeSpace D.structureY Tt).2).O).mapIso e1).app Lt ≪≫
        sheafTensorModulePushforwardIso B S hS πt hπt N Lt)).trans ?_
  refine (eulerCharacteristicAlong_modulePushforward_of_isAffineHom B S hS πt hrep
    (A.testScheme.residueField t) _ _ haff hc _ hW).symm.trans ?_
  exact eulerCharacteristicAlong_congr _ _ _ _ _ (A.testScheme.residueField t) _
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS (baseChangeSpace D.structureX Tt).1
          (baseChangeSpace D.structureX Tt).2).O).obj N).mapIso e4)

/-! ### The isomorphism of Stacks 0DP4 on the Quot presheaves of the site -/

/-- The direct image of a quotient over a scheme of the site: the same morphism to the base and
the direct image quotient of Stacks 0DP1. -/
abbrev directImageQuotFamily {T : BigFppfOver B S hS} (x : QuotFamilyOver D.sourceSituation T) :
    QuotFamilyOver D.directImageSituation T where
  toBase := x.toBase
  subobject := D.directImageQuotient _ x.subobject
  mem := D.directImageQuotient_mem D.pushforwardIsCoherent _ x.subobject x.mem

/-- The direct image of quotients commutes with base change along a morphism `g : T' ⟶ T` of
schemes of the site. -/
theorem directImageQuotFamily_baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D.sourceSituation T) :
    D.directImageQuotFamily (x.baseChange g) = (D.directImageQuotFamily x).baseChange g := by
  have key : D.directImageQuotient _ (D.sourceSituation.quotientPullback
      (QuotFamilyOver.restrict g x.toBase) x.subobject) =
      D.directImageSituation.quotientPullback (QuotFamilyOver.restrict g x.toBase)
        (D.directImageQuotient _ x.subobject) :=
    D.directImageQuotient_quotientPullback _ x.subobject x.mem.1.1.1
  refine QuotFamilyOver.ext rfl ?_
  dsimp only [directImageQuotFamily, QuotFamilyOver.baseChange]
  exact heq_of_eq key

/-- The morphism of Stacks 0DP1 on test schemes sends a quotient to its direct image quotient. -/
theorem directImageQuotFunctorMap_app_val (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    ((D.directImageQuotFunctorMap D.pushforwardIsCoherent).app (Opposite.op T) ⟨K, hK⟩).1 =
      D.directImageQuotient T K :=
  rfl

/-- For a closed immersion `π`, the direct image of quotients over a scheme `T` of the site is a
bijection. -/
theorem directImageQuotFamily_bijective (hπ : IsClosedImmersion B S hS D.π.hom)
    (T : BigFppfOver B S hS) :
    Function.Bijective (D.directImageQuotFamily (T := T)) := by
  have := D.isIso_directImageQuotFunctorMap_of_isClosedImmersion D.pushforwardIsCoherent hπ
  have hb : ∀ T' : SchemesOver D.base, Function.Bijective
      ((D.directImageQuotFunctorMap D.pushforwardIsCoherent).app (Opposite.op T')) :=
    fun T' => (isIso_iff_bijective _).1 (NatIso.isIso_app_of_isIso _ _)
  refine ⟨fun x y hxy => ?_, fun x' => ?_⟩
  · obtain ⟨xb, xK, xm⟩ := x
    obtain ⟨yb, yK, ym⟩ := y
    obtain ⟨rfl, hs⟩ := QuotFamilyOver.mk.inj hxy
    have h := (hb (CostructuredArrow.mk xb)).1 (Subtype.ext
      ((D.directImageQuotFunctorMap_app_val _ xK xm).trans
        ((eq_of_heq hs).trans (D.directImageQuotFunctorMap_app_val _ yK ym).symm)))
    cases congrArg Subtype.val h
    rfl
  · obtain ⟨b, K', hK'⟩ := x'
    obtain ⟨⟨K, hK⟩, e⟩ := (hb (CostructuredArrow.mk b)).2 ⟨K', hK'⟩
    refine ⟨⟨b, K, hK⟩, QuotFamilyOver.ext rfl ?_⟩
    dsimp only [directImageQuotFamily]
    exact heq_of_eq
      ((D.directImageQuotFunctorMap_app_val _ K hK).symm.trans (congrArg Subtype.val e))

/-- **Stacks 0DP4 on the Quot presheaves of the site**: the direct image along a closed
immersion is an isomorphism `Quot_{F/X/B} ≅ Quot_{π_*F/Y/B}` of presheaves on the schemes of the
big fppf site. -/
def directImageQuotSitePresheafIso (hπ : IsClosedImmersion B S hS D.π.hom) :
    D.sourceSituation.quotSitePresheaf ≅ D.directImageSituation.quotSitePresheaf :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Equiv.ofBijective _ (D.directImageQuotFamily_bijective hπ T.unop)))
    fun g => ConcreteCategory.hom_ext _ _ fun x =>
      D.directImageQuotFamily_baseChange g.unop x

/-- The isomorphism `directImageQuotSitePresheafIso` sends a quotient to its direct image
quotient. -/
@[simp]
theorem directImageQuotSitePresheafIso_hom_app (hπ : IsClosedImmersion B S hS D.π.hom)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : D.sourceSituation.quotSitePresheaf.obj T) :
    (D.directImageQuotSitePresheafIso hπ).hom.app T x = D.directImageQuotFamily x :=
  rfl

/-- **The isomorphism of Stacks 0DP4 carries `Quot^{P, π^*M}_{F/X/B}` onto
`Quot^{P, M}_{π_*F/Y/B}`**: a quotient has Hilbert polynomial `P` with respect to `π^*M` exactly
when its direct image has Hilbert polynomial `P` with respect to `M`
(`twistedEuler_directImageQuotient`). -/
theorem directImageQuotFamily_mem_hilbertPolynomialQuot_iff
    (hπ : IsClosedImmersion B S hS D.π.hom) (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
    (P : ℤ → ℤ) {T : (BigFppfOver B S hS)ᵒᵖ} (x : D.sourceSituation.quotSitePresheaf.obj T) :
    D.directImageQuotFamily x ∈
        (D.directImageSituation.hilbertPolynomialQuot M (hL := hM) P).obj T ↔
      x ∈ (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.π).obj M)
        (hL := isInvertible_modulePullback B S hS D.π M) P).obj T :=
  forall_congr' fun t => forall_congr' fun n =>
    Iff.of_eq (congrArg (fun z => P n = z)
      (D.twistedEuler_directImageQuotient hπ M _ x.subobject x.mem t n))

section HilbertPolynomial

variable (hπ : IsClosedImmersion B S hS D.π.hom) (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
  [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
  (P : ℤ → ℤ)

/-- **Stacks 0DP4 on `Quot^P`**: the direct image along a closed immersion `π` is an isomorphism
`Quot^{P, π^*M}_{F/X/B} ≅ Quot^{P, M}_{π_*F/Y/B}`. -/
def directImageHilbertPolynomialQuotIso :
    (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.π).obj M)
        (hL := isInvertible_modulePullback B S hS D.π M) P).toFunctor ≅
      (D.directImageSituation.hilbertPolynomialQuot M (hL := hM) P).toFunctor :=
  NatIso.ofComponents
    (fun T => Equiv.toIso ((Equiv.ofBijective _
      (D.directImageQuotFamily_bijective hπ T.unop)).subtypeEquiv fun x =>
        (D.directImageQuotFamily_mem_hilbertPolynomialQuot_iff hπ M P x).symm))
    fun g => ConcreteCategory.hom_ext _ _ fun x =>
      Subtype.ext (D.directImageQuotFamily_baseChange g.unop x.1)

include hπ in
/-- The isomorphism on `Quot^P` does not change the morphism to `B` a quotient lies over. -/
theorem directImageHilbertPolynomialQuotIso_hom_app_toBase {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.π).obj M)
        (hL := isInvertible_modulePullback B S hS D.π M) P).toFunctor.obj T) :
    ((D.directImageHilbertPolynomialQuotIso hπ M P).hom.app T x).1.toBase = x.1.toBase :=
  rfl

include hπ in
/-- **Reduction of `Quot^P` along a closed immersion** (the last step of the proof of Stacks
0DPC): if `Quot^{P, M}_{π_*F/Y/B}` is an algebraic space proper over `B`, so is
`Quot^{P, π^*M}_{F/X/B}`, the two being isomorphic over `B` by Stacks 0DP4. -/
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_directImage
    (h : D.directImageSituation.IsProperAlgebraicSpaceOver
      (D.directImageSituation.hilbertPolynomialQuot M (hL := hM) P)) :
    D.sourceSituation.IsProperAlgebraicSpaceOver
      (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.π).obj M)
        (hL := isInvertible_modulePullback B S hS D.π M) P) := by
  obtain ⟨M₂, halg, hprop⟩ := h
  let e := D.directImageHilbertPolynomialQuotIso hπ M P
  let M₁ : D.sourceSituation.SubfunctorModel _ := ⟨M₂.presheaf, M₂.iso ≪≫ e.symm⟩
  have htb : M₁.toBase = M₂.toBase := by
    ext T z
    have hy := types_congr_hom (e.inv_hom_id_app T) (M₂.iso.hom.app T ⟨z⟩)
    show yonedaEquiv (e.inv.app T (M₂.iso.hom.app T ⟨z⟩)).1.toBase.hom =
      yonedaEquiv (M₂.iso.hom.app T ⟨z⟩).1.toBase.hom
    rw [← D.directImageHilbertPolynomialQuotIso_hom_app_toBase hπ M P
      (e.inv.app T (M₂.iso.hom.app T ⟨z⟩))]
    exact congrArg (fun y => yonedaEquiv y.1.toBase.hom) hy
  refine ⟨M₁, halg, ?_⟩
  rwa [htb]

end HilbertPolynomial

end QuotPushforwardSituation

end AlgebraicGeometry.Space
