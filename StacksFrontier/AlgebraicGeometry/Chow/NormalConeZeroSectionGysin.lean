module

public import StacksFrontier.AlgebraicGeometry.Chow.DeformationGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionRelation
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.NestedDivisorAgreement
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.WeakBivariantCriterionProof
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction

/-!
# The Gysin pullback of the normal cone along the zero section

This file proves [Stacks, Tag 0FEB]: for an integral scheme `X` of δ-dimension `n` and effective
Cartier divisors `Z ⊆ Y ⊆ X`,

  `o^*[C_ZX]_n = [C_ZY]_{n-1}` in `CH_{n-1}(Y ×_{o, C_YX} C_ZX)`,

where `o : Y ⟶ C_YX` is the zero section
(`Stacks.Chow.gysinBivariantCap_fundamentalChowClass_normalCone`).

## Strategy

Let `M = D(Z ⊆ X)` be the deformation to the normal cone, with parameter `t⁻¹`, and let
`φ : M ⟶ D(Y ⊆ X)` and `ψ : D(Z ⊆ Y) ⟶ M` be the induced morphisms. Then

* `Z(t⁻¹) ⊆ M` is `C_ZX` (`Stacks.Deformation.ker_normalConeToDeformation`);
* `E_Z = φ⁻¹E`, for `E` the strict part of the inverse image of `Y` in `D(Y ⊆ X)`, is an
  effective Cartier divisor containing `D(Z ⊆ Y)` and agreeing with it away from `Z(t⁻¹)`
  (`Stacks.Deformation.exists_affineOpen_ker_nestedInnerMap_eq`);
* the restriction of `(φ^*𝒪(E), φ^*1_E)` to `C_ZX` is `g^*(𝒪(o(Y)), 1_{o(Y)})`
  (`Stacks.Chow.NormalConeGysin.moduleIso`, `Stacks.Chow.NormalConeGysin.zeroScheme_eZ_eq`).

The Gysin identity `Stacks.Chow.deformation_gysin_identity` (Stacks 0B73, 02TB, 02T9) applied to
`t⁻¹` and `φ^*1_E` then gives the statement after transport along the isomorphisms
`Z(t⁻¹) ∩ E_Z ≅ Y ×_{o, C_YX} C_ZX` (`Stacks.Chow.NormalConeGysin.rho`) and
`C_ZY ≅ D(Z ⊆ Y) ∩ Z(t⁻¹)` (`Stacks.Chow.NormalConeGysin.ker_innerIdeal_inter_eq`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

attribute [local instance] Stacks.Conormal.isEffectiveCartierDivisor_ker_normalConeZeroSection

/-! ### Cycles of closed subschemes which agree off a closed subset -/

section Agreement

variable (C : ChowSituation.{u}) {M : Scheme.{u}} (p : M ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- The coefficient at a point of the cycle of a closed subscheme only depends on the ideal on an
affine neighbourhood of the point. -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_of_ideal_eq (I J : M.IdealSheafData)
    (W : M.affineOpens) (h : I.ideal W = J.ideal W) (x : M) (hx : x ∈ W.1) :
    (cycleAssociatedToClosedSubscheme C p I.subschemeι k).1 x =
      (cycleAssociatedToClosedSubscheme C p J.subschemeι k).1 x := by
  obtain ⟨x', rfl⟩ : x ∈ Set.range W.1.ι.base := by rw [Scheme.Opens.range_ι]; exact hx
  rw [← cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion C p (W.1.ι ≫ p) W.1.ι rfl I k x',
    ← cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion C p (W.1.ι ≫ p) W.1.ι rfl J k x',
    Stacks.Deformation.comap_ι_eq_of_ideal_eq W h]

/-- The kernel of `K ∩ Z ⊆ Z ⊆ M` is `K` when `Z ⊆ K`. -/
private theorem ker_comap_subschemeι_comp_of_le {M : Scheme.{u}} (Zb K : M.IdealSheafData)
    (hZK : Zb ≤ K) : ((K.comap Zb.subschemeι).subschemeι ≫ Zb.subschemeι).ker = K := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.map_comap_subschemeι, sup_eq_right.2 hZK]

/-- The cycle of `K ∩ Z ⊆ Z ⊆ M` is the cycle of `K ⊆ M` when `K ⊆ Z`. -/
theorem cycleAssociatedToClosedSubscheme_comap_subschemeι (Zb K : M.IdealSheafData)
    (hZK : Zb ≤ K) :
    cycleAssociatedToClosedSubscheme C p ((K.comap Zb.subschemeι).subschemeι ≫ Zb.subschemeι) k =
      cycleAssociatedToClosedSubscheme C p K.subschemeι k := by
  rw [cycleAssociatedToClosedSubscheme_ker, ker_comap_subschemeι_comp_of_le Zb K hZK]

/-- **The fundamental cycle of `Z` and the cycle of `K ∩ Z` agree off `A`** when `Z ⊆ K` and the
ideals of `Z` and `K` agree near every point off `A`. -/
theorem fundamentalCycle_apply_eq_of_local (Zb K A : M.IdealSheafData) (hZK : Zb ≤ K)
    (hloc : ∀ x ∉ A.support, ∃ W : M.affineOpens, x ∈ W.1 ∧ K.ideal W = Zb.ideal W)
    (y : Zb.subscheme) (hy : y ∉ Set.range (A.comap Zb.subschemeι).subschemeι.base) :
    (fundamentalCycle C (Zb.subschemeι ≫ p) k).1 y =
      (cycleAssociatedToClosedSubscheme C (Zb.subschemeι ≫ p)
        (K.comap Zb.subschemeι).subschemeι k).1 y := by
  have hx : Zb.subschemeι y ∉ A.support := fun h ↦ hy (by
    rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap])
  obtain ⟨W, hxW, hW⟩ := hloc _ hx
  rw [← properPushforward_apply_image C (Zb.subschemeι ≫ p) p Zb.subschemeι rfl k,
    ← properPushforward_apply_image C (Zb.subschemeι ≫ p) p Zb.subschemeι rfl k,
    properPushforward_fundamentalCycle_of_isClosedImmersion,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_comap_subschemeι C p k Zb K hZK]
  exact (cycleAssociatedToClosedSubscheme_apply_eq_of_ideal_eq C p k K Zb W hW _ hxW).symm

end Agreement

/-! ### Ideals and cycles of closed immersions -/

section Immersions

variable (C : ChowSituation.{u})

/-- A closed immersion is isomorphic onto its scheme-theoretic image. -/
theorem isIso_toImage_of_isClosedImmersion {T M : Scheme.{u}} (i : T ⟶ M) [IsClosedImmersion i] :
    IsIso i.toImage :=
  IsClosedImmersion.isIso_of_ker_eq i i.imageι i.toImage i.toImage_imageι
    (Scheme.IdealSheafData.ker_subschemeι _).symm

/-- **The image of the inverse image of an ideal along a closed immersion `i` is `ker i ⊔ J`.** -/
theorem map_comap_of_isClosedImmersion {T M : Scheme.{u}} (i : T ⟶ M) [IsClosedImmersion i]
    (J : M.IdealSheafData) : (J.comap i).map i = i.ker ⊔ J := by
  have := isIso_toImage_of_isClosedImmersion i
  calc (J.comap i).map i = (J.comap (i.toImage ≫ i.imageι)).map (i.toImage ≫ i.imageι) := by
        rw [i.toImage_imageι]
    _ = i.ker ⊔ J := by
        rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.map_comp,
          Scheme.IdealSheafData.map_comap_of_isIso, Scheme.IdealSheafData.map_comap_subschemeι]

/-- Inverse image of ideal sheaves preserves binary suprema. -/
theorem comap_sup_ideal {T M : Scheme.{u}} (f : T ⟶ M) (I J : M.IdealSheafData) :
    (I ⊔ J).comap f = I.comap f ⊔ J.comap f :=
  (Scheme.IdealSheafData.map_gc f).l_sup

/-- **Two closed subschemes of `P` have the same cycle when their images under a closed immersion
`P ⟶ W` have the same ideal.** -/
theorem cycleAssociatedToClosedSubscheme_eq_of_ker_comp_eq {P W A B : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (x₁ : A ⟶ P) (x₂ : B ⟶ P) [IsClosedImmersion x₁] [IsClosedImmersion x₂]
    (w : P ⟶ W) [IsClosedImmersion w] (h : (x₁ ≫ w).ker = (x₂ ≫ w).ker) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sP x₁ k = cycleAssociatedToClosedSubscheme C sP x₂ k := by
  have := IsClosedImmersion.isIso_lift (x₁ ≫ w) (x₂ ≫ w) h
  exact (cycleAssociatedToClosedSubscheme_eq_of_iso C sP x₂ x₁
    (asIso (IsClosedImmersion.lift (x₁ ≫ w) (x₂ ≫ w) h.le)) ((cancel_mono w).1 (by simp)) k).symm

/-- **Pushing forward heterogeneously equal classes from equal closed subschemes** along closed
immersions that agree after a monomorphism. -/
theorem chowPushforwardOfIsClosedImmersion_eq_of_heq {T P W : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (w : P ⟶ W) [Mono w]
    (v : T ⟶ W) {Z₁ Z₂ : T.IdealSheafData} (hZ : Z₁ = Z₂) (σ₁ : Z₁.subscheme ⟶ P)
    (σ₂ : Z₂.subscheme ⟶ P) [IsClosedImmersion σ₁] [IsClosedImmersion σ₂]
    (h₁ : σ₁ ≫ sP = Z₁.subschemeι ≫ q) (h₂ : σ₂ ≫ sP = Z₂.subschemeι ≫ q)
    (hw₁ : σ₁ ≫ w = Z₁.subschemeι ≫ v) (hw₂ : σ₂ ≫ w = Z₂.subschemeι ≫ v) (k : ℤ)
    (x₁ : chowGroup C (Z₁.subschemeι ≫ q) k) (x₂ : chowGroup C (Z₂.subschemeι ≫ q) k)
    (hx : x₁ ≍ x₂) :
    chowPushforwardOfIsClosedImmersion C _ sP σ₁ h₁ k x₁ =
      chowPushforwardOfIsClosedImmersion C _ sP σ₂ h₂ k x₂ := by
  subst hZ
  cases eq_of_heq hx
  have hσ : σ₁ = σ₂ := (cancel_mono w).1 (hw₁.trans hw₂.symm)
  subst hσ
  rfl

end Immersions

/-- The kernel of `K ∩ Z ⊆ Z ⊆ M` is `K` when `Z ⊆ K`. -/
theorem ker_comap_subschemeι_comp {M : Scheme.{u}} (Zb K : M.IdealSheafData) (hZK : Zb ≤ K) :
    ((K.comap Zb.subschemeι).subschemeι ≫ Zb.subschemeι).ker = K :=
  ker_comap_subschemeι_comp_of_le Zb K hZK

/-! ### The deformation space of `Z ⊆ X` and its two divisors -/

namespace NormalConeGysin

open Stacks.Deformation Stacks.Conormal

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (DY : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  (DZ : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DZ] (hZY : DY ≤ DZ)

/-- The structure morphism of `M = D(Z ⊆ X)` over the base. -/
abbrev defBase : deformationSpace (idealZX DZ) ⟶ C.S :=
  deformationSpaceToBase (idealZX DZ) ≫ DZ.subschemeι.coborderRange.ι ≫ sX

/-- The deformation space `D(Z ⊆ X)` is locally of finite type over its base. -/
instance locallyOfFiniteType_deformationSpaceToBase_idealZX :
    LocallyOfFiniteType (deformationSpaceToBase (idealZX DZ)) :=
  locallyOfFiniteType_deformationSpaceToBase (isLocallyPrincipalIdeal_of_isEffectiveCartierDivisor
    (isEffectiveCartierDivisor_coborderIdeal DZ))

/-- The deformation space `D(Z ⊆ Y)` is locally of finite type over its base. -/
instance locallyOfFiniteType_deformationSpaceToBase_idealZY :
    LocallyOfFiniteType (deformationSpaceToBase (idealZY DY DZ hZY)) :=
  locallyOfFiniteType_deformationSpaceToBase (by
    rw [← inner_eq DY DZ hZY]
    exact isLocallyPrincipalIdeal_comap (isLocallyPrincipalIdeal_of_isEffectiveCartierDivisor
      (isEffectiveCartierDivisor_coborderIdeal DZ)) _)

/-- The strict part `E` of the inverse image of `Y` in `D(Y ⊆ X)` is an effective Cartier
divisor. -/
instance isEffectiveCartierDivisor_divisorStrict :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorStrict DY) :=
  isEffectiveCartierDivisor_strictDivisor _ _

/-- The invertible module `φ^*𝒪(E)` on `M`. -/
abbrev bModule : (deformationSpace (idealZX DZ)).Modules :=
  (Scheme.Modules.pullback (nestedOuterMap DY DZ hZY)).obj
    (Stacks.Divisors.divisorSheaf (divisorStrict DY))

/-- Its section `φ^* 1_E`, whose zero scheme is `E_Z`. -/
abbrev bSection : Γ(bModule DY DZ hZY, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (nestedOuterMap DY DZ hZY) _
    (Stacks.Divisors.divisorSheafGlobalSection (divisorStrict DY))

/-- The parameter `t⁻¹` of `M`. -/
abbrev aSection : Γ(Scheme.unitModule (deformationSpace (idealZX DZ)), ⊤) :=
  paramGlobal (idealZX DZ)

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The zero scheme of `φ^* 1_E` is the divisor `E_Z = φ⁻¹E` of `M`. -/
theorem zeroScheme_bSection :
    Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY) =
      nestedDivisor DY DZ hZY := by
  rw [Stacks.Divisors.zeroScheme_pullback]
  exact congrArg (fun D => Scheme.IdealSheafData.comap D (nestedOuterMap DY DZ hZY))
    (Stacks.Divisors.zeroScheme_canonicalSection _)

/-- The closed subscheme `D(Z ⊆ Y) ⊆ E_Z`. -/
abbrev innerIdeal :
    (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY)
      (bSection DY DZ hZY)).subscheme.IdealSheafData :=
  (nestedInnerMap DY DZ hZY).ker.comap
    (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `D(Z ⊆ Y)` is contained in `E_Z`. -/
theorem zeroScheme_bSection_le :
    Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY) ≤
      (nestedInnerMap DY DZ hZY).ker := by
  rw [zeroScheme_bSection]
  exact nestedDivisor_le_ker DY DZ hZY

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The closed subscheme `innerIdeal` of `E_Z` has, as a closed subscheme of `M`, the ideal of
`D(Z ⊆ Y)`. -/
theorem ker_innerIdeal :
    ((innerIdeal DY DZ hZY).subschemeι ≫
      (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι).ker =
      (nestedInnerMap DY DZ hZY).ker :=
  ker_comap_subschemeι_comp _ _ (zeroScheme_bSection_le DY DZ hZY)

/-- `D(Z ⊆ Y)` is the closed subscheme `innerIdeal` of `E_Z`. -/
def innerLift : deformationSpace (idealZY DY DZ hZY) ⟶ (innerIdeal DY DZ hZY).subscheme :=
  IsClosedImmersion.lift _ (nestedInnerMap DY DZ hZY) (ker_innerIdeal DY DZ hZY).le

/-- `D(Z ⊆ Y) ⟶ innerIdeal` is an isomorphism. -/
instance isIso_innerLift : IsIso (innerLift DY DZ hZY) :=
  IsClosedImmersion.isIso_lift _ _ (ker_innerIdeal DY DZ hZY)

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `innerLift` followed by the inclusions `innerIdeal ⊆ E_Z ⊆ M` is the inclusion of
`D(Z ⊆ Y)` in `M`. -/
theorem innerLift_comp :
    innerLift DY DZ hZY ≫ (innerIdeal DY DZ hZY).subschemeι ≫
        (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι =
      nestedInnerMap DY DZ hZY :=
  IsClosedImmersion.lift_fac _ _ _

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The inverse of `innerLift` followed by the inclusion of `D(Z ⊆ Y)` in `M` is the inclusion
`innerIdeal ⊆ E_Z ⊆ M`. -/
theorem inv_innerLift_comp :
    inv (innerLift DY DZ hZY) ≫ nestedInnerMap DY DZ hZY =
      (innerIdeal DY DZ hZY).subschemeι ≫
        (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι := by
  rw [← innerLift_comp, IsIso.inv_hom_id_assoc]

/-! #### δ-dimensions -/

variable [IsIntegral X]

omit [IsIntegral X] in
/-- `M = D(Z ⊆ X)` has δ-dimension at most `n + 1` when `X` has δ-dimension `n`. -/
theorem schemeDeltaDimension_defBase {n : ℤ} (hn : schemeDeltaDimension C sX = (n : EInt)) :
    schemeDeltaDimension C (defBase C sX DZ) ≤ ((n - 1 + 1 + 1 : ℤ) : EInt) := by
  have h0 : schemeDeltaDimension C (DZ.subschemeι.coborderRange.ι ≫ sX) ≤ (n : EInt) :=
    schemeDeltaDimension_le_of_isClosedImmersion C sX _ hn.le
  have h := schemeDeltaDimension_deformationSpace_le
    (isLocallyPrincipalIdeal_of_isEffectiveCartierDivisor
      (isEffectiveCartierDivisor_coborderIdeal DZ)) C _ h0
  rwa [show n - 1 + 1 + 1 = n + 1 by ring]

/-- `D(Z ⊆ Y)` has δ-dimension at most `n` when `X` has δ-dimension `n`. -/
theorem schemeDeltaDimension_inner {n : ℤ} (hn : schemeDeltaDimension C sX = (n : EInt)) :
    schemeDeltaDimension C (nestedInnerMap DY DZ hZY ≫ defBase C sX DZ) ≤
      ((n - 1 + 1 : ℤ) : EInt) := by
  have hY : schemeDeltaDimension C (DY.subschemeι ≫ sX) ≤ ((n - 1 : ℤ) : EInt) := by
    refine (schemeDeltaDimension_isEffectiveCartierDivisor_le C sX DY ‹_›).trans ?_
    rw [hn, ← coe_add_coe_eq_coe_add, show n + (-1) = n - 1 by ring]
  have h1 : schemeDeltaDimension C (innerBase DY DZ hZY ≫ DZ.subschemeι.coborderRange.ι ≫ sX) ≤
      ((n - 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_congr C
      (show innerBase DY DZ hZY ≫ DZ.subschemeι.coborderRange.ι ≫ sX =
        (Scheme.IdealSheafData.inclusion hZY).coborderRange.ι ≫ DY.subschemeι ≫ sX by
          rw [coborderMap_ι_assoc])]
    exact schemeDeltaDimension_le_of_isClosedImmersion C _ _ hY
  have h2 := schemeDeltaDimension_deformationSpace_le (I := idealZY DY DZ hZY) (by
    rw [← inner_eq DY DZ hZY]
    exact isLocallyPrincipalIdeal_comap (isLocallyPrincipalIdeal_of_isEffectiveCartierDivisor
      (isEffectiveCartierDivisor_coborderIdeal DZ)) _) C _ h1
  rw [schemeDeltaDimension_congr C (show nestedInnerMap DY DZ hZY ≫ defBase C sX DZ =
    deformationSpaceToBase (idealZY DY DZ hZY) ≫ innerBase DY DZ hZY ≫
      DZ.subschemeι.coborderRange.ι ≫ sX by
        change nestedInnerMap DY DZ hZY ≫ deformationSpaceToBase (idealZX DZ) ≫ _ = _
        rw [← Category.assoc, nestedInnerMap_toBase, Category.assoc])]
  exact h2

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] [IsIntegral X] in
/-- `D(Z ⊆ Y)` meets `Z(t⁻¹)` in an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_inter_innerIdeal :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((zeroSchemeInter (bModule DY DZ hZY) (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (bSection DY DZ hZY) (aSection DZ)).comap (innerIdeal DY DZ hZY).subschemeι) := by
  rw [zeroSchemeInter_eq_comap, ← Scheme.IdealSheafData.comap_comp]
  have h1 : (Stacks.Divisors.zeroScheme _ (Scheme.unitModule (deformationSpace (idealZX DZ)))
      (aSection DZ)).comap ((innerIdeal DY DZ hZY).subschemeι ≫
        (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι) =
      ((Stacks.Divisors.zeroScheme _ (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (aSection DZ)).comap (nestedInnerMap DY DZ hZY)).comap (inv (innerLift DY DZ hZY)) := by
    rw [← Scheme.IdealSheafData.comap_comp, inv_innerLift_comp]
  have h2 : (Stacks.Divisors.zeroScheme _ (Scheme.unitModule (deformationSpace (idealZX DZ)))
      (aSection DZ)).comap (nestedInnerMap DY DZ hZY) =
      Stacks.Divisors.zeroScheme _ (Scheme.unitModule (deformationSpace (idealZY DY DZ hZY)))
        (paramGlobal (idealZY DY DZ hZY)) :=
    comap_zeroScheme_paramGlobal _ _ _ _
  rw [h1, h2]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (isEffectiveCartierDivisor_zeroScheme_paramGlobal _) _

omit [IsIntegral X] in
/-- **`[E_Z]` and `[D(Z ⊆ Y)]` have the same coefficients away from `Z(t⁻¹)`.** -/
theorem fundamentalCycle_apply_eq_innerIdeal (k : ℤ)
    (y : (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subscheme)
    (hy : y ∉ Set.range (zeroSchemeInter (bModule DY DZ hZY)
      (Scheme.unitModule (deformationSpace (idealZX DZ))) (bSection DY DZ hZY)
        (aSection DZ)).subschemeι.base) :
    (fundamentalCycle C ((Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY)
        (bSection DY DZ hZY)).subschemeι ≫ defBase C sX DZ) k).1 y =
      (cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY)
        (bSection DY DZ hZY)).subschemeι ≫ defBase C sX DZ)
        (innerIdeal DY DZ hZY).subschemeι k).1 y := by
  rw [zeroSchemeInter_eq_comap] at hy
  refine fundamentalCycle_apply_eq_of_local C (defBase C sX DZ) k _ _ _
    (zeroScheme_bSection_le DY DZ hZY) (fun x hx => ?_) y hy
  obtain ⟨W, hxW, hW⟩ := exists_affineOpen_ker_nestedInnerMap_eq DY DZ hZY x hx
  exact ⟨W, hxW, hW.trans (by rw [zeroScheme_bSection])⟩

/-- `D(Z ⊆ Y) ⊆ E_Z` has δ-dimension at most `n`. -/
theorem schemeDeltaDimension_innerIdeal {n : ℤ} (hn : schemeDeltaDimension C sX = (n : EInt)) :
    schemeDeltaDimension C ((innerIdeal DY DZ hZY).subschemeι ≫
      (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι ≫
        defBase C sX DZ) ≤ ((n - 1 + 1 : ℤ) : EInt) := by
  rw [schemeDeltaDimension_congr C (show (innerIdeal DY DZ hZY).subschemeι ≫
      (Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)).subschemeι ≫
        defBase C sX DZ =
          inv (innerLift DY DZ hZY) ≫ (nestedInnerMap DY DZ hZY ≫ defBase C sX DZ) by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ defBase C sX DZ)
        (inv_innerLift_comp DY DZ hZY)).symm.trans (Category.assoc _ _ _)))]
  exact schemeDeltaDimension_le_of_isClosedImmersion C _ _
    (schemeDeltaDimension_inner C sX DY DZ hZY hn)

/-! #### The fibre product `Y ×_{o, C_YX} C_ZX` inside `M` -/

omit [IsIntegral X]

/-- The morphism `C_ZX ⟶ C_YX`. -/
abbrev gMap : normalCone DZ.subschemeι ⟶ normalCone DY.subschemeι :=
  normalConeMapOfFactorization DZ.subschemeι DY.subschemeι (Scheme.IdealSheafData.inclusion hZY)
    (Scheme.IdealSheafData.inclusion_subschemeι hZY)

/-- The inclusion of `o(Y)`, presented as a zero scheme. -/
abbrev oIncl := gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)

/-- The divisor `E_Z ⊆ M`, presented as a zero scheme. -/
abbrev Zb := Stacks.Divisors.zeroScheme _ (bModule DY DZ hZY) (bSection DY DZ hZY)

/-- The intersection `E_Z ∩ Z(t⁻¹)`, inside `E_Z`. -/
abbrev Qb := zeroSchemeInter (bModule DY DZ hZY) (Scheme.unitModule (deformationSpace (idealZX DZ)))
  (bSection DY DZ hZY) (aSection DZ)

/-- The divisor `Z(t⁻¹) ⊆ M`. -/
abbrev Za := Stacks.Divisors.zeroScheme _ (Scheme.unitModule (deformationSpace (idealZX DZ)))
  (aSection DZ)

/-- The closed immersion `Y ×_{o, C_YX} C_ZX ⟶ C_ZX ⟶ M`. -/
abbrev jF : pullback (oIncl DY) (gMap DY DZ hZY) ⟶ deformationSpace (idealZX DZ) :=
  pullback.snd (oIncl DY) (gMap DY DZ hZY) ≫ normalConeToDeformation DZ.subschemeι

/-- The zero-scheme presentation of `o(Y)` has the ideal of the zero section. -/
theorem ker_oIncl : (oIncl DY).ker = (normalConeZeroSection DY).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact Stacks.Divisors.zeroScheme_canonicalSection _

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `o(Y)` pulled back to `C_ZX` is `E_Z` pulled back along `κ_Z`. -/
theorem comap_ker_zeroSection :
    (normalConeZeroSection DY).ker.comap (gMap DY DZ hZY) =
      (Zb DY DZ hZY).comap (normalConeToDeformation DZ.subschemeι) := by
  dsimp only [Zb]
  rw [zeroScheme_bSection, ← comap_divisorStrict_eq_ker, ← Scheme.IdealSheafData.comap_comp,
    ← normalConeToDeformation_comp_nestedOuterMap, Scheme.IdealSheafData.comap_comp]
  rfl

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The ideal of `Y ×_{o, C_YX} C_ZX` in `M` is that of `Z(t⁻¹) ∩ E_Z`. -/
theorem ker_jF : (jF DY DZ hZY).ker = Za DZ ⊔ Zb DY DZ hZY := by
  have hsnd : (pullback.snd (oIncl DY) (gMap DY DZ hZY)).ker =
      (normalConeZeroSection DY).ker.comap (gMap DY DZ hZY) := by
    rw [← pullbackSymmetry_hom_comp_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ker_oIncl]
  rw [← Scheme.IdealSheafData.map_ker, hsnd, comap_ker_zeroSection,
    map_comap_of_isClosedImmersion, ker_normalConeToDeformation]

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The ideal of `E_Z ∩ Z(t⁻¹)` in `M` is the supremum of the ideals of `Z(t⁻¹)` and `E_Z`. -/
theorem ker_Qb : ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι).ker =
    Za DZ ⊔ Zb DY DZ hZY := by
  dsimp only [Qb, Za, Zb]
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    zeroSchemeInter_eq_comap, Scheme.IdealSheafData.map_comap_subschemeι, sup_comm]

/-- **`E_Z ∩ Z(t⁻¹) ≅ Y ×_{o, C_YX} C_ZX`** over `M`. -/
def rho : (Qb DY DZ hZY).subscheme ⟶ pullback (oIncl DY) (gMap DY DZ hZY) :=
  IsClosedImmersion.lift (jF DY DZ hZY) ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι)
    ((ker_jF DY DZ hZY).trans (ker_Qb DY DZ hZY).symm).le

/-- `rho` is an isomorphism. -/
instance isIso_rho : IsIso (rho DY DZ hZY) :=
  IsClosedImmersion.isIso_lift _ _ ((ker_jF DY DZ hZY).trans (ker_Qb DY DZ hZY).symm)

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `rho` is compatible with the closed immersions of both sides into `M`. -/
theorem rho_jF : rho DY DZ hZY ≫ jF DY DZ hZY =
    (Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- **The two closed subschemes `C_ZY` and `D(Z ⊆ Y) ∩ Z(t⁻¹)` of `M` agree.** -/
theorem ker_innerIdeal_inter_eq :
    (((innerIdeal DY DZ hZY).comap (Qb DY DZ hZY).subschemeι).subschemeι ≫
        (Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι).ker =
      (normalConeToDeformation (Scheme.IdealSheafData.inclusion hZY) ≫
        nestedInnerMap DY DZ hZY).ker := by
  dsimp only [Qb, Zb, innerIdeal]
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.map_comp, Scheme.IdealSheafData.map_comap_subschemeι,
    zeroSchemeInter_eq_comap, ← comap_sup_ideal, Scheme.IdealSheafData.map_comap_subschemeι,
    ← Scheme.IdealSheafData.map_ker, ker_normalConeToDeformation]
  have h2 : (Za DZ).comap (nestedInnerMap DY DZ hZY) =
      Stacks.Divisors.zeroScheme _ (Scheme.unitModule (deformationSpace (idealZY DY DZ hZY)))
        (paramGlobal (idealZY DY DZ hZY)) :=
    comap_zeroScheme_paramGlobal _ _ _ _
  rw [← h2, map_comap_of_isClosedImmersion]
  exact (sup_eq_right.2 (le_sup_of_le_right (zeroScheme_bSection_le DY DZ hZY))).trans
    (sup_comm _ _)

/-! #### `C_ZX ≅ Z(t⁻¹)` and the restriction of `φ^*𝒪(E)` to it -/

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `Z(t⁻¹)` and `κ_Z : C_ZX ⟶ M` have the same ideal. -/
theorem ker_Za_eq : (Za DZ).subschemeι.ker = (normalConeToDeformation DZ.subschemeι).ker :=
  (Scheme.IdealSheafData.ker_subschemeι _).trans (ker_normalConeToDeformation _).symm

/-- **`C_ZX ≅ Z(t⁻¹)`** over `M`. -/
def eZ : normalCone DZ.subschemeι ⟶ (Za DZ).subscheme :=
  IsClosedImmersion.lift (Za DZ).subschemeι (normalConeToDeformation DZ.subschemeι)
    (ker_Za_eq DZ).le

/-- `eZ : C_ZX ⟶ Z(t⁻¹)` is an isomorphism. -/
instance isIso_eZ : IsIso (eZ DZ) := IsClosedImmersion.isIso_lift _ _ (ker_Za_eq DZ)

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `eZ` followed by the inclusion of `Z(t⁻¹)` is `κ_Z`. -/
theorem eZ_comp : eZ DZ ≫ (Za DZ).subschemeι = normalConeToDeformation DZ.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `κ_Z` lies over the base as `C_ZX ⟶ C_YX` does. -/
theorem normalConeToDeformation_defBase :
    normalConeToDeformation DZ.subschemeι ≫ defBase C sX DZ =
      gMap DY DZ hZY ≫ normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX := by
  rw [← Category.assoc, normalConeToDeformation_toBase, Category.assoc,
    Scheme.Hom.liftCoborder_ι_assoc, ← Category.assoc (gMap DY DZ hZY),
    normalConeMapOfFactorization_toBase, Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι_assoc]

omit [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `C_ZX ⟶ Z(t⁻¹) ⟶ M ⟶ D(Y ⊆ X)` factors as `C_ZX ⟶ C_YX ⟶ D(Y ⊆ X)`. -/
theorem eZ_comp_comp : eZ DZ ≫ (Za DZ).subschemeι ≫ nestedOuterMap DY DZ hZY =
    gMap DY DZ hZY ≫ normalConeToDeformation DY.subschemeι := by
  rw [← Category.assoc, eZ_comp, normalConeToDeformation_comp_nestedOuterMap]

/-- The inverse image of `E` along `κ_Y : C_YX ⟶ D(Y ⊆ X)` is defined: it is the effective
Cartier divisor `o(Y)`. -/
instance isPullbackDefined_divisorStrict :
    Stacks.Divisors.IsPullbackDefined (normalConeToDeformation DY.subschemeι)
      (divisorStrict DY) := by
  change Stacks.Divisors.IsEffectiveCartierDivisor _
  rw [comap_divisorStrict_eq_ker]
  infer_instance

/-- **The restriction of `φ^*𝒪(E)` to `C_ZX ≅ Z(t⁻¹)` is `g^*𝒪(o(Y))`.** -/
def moduleIso : (Scheme.Modules.pullback (eZ DZ)).obj
      (zeroSchemeRestrictModule (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (bModule DY DZ hZY) (aSection DZ)) ≅
    gysinTripleModule (zeroSectionDivisorSheaf DY) (gMap DY DZ hZY) :=
  (Scheme.Modules.pullback (eZ DZ)).mapIso ((Scheme.Modules.pullbackComp (Za DZ).subschemeι
      (nestedOuterMap DY DZ hZY)).app _) ≪≫
    (Scheme.Modules.pullbackComp (eZ DZ) ((Za DZ).subschemeι ≫ nestedOuterMap DY DZ hZY)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (eZ_comp_comp DY DZ hZY)).app _ ≪≫
    ((Scheme.Modules.pullbackComp (gMap DY DZ hZY) (normalConeToDeformation DY.subschemeι)).app
      _).symm ≪≫
    (Scheme.Modules.pullback (gMap DY DZ hZY)).mapIso
      (Stacks.Divisors.invertibleSheafPullbackIso (normalConeToDeformation DY.subschemeι)
          (divisorStrict DY) ≪≫
        eqToIso (congrArg Stacks.Divisors.invertibleSheaf' (comap_divisorStrict_eq_ker DY)))

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- **The zero schemes of the two restricted sections agree on `C_ZX`**: both are the inverse
image of `o(Y)`. -/
theorem zeroScheme_eZ_eq :
    pullbackZeroScheme (eZ DZ)
        (zeroSchemeRestrictModule (Scheme.unitModule (deformationSpace (idealZX DZ)))
          (bModule DY DZ hZY) (aSection DZ))
        (restrictSectionToZeroScheme (Scheme.unitModule (deformationSpace (idealZX DZ)))
          (bModule DY DZ hZY) (aSection DZ) (bSection DY DZ hZY)) =
      gysinTripleDivisor (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
        (gMap DY DZ hZY) := by
  dsimp only [pullbackZeroScheme, gysinTripleDivisor, restrictSectionToZeroScheme,
    zeroSchemeRestrictModule, gysinTripleModule, gysinTripleSection]
  have h3 : Stacks.Divisors.zeroScheme (normalCone DY.subschemeι) (zeroSectionDivisorSheaf DY)
      (zeroSectionDivisorSection DY) = (normalConeZeroSection DY).ker :=
    Stacks.Divisors.zeroScheme_canonicalSection _
  rw [Stacks.Divisors.zeroScheme_pullback (gMap DY DZ hZY), h3, comap_ker_zeroSection,
    Stacks.Divisors.zeroScheme_pullback (eZ DZ), Stacks.Divisors.zeroScheme_pullback,
    ← Scheme.IdealSheafData.comap_comp, eZ_comp]

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The fibre product lies over the base through `M`. -/
theorem jF_defBase : jF DY DZ hZY ≫ defBase C sX DZ =
    pullback.fst (oIncl DY) (gMap DY DZ hZY) ≫ oIncl DY ≫
      normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX := by
  rw [Category.assoc, normalConeToDeformation_defBase C sX DY DZ hZY, ← Category.assoc,
    ← pullback.condition, Category.assoc]

/-- The map from the zero scheme of the restricted section on `C_ZX` to `Z(t⁻¹) ∩ E_Z` is a
closed immersion. -/
instance isClosedImmersion_zeroSchemePullbackHom_eZ :
    IsClosedImmersion (zeroSchemePullbackHom (eZ DZ)
      (zeroSchemeRestrictModule (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (bModule DY DZ hZY) (aSection DZ))
      (restrictSectionToZeroScheme (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (bModule DY DZ hZY) (aSection DZ) (bSection DY DZ hZY))) := by
  have : IsClosedImmersion (zeroSchemePullbackHom (eZ DZ)
      (zeroSchemeRestrictModule (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (bModule DY DZ hZY) (aSection DZ))
      (restrictSectionToZeroScheme (Scheme.unitModule (deformationSpace (idealZX DZ)))
        (bModule DY DZ hZY) (aSection DZ) (bSection DY DZ hZY)) ≫
      (Stacks.Divisors.zeroScheme _ _ _).subschemeι) := by
    rw [zeroSchemePullbackHom_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (Stacks.Divisors.zeroScheme _ _ _).subschemeι

end NormalConeGysin

/-! ### Stacks 0FEB -/

namespace NormalConeGysin

open Stacks.Deformation Stacks.Conormal

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (DY : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  (DZ : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DZ] (hZY : DY ≤ DZ)
  (n : ℤ)

/-- The structure morphism of `C_ZX` in the statement. -/
abbrev qC : normalCone DZ.subschemeι ⟶ C.S :=
  gMap DY DZ hZY ≫ normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX

/-- The structure morphism of `Y ×_{o, C_YX} C_ZX` in the statement. -/
abbrev sP : pullback (oIncl DY) (gMap DY DZ hZY) ⟶ C.S :=
  pullback.fst (oIncl DY) (gMap DY DZ hZY) ≫ oIncl DY ≫ normalConeToBase DY.subschemeι ≫
    DY.subschemeι ≫ sX

/-- The intersection `Z(t⁻¹) ∩ E_Z`, inside `Z(t⁻¹)`. -/
abbrev Qa := zeroSchemeInter (Scheme.unitModule (deformationSpace (idealZX DZ))) (bModule DY DZ hZY)
  (aSection DZ) (bSection DY DZ hZY)

/-- The restriction of `φ^*𝒪(E)` to `Z(t⁻¹)`. -/
abbrev rModule := zeroSchemeRestrictModule (Scheme.unitModule (deformationSpace (idealZX DZ)))
  (bModule DY DZ hZY) (aSection DZ)

/-- The restriction of `φ^* 1_E` to `Z(t⁻¹)`. -/
abbrev rSection := restrictSectionToZeroScheme (Scheme.unitModule (deformationSpace (idealZX DZ)))
  (bModule DY DZ hZY) (aSection DZ) (bSection DY DZ hZY)

/-- The zero scheme of the restricted section, on `C_ZX`. -/
abbrev Z₁ := pullbackZeroScheme (eZ DZ) (rModule DY DZ hZY) (rSection DY DZ hZY)

/-- Its map to `Z(t⁻¹) ∩ E_Z`. -/
abbrev zsph := zeroSchemePullbackHom (eZ DZ) (rModule DY DZ hZY) (rSection DY DZ hZY)

/-- The identification of the two presentations of `Z(t⁻¹) ∩ E_Z`. -/
def eIso : (Qa DY DZ hZY).subscheme ≅ (Qb DY DZ hZY).subscheme :=
  Classical.choose (exists_iso_zeroSchemeInter (Scheme.unitModule (deformationSpace (idealZX DZ)))
    (bModule DY DZ hZY) (aSection DZ) (bSection DY DZ hZY))

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `eIso` is compatible with the closed immersions of both presentations into `M`. -/
theorem eIso_spec : (eIso DY DZ hZY).hom ≫ (Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι =
    (Qa DY DZ hZY).subschemeι ≫ (Za DZ).subschemeι :=
  Classical.choose_spec (exists_iso_zeroSchemeInter
    (Scheme.unitModule (deformationSpace (idealZX DZ)))
    (bModule DY DZ hZY) (aSection DZ) (bSection DY DZ hZY))

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `eZ` lies over the base. -/
theorem heZ : eZ DZ ≫ (Za DZ).subschemeι ≫ defBase C sX DZ = qC C sX DY DZ hZY := by
  rw [← Category.assoc, eZ_comp, normalConeToDeformation_defBase C sX DY DZ hZY]

/-- A map to the fibre product lies over the base through `M`. -/
private theorem comp_sP_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    (DY DZ : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DY] (hZY : DY ≤ DZ)
    {T : Scheme.{u}} (f : T ⟶ pullback (oIncl DY) (gMap DY DZ hZY)) :
    f ≫ sP C sX DY DZ hZY = (f ≫ jF DY DZ hZY) ≫ defBase C sX DZ := by
  rw [Category.assoc, jF_defBase C sX DY DZ hZY]

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `zsph` lies over the base. -/
theorem hu : zsph DY DZ hZY ≫ ((Qa DY DZ hZY).subschemeι ≫ (Za DZ).subschemeι ≫ defBase C sX DZ) =
    (Z₁ DY DZ hZY).subschemeι ≫ qC C sX DY DZ hZY :=
  zeroSchemePullbackHom_comp (eZ DZ) (rModule DY DZ hZY) (rSection DY DZ hZY) C
    ((Za DZ).subschemeι ≫ defBase C sX DZ) _ (heZ C sX DY DZ hZY)

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `eIso` lies over the base. -/
theorem hv : (eIso DY DZ hZY).hom ≫ ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫
    defBase C sX DZ) = (Qa DY DZ hZY).subschemeι ≫ (Za DZ).subschemeι ≫ defBase C sX DZ :=
  iso_zeroSchemeInter_comp_structureMorphism C (defBase C sX DZ)
    (Scheme.unitModule (deformationSpace (idealZX DZ))) (bModule DY DZ hZY) (aSection DZ)
    (bSection DY DZ hZY) (eIso DY DZ hZY) (eIso_spec DY DZ hZY)

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `rho` lies over the base. -/
theorem hw : rho DY DZ hZY ≫ sP C sX DY DZ hZY =
    (Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫ defBase C sX DZ := by
  rw [comp_sP_eq, rho_jF, Category.assoc]

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `eIso` followed by `rho` lies over the base. -/
theorem hvw : ((eIso DY DZ hZY).hom ≫ rho DY DZ hZY) ≫ sP C sX DY DZ hZY =
    (Qa DY DZ hZY).subschemeι ≫ (Za DZ).subschemeι ≫ defBase C sX DZ := by
  rw [Category.assoc, hw, hv]

/-- The comparison map `Z₁ ⟶ Y ×_{o, C_YX} C_ZX`. -/
abbrev σ₁ := zsph DY DZ hZY ≫ (eIso DY DZ hZY).hom ≫ rho DY DZ hZY

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `σ₁` is compatible with the closed immersions of `Z₁` and of the fibre product into `M`. -/
theorem hw₁ : σ₁ DY DZ hZY ≫ jF DY DZ hZY =
    (Z₁ DY DZ hZY).subschemeι ≫ normalConeToDeformation DZ.subschemeι := by
  dsimp only [σ₁, zsph, Z₁]
  rw [Category.assoc, Category.assoc, rho_jF, eIso_spec, ← Category.assoc,
    zeroSchemePullbackHom_subschemeι, Category.assoc, eZ_comp]

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- `σ₁` lies over the base. -/
theorem h₁ : σ₁ DY DZ hZY ≫ sP C sX DY DZ hZY = (Z₁ DY DZ hZY).subschemeι ≫ qC C sX DY DZ hZY := by
  rw [comp_sP_eq, hw₁, Category.assoc, normalConeToDeformation_defBase C sX DY DZ hZY]

omit [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The base-change isomorphism of the Gysin divisor is compatible with the closed immersions
into `M`. -/
theorem hw₂ : (gysinDivisorBaseChangeIso (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
      (gMap DY DZ hZY)).hom ≫ jF DY DZ hZY =
    (gysinTripleDivisor (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
      (gMap DY DZ hZY)).subschemeι ≫ normalConeToDeformation DZ.subschemeι := by
  rw [← Category.assoc, gysinDivisorBaseChangeIso_hom_snd]

omit [LocallyOfFiniteType sX] [Stacks.Divisors.IsEffectiveCartierDivisor DZ] in
/-- The base-change isomorphism of the Gysin divisor lies over the base. -/
theorem h₂ : (gysinDivisorBaseChangeIso (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
      (gMap DY DZ hZY)).hom ≫ sP C sX DY DZ hZY =
    (gysinTripleDivisor (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
      (gMap DY DZ hZY)).subschemeι ≫ qC C sX DY DZ hZY := by
  rw [comp_sP_eq, hw₂, Category.assoc, normalConeToDeformation_defBase C sX DY DZ hZY]

/-- The Gysin class of the restricted section on `C_ZX`. -/
abbrev GM : chowGroup C ((Z₁ DY DZ hZY).subschemeι ≫ qC C sX DY DZ hZY) (n - 1) :=
  gysinChowOfInvertible C (qC C sX DY DZ hZY) (n - 1)
    ((Scheme.Modules.pullback (eZ DZ)).obj (rModule DY DZ hZY))
    (AlgebraicGeometry.pullbackGlobalSections (eZ DZ) _ (rSection DY DZ hZY))
    (fundamentalChowClass C (qC C sX DY DZ hZY) (n - 1 + 1))

/-- **The deformation identity, read on `C_ZX`.** -/
theorem key_identity [IsIntegral X] (hn : schemeDeltaDimension C sX = (n : EInt)) :
    chowPushforwardOfIso C ((Qa DY DZ hZY).subschemeι ≫ (Za DZ).subschemeι ≫ defBase C sX DZ)
        ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫ defBase C sX DZ)
        (eIso DY DZ hZY).hom (hv C sX DY DZ hZY) (n - 1)
        (properChowPushforward C _ _ (zsph DY DZ hZY) (hu C sX DY DZ hZY) (n - 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _
            (hu C sX DY DZ hZY) _)
          (GM C sX DY DZ hZY n)) =
      QuotientAddGroup.mk' (rationalEquivalences C
          ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫ defBase C sX DZ) (n - 1))
        (cycleAssociatedToClosedSubscheme C
          ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫ defBase C sX DZ)
          ((innerIdeal DY DZ hZY).comap (Qb DY DZ hZY).subschemeι).subschemeι (n - 1)) := by
  have key := deformation_gysin_identity C (defBase C sX DZ) (n - 1) (aSection DZ)
    (bModule DY DZ hZY) (bSection DY DZ hZY) (schemeDeltaDimension_defBase C sX DZ hn)
    (by rw [zeroScheme_bSection]; exact isEffectiveCartierDivisor_nestedDivisor DY DZ hZY)
    (innerIdeal DY DZ hZY) (schemeDeltaDimension_innerIdeal C sX DY DZ hZY hn)
    (isEffectiveCartierDivisor_inter_innerIdeal DY DZ hZY)
    (fundamentalCycle_apply_eq_innerIdeal C sX DY DZ hZY _) (eIso DY DZ hZY) (eIso_spec DY DZ hZY)
  rw [gysinChowOfInvertible_fundamentalChowClass C (defBase C sX DZ) (n - 1 + 1) _ (aSection DZ)
      (schemeDeltaDimension_defBase C sX DZ hn)
      (isEffectiveCartierDivisor_zeroScheme_paramGlobal _),
    ← chowPushforwardOfIso_fundamentalChowClass C _ ((Za DZ).subschemeι ≫ defBase C sX DZ)
      (eZ DZ) (heZ C sX DY DZ hZY)] at key
  have h3 := gysinChowOfInvertible_properChowPushforward C ((Za DZ).subschemeι ≫ defBase C sX DZ)
    (qC C sX DY DZ hZY) (eZ DZ) (heZ C sX DY DZ hZY) (n - 1) (rModule DY DZ hZY)
    (rSection DY DZ hZY)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ (eZ DZ)
      (heZ C sX DY DZ hZY) (n - 1 + 1))
    (fundamentalChowClass C (qC C sX DY DZ hZY) (n - 1 + 1))
  rw [show chowPushforwardOfIso C (qC C sX DY DZ hZY) ((Za DZ).subschemeι ≫ defBase C sX DZ)
      (eZ DZ) (heZ C sX DY DZ hZY) (n - 1 + 1) =
      properChowPushforward C _ _ (eZ DZ) (heZ C sX DY DZ hZY) (n - 1 + 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ (eZ DZ)
          (heZ C sX DY DZ hZY) (n - 1 + 1))
      from rfl, h3] at key
  exact key

/-- **The two Gysin classes on `C_ZX` agree after pushing forward to the fibre product.** -/
theorem pushforward_gysin_eq :
    chowPushforwardOfIsClosedImmersion C _ (sP C sX DY DZ hZY)
        (gysinDivisorBaseChangeIso (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
          (gMap DY DZ hZY)).hom (h₂ C sX DY DZ hZY) (n - 1)
        (gysinChowOfInvertible C (qC C sX DY DZ hZY) (n - 1)
          (gysinTripleModule (zeroSectionDivisorSheaf DY) (gMap DY DZ hZY))
          (gysinTripleSection (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
            (gMap DY DZ hZY))
          (fundamentalChowClass C (qC C sX DY DZ hZY) (n - 1 + 1))) =
      chowPushforwardOfIsClosedImmersion C _ (sP C sX DY DZ hZY) (σ₁ DY DZ hZY)
        (h₁ C sX DY DZ hZY) (n - 1) (GM C sX DY DZ hZY n) := by
  have hG := gysinChowOfInvertible_heq_of_eq C (q := qC C sX DY DZ hZY) rfl (k := n - 1) rfl
    (AlgebraicGeometry.pullbackGlobalSections (eZ DZ) _ (rSection DY DZ hZY))
    (gysinTripleSection (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
      (gMap DY DZ hZY))
    (moduleIso DY DZ hZY) (zeroScheme_eZ_eq DY DZ hZY)
    (HEq.refl (fundamentalChowClass C (qC C sX DY DZ hZY) (n - 1 + 1)))
  exact (chowPushforwardOfIsClosedImmersion_eq_of_heq C (qC C sX DY DZ hZY) (sP C sX DY DZ hZY)
    (jF DY DZ hZY) (normalConeToDeformation DZ.subschemeι) (zeroScheme_eZ_eq DY DZ hZY) _ _
    (h₁ C sX DY DZ hZY) (h₂ C sX DY DZ hZY) (hw₁ DY DZ hZY) (hw₂ DY DZ hZY) (n - 1) _ _ hG).symm

/-- The pushforward along `Z₁ ⟶ Z(t⁻¹) ∩ E_Z ⟶ Y ×_{o, C_YX} C_ZX` in three steps. -/
theorem pushforward_σ₁ (x : chowGroup C ((Z₁ DY DZ hZY).subschemeι ≫ qC C sX DY DZ hZY) (n - 1)) :
    chowPushforwardOfIsClosedImmersion C _ (sP C sX DY DZ hZY) (σ₁ DY DZ hZY)
        (h₁ C sX DY DZ hZY) (n - 1) x =
      properChowPushforward C _ _ (rho DY DZ hZY) (hw C sX DY DZ hZY) (n - 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _
          (hw C sX DY DZ hZY) _)
        (chowPushforwardOfIso C ((Qa DY DZ hZY).subschemeι ≫ (Za DZ).subschemeι ≫ defBase C sX DZ)
          ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫ defBase C sX DZ)
          (eIso DY DZ hZY).hom (hv C sX DY DZ hZY) (n - 1)
          (properChowPushforward C _ _ (zsph DY DZ hZY) (hu C sX DY DZ hZY) (n - 1)
            (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _
              (hu C sX DY DZ hZY) _) x)) :=
  properChowPushforward_comp₃_apply C _ _ _ _ _ (eIso DY DZ hZY).hom (rho DY DZ hZY)
    (hu C sX DY DZ hZY) (hv C sX DY DZ hZY) (hw C sX DY DZ hZY) (hvw C sX DY DZ hZY)
    (h₁ C sX DY DZ hZY) (n - 1) _ _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _
      (hvw C sX DY DZ hZY) _) _ x

attribute [local instance] isClosedImmersion_normalConeToZeroFibre

/-- **`C_ZY` and `D(Z ⊆ Y) ∩ Z(t⁻¹)` have the same cycle on the fibre product.** -/
theorem pushforward_rho_cycle :
    properPushforward C _ _ (rho DY DZ hZY) (hw C sX DY DZ hZY) (n - 1)
        (cycleAssociatedToClosedSubscheme C
          ((Qb DY DZ hZY).subschemeι ≫ (Zb DY DZ hZY).subschemeι ≫ defBase C sX DZ)
          ((innerIdeal DY DZ hZY).comap (Qb DY DZ hZY).subschemeι).subschemeι (n - 1)) =
      cycleAssociatedToClosedSubscheme C (sP C sX DY DZ hZY)
        (normalConeToZeroFibre DY DZ.subschemeι (Scheme.IdealSheafData.inclusion hZY)
          (Scheme.IdealSheafData.inclusion_subschemeι hZY)) (n - 1) := by
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
  refine cycleAssociatedToClosedSubscheme_eq_of_ker_comp_eq C _ _ _ (jF DY DZ hZY) ?_ (n - 1)
  rw [Category.assoc, rho_jF, ker_innerIdeal_inter_eq]
  have hj : normalConeToZeroFibre DY DZ.subschemeι (Scheme.IdealSheafData.inclusion hZY)
      (Scheme.IdealSheafData.inclusion_subschemeι hZY) ≫ jF DY DZ hZY =
      normalConeToDeformation (Scheme.IdealSheafData.inclusion hZY) ≫ nestedInnerMap DY DZ hZY := by
    rw [normalConeToDeformation_comp_nestedInnerMap]
    dsimp only [jF]
    rw [← Category.assoc, normalConeToZeroFibre_snd]
  rw [hj]

end NormalConeGysin

/-! ### The theorem -/

section Main

open Stacks.Deformation NormalConeGysin Scheme.IdealSheafData

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (DY : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DY]
  (DZ : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor DZ] (hZY : DY ≤ DZ)
  (n : ℤ)

attribute [local instance] isClosedImmersion_normalConeToZeroFibre

/-- **Stacks Project, Tag 0FEB.** Let `(S, δ)` be as in Situation 02QL, let `X` be an integral
scheme locally of finite type over `S` of δ-dimension `n`, and let `Z ⊆ Y ⊆ X` be closed
subschemes which are both effective Cartier divisors in `X`. Write `o : Y ⟶ C_YX` for the zero
section of the normal line cone of `Y` in `X`. Then

    `o^*[C_ZX]_n = [C_ZY]_{n-1}` in `CH_{n-1}(Y ×_{o, C_YX} C_ZX)`.

Here `Y` and `Z` are `DY.subscheme` and `DZ.subscheme`, `Z ⊆ Y` is `hZY : DY ≤ DZ`, `o` is
`Stacks.Conormal.normalConeZeroSection`, the morphism `C_ZX ⟶ C_YX` is
`Stacks.Conormal.normalConeMapOfFactorization`, `o^*` is the cap operation
`Stacks.Chow.gysinBivariantCap` of the canonical Gysin system at the presentation of `o(Y)` by
`Stacks.Chow.zeroSectionDivisorSheaf` and `Stacks.Chow.zeroSectionDivisorSection`, and the closed
immersion `C_ZY ⟶ Y ×_{o, C_YX} C_ZX` is `Stacks.Chow.normalConeToZeroFibre`.

The proof is by the deformation to the normal cone `M = D(Z ⊆ X)`, of δ-dimension at most
`n + 1`. It carries the divisor `Z(t⁻¹) ≅ C_ZX` and the divisor `E_Z`, the inverse image of the
strict transform `E` of `Y` in `D(Y ⊆ X)`. On `C_ZX` the restriction of `𝒪(E_Z)` with its
canonical section is `g^*𝒪(o(Y))` with its canonical section (Stacks 0C4U, as `κ_Y⁻¹E = o(Y)`), so
the left-hand side is `1_{E_Z}|^* (t⁻¹)^*[M]_{n+1}` (Stacks 02TB(1) and 02TA). By
[Stacks, Tag 0B73] this is `(t⁻¹)|^* 1_{E_Z}^*[M] = (t⁻¹)|^*[E_Z]`; `[E_Z]` and `[D(Z ⊆ Y)]` differ
by a cycle supported in `Z(t⁻¹)`, on which the Gysin map of the trivial module kills it
(Stacks 02T9); and `(t⁻¹)|^*[D(Z ⊆ Y)] = [D(Z ⊆ Y) ∩ Z(t⁻¹)] = [C_ZY]` by [Stacks, Tag 02TB]. -/
@[stacks 0FEB "PROVED, at the canonical Gysin system `Stacks.Chow.canonicalGysinSystem` (whose \
contained-component rule is the first Chern class of the restricted invertible module, Stacks \
02SO), which is the o^* of the source. No hypothesis beyond the source's: X integral, locally of \
finite type over the base of delta-dimension n, Z and Y effective Cartier divisors with Z inside \
Y. The closed immersion C_ZY -> Y x_{o, C_YX} C_ZX that the source leaves implicit is \
constructed, as `Stacks.Chow.normalConeToZeroFibre`, the unique morphism with the two components \
the source names (`Stacks.Chow.normalConeZeroSectionGysinRelation_hom_ext`). The proof goes \
through the deformation to the normal cone D(Z in X) and Tags 0B73, 02TB, 02TA, 02T9 and 0C4U \
rather than through the blowups of Tag 0FBG used by the source."]
theorem gysinBivariantCap_fundamentalChowClass_normalCone [IsIntegral X]
    (hn : schemeDeltaDimension C sX = (n : EInt)) :
    gysinBivariantCap C (canonicalGysinSystem C)
        (Stacks.Conormal.normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX)
        (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY)
        (Stacks.Conormal.normalConeMapOfFactorization DZ.subschemeι DY.subschemeι (inclusion hZY)
          (inclusion_subschemeι hZY)) n
        (fundamentalChowClass C
          (Stacks.Conormal.normalConeMapOfFactorization DZ.subschemeι DY.subschemeι
              (inclusion hZY) (inclusion_subschemeι hZY) ≫
            (Stacks.Conormal.normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX)) n) =
      QuotientAddGroup.mk'
        (rationalEquivalences C
          (pullback.fst
              (gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY))
              (Stacks.Conormal.normalConeMapOfFactorization DZ.subschemeι DY.subschemeι
                (inclusion hZY) (inclusion_subschemeι hZY)) ≫
            (gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY) ≫
              (Stacks.Conormal.normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX)))
          (n - 1))
        (cycleAssociatedToClosedSubscheme C
          (pullback.fst
              (gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY))
              (Stacks.Conormal.normalConeMapOfFactorization DZ.subschemeι DY.subschemeι
                (inclusion hZY) (inclusion_subschemeι hZY)) ≫
            (gysinTripleInclusion (zeroSectionDivisorSheaf DY) (zeroSectionDivisorSection DY) ≫
              (Stacks.Conormal.normalConeToBase DY.subschemeι ≫ DY.subschemeι ≫ sX)))
          (normalConeToZeroFibre DY DZ.subschemeι (inclusion hZY) (inclusion_subschemeι hZY))
          (n - 1)) := by
  rw [gysinBivariantCap_apply, canonicalGysinSystem_onChow,
    chowGroupDegreeEquiv_fundamentalChowClass]
  exact (pushforward_gysin_eq C sX DY DZ hZY n).trans ((pushforward_σ₁ C sX DY DZ hZY n _).trans
    ((congrArg _ (key_identity C sX DY DZ hZY n hn)).trans
      (congrArg _ (pushforward_rho_cycle C sX DY DZ hZY n))))

end Main

end Stacks.Chow

end
