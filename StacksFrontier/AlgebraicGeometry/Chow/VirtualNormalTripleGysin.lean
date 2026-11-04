module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.GysinChowPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafEqToHom

/-!
# The Gysin map of a locally principal closed subscheme with a virtual normal bundle

Let `X` be a scheme locally of finite type over the base `S` of a Chow situation (Situation
02QL). Remark 0B70 considers triples `(D, 𝒩, σ)` consisting of a locally principal closed
subscheme `i : D ⟶ X` (Definition 01WR), an invertible `𝒪_D`-module `𝒩` and a surjection
`σ : 𝒩^{⊗ -1} ⟶ i^*ℐ_D` of `𝒪_D`-modules, and asserts that the Gysin homomorphism
`i^* : Z_{k+1}(X) ⟶ A_k(D)` of Definition 02T8 generalizes to such triples; its footnote asserts
that `σ` forces `𝒩 ≅ 𝒪_X(D)|_D` when `D` is an effective Cartier divisor.

The construction is the recipe of Definition 02T8 with `𝒩` in place of `ℒ|_D`: an integral closed
subscheme `W ⊆ X` of delta-dimension `k + 1` goes to `[D ∩ W]_k` if `W ⊄ D` and to
`i'_*(c₁(𝒩|_W) ∩ [W])` if `W ⊆ D`, and the two rules are extended over locally finite sums.

## Main definitions

* `Stacks.Chow.VirtualNormalTriple` — a triple `(D, 𝒩, σ)`.
* `Stacks.Chow.VirtualNormalTriple.normalIsoOfIsEffectiveCartier` — the isomorphism
  `𝒩 ≅ 𝒪_X(D)|_D` of the footnote.
* `Stacks.Chow.VirtualNormalTriple.ofIsEffectiveCartier` — the triple `(D, 𝒪_X(D)|_D, σ)` of an
  effective Cartier divisor.
* `Stacks.Chow.virtualNormalChernClass` — the class `c₁(𝒩|_W) ∩ [W] ∈ A_k(W)`.
* `Stacks.Chow.virtualNormalGysinOfIdeal` — the Gysin map of a closed subscheme with an invertible
  module on it, and `Stacks.Chow.VirtualNormalTriple.gysin` that of a triple.

## Main results

* `Stacks.Chow.VirtualNormalTriple.gysin_of_not_le`, `gysin_of_le`, `gysin_finsum` — the rules
  of Definition 02T8 for the Gysin map of a triple.
* `Stacks.Chow.VirtualNormalTriple.nonempty_normalIso_of_isEffectiveCartier` — the footnote.
* `Stacks.Chow.virtualNormalGysinOfIdeal_zeroScheme` and
  `Stacks.Chow.VirtualNormalTriple.gysin_heq_of_zeroScheme_eq` — the construction generalizes
  Definition 02T8: for `D = Z(s)` and `𝒩 ≅ ℒ|_D` it is `Stacks.Chow.gysinHomomorphismOfInvertible`.
* `Stacks.Chow.VirtualNormalTriple.gysin_heq_divisorSheaf` and
  `Stacks.Chow.VirtualNormalTriple.chowPushforwardOfIso_gysinHomomorphismOfInvertible_divisorSheaf`
  — for an effective Cartier divisor `D` it is the Gysin map of `(𝒪_X(D), 1_D)`.
* `Stacks.Chow.virtualNormalTriple_remark` — all of the above as one statement.

## Implementation notes

The integral-component cycle is `Stacks.Chow.gysinComponentCycleOfIdeal` (the cycle of
Definition 02T8 with the zero scheme abstracted into an arbitrary closed subscheme), fed with the
component rule `Stacks.Chow.virtualNormalChernRule` of `𝒩`; the class `c₁(𝒩|_W) ∩ [W]` is
`Stacks.Chow.chernComponentCycle` of `𝒩|_W`, the model used by
`Stacks.Chow.firstChernComponentClass`, and it does not depend on the chosen section
(`Stacks.Chow.virtualNormalChernClass_eq_mk`). The surjection `σ` does not enter the recipe.

The Gysin maps of `(D, 𝒩)` and of `(𝒪_X(D), 1_D)` have the targets `A_k(D)` and `A_k(Z(1_D))`,
which are equal types only after rewriting `Z(1_D) = D`; the comparison is therefore stated as a
heterogeneous equality and, equivalently, as an identity of Chow classes after pushforward along
the identification of the two subschemes.

## References

* [Stacks Project, Tag 0B70](https://stacks.math.columbia.edu/tag/0B70)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-- **Remark 0B70.** A triple `(D, 𝒩, σ)` on a scheme `X`: a locally principal closed subscheme
`i : D ⟶ X`, an invertible `𝒪_D`-module `𝒩` (the virtual normal bundle of `D` in `X`) and a
surjection `σ : 𝒩^{⊗ -1} ⟶ i^*ℐ_D` of `𝒪_D`-modules. -/
@[stacks 0B70 "the triple (D, N, σ): D locally principal, N an invertible O_D-module, σ a \
surjection from the inverse of N onto the pullback of the ideal sheaf of D"]
structure VirtualNormalTriple (X : Scheme.{u}) where
  /-- The locally principal closed subscheme `D ⊆ X`. -/
  D : X.IdealSheafData
  /-- `D` is locally principal (Definition 01WR). -/
  isLocallyPrincipal : IsLocallyPrincipal D
  /-- The virtual normal bundle `𝒩`, an invertible `𝒪_D`-module. -/
  N : D.subscheme.Modules
  /-- `𝒩` is invertible. -/
  [isInvertible : AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.sheaf.obj
    D.subscheme.ringCatSheaf.property N]
  /-- The surjection `σ : 𝒩^{⊗ -1} ⟶ i^*ℐ_D`. -/
  σ : Stacks.SheafOfModules.Invertible.tensorPower D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property N (-1) ⟶
    (Scheme.Modules.pullback D.subschemeι).obj (negativeTwist' D)
  /-- `σ` is surjective. -/
  epi_σ : Epi σ

attribute [instance] VirtualNormalTriple.isInvertible

namespace VirtualNormalTriple

variable {X : Scheme.{u}} (T : VirtualNormalTriple X)

/-- The pairing `𝒩 ⊗ 𝒩^{⊗ -1} ≅ 𝒪_D`. -/
def tensorInverseIsoUnit :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.D.subscheme.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ T.D.subscheme.sheaf.obj (forget₂ CommRingCat RingCat)
        T.D.subscheme.ringCatSheaf.property⟩).obj T.N).obj
        (Stacks.SheafOfModules.Invertible.tensorPower T.D.subscheme.sheaf.obj
          T.D.subscheme.ringCatSheaf.property T.N (-1)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        T.D.subscheme.sheaf.obj T.D.subscheme.ringCatSheaf.property) :=
  Stacks.SheafOfModules.tensorSheafBraiding _ _ _ _ ≪≫
    Stacks.SheafOfModules.Invertible.tensorPowerSuccIso T.D.subscheme.sheaf.obj
      T.D.subscheme.ringCatSheaf.property T.N (-1) ≪≫
    Stacks.SheafOfModules.Invertible.tensorPowerReindex T.D.subscheme.sheaf.obj
      T.D.subscheme.ringCatSheaf.property T.N (neg_add_cancel 1) ≪≫
    eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_zero T.D.subscheme.sheaf.obj
      T.D.subscheme.ringCatSheaf.property T.N)

/-- `𝒩^{⊗ -1}` is invertible. -/
theorem isTensorInvertible_tensorPower_neg_one :
    Stacks.SheafOfModules.IsInvertible T.D.subscheme.sheaf.obj
      T.D.subscheme.ringCatSheaf.property
      (Stacks.SheafOfModules.Invertible.tensorPower T.D.subscheme.sheaf.obj
        T.D.subscheme.ringCatSheaf.property T.N (-1)) :=
  Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit _ _ _ T.N T.tensorInverseIsoUnit

variable [IsEffectiveCartierDivisor T.D]

/-- For an effective Cartier divisor `D`, the module `i^*ℐ_D` is invertible. -/
theorem isTensorInvertible_pullback_negativeTwist :
    Stacks.SheafOfModules.IsInvertible T.D.subscheme.sheaf.obj
      T.D.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback T.D.subschemeι).obj (negativeTwist' T.D)) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (negativeTwist' T.D) := ‹IsEffectiveCartierDivisor T.D›
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_presheaf_modulePullback (negativeTwist' T.D) T.D.subschemeι)

/-- For an effective Cartier divisor the surjection `σ` is an isomorphism. -/
theorem isIso_σ : IsIso T.σ :=
  @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible T.D.subscheme.toRingedSpace _ _ T.σ T.epi_σ
    T.isTensorInvertible_tensorPower_neg_one T.isTensorInvertible_pullback_negativeTwist

/-- The pairing `i^*𝒪_X(D) ⊗ 𝒩^{⊗ -1} ≅ 𝒪_D`. -/
def pullbackDivisorSheafTensorIsoUnit :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.D.subscheme.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ T.D.subscheme.sheaf.obj (forget₂ CommRingCat RingCat)
        T.D.subscheme.ringCatSheaf.property⟩).obj
        ((Scheme.Modules.pullback T.D.subschemeι).obj (divisorSheaf T.D))).obj
        (Stacks.SheafOfModules.Invertible.tensorPower T.D.subscheme.sheaf.obj
          T.D.subscheme.ringCatSheaf.property T.N (-1)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        T.D.subscheme.sheaf.obj T.D.subscheme.ringCatSheaf.property) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.D.subscheme.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ T.D.subscheme.sheaf.obj (forget₂ CommRingCat RingCat)
        T.D.subscheme.ringCatSheaf.property⟩).obj
        ((Scheme.Modules.pullback T.D.subschemeι).obj (divisorSheaf T.D))).mapIso
      (@asIso _ _ _ _ T.σ T.isIso_σ) ≪≫
    Stacks.RingedSpace.tensorIsoUnitPullback T.D.subschemeι.toLRSHom.toShHom
      (invertibleSheaf' T.D) (negativeTwist' T.D)
      (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' T.D))
      (Stacks.RingedSpace.isIso_comparison _ _ _)

/-- **The footnote of Remark 0B70.** If `D` is an effective Cartier divisor, then
`𝒩 ≅ 𝒪_X(D)|_D`. -/
@[stacks 0B70 "footnote: if D is an effective Cartier divisor, then N is isomorphic to the \
restriction of O_X(D) to D"]
def normalIsoOfIsEffectiveCartier :
    T.N ≅ (Scheme.Modules.pullback T.D.subschemeι).obj (divisorSheaf T.D) :=
  have := T.isTensorInvertible_tensorPower_neg_one
  Stacks.SheafOfModules.isoOfTensorIsoUnit T.D.subscheme.sheaf.obj
    T.D.subscheme.ringCatSheaf.property _ T.N _ T.tensorInverseIsoUnit
    T.pullbackDivisorSheafTensorIsoUnit

section OfEffectiveCartier

variable (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- `𝒪_X(D)|_D` is invertible. -/
instance isInvertible_pullback_divisorSheaf :
    AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) :=
  isInvertible_presheaf_modulePullback (divisorSheaf D) D.subschemeι

/-- The pairing `i^*ℐ_D ⊗ i^*𝒪_X(D) ≅ 𝒪_D`, the pullback of the evaluation pairing. -/
def pullbackNegativeTwistTensorIsoUnit :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨D.subscheme.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ D.subscheme.sheaf.obj (forget₂ CommRingCat RingCat)
        D.subscheme.ringCatSheaf.property⟩).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist' D))).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        D.subscheme.sheaf.obj D.subscheme.ringCatSheaf.property) :=
  Stacks.RingedSpace.tensorIsoUnitPullback D.subschemeι.toLRSHom.toShHom
    (negativeTwist' D) (invertibleSheaf' D)
    (Stacks.SheafOfModules.tensorSheafBraiding _ _ _ _ ≪≫
      Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D))
    (Stacks.RingedSpace.isIso_comparison _ _ _)

/-- `(𝒪_X(D)|_D)^{⊗ -1} ≅ i^*ℐ_D` for an effective Cartier divisor `D`. -/
def pullbackDivisorSheafInverseIso :
    Stacks.SheafOfModules.Invertible.tensorPower D.subscheme.sheaf.obj
        D.subscheme.ringCatSheaf.property
        ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) (-1) ≅
      (Scheme.Modules.pullback D.subschemeι).obj (negativeTwist' D) :=
  have : Stacks.SheafOfModules.IsInvertible D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  Stacks.SheafOfModules.isoOfTensorIsoUnit D.subscheme.sheaf.obj D.subscheme.ringCatSheaf.property
    _ _ _
    (Stacks.SheafOfModules.Invertible.tensorPowerSuccIso D.subscheme.sheaf.obj
        D.subscheme.ringCatSheaf.property _ (-1) ≪≫
      Stacks.SheafOfModules.Invertible.tensorPowerReindex D.subscheme.sheaf.obj
        D.subscheme.ringCatSheaf.property _ (neg_add_cancel 1) ≪≫
      eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_zero D.subscheme.sheaf.obj
        D.subscheme.ringCatSheaf.property _))
    (pullbackNegativeTwistTensorIsoUnit D)

/-- **The triple of an effective Cartier divisor**: `(D, 𝒪_X(D)|_D, σ)` with `σ` the canonical
isomorphism `(𝒪_X(D)|_D)^{⊗ -1} ≅ i^*ℐ_D`. -/
def ofIsEffectiveCartier : VirtualNormalTriple X where
  D := D
  isLocallyPrincipal := isLocallyPrincipal_of_isEffectiveCartierDivisor D ‹_›
  N := (Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)
  σ := (pullbackDivisorSheafInverseIso D).hom
  epi_σ := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom (pullbackDivisorSheafInverseIso D))

end OfEffectiveCartier

end VirtualNormalTriple

/-! ### The Gysin map of a closed subscheme with an invertible module on it -/

section Gysin

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (D : X.IdealSheafData) (N : D.subscheme.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.sheaf.obj
    D.subscheme.ringCatSheaf.property N]

/-- The restriction `𝒩|_W` of an invertible `𝒪_D`-module to an integral closed subscheme
`W ⊆ D` is trivialized near every point. -/
theorem isTrivializedNear_pullback_inclusion (W : X.IdealSheafData) (h : D ≤ W)
    (x : W.subscheme) :
    IsTrivializedNear
      ((Scheme.Modules.pullback (Scheme.IdealSheafData.inclusion h)).obj N) x :=
  have := isInvertible_presheaf_modulePullback N (Scheme.IdealSheafData.inclusion h)
  isTrivializedNear_of_isInvertible _ x

/-- **The class `c₁(𝒩|_W) ∩ [W] ∈ A_k(W)`** for an integral closed subscheme `W ⊆ D` of
delta-dimension `k + 1`: the class of the divisor of a nonzero meromorphic section of `𝒩|_W`. -/
def virtualNormalChernClass (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : D ≤ W) :
    chowGroup C (W.subschemeι ≫ p) k :=
  letI : IsIntegral W.subscheme := hW
  letI : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  QuotientAddGroup.mk (chernComponentCycle C (W.subschemeι ≫ p) hDim
    (isTrivializedNear_pullback_inclusion D N W h)
    (exists_ne_zero_genericStalk
      (isTrivializedNear_pullback_inclusion D N W h (genericPoint W.subscheme))).choose)

/-- The class `c₁(𝒩|_W) ∩ [W]` is the class of the divisor of every nonzero meromorphic section
of `𝒩|_W` (Stacks 02SJ (2)), so it does not depend on the section chosen. -/
theorem virtualNormalChernClass_eq_mk (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : D ≤ W)
    [IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme]
    (t : ((Scheme.Modules.pullback (Scheme.IdealSheafData.inclusion h)).obj N).presheaf.stalk
      (genericPoint W.subscheme)) (ht : t ≠ 0) :
    virtualNormalChernClass C p k D N W hW hDim h =
      QuotientAddGroup.mk (chernComponentCycle C (W.subschemeι ≫ p) hDim
        (isTrivializedNear_pullback_inclusion D N W h) t) :=
  mk_chernComponentCycle_eq C (W.subschemeι ≫ p) hDim
    (isTrivializedNear_pullback_inclusion D N W h)
    (exists_ne_zero_genericStalk
      (isTrivializedNear_pullback_inclusion D N W h (genericPoint W.subscheme))).choose_spec ht

/-- The first Chern class component rule of `𝒩`: `c₁(𝒩|_W) ∩ [W]` on the integral closed
subschemes `W ⊆ X` contained in `D`, and `0` on the others. -/
def virtualNormalChernRule : FirstChernComponentClassRule C p k := fun W hW hDim =>
  open Classical in
  if h : D ≤ W then virtualNormalChernClass C p k D N W hW hDim h else 0

/-- On `W ⊆ D` the component rule of `𝒩` is `c₁(𝒩|_W) ∩ [W]`. -/
theorem virtualNormalChernRule_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : D ≤ W) :
    virtualNormalChernRule C p k D N W hW hDim = virtualNormalChernClass C p k D N W hW hDim h := by
  classical
  rw [virtualNormalChernRule, dite_eq_left h]

/-- The Gysin component cycle of Stacks 02T8, with the zero scheme abstracted into a closed
subscheme `D`, is supported over `W`. -/
theorem support_gysinComponentCycleOfIdeal_subset (chern : FirstChernComponentClassRule C p k)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    Function.support (gysinComponentCycleOfIdeal C p k chern D W hW hDim).1 ⊆
      D.subschemeι.base ⁻¹' (W.support : Set X) := by
  classical
  by_cases h : D ≤ W
  · rw [gysinComponentCycleOfIdeal, dite_eq_left h]
    refine (support_properPushforward_subset C (W.subschemeι ≫ p) (D.subschemeι ≫ p)
      (Scheme.IdealSheafData.inclusion h) (by simp) k _).trans ?_
    rintro _ ⟨w, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι,
      ← W.range_subschemeι]
    exact ⟨w, rfl⟩
  · rw [gysinComponentCycleOfIdeal, dite_eq_right h]
    refine (support_cycleAssociatedToClosedSubscheme_subset C (D.subschemeι ≫ p)
      ((W.comap D.subschemeι).subschemeι) k).trans ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact fun _ ↦ id

/-- The two integral-component rules of Remark 0B70: `[D ∩ W]_k` for `W ⊄ D` and
`i'_*(c₁(𝒩|_W) ∩ [W])` for `W ⊆ D`. -/
def virtualNormalGysinRule : IntegralComponentRule C p (D.subschemeι ≫ p) D.subschemeι k where
  cycle := gysinComponentCycleOfIdeal C p k (virtualNormalChernRule C p k D N) D
  support_subset := support_gysinComponentCycleOfIdeal_subset C p k D
    (virtualNormalChernRule C p k D N)

/-- The Gysin map `i^* : Z_{k+1}(X) ⟶ A_k(D)` of a closed subscheme `D ⊆ X` with an invertible
`𝒪_D`-module `𝒩`, by the rules of Definition 02T8 with `𝒩` in place of `ℒ|_D`. -/
def virtualNormalGysinOfIdeal : CycleGroup C p (k + 1) →+ chowGroup C (D.subschemeι ≫ p) k :=
  (virtualNormalGysinRule C p k D N).extendChow

/-- The Gysin map of `(D, 𝒩)` sends `[W]` to the class of the Gysin component cycle of `W`. -/
private theorem virtualNormalGysinOfIdeal_apply_cycle (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    virtualNormalGysinOfIdeal C p k D N
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk (gysinComponentCycleOfIdeal C p k
        (virtualNormalChernRule C p k D N) D W hW hDim) := by
  classical
  change QuotientAddGroup.mk
    ((virtualNormalGysinRule C p k D N).extendCycleGroup
      (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) = _
  rw [(virtualNormalGysinRule C p k D N).extendCycleGroup_cycleAssociatedToClosedSubscheme
    W hW hDim]
  rfl

/-- For `W ⊄ D`, `i^*[W] = [D ∩ W]_k`. -/
theorem virtualNormalGysinOfIdeal_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : ¬ D ≤ W) :
    virtualNormalGysinOfIdeal C p k D N
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
          ((W.comap D.subschemeι).subschemeι) k) := by
  rw [virtualNormalGysinOfIdeal_apply_cycle C p k D N W hW hDim]
  rw [gysinComponentCycleOfIdeal, dite_eq_right h]

/-- For `W ⊆ D`, `i^*[W] = i'_*(c₁(𝒩|_W) ∩ [W])`. -/
theorem virtualNormalGysinOfIdeal_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : D ≤ W) :
    virtualNormalGysinOfIdeal C p k D N
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      properChowPushforward C (W.subschemeι ≫ p) (D.subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h) (by simp) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Scheme.IdealSheafData.inclusion h) C (W.subschemeι ≫ p) (D.subschemeι ≫ p)
          (by simp) k)
        (virtualNormalChernClass C p k D N W hW hDim h) := by
  rw [virtualNormalGysinOfIdeal_apply_cycle C p k D N W hW hDim]
  rw [gysinComponentCycleOfIdeal, dite_eq_left h,
    virtualNormalChernRule_of_le C p k D N W hW hDim h]
  conv_rhs => rw [← Quotient.out_eq (virtualNormalChernClass C p k D N W hW hDim h)]
  rfl

/-- The locally finite component formula for the Gysin map of `(D, 𝒩)`. -/
theorem virtualNormalGysinOfIdeal_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X))) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C (D.subschemeι ≫ p) k,
      virtualNormalGysinOfIdeal C p k D N α = QuotientAddGroup.mk β ∧
      ∀ x : D.subscheme, β.1 x = ∑ᶠ j : J, n j *
        (gysinComponentCycleOfIdeal C p k (virtualNormalChernRule C p k D N) D
          (W j) (hW j) (hDim j)).1 x :=
  ⟨(virtualNormalGysinRule C p k D N).extendCycleGroup α, rfl,
    (virtualNormalGysinRule C p k D N).extendCycleGroup_apply_of_presentation W hW hDim hLocal n
      α hα⟩

/-! ### Comparison with Definition 02T8 -/

/-- If `𝒩 ≅ ℒ|_D`, the class `c₁(𝒩|_W) ∩ [W]` is the first Chern class component of `ℒ`. -/
theorem virtualNormalChernClass_eq_firstChernComponentClass (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (ψ : N ≅ (Scheme.Modules.pullback D.subschemeι).obj L)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : D ≤ W) :
    virtualNormalChernClass C p k D N W hW hDim h = firstChernComponentClass C p k L W hW hDim := by
  let : IsIntegral W.subscheme := hW
  let : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have hL : ∀ x : W.subscheme,
      IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x :=
    have := isInvertible_presheaf_modulePullback L W.subschemeι
    isTrivializedNear_of_isInvertible _
  let φ : (Scheme.Modules.pullback (Scheme.IdealSheafData.inclusion h)).obj N ≅
      (Scheme.Modules.pullback W.subschemeι).obj L :=
    (Scheme.Modules.pullback (Scheme.IdealSheafData.inclusion h)).mapIso ψ ≪≫
      (Scheme.Modules.pullbackComp (Scheme.IdealSheafData.inclusion h) D.subschemeι).app L ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).app L
  exact mk_chernComponentCycle_eq_of_moduleIso C (W.subschemeι ≫ p) hDim φ
    (isTrivializedNear_pullback_inclusion D N W h) hL
    (exists_ne_zero_genericStalk
      (isTrivializedNear_pullback_inclusion D N W h (genericPoint W.subscheme))).choose_spec
    (exists_ne_zero_genericStalk (hL _)).choose_spec

/-- **The construction generalizes Definition 02T8.** For the zero scheme `D = Z(s)` of a section
`s` of an invertible module `ℒ`, and any invertible `𝒪_D`-module `𝒩 ≅ ℒ|_D`, the Gysin map of
`(D, 𝒩)` is the Gysin map of Definition 02T8. -/
@[stacks 0B70 "the construction generalizes Definition 02T8: for D = Z(s) and N isomorphic to \
the restriction of L the two Gysin maps are equal"]
theorem virtualNormalGysinOfIdeal_zeroScheme (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (N : (Stacks.Divisors.zeroScheme X L s).subscheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property N]
    (ψ : N ≅ (Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L) :
    virtualNormalGysinOfIdeal C p k (Stacks.Divisors.zeroScheme X L s) N =
      gysinHomomorphismOfInvertible C p k L s := by
  have hcyc : gysinComponentCycleOfIdeal C p k
      (virtualNormalChernRule C p k (Stacks.Divisors.zeroScheme X L s) N)
      (Stacks.Divisors.zeroScheme X L s) =
      gysinComponentCycle C p k L s (firstChernComponentClass C p k L) := by
    rw [gysinComponentCycle_eq_ofIdeal]
    funext W hW hDim
    classical
    by_cases h : Stacks.Divisors.zeroScheme X L s ≤ W
    · rw [gysinComponentCycleOfIdeal, gysinComponentCycleOfIdeal, dite_eq_left h, dite_eq_left h,
        virtualNormalChernRule_of_le C p k _ N W hW hDim h,
        virtualNormalChernClass_eq_firstChernComponentClass C p k _ N L ψ W hW hDim h]
    · rw [gysinComponentCycleOfIdeal, gysinComponentCycleOfIdeal, dite_eq_right h, dite_eq_right h]
  have hrule : virtualNormalGysinRule C p k (Stacks.Divisors.zeroScheme X L s) N =
      gysinRule C p k L s (firstChernComponentClass C p k L) := by
    unfold virtualNormalGysinRule gysinRule
    congr 1
  exact congrArg IntegralComponentRule.extendChow hrule

/-- The comparison with Definition 02T8 along an equality `Z(s) = D`, as a heterogeneous
equality (the targets `A_k(Z(s))` and `A_k(D)` are equal types only after rewriting). -/
theorem virtualNormalGysinOfIdeal_heq_of_zeroScheme_eq (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hz : Stacks.Divisors.zeroScheme X L s = D)
    (ψ : N ≅ (Scheme.Modules.pullback D.subschemeι).obj L) :
    HEq (virtualNormalGysinOfIdeal C p k D N) (gysinHomomorphismOfInvertible C p k L s) := by
  subst hz
  exact heq_of_eq (virtualNormalGysinOfIdeal_zeroScheme C p k L s N ψ)

end Gysin

/-! ### The Gysin map of a triple -/

namespace VirtualNormalTriple

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (T : VirtualNormalTriple X)

/-- **Remark 0B70.** The Gysin homomorphism `i^* : Z_{k+1}(X) ⟶ A_k(D)` of a triple
`(D, 𝒩, σ)`. -/
@[stacks 0B70 "the Gysin homomorphism i^* from (k+1)-cycles on X to CH_k(D) of a triple"]
def gysin : CycleGroup C p (k + 1) →+ chowGroup C (T.D.subschemeι ≫ p) k :=
  virtualNormalGysinOfIdeal C p k T.D T.N

/-- **Remark 0B70, rule (1)(a) of Definition 02T8 for a triple.** For an integral closed
subscheme `W ⊆ X` of delta-dimension `k + 1` with `W ⊄ D`, `i^*[W] = [D ∩ W]_k`. -/
@[stacks 0B70 "rule (1)(a) of Definition 02T8 for a triple: W not contained in D"]
theorem gysin_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : ¬ T.D ≤ W) :
    T.gysin C p k (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C (T.D.subschemeι ≫ p)
          ((W.comap T.D.subschemeι).subschemeι) k) :=
  virtualNormalGysinOfIdeal_of_not_le C p k T.D T.N W hW hDim h

/-- **Remark 0B70, rule (1)(b) of Definition 02T8 for a triple.** For an integral closed
subscheme `W ⊆ D` of delta-dimension `k + 1`, `i^*[W] = i'_*(c₁(𝒩|_W) ∩ [W])`, where
`i' : W ⟶ D` is the induced closed immersion. -/
@[stacks 0B70 "rule (1)(b) of Definition 02T8 for a triple: W contained in D, with c_1(N|_W)"]
theorem gysin_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (h : T.D ≤ W) :
    T.gysin C p k (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      properChowPushforward C (W.subschemeι ≫ p) (T.D.subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h) (by simp) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Scheme.IdealSheafData.inclusion h) C (W.subschemeι ≫ p) (T.D.subschemeι ≫ p)
          (by simp) k)
        (virtualNormalChernClass C p k T.D T.N W hW hDim h) :=
  virtualNormalGysinOfIdeal_of_le C p k T.D T.N W hW hDim h

/-- **Remark 0B70, rule (2) of Definition 02T8 for a triple.** For `α = ∑ n_j [W_j]` locally
finite, `i^*α = ∑ n_j i^*[W_j]`. -/
@[stacks 0B70 "rule (2) of Definition 02T8 for a triple: locally finite sums"]
theorem gysin_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X))) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C (T.D.subschemeι ≫ p) k,
      T.gysin C p k α = QuotientAddGroup.mk β ∧
      ∀ x : T.D.subscheme, β.1 x = ∑ᶠ j : J, n j *
        (gysinComponentCycleOfIdeal C p k (virtualNormalChernRule C p k T.D T.N) T.D
          (W j) (hW j) (hDim j)).1 x :=
  virtualNormalGysinOfIdeal_finsum C p k T.D T.N W hW hDim hLocal n α hα

/-- **The footnote of Remark 0B70.** If `D` is an effective Cartier divisor, then
`𝒩 ≅ 𝒪_X(D)|_D`. -/
@[stacks 0B70 "footnote: if D is an effective Cartier divisor, then N is isomorphic to the \
restriction of O_X(D) to D"]
theorem nonempty_normalIso_of_isEffectiveCartier (hD : IsEffectiveCartierDivisor T.D) :
    Nonempty (T.N ≅ (Scheme.Modules.pullback T.D.subschemeι).obj (divisorSheaf T.D)) :=
  have := hD
  ⟨T.normalIsoOfIsEffectiveCartier⟩

/-- **Remark 0B70: the construction generalizes Definition 02T8.** If `D = Z(s)` for a global
section `s` of an invertible `𝒪_X`-module `ℒ` and `𝒩 ≅ ℒ|_D`, the Gysin map of the triple is the
Gysin map of Definition 02T8 of `(ℒ, s)`. -/
@[stacks 0B70 "the construction generalizes Definition 02T8: agreement when D = Z(s) and N is \
the restriction of L"]
theorem gysin_heq_of_zeroScheme_eq (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hz : Stacks.Divisors.zeroScheme X L s = T.D)
    (ψ : T.N ≅ (Scheme.Modules.pullback T.D.subschemeι).obj L) :
    HEq (T.gysin C p k) (gysinHomomorphismOfInvertible C p k L s) :=
  virtualNormalGysinOfIdeal_heq_of_zeroScheme_eq C p k T.D T.N L s hz ψ

/-- **Remark 0B70 at an effective Cartier divisor.** If `D` is an effective Cartier divisor (so
that `𝒩 ≅ 𝒪_X(D)|_D` by the footnote), the Gysin map of the triple is the Gysin map of
Definition 02T8 of `(𝒪_X(D), 1_D)`, whose zero scheme is `D`. -/
@[stacks 0B70 "agreement with Definition 02T8 when D is an effective Cartier divisor"]
theorem gysin_heq_divisorSheaf (hD : IsEffectiveCartierDivisor T.D) :
    HEq (T.gysin C p k)
      (gysinHomomorphismOfInvertible C p k (divisorSheaf T.D) (divisorSheafGlobalSection T.D)) :=
  have := hD
  T.gysin_heq_of_zeroScheme_eq C p k (divisorSheaf T.D) (divisorSheafGlobalSection T.D)
    (zeroScheme_canonicalSection T.D) T.normalIsoOfIsEffectiveCartier

end VirtualNormalTriple

/-- Two heterogeneously equal homomorphisms from cycles to Chow groups of two equal closed
subschemes agree after pushforward along the identification of the subschemes. -/
theorem chowPushforwardOfIso_eqToHom_cycleGroupHom_apply_of_heq (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {D D' : X.IdealSheafData}
    (hD : D = D')
    {F : CycleGroup C p (k + 1) →+ chowGroup C (D.subschemeι ≫ p) k}
    {G : CycleGroup C p (k + 1) →+ chowGroup C (D'.subschemeι ≫ p) k} (hFG : HEq F G)
    (α : CycleGroup C p (k + 1)) :
    chowPushforwardOfIso C (D.subschemeι ≫ p) (D'.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD))
        (by rw [← Category.assoc, eqToHom_subscheme_comp_subschemeι _ _ hD]) k (F α) = G α := by
  subst hD
  cases hFG
  exact chowPushforwardOfIso_id C (D.subschemeι ≫ p) k (F α)

namespace VirtualNormalTriple

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (T : VirtualNormalTriple X)

/-- **Remark 0B70 at an effective Cartier divisor**, as an identity of Chow classes: the Gysin
map of Definition 02T8 of `(𝒪_X(D), 1_D)`, transported along `Z(1_D) = D`, is the Gysin map of
the triple. -/
@[stacks 0B70 "agreement with Definition 02T8 when D is an effective Cartier divisor, as an \
identity of Chow classes"]
theorem chowPushforwardOfIso_gysinHomomorphismOfInvertible_divisorSheaf
    (hD : IsEffectiveCartierDivisor T.D) (α : CycleGroup C p (k + 1)) :
    chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme X (divisorSheaf T.D)
          (divisorSheafGlobalSection T.D)).subschemeι ≫ p) (T.D.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (@zeroScheme_canonicalSection X T.D hD)))
        (by rw [← Category.assoc, eqToHom_subscheme_comp_subschemeι _ _
          (@zeroScheme_canonicalSection X T.D hD)]) k
        (@gysinHomomorphismOfInvertible C X p _ k (divisorSheaf T.D)
          (@isInvertible_divisorSheaf X T.D hD) (divisorSheafGlobalSection T.D) α) =
      T.gysin C p k α :=
  chowPushforwardOfIso_eqToHom_cycleGroupHom_apply_of_heq C p k
    (@zeroScheme_canonicalSection X T.D hD) (T.gysin_heq_divisorSheaf C p k hD).symm α

end VirtualNormalTriple

/-- **Remark 0B70**, all of its assertions together. Let `X` be locally of finite type over the
base of a Chow situation (Situation 02QL) and let `(D, 𝒩, σ)` be a triple: `D` a locally
principal closed subscheme, `𝒩` an invertible `𝒪_D`-module and `σ : 𝒩^{⊗ -1} ⟶ i^*ℐ_D` a
surjection. Then:
* (footnote) if `D` is an effective Cartier divisor, `𝒩 ≅ 𝒪_X(D)|_D`, and every effective Cartier
  divisor carries such a triple;
* the Gysin homomorphism `i^* : Z_{k+1}(X) ⟶ A_k(D)` of the triple obeys the rules of
  Definition 02T8 with `𝒩` in place of `ℒ|_D`: `i^*[W] = [D ∩ W]_k` for `W ⊄ D`,
  `i^*[W] = i'_*(c₁(𝒩|_W) ∩ [W])` for `W ⊆ D`, and `i^*(∑ n_j [W_j]) = ∑ n_j i^*[W_j]`;
* it generalizes Definition 02T8: for `D = Z(s)` and `𝒩 ≅ ℒ|_D` it is the Gysin map of `(ℒ, s)`,
  and for `D` an effective Cartier divisor it is the Gysin map of `(𝒪_X(D), 1_D)`. -/
@[stacks 0B70 "the whole remark: the footnote, the Gysin homomorphism of a triple with the rules \
of Definition 02T8, and its agreement with Definition 02T8"]
theorem virtualNormalTriple_remark (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] :
    (∀ T : VirtualNormalTriple X, IsEffectiveCartierDivisor T.D →
      Nonempty (T.N ≅ (Scheme.Modules.pullback T.D.subschemeι).obj (divisorSheaf T.D))) ∧
    (∀ D : X.IdealSheafData, IsEffectiveCartierDivisor D →
      ∃ T : VirtualNormalTriple X, T.D = D) ∧
    (∀ (k : ℤ) (T : VirtualNormalTriple X) (W : X.IdealSheafData), IsIntegral W.subscheme →
      schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) →
      ¬ T.D ≤ W →
      T.gysin C p k (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
        QuotientAddGroup.mk
          (cycleAssociatedToClosedSubscheme C (T.D.subschemeι ≫ p)
            ((W.comap T.D.subschemeι).subschemeι) k)) ∧
    (∀ (k : ℤ) (T : VirtualNormalTriple X) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
      (h : T.D ≤ W),
      T.gysin C p k (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
        properChowPushforward C (W.subschemeι ≫ p) (T.D.subschemeι ≫ p)
          (Scheme.IdealSheafData.inclusion h) (by simp) k
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (Scheme.IdealSheafData.inclusion h) C (W.subschemeι ≫ p) (T.D.subschemeι ≫ p)
            (by simp) k)
          (virtualNormalChernClass C p k T.D T.N W hW hDim h)) ∧
    (∀ (k : ℤ) (T : VirtualNormalTriple X) {J : Type u} (W : J → X.IdealSheafData)
      (hW : ∀ j, IsIntegral (W j).subscheme)
      (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      LocallyFinite (fun j ↦ ((W j).support : Set X)) → ∀ (n : J → ℤ)
      (α : CycleGroup C p (k + 1)),
      (∀ x : X, α.1 x = ∑ᶠ j : J, n j *
        (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) →
      ∃ β : CycleGroup C (T.D.subschemeι ≫ p) k,
        T.gysin C p k α = QuotientAddGroup.mk β ∧
        ∀ x : T.D.subscheme, β.1 x = ∑ᶠ j : J, n j *
          (gysinComponentCycleOfIdeal C p k (virtualNormalChernRule C p k T.D T.N) T.D
            (W j) (hW j) (hDim j)).1 x) ∧
    (∀ (k : ℤ) (T : VirtualNormalTriple X) (L : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
      (s : Γ(L, ⊤)), Stacks.Divisors.zeroScheme X L s = T.D →
      (T.N ≅ (Scheme.Modules.pullback T.D.subschemeι).obj L) →
      HEq (T.gysin C p k) (gysinHomomorphismOfInvertible C p k L s)) ∧
    (∀ (k : ℤ) (T : VirtualNormalTriple X) [IsEffectiveCartierDivisor T.D],
      HEq (T.gysin C p k)
        (gysinHomomorphismOfInvertible C p k (divisorSheaf T.D)
          (divisorSheafGlobalSection T.D))) :=
  ⟨fun T hD => T.nonempty_normalIso_of_isEffectiveCartier hD,
    fun D hD => ⟨@VirtualNormalTriple.ofIsEffectiveCartier X D hD, rfl⟩,
    fun k T W hW hDim h => T.gysin_of_not_le C p k W hW hDim h,
    fun k T W hW hDim h => T.gysin_of_le C p k W hW hDim h,
    fun k T _ W hW hDim hLocal n α hα => T.gysin_finsum C p k W hW hDim hLocal n α hα,
    fun k T L _ s hz ψ => T.gysin_heq_of_zeroScheme_eq C p k L s hz ψ,
    fun k T _ => T.gysin_heq_divisorSheaf C p k ‹_›⟩

end Stacks.Chow

end
