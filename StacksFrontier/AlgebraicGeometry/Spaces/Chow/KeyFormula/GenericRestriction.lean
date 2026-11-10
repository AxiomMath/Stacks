module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldValueSemilinear
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.RegularMeromorphicSectionMultiples
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular

/-!
# The restriction `s_ξ|_Z` of the generator at the generic point of a prime divisor

Let `X` be a decent, locally Noetherian algebraic space over a scheme `S`, let `Z ⊂ X` be a prime
divisor with generic point `ξ`, let `(U, u)` be the chosen affine elementary étale neighbourhood
of `ξ`, and let `ℒ` be an invertible `𝒪_X`-module with the chosen generator `s_ξ` of its pullback
to `Spec 𝒪_{U, u}`.  Section 0EQU of the Stacks project uses "the image of `s_ξ` in the fibre
`ℒ_ξ ⊗ κ(ξ)`, a nonzero meromorphic section of `ℒ|_Z`, denoted `s_ξ|_Z`".  This file constructs
that meromorphic section.

The value at the generic point of `Z`
(`AlgebraicGeometry.Space.PrimeDivisor.genericFieldValue`) reads a meromorphic section `σ` of
`ℒ|_Z` by pulling it back along `ρ_Z : Spec κ(u) → Z` and comparing with the image of `s_ξ`
there.  It is **bijective** onto `κ(u)`: every meromorphic section of `ℒ|_Z` is `g · t` for a
fixed regular section `t` and a unique rational function `g` of `Z` (Stacks 0EPQ, 0EPT and the
identification `R(Z) = Γ(Z, 𝒦_Z)` of Stacks 0ENA), the value of `g · t` is
`θ_Z⁻¹(g) · value(t)`, and `value(t) ≠ 0` because the pullback of a regular section is regular
(Stacks 0ENC, part (2)).  So for every `c ∈ κ(u)` there is exactly one meromorphic section of
`ℒ|_Z` whose pullback along `ρ_Z` is `c` times the image of `s_ξ`; for `c = 1` this is
`s_ξ|_Z`, and in general it is `θ_Z(c) · s_ξ|_Z`.  The change of generator of the key formula,
from `s_ξ` to `v · s_ξ` for a unit `v` of `𝒪^h_{X, ξ}`, is the case `c = v̄`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericRestrictionOf`: the meromorphic section of
  `ℒ|_Z` whose value at the generic point is a given `c ∈ κ(u)`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericRestriction`: **`σ_Z = s_ξ|_Z`**, the case
  `c = 1`.
* `AlgebraicGeometry.Space.PrimeDivisor.henselianUnitRestriction`: the restriction of `v · s_ξ`
  for a unit `v` of `𝒪^h_{X, ξ}`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.bijective_genericFieldValue`: the value at the generic
  point is a bijection from the meromorphic sections of `ℒ|_Z` onto `κ(u)`.
* `AlgebraicGeometry.Space.PrimeDivisor.existsUnique_pullback_eq_genericFibreGenerator`:
  existence and uniqueness of `s_ξ|_Z` as the meromorphic section of `ℒ|_Z` whose pullback along
  `ρ_Z` is the image of `s_ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.isRegularMeromorphicSection_genericRestriction`: `s_ξ|_Z`
  is a regular meromorphic section.
* `AlgebraicGeometry.Space.PrimeDivisor.genericRestrictionOf_eq_smul`: the section with value `c`
  is `θ_Z(c) · s_ξ|_Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.henselianUnitRestriction_eq_smul`: the restriction of
  `v · s_ξ` is `θ(v̄) · s_ξ|_Z`, with `θ : κ(𝒪^h_{X, ξ}) ≃+* R(Z)`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN0](https://stacks.math.columbia.edu/tag/0EN0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-! ### A regular meromorphic section of `ℒ|_Z` has nonzero value -/

include hL in
/-- The restriction `ℒ|_Z` of an invertible module is invertible, by Stacks 0B8P. -/
theorem PrimeDivisor.isInvertibleModule_restrictModule :
    IsInvertibleModule (Z.space B S hS) (Z.restrictModule B S hS hX L) :=
  modulePullbackInvertible (Z.inclusion B S hS hX) L hL

include hN hL in
/-- **`ℒ|_Z` has a regular meromorphic section**, by Stacks 0EPQ on the integral, locally
Noetherian prime divisor. -/
theorem PrimeDivisor.exists_isRegularMeromorphicSection_restrictModule :
    ∃ t : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
        (Z.restrictModule B S hS hX L),
      IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
        (Z.restrictModule B S hS hX L) t :=
  exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints Z.closed.1
    (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_space B S hS)
    (Z.hasLocallyFiniteIrreducibleComponents_space B S hS hX hN)
    (Z.hasMonomorphicCodimensionZeroPoints_space B S hS) _
    (Z.isInvertibleModule_restrictModule B S hS hX L hL)

/-- The meromorphic functions on `Spec κ(u)` form a nontrivial ring, being a copy of `κ(u)`. -/
theorem PrimeDivisor.nontrivial_genericFieldMeromorphic :
    Nontrivial ((meromorphicFunctionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericFieldSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericFieldChart B S hS hX hdec))) :=
  (Z.genericFieldMeromorphicEquiv B S hS hX hdec).toEquiv.symm.nontrivial

/-- **A regular meromorphic section of `ℒ|_Z` has nonzero value at the generic point**: its
pullback along `ρ_Z` is regular by Stacks 0ENC, part (2), hence nonzero, the meromorphic
functions on `Spec κ(u)` forming a field. -/
theorem PrimeDivisor.genericFieldValue_ne_zero_of_isRegular
    (t : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L))
    (ht : IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) t) :
    Z.genericFieldValue B S hS hX hdec L hL t ≠ 0 := by
  intro h0
  have hreg := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS
    (Z.genericFieldMorphism B S hS hX hdec)
    (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec)
    (Z.restrictModule B S hS hX L)
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (Z.isInvertibleModule_restrictModule B S hS hX L hL)) t ht
    (Z.genericFieldChart B S hS hX hdec)
  have hspec := Z.genericFieldValue_spec B S hS hX hdec L hL t
  rw [h0, map_zero] at hspec
  have hsmul : ∀ r : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).O).obj.obj
          (op (Z.genericFieldChart B S hS hX hdec)),
      r • (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.restrictModule B S hS hX L)
        (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) t).eval
          (op (Z.genericFieldChart B S hS hX hdec)) =
        (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.restrictModule B S hS hX L)
        (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) t).eval
          (op (Z.genericFieldChart B S hS hX hdec)) := by
    intro r
    refine (congrArg (r • ·) hspec).trans ?_
    refine (toMeromorphicSectionSheaf_smul B S hS _ _ _ _ _ _).symm.trans ?_
    refine Eq.trans ?_ hspec.symm
    refine congrArg _ ((meromorphicSectionModule_smul_tmul B S hS _ _ _ _ _ _ _ _ rfl).trans ?_)
    exact congrArg (· ⊗ₜ _) (mul_zero r)
  have : Nontrivial ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS (Z.genericFieldSpace B S hS hX hdec).1
        (Z.genericFieldSpace B S hS hX hdec).2).O).obj.obj
          (op (Z.genericFieldChart B S hS hX hdec))) :=
    Z.nontrivial_genericFieldMeromorphic B S hS hX hdec
  exact one_ne_zero (hreg ((hsmul 1).trans (hsmul 0).symm))

/-! ### The value at the generic point is bijective -/

/-- A chosen regular meromorphic section of `ℒ|_Z`. -/
def PrimeDivisor.restrictModuleRegularSection :
    MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) :=
  (Z.exists_isRegularMeromorphicSection_restrictModule B S hS hX hN L hL).choose

/-- The chosen section `PrimeDivisor.restrictModuleRegularSection` of `ℒ|_Z` is regular. -/
theorem PrimeDivisor.isRegular_restrictModuleRegularSection :
    IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) (Z.restrictModuleRegularSection B S hS hX hN L hL) :=
  (Z.exists_isRegularMeromorphicSection_restrictModule B S hS hX hN L hL).choose_spec

include hN hL in
/-- **Every meromorphic section of `ℒ|_Z` is a unique rational multiple of a regular one**, the
rational functions of `Z` acting through `R(Z) = Γ(Z, 𝒦_Z)`. -/
theorem PrimeDivisor.existsUnique_functionField_smul_eq
    (t : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L))
    (ht : IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) t)
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    ∃! x : rationalFunctions B S hS Z.closed.1,
      σ = Z.functionFieldToMeromorphic B S hS hX hN x • t := by
  obtain ⟨a, ha, hu⟩ := existsUnique_smul_eq_of_isRegularMeromorphicSection B S hS Z.closed.1
    Z.integral (Z.hasEtaleLocalProperty_isLocallyNoetherian_subspace B S hS hX hN) _
    (Z.isInvertibleModule_restrictModule B S hS hX L hL) t ht σ
  obtain ⟨x, rfl⟩ := (Z.bijective_functionFieldToMeromorphic B S hS hX hN).2 a
  exact ⟨x, ha, fun y hy => (Z.bijective_functionFieldToMeromorphic B S hS hX hN).1 (hu _ hy)⟩

include hN in
/-- **The value at the generic point of `Z` is a bijection** from the meromorphic sections of
`ℒ|_Z` onto `κ(u)`. -/
theorem PrimeDivisor.bijective_genericFieldValue :
    Function.Bijective (Z.genericFieldValue B S hS hX hdec L hL) := by
  set t := Z.restrictModuleRegularSection B S hS hX hN L hL
  have ht := Z.isRegular_restrictModuleRegularSection B S hS hX hN L hL
  have ht0 := Z.genericFieldValue_ne_zero_of_isRegular B S hS hX hdec L hL t ht
  refine ⟨fun σ σ' h => ?_, fun c => ?_⟩
  · obtain ⟨x, hx, -⟩ := Z.existsUnique_functionField_smul_eq B S hS hX hN L hL t ht σ
    obtain ⟨x', hx', -⟩ := Z.existsUnique_functionField_smul_eq B S hS hX hN L hL t ht σ'
    simp only [hx, hx', Z.genericFieldValue_functionField_smul B S hS hX hdec hN] at h
    rw [hx, hx', (Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm.injective
      (mul_right_cancel₀ ht0 h)]
  · refine ⟨Z.functionFieldToMeromorphic B S hS hX hN
      (Z.genericResidueFieldEquivFunctionField B S hS hX hdec
        (c * (Z.genericFieldValue B S hS hX hdec L hL t)⁻¹)) • t, ?_⟩
    rw [Z.genericFieldValue_functionField_smul B S hS hX hdec hN, RingEquiv.symm_apply_apply,
      mul_assoc, inv_mul_cancel₀ ht0, mul_one]

/-! ### The sections `θ_Z(c) · s_ξ|_Z` and `s_ξ|_Z` -/

/-- **The meromorphic section of `ℒ|_Z` with value `c` at the generic point**: the unique one
whose pullback along `ρ_Z : Spec κ(u) → Z` is `c` times the image of the generator `s_ξ` in the
fibre.  It is `θ_Z(c) · s_ξ|_Z`, by
`AlgebraicGeometry.Space.PrimeDivisor.genericRestrictionOf_eq_smul`. -/
def PrimeDivisor.genericRestrictionOf (c : Z.genericResidueField B S hS hX hdec) :
    MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) :=
  (Equiv.ofBijective _ (Z.bijective_genericFieldValue B S hS hX hdec hN L hL)).symm c

/-- The value of the section with value `c` is `c`. -/
theorem PrimeDivisor.genericFieldValue_genericRestrictionOf
    (c : Z.genericResidueField B S hS hX hdec) :
    Z.genericFieldValue B S hS hX hdec L hL (Z.genericRestrictionOf B S hS hX hdec hN L hL c) =
      c :=
  (Equiv.ofBijective _ (Z.bijective_genericFieldValue B S hS hX hdec hN L hL)).apply_symm_apply c

/-- A meromorphic section of `ℒ|_Z` is the section with value its value. -/
theorem PrimeDivisor.genericRestrictionOf_genericFieldValue
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    Z.genericRestrictionOf B S hS hX hdec hN L hL (Z.genericFieldValue B S hS hX hdec L hL σ) =
      σ :=
  (Equiv.ofBijective _ (Z.bijective_genericFieldValue B S hS hX hdec hN L hL)).symm_apply_apply σ

/-- **The characterization of the section with value `c`**: a meromorphic section of `ℒ|_Z` is
it exactly when its pullback along `ρ_Z` is `c` times the image of the generator `s_ξ`. -/
theorem PrimeDivisor.eq_genericRestrictionOf_iff (c : Z.genericResidueField B S hS hX hdec)
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    σ = Z.genericRestrictionOf B S hS hX hdec hN L hL c ↔
      (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.restrictModule B S hS hX L)
          (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
          (op (Z.genericFieldChart B S hS hX hdec)) =
        toMeromorphicSectionSheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2
          ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
            (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
          (Z.genericFieldMeromorphicEquiv B S hS hX hdec c ⊗ₜ[chartRing B S hS
              (Z.genericFieldSpace B S hS hX hdec).1 (Z.genericFieldSpace B S hS hX hdec).2
              (Z.genericFieldChart B S hS hX hdec)]
            Z.genericFieldGenerator B S hS hX hdec L hL (Z.genericFieldChart B S hS hX hdec)
              (𝟙 (Z.genericFieldChart B S hS hX hdec)) :
            (meromorphicSectionModule B S hS (Z.genericFieldSpace B S hS hX hdec).1
              (Z.genericFieldSpace B S hS hX hdec).2
              ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
                (Z.restrictModule B S hS hX L))).obj
                  (op (Z.genericFieldChart B S hS hX hdec))) := by
  rw [← Z.genericFieldValue_eq_iff B S hS hX hdec L hL]
  constructor
  · rintro rfl
    exact Z.genericFieldValue_genericRestrictionOf B S hS hX hdec hN L hL c
  · rintro rfl
    exact (Z.genericRestrictionOf_genericFieldValue B S hS hX hdec hN L hL σ).symm

/-- **`σ_Z = s_ξ|_Z`, the restriction to a prime divisor of the generator at its generic point**:
the unique meromorphic section of `ℒ|_Z` whose pullback along `ρ_Z : Spec κ(u) → Z` is the image
of the generator `s_ξ` of `ℒ` at the generic point. -/
@[stacks 0EQU "the image s_ξ|_Z of a generator s_ξ of ℒ_ξ in the fibre at the generic point, as \
  a meromorphic section of ℒ|_Z"]
def PrimeDivisor.genericRestriction :
    MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) :=
  Z.genericRestrictionOf B S hS hX hdec hN L hL 1

include hN in
/-- **Existence and uniqueness of `s_ξ|_Z`**: there is exactly one meromorphic section of `ℒ|_Z`
whose pullback along `ρ_Z` is the image of `s_ξ` in the fibre, and it is
`AlgebraicGeometry.Space.PrimeDivisor.genericRestriction`. -/
theorem PrimeDivisor.existsUnique_pullback_eq_genericFibreGenerator :
    ∃! σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
        (Z.restrictModule B S hS hX L),
      (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.restrictModule B S hS hX L)
          (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
          (op (Z.genericFieldChart B S hS hX hdec)) =
        toMeromorphicSectionValue B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2
          ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
            (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
          (Z.genericFibreGenerator B S hS hX hdec L hL) := by
  have key := Z.eq_genericRestrictionOf_iff B S hS hX hdec hN L hL 1
  simp only [map_one, Z.genericFieldGenerator_id B S hS hX hdec L hL] at key
  exact ⟨_, (key _).1 rfl, fun σ hσ => (key σ).2 hσ⟩

/-- `s_ξ|_Z` has value `1` at the generic point. -/
theorem PrimeDivisor.genericFieldValue_genericRestriction :
    Z.genericFieldValue B S hS hX hdec L hL (Z.genericRestriction B S hS hX hdec hN L hL) = 1 :=
  Z.genericFieldValue_genericRestrictionOf B S hS hX hdec hN L hL 1

/-- **The section with value `c` is `θ_Z(c) · s_ξ|_Z`**: the semilinear map
`c ↦ θ_Z(c) · s_ξ|_Z` from `κ(u)` to the meromorphic sections of `ℒ|_Z`, which is the reading of
the restriction of `u · s_ξ` for a unit `u` of `𝒪_{U, u}` with residue `c`. -/
theorem PrimeDivisor.genericRestrictionOf_eq_smul (c : Z.genericResidueField B S hS hX hdec) :
    Z.genericRestrictionOf B S hS hX hdec hN L hL c =
      Z.functionFieldToMeromorphic B S hS hX hN
          (Z.genericResidueFieldEquivFunctionField B S hS hX hdec c) •
        Z.genericRestriction B S hS hX hdec hN L hL := by
  refine ((Z.bijective_genericFieldValue B S hS hX hdec hN L hL).1 ?_).symm
  rw [Z.genericFieldValue_functionField_smul B S hS hX hdec hN, RingEquiv.symm_apply_apply,
    Z.genericFieldValue_genericRestriction, mul_one,
    Z.genericFieldValue_genericRestrictionOf]

/-- **A rational multiple of `s_ξ|_Z` is the section with value `θ_Z⁻¹` of the multiplier.** -/
theorem PrimeDivisor.functionField_smul_genericRestriction
    (x : rationalFunctions B S hS Z.closed.1) :
    Z.functionFieldToMeromorphic B S hS hX hN x • Z.genericRestriction B S hS hX hdec hN L hL =
      Z.genericRestrictionOf B S hS hX hdec hN L hL
        ((Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm x) := by
  rw [Z.genericRestrictionOf_eq_smul, RingEquiv.apply_symm_apply]

/-! ### Regularity -/

include hN in
/-- **A nonzero global meromorphic multiple of a regular meromorphic section is regular**: the
multiplier is a unit of the field of global meromorphic functions. -/
theorem PrimeDivisor.isRegularMeromorphicSection_smul
    (a : ↥(RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS Z.subspace.toFunctor Z.closed.1).O).obj)))
    (ha : a ≠ 0)
    (t : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L))
    (ht : IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) t) :
    IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) (a • t) := by
  obtain ⟨b, hb⟩ := (isField_globalMeromorphicFunctions B S hS Z.closed.1 Z.integral
    (Z.hasEtaleLocalProperty_isLocallyNoetherian_subspace B S hS hX hN)).mul_inv_cancel ha
  intro V r r' h
  have h' : (r * a.1 (op V)) • t.eval (op V) = (r' * a.1 (op V)) • t.eval (op V) := by
    rw [mul_smul, mul_smul]
    exact h
  have h'' := congrArg (· * b.1 (op V)) (ht V h')
  have hab : a.1 (op V) * b.1 (op V) = 1 := congrFun (congrArg Subtype.val hb) (op V)
  simpa only [mul_assoc, hab, mul_one] using h''

include hN hL in
/-- **`s_ξ|_Z` is a regular meromorphic section of `ℒ|_Z`.**  It is a nonzero multiple of a
regular section: its value at the generic point is `1`, while the zero section has value
`0`. -/
theorem PrimeDivisor.isRegularMeromorphicSection_genericRestrictionOf
    (c : Z.genericResidueField B S hS hX hdec) (hc : c ≠ 0) :
    IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) (Z.genericRestrictionOf B S hS hX hdec hN L hL c) := by
  set t := Z.restrictModuleRegularSection B S hS hX hN L hL
  have ht := Z.isRegular_restrictModuleRegularSection B S hS hX hN L hL
  obtain ⟨x, hx, -⟩ := Z.existsUnique_functionField_smul_eq B S hS hX hN L hL t ht
    (Z.genericRestrictionOf B S hS hX hdec hN L hL c)
  rw [hx]
  refine Z.isRegularMeromorphicSection_smul B S hS hX hN L _ (fun h0 => hc ?_) t ht
  have hv := Z.genericFieldValue_genericRestrictionOf B S hS hX hdec hN L hL c
  rw [hx, Z.genericFieldValue_functionField_smul B S hS hX hdec hN] at hv
  have hx0 : x = 0 := (Z.bijective_functionFieldToMeromorphic B S hS hX hN).1
    (h0.trans (map_zero _).symm)
  rw [← hv, hx0, map_zero, zero_mul]

/-- **`s_ξ|_Z` is a regular meromorphic section of `ℒ|_Z`.** -/
theorem PrimeDivisor.isRegularMeromorphicSection_genericRestriction :
    IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) (Z.genericRestriction B S hS hX hdec hN L hL) :=
  Z.isRegularMeromorphicSection_genericRestrictionOf B S hS hX hdec hN L hL 1 one_ne_zero

/-! ### Units of the henselian local ring -/

/-- **The restriction to `Z` of the generator `v · s_ξ`** for a unit `v` of the henselian local
ring `𝒪^h_{X, ξ}`: the meromorphic section of `ℒ|_Z` whose value at the generic point is the
residue of `v`, read in `κ(u)` through the henselization. -/
def PrimeDivisor.henselianUnitRestriction
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ) :
    MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) :=
  letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  Z.genericRestrictionOf B S hS hX hdec hN L hL
    ((Z.genericResidueFieldEquivHenselian B S hS hX hdec).symm
      (IsLocalRing.residue _ (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec))))

/-- **The restriction of `v · s_ξ` is `θ(v̄) · s_ξ|_Z`**, with `θ : κ(𝒪^h_{X, ξ}) ≃+* R(Z)` the
canonical identification. -/
theorem PrimeDivisor.henselianUnitRestriction_eq_smul
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.henselianUnitRestriction B S hS hX hdec hN L hL v =
      Z.functionFieldToMeromorphic B S hS hX hN
          (Z.henselianResidueFieldEquivFunctionField B S hS hX hdec
            (IsLocalRing.residue _ (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)))) •
        Z.genericRestriction B S hS hX hdec hN L hL :=
  Z.genericRestrictionOf_eq_smul B S hS hX hdec hN L hL _

/-- The restriction of `v · s_ξ`, for a unit `v` of `𝒪^h_{X, ξ}`, is regular. -/
theorem PrimeDivisor.isRegularMeromorphicSection_henselianUnitRestriction
    (v : (↥(Z.genericHenselianLocalRing B S hS hX hdec))ˣ) :
    IsRegularMeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L) (Z.henselianUnitRestriction B S hS hX hdec hN L hL v) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  refine Z.isRegularMeromorphicSection_genericRestrictionOf B S hS hX hdec hN L hL _ ?_
  rw [Ne, RingEquiv.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]
  exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h v.isUnit

/-! ### Multiples of the generator by regular functions on `Spec 𝒪_{U, u}` -/

/-- The pullback of regular functions along the closed point `Spec κ(u) → Spec 𝒪_{U, u}` is the
residue map, read through the global sections of the two spectra. -/
theorem PrimeDivisor.chartDiagramPullback_genericFieldToStalk
    (w : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec)) :
    chartDiagramPullback B S hS (Z.genericFieldToStalk B S hS hX hdec)
        (Z.genericFieldToStalkChartDiagram B S hS hX hdec) w =
      (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
        (IsLocalRing.residue _
          ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom w)) := by
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (Z.genericFieldToStalkSpec B S hS hX hdec)).op).hom w = _
  rw [Z.toScheme_map_genericFieldToStalkSpec B S hS hX hdec]
  have h : (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).hom
      ((Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue ↥(Z.genericStalkRing B S hS hX hdec)))).appTop w) =
        IsLocalRing.residue _ ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom w) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (IsLocalRing.residue ↥(Z.genericStalkRing B S hS hX hdec)))) w
  refine Eq.trans ?_ (congrArg (Scheme.ΓSpecIso
    (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv h)
  exact (CommRingCat.inv_hom_apply _ _).symm

/-- **The image in the fibre of a multiple of `s_ξ`**: for a regular function `w` on
`Spec 𝒪_{U, u}`, the image of `w · s_ξ` is the residue of `w` times the image of `s_ξ`. -/
theorem PrimeDivisor.modulePullbackChartValue_smul_genericStalkGenerator
    (w : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec)) :
    modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) _
        (Z.genericFieldPullbackIso B S hS hX hdec L).hom
        (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
        (w • Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
          (𝟙 (Z.genericStalkChart B S hS hX hdec))) =
      (show chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2 (Z.genericFieldChart B S hS hX hdec) from
        (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
          (IsLocalRing.residue _
            ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom w))) •
        Z.genericFibreGenerator B S hS hX hdec L hL := by
  refine (modulePullbackChartValue_smul B S hS (Z.genericFieldToStalk B S hS hX hdec)
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) _
    (Z.genericFieldPullbackIso B S hS hX hdec L).hom
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec) w
    (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
      (𝟙 (Z.genericStalkChart B S hS hX hdec)))).trans ?_
  rw [Z.chartDiagramPullback_genericFieldToStalk B S hS hX hdec w]
  rfl

include hN in
/-- **The restriction of `w · s_ξ` is the section with value the residue of `w`**: for a regular
function `w` on `Spec 𝒪_{U, u}`, a meromorphic section of `ℒ|_Z` pulls back along `ρ_Z` to the
image of `w · s_ξ` in the fibre exactly when it is the section with value `w̄ ∈ κ(u)`, that is
`θ_Z(w̄) · s_ξ|_Z`. -/
theorem PrimeDivisor.eq_genericRestrictionOf_residue_iff
    (w : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec))
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L)) :
    σ = Z.genericRestrictionOf B S hS hX hdec hN L hL (IsLocalRing.residue _
        ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom w)) ↔
      (pullbackMeromorphicSection B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.restrictModule B S hS hX L)
          (Z.pullbacksMeromorphicSections_genericFieldMorphism B S hS hX hdec) σ).eval
          (op (Z.genericFieldChart B S hS hX hdec)) =
        toMeromorphicSectionValue B S hS (Z.genericFieldSpace B S hS hX hdec).1
          (Z.genericFieldSpace B S hS hX hdec).2
          ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
            (Z.restrictModule B S hS hX L)) (Z.genericFieldChart B S hS hX hdec)
          (modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) _
            (Z.genericFieldPullbackIso B S hS hX hdec L).hom
            (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
            (w • Z.genericStalkGenerator B S hS hX hdec L hL
              (Z.genericStalkChart B S hS hX hdec) (𝟙 (Z.genericStalkChart B S hS hX hdec)))) := by
  rw [Z.eq_genericRestrictionOf_iff B S hS hX hdec hN L hL,
    Z.modulePullbackChartValue_smul_genericStalkGenerator B S hS hX hdec L hL w,
    toMeromorphicSectionValue_eq, pureMeromorphicSection_smul_eq_algebraMap_tmul,
    Z.genericFieldGenerator_id B S hS hX hdec L hL]
  rfl

/-- For a unit of `𝒪_{U, u}`, the restriction of its image in `𝒪^h_{X, ξ}` times `s_ξ` is the
section with value its residue. -/
theorem PrimeDivisor.henselianUnitRestriction_map
    (w : (↥(Z.genericStalkRing B S hS hX hdec))ˣ) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    haveI := Z.isLocalHom_stalkToGenericHenselianLocalRing B S hS hX hdec
    Z.henselianUnitRestriction B S hS hX hdec hN L hL
        (Units.map (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
          (Z.genericChart B S hS hX hdec)).toMonoidHom w) =
      Z.genericRestrictionOf B S hS hX hdec hN L hL
        (IsLocalRing.residue _ (w : ↥(Z.genericStalkRing B S hS hX hdec))) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have := Z.isLocalHom_stalkToGenericHenselianLocalRing B S hS hX hdec
  rw [henselianUnitRestriction, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, ← Z.genericResidueFieldEquivHenselian_residue B S hS hX hdec,
    RingEquiv.symm_apply_apply]

end AlgebraicGeometry.Space

end
