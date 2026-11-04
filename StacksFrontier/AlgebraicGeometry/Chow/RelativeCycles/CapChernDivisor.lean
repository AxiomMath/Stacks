module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisorLocal
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GysinAction
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimensionTwoOpen

/-!
# The action of a relative cycle on the divisor of a meromorphic section

Let `(S, δ)` be as in Section 0H65, let `q : X ⟶ W` be a morphism of schemes locally of finite
type over `S` with `W` integral of `δ`-dimension `k + 1`, let `r ≥ 0` and let `α ∈ z(X/W, r)`.
Write `α ∩ [W] = ∑_x m_x [Z_x]`, the sum running over the points `x` of the generic fibre at which
`α` has a nonzero coefficient, with `Z_x` the closure of `x` and `m_x` that coefficient. For an
invertible `𝒪_W`-module `M` and a nonzero meromorphic section `t` of `M`,

  `α ∩ div_M(t) = ∑_x m_x (Z_x ⟶ X)_* div_{M|_{Z_x}}(t|_{Z_x})`

as `(r + k)`-cycles on `X`, where `t|_{Z_x}` is the pullback of `t` along the dominant morphism
`Z_x ⟶ W`. This is the cycle-level identity behind the compatibility of the action with the
first Chern class, hence with the Gysin maps of all invertible modules, in Stacks 0H6F.

## Main definitions

* `Stacks.Chow.capSupport` — the points of `X` at which `α ∩ [W]` has a nonzero coefficient.
* `Stacks.Chow.capComponentMap` — the dominant morphism `Z_x ⟶ W` of such a point.

## Main results

* `Stacks.Chow.ord_mul_capCoeff_eq_finsum_of_global` — the identity for the principal divisor of a
  global function, from Stacks 0H6E applied to the trivial invertible module.
* `Stacks.Chow.capPrincipalIdentity` — the identity for the principal divisor of any nonzero
  rational function: on an affine open of `W` the function is a ratio of two functions, and the
  open is reached by restriction.
* `Stacks.Chow.cap_chernComponentCycle_apply` — the identity above, coefficientwise: on a
  trivializing open the divisor of a meromorphic section is the principal divisor of a
  coordinate, and so are the divisors of its pullbacks.

## References

* [Stacks Project, Tag 0H6F](https://stacks.math.columbia.edu/tag/0H6F)
* [Stacks Project, Tag 0H6E](https://stacks.math.columbia.edu/tag/0H6E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Divisors

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

section Support

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  [IsIntegral W] (q : X ⟶ W) [LocallyOfFiniteType q] (r : ℕ) (α : FamilyOfCycles q r) (k : ℤ)

/-- The points of `X` at which `α ∩ [W]_{k+1}` has a nonzero coefficient: the generic points of
the components of the cycle `α ∩ [W]`. -/
abbrev capSupport : Type u :=
  {x : X // (cap C sW q α (fundamentalCycle C sW (k + 1))).1 x ≠ 0}

variable {C sW q r α k}

/-- The fundamental cycle of an integral scheme is supported at its generic point. -/
theorem fundamentalCycle_apply_eq_zero_of_ne {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] [IsIntegral T] (j : ℤ) {t : T} (ht : t ≠ genericPoint T) :
    (fundamentalCycle C sT j).1 t = 0 := by
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sT (𝟙 T) j t ?_
  rintro ⟨ξ, hξ, -⟩
  refine ht ?_
  rw [← hξ]
  have hsingle : genericPoints T = {genericPoint T} := genericPoints_eq_singleton
  have hgen : (ξ : T) = genericPoint T := by
    have h : (ξ : T) ∈ ({genericPoint T} : Set T) := hsingle ▸ ξ.2
    exact h
  simpa using hgen

/-- A point of `capSupport` lies over the generic point of `W`. -/
theorem capSupport.base_eq (x : capSupport C sW q r α k) : q.base x.1 = genericPoint W := by
  by_contra h
  apply x.2
  change capCoeff q α (fundamentalCycle C sW (k + 1)).1 x.1 = 0
  rw [capCoeff, fundamentalCycle_apply_eq_zero_of_ne sW (k + 1) h, zero_mul]

omit [IsIntegral W] in
/-- A point of `capSupport` has relative dimension `r + k + 1`. -/
theorem capSupport.relativeDimension_eq (x : capSupport C sW q r α k) :
    relativeDimension C.dimensionFunction (q ≫ sW) x.1 = (r : ℤ) + k + 1 := by
  have h := (mem_cyclesOfDimension_iff_forall_point C (q ≫ sW) _ _).1
    (cap C sW q α (fundamentalCycle C sW (k + 1))).2 x.1 x.2
  rw [h]
  ring

omit [IsIntegral W] in
/-- The closure of a point of `capSupport` has delta-dimension `r + k + 1`. -/
theorem capSupport.schemeDeltaDimension_eq (x : capSupport C sW q r α k) :
    schemeDeltaDimension C ((integralComponentAt x.1).subschemeι ≫ q ≫ sW) =
      (((r : ℤ) + k + 1 : ℤ) : EInt) :=
  schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C (q ≫ sW) x.1
    x.relativeDimension_eq

/-- The morphism `Z_x ⟶ W` of a point of `capSupport` is dominant: it carries the generic point of
`Z_x` to the generic point of `W`. -/
theorem capSupport.isDominant (x : capSupport C sW q r α k) :
    IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := by
  refine ⟨?_⟩
  have hη : genericPoint W ∈ Set.range ((integralComponentAt x.1).subschemeι ≫ q).base := by
    refine ⟨genericPoint (integralComponentAt x.1).subscheme, ?_⟩
    have hgen : (integralComponentAt x.1).subschemeι.base
        (genericPoint (integralComponentAt x.1).subscheme) = x.1 := by
      simpa [genericPointOf] using genericPointOf_integralComponentAt x.1
    rw [Scheme.Hom.comp_base, TopCat.comp_app, hgen, x.base_eq]
  rw [DenseRange, Dense]
  intro w
  have hcl : closure ({genericPoint W} : Set W) = Set.univ := (genericPoint_spec W).def
  have hw : w ∈ closure ({genericPoint W} : Set W) := by rw [hcl]; trivial
  exact closure_mono (Set.singleton_subset_iff.2 hη) hw

end Support

/-! ### The case of a principal divisor -/

section Principal

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  [IsIntegral W] (q : X ⟶ W) [LocallyOfFiniteType q] (r : ℕ) (α : FamilyOfCycles q r) {k : ℤ}

/-- The pushforward to `X` of the principal divisor of the pullback of a rational function `f` on
`W` to the closure of a point of `capSupport`. -/
def capComponentPrincipal (f : W.functionField) (x : capSupport C sW q r α k) :
    CycleGroup C (q ≫ sW) (((r : ℤ) + k + 1) - 1) :=
  letI : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
  properPushforward C ((integralComponentAt x.1).subschemeι ≫ q ≫ sW) (q ≫ sW)
    (integralComponentAt x.1).subschemeι rfl _
    (principalDivisorCycle C ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
      x.schemeDeltaDimension_eq
      (dominantFunctionFieldMap ((integralComponentAt x.1).subschemeι ≫ q) f))

/-- The germ at the generic point of a pulled-back global function. -/
theorem germToFunctionField_appTop {A B : Scheme.{u}} (f : A ⟶ B) [IsIntegral A] [IsIntegral B]
    [IsDominant f] [Nonempty (⊤ : A.Opens)] [Nonempty (⊤ : B.Opens)] (a : Γ(B, ⊤)) :
    A.germToFunctionField ⊤ (f.appTop a) = dominantFunctionFieldMap f (B.germToFunctionField ⊤ a) :=
  by
  rw [dominantFunctionFieldMap_germToFunctionField_of_mem f (genericPoint A) ⊤ trivial ⊤ trivial
    le_top a]
  simp [Scheme.Hom.appLE]
  rfl

/-- On an integral scheme of delta-dimension `k + 1`, the fundamental cycle has coefficient one
at the generic point. -/
theorem fundamentalCycle_apply_genericPoint {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] [IsIntegral T] {j : ℤ} (hj : schemeDeltaDimension C sT = (j : EInt)) :
    (fundamentalCycle C sT j).1 (genericPoint T) = 1 := by
  classical
  have hdim : relativeDimension C.dimensionFunction sT (genericPoint T) = j := by
    have h := schemeDeltaDimension_eq_genericPoint C sT
    rw [hj] at h
    exact (WithBotTop.coe_injective h).symm
  rw [fundamentalCycle_eq_single C sT genericPoints_eq_singleton hdim
    (Field.toIsField T.functionField)]
  simp

/-- On an integral scheme the integral closed subscheme attached to the generic point is the whole
scheme. -/
theorem integralComponentAt_genericPoint_eq_bot (T : Scheme.{u}) [IsIntegral T] :
    integralComponentAt (genericPoint T) = ⊥ := by
  have hcl : Closeds.closure ({genericPoint T} : Set T) = ⊤ :=
    Closeds.ext (genericPoint_spec T).def
  rw [integralComponentAt, hcl, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot]

/-- The generic point is not in the support of the zero scheme of a nonzero global function. -/
private theorem genericPoint_notMem_support_zeroScheme_unitModule (W : Scheme.{u}) [IsIntegral W]
    [IsLocallyNoetherian W] [Nonempty (⊤ : W.Opens)] (a : Γ(W, ⊤)) (ha : a ≠ 0) :
    genericPoint W ∉ ((Stacks.Divisors.zeroScheme W (Scheme.unitModule W) a).support : Set W) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Stacks.ChernCap42.genericPoint_notMem_range_subschemeι_zeroScheme
    (Scheme.unitModule W) a ha

/-- **`i_* i^* [W] = div(a)`, coefficientwise**, for a nonzero function `a` on an integral scheme
`W` of delta-dimension `k + 1`. -/
theorem gysinCycleMapPushforward_fundamentalCycle_apply
    (hk : schemeDeltaDimension C sW = ((k + 1 : ℤ) : EInt)) (a : Γ(W, ⊤)) (ha : a ≠ 0) (v : W) :
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    haveI : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
    (gysinCycleMapPushforward C sW k (Scheme.unitModule W) a (isTrivial_pullback_unitModule _)
        (fundamentalCycle C sW (k + 1))).1 v =
      W.ord (W.germToFunctionField ⊤ a) v := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  set D := Stacks.Divisors.zeroScheme W (Scheme.unitModule W) a with hD
  have hgen : ∀ w : cycleSupportIndex (fundamentalCycle C sW (k + 1)), w.1 = genericPoint W :=
    fun w ↦ by_contra fun h ↦ w.2 (fundamentalCycle_apply_eq_zero_of_ne sW (k + 1) h)
  have hηD := genericPoint_notMem_support_zeroScheme_unitModule W a ha
  have hβ : ∀ w : cycleSupportIndex (fundamentalCycle C sW (k + 1)),
      ¬ D ≤ integralComponentAt w.1 := fun w hle ↦ by
    rw [le_integralComponentAt_iff_mem_support, hgen w] at hle
    exact hηD hle
  rw [gysinCycleMapPushforward_unitModule_apply C sW k a _ hβ v]
  set w₀ : cycleSupportIndex (fundamentalCycle C sW (k + 1)) :=
    ⟨genericPoint W, by rw [fundamentalCycle_apply_genericPoint C sW hk]; exact one_ne_zero⟩
  rw [finsum_eq_single _ w₀ fun w hw ↦ absurd (Subtype.ext (hgen w)) hw]
  change (fundamentalCycle C sW (k + 1)).1 (genericPoint W) * _ = _
  rw [fundamentalCycle_apply_genericPoint C sW hk, one_mul]
  have hiso : IsIso (integralComponentAt (genericPoint W)).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2
      (integralComponentAt_genericPoint_eq_bot W)
  have : IsLocallyNoetherian (integralComponentAt (genericPoint W)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt (genericPoint W)).subschemeι ≫ sW)
  obtain ⟨z, rfl⟩ := (integralComponentAt (genericPoint W)).subschemeι.surjective v
  change (properPushforward C ((integralComponentAt (genericPoint W)).subschemeι ≫ sW) sW
    (integralComponentAt (genericPoint W)).subschemeι rfl (k + 1 - 1)
    (principalDivisorCycle C ((integralComponentAt (genericPoint W)).subschemeι ≫ sW) _
      ((integralComponentAt (genericPoint W)).subscheme.germToFunctionField ⊤
        ((integralComponentAt (genericPoint W)).subschemeι.appTop a)))).1 _ = _
  rw [properPushforward_apply_image_of_isClosedImmersion, principalDivisorCycle_apply,
    germToFunctionField_appTop, ord_dominantFunctionFieldMap_of_isOpenImmersion]

/-- **Stacks 0H6E for a global function, read at a point.** For a nonzero function `a` on `W`,
the coefficient at `y` of `α ∩ div(a)` is `∑_x m_x` times the coefficient at `y` of the
pushforward of `div(a|_{Z_x})`. -/
theorem ord_mul_capCoeff_eq_finsum_of_global
    (hα : letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
      IsRelativeCycle q r α)
    (hk : schemeDeltaDimension C sW = ((k + 1 : ℤ) : EInt)) (a : Γ(W, ⊤)) (ha : a ≠ 0) (y : X) :
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    haveI : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
    W.ord (W.germToFunctionField ⊤ a) (q.base y) * (α (q.base y)).1 (q.asFiber y) =
      ∑ᶠ x : capSupport C sW q r α k, (cap C sW q α (fundamentalCycle C sW (k + 1))).1 x.1 *
        (capComponentPrincipal C sW q r α (W.germToFunctionField ⊤ a) x).1 y := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  set D := Stacks.Divisors.zeroScheme W (Scheme.unitModule W) a with hD
  have hzero := zeroScheme_unitModule_appTop q a
  have h := capCommutesWithGysin_of_isRelativeCycle C sW q r k (Scheme.unitModule W) a
    (isTrivial_pullback_unitModule _) (Scheme.unitModule X) (q.appTop a)
    (isTrivial_pullback_unitModule _) hzero α hα (fundamentalCycle C sW (k + 1))
  have hy := congrArg (fun c : CycleGroup C (q ≫ sW) ((r : ℤ) + k) ↦ c.1 y) h
  simp only at hy
  have hL : (cap C sW q α (gysinCycleMapPushforward C sW k (Scheme.unitModule W) a
      (isTrivial_pullback_unitModule _) (fundamentalCycle C sW (k + 1)))).1 y =
      (gysinCycleMapPushforward C sW k (Scheme.unitModule W) a (isTrivial_pullback_unitModule _)
        (fundamentalCycle C sW (k + 1))).1 (q.base y) * (α (q.base y)).1 (q.asFiber y) := rfl
  rw [hL, gysinCycleMapPushforward_fundamentalCycle_apply C sW hk a ha] at hy
  rw [hy]
  have hηD := genericPoint_notMem_support_zeroScheme_unitModule W a ha
  have hβ : ∀ x : cycleSupportIndex (cycleGroupCongr C (q ≫ sW)
        (show (r : ℤ) + (k + 1) = (r : ℤ) + k + 1 by ring)
        (cap C sW q α (fundamentalCycle C sW (k + 1)))),
      ¬ Stacks.Divisors.zeroScheme X (Scheme.unitModule X) (q.appTop a) ≤
        integralComponentAt x.1 := fun x hle ↦ by
    rw [le_integralComponentAt_iff_mem_support, hzero, Scheme.IdealSheafData.support_comap] at hle
    have hx : q.base x.1 = genericPoint W :=
      capSupport.base_eq (C := C) (sW := sW) (r := r) (α := α) (k := k) ⟨x.1, x.2⟩
    exact hηD (hx ▸ hle)
  rw [gysinCycleMapPushforward_unitModule_apply C (q ≫ sW) ((r : ℤ) + k) (q.appTop a) _ hβ y]
  refine finsum_congr fun x ↦ ?_
  congr 1
  let : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) :=
    capSupport.isDominant (C := C) (sW := sW) (r := r) (α := α) (k := k) ⟨x.1, x.2⟩
  have : Nonempty (⊤ : (integralComponentAt x.1).subscheme.Opens) :=
    ⟨⟨genericPoint _, trivial⟩⟩
  have hg := germToFunctionField_appTop ((integralComponentAt x.1).subschemeι ≫ q) a
  rw [Scheme.Hom.comp_appTop] at hg
  simp only [capComponentPrincipal]
  rw [← hg]
  rfl

/-- The order of vanishing of the inverse of a nonzero rational function. -/
theorem ord_inv_of_ne_zero {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    {f : T.functionField} (hf : f ≠ 0) (t : T) : T.ord f⁻¹ t = -T.ord f t := by
  have h := congrArg (fun c : AlgebraicCycle T ℤ ↦ c t) (principalCycle_inv T hf)
  simpa using h

open Classical in
variable {C sW q r α} in
/-- The coefficient at `y` of `capComponentPrincipal` is an order of vanishing on `Z_x` when `y`
lies on `Z_x`, and zero otherwise. -/
theorem capComponentPrincipal_apply (f : W.functionField) (x : capSupport C sW q r α k) (y : X) :
    letI : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
    haveI : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
    (capComponentPrincipal C sW q r α f x).1 y =
      if h : y ∈ Set.range (integralComponentAt x.1).subschemeι.base then
        (integralComponentAt x.1).subscheme.ord
          (dominantFunctionFieldMap ((integralComponentAt x.1).subschemeι ≫ q) f) h.choose
      else 0 := by
  let : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
  have : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
  split_ifs with h
  · conv_lhs => rw [← h.choose_spec]
    simp only [capComponentPrincipal]
    rw [properPushforward_apply_image_of_isClosedImmersion, principalDivisorCycle_apply]
  · exact properPushforward_apply_eq_zero_of_notMem_range C _ _ _ rfl _ _ y h

variable {C sW q r α} in
/-- For nonzero rational functions `f` and `g`, the coefficient at `y` of `capComponentPrincipal`
of `f * g` is the sum of those of `f` and of `g`. -/
theorem capComponentPrincipal_mul {f g : W.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (x : capSupport C sW q r α k) (y : X) :
    (capComponentPrincipal C sW q r α (f * g) x).1 y =
      (capComponentPrincipal C sW q r α f x).1 y + (capComponentPrincipal C sW q r α g x).1 y := by
  have : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
  let : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
  rw [capComponentPrincipal_apply, capComponentPrincipal_apply, capComponentPrincipal_apply]
  split_ifs
  · rw [map_mul, Scheme.ord_mul ((map_ne_zero _).2 hf) ((map_ne_zero _).2 hg)]
  · simp

variable {C sW q r α} in
/-- For a nonzero rational function `f`, the coefficient at `y` of `capComponentPrincipal` of
`f⁻¹` is the negative of that of `f`. -/
theorem capComponentPrincipal_inv {f : W.functionField} (hf : f ≠ 0)
    (x : capSupport C sW q r α k) (y : X) :
    (capComponentPrincipal C sW q r α f⁻¹ x).1 y = -(capComponentPrincipal C sW q r α f x).1 y := by
  have : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
  let : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
  rw [capComponentPrincipal_apply, capComponentPrincipal_apply]
  split_ifs
  · rw [map_inv₀, ord_inv_of_ne_zero ((map_ne_zero _).2 hf)]
  · simp

variable {C sW q r α} in
/-- At a point `y` only finitely many points of `capSupport` contribute a nonzero
`capComponentPrincipal`. -/
theorem finite_support_capComponentPrincipal (f : W.functionField) (y : X) :
    (Function.support fun x : capSupport C sW q r α k ↦
      (cap C sW q α (fundamentalCycle C sW (k + 1))).1 x.1 *
        (capComponentPrincipal C sW q r α f x).1 y).Finite := by
  have hfin := finite_support_inter_generalizations
    (cap C sW q α (fundamentalCycle C sW (k + 1))).1.locallyFiniteSupport
    (isCompact_singleton (x := y))
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro x hx
  have hne := right_ne_zero_of_mul hx
  rw [capComponentPrincipal_apply] at hne
  split_ifs at hne with h
  · refine ⟨⟨y, rfl, ?_⟩, x.2⟩
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt] at h
    exact h
  · exact absurd rfl hne

/-- The identity of Stacks 0H6E for a rational function `f`, read at `y`. -/
def CapPrincipalIdentity (f : W.functionField) (y : X) : Prop :=
  letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  W.ord f (q.base y) * (α (q.base y)).1 (q.asFiber y) =
    ∑ᶠ x : capSupport C sW q r α k, (cap C sW q α (fundamentalCycle C sW (k + 1))).1 x.1 *
      (capComponentPrincipal C sW q r α f x).1 y

variable {C sW q r α} in
/-- If `CapPrincipalIdentity` holds at `y` for nonzero rational functions `f` and `g`, then it
holds at `y` for `f * g`. -/
theorem CapPrincipalIdentity.mul {f g : W.functionField} (hf : f ≠ 0) (hg : g ≠ 0) {y : X}
    (h₁ : CapPrincipalIdentity C sW q r α (k := k) f y)
    (h₂ : CapPrincipalIdentity C sW q r α (k := k) g y) :
    CapPrincipalIdentity C sW q r α (k := k) (f * g) y := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  unfold CapPrincipalIdentity at h₁ h₂ ⊢
  rw [Scheme.ord_mul hf hg, add_mul, h₁, h₂, ← finsum_add_distrib
    (finite_support_capComponentPrincipal f y) (finite_support_capComponentPrincipal g y)]
  refine finsum_congr fun x ↦ ?_
  rw [capComponentPrincipal_mul hf hg, mul_add]

variable {C sW q r α} in
/-- If `CapPrincipalIdentity` holds at `y` for a nonzero rational function `f`, then it holds at
`y` for `f⁻¹`. -/
theorem CapPrincipalIdentity.inv {f : W.functionField} (hf : f ≠ 0) {y : X}
    (h : CapPrincipalIdentity C sW q r α (k := k) f y) :
    CapPrincipalIdentity C sW q r α (k := k) f⁻¹ y := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  unfold CapPrincipalIdentity at h ⊢
  rw [ord_inv_of_ne_zero hf, neg_mul, h, ← finsum_neg_distrib]
  refine finsum_congr fun x ↦ ?_
  rw [capComponentPrincipal_inv hf, mul_neg]

/-- **Stacks 0H6E for a rational function on an affine base, read at a point.** -/
theorem capPrincipalIdentity_of_isAffine [IsAffine W]
    (hα : letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
      IsRelativeCycle q r α)
    (hk : schemeDeltaDimension C sW = ((k + 1 : ℤ) : EInt)) {f : W.functionField} (hf : f ≠ 0)
    (y : X) : CapPrincipalIdentity C sW q r α (k := k) f y := by
  have : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen W ⊤ (isAffineOpen_top W)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(W, ⊤)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hgerm : ∀ c : Γ(W, ⊤), c ≠ 0 → algebraMap Γ(W, ⊤) W.functionField c ≠ 0 := fun c hc ↦
    (map_ne_zero_iff _ (IsFractionRing.injective Γ(W, ⊤) W.functionField)).2 hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (by simp)
  rw [div_eq_mul_inv]
  refine CapPrincipalIdentity.mul (hgerm a ha0) (inv_ne_zero (hgerm b hb0)) ?_
    (CapPrincipalIdentity.inv (hgerm b hb0) ?_)
  · exact ord_mul_capCoeff_eq_finsum_of_global C sW q r α hα hk a ha0 y
  · exact ord_mul_capCoeff_eq_finsum_of_global C sW q r α hα hk b hb0 y

/-- **Stacks 0H6E for a rational function, read at a point.** For a relative `r`-cycle `α` on
`X/W`, `W` integral of delta-dimension `k + 1`, a nonzero rational function `f` on `W` and a point
`y` of `X`, the coefficient at `y` of `α ∩ div(f)` is `∑_x m_x` times the coefficient at `y` of
the pushforward of `div(f|_{Z_x})`. -/
theorem capPrincipalIdentity
    (hα : letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
      IsRelativeCycle q r α)
    (hk : schemeDeltaDimension C sW = ((k + 1 : ℤ) : EInt)) {f : W.functionField} (hf : f ≠ 0)
    (y : X) : CapPrincipalIdentity C sW q r α (k := k) f y := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  obtain ⟨V, hV, hvV, -⟩ := exists_isAffineOpen_mem_and_subset (X := W) (x := q.base y)
    (U := ⊤) trivial
  have : Nonempty V := ⟨⟨_, hvV⟩⟩
  have : IsAffine V.toScheme := hV
  have : IsDominant V.ι := AlgebraicGeometry.isDominant_opensι V
  set U : X.Opens := q ⁻¹ᵁ V with hUdef
  set fU := q.resLE V U le_rfl with hfU
  have hsq : U.ι ≫ q = fU ≫ V.ι := (q.resLE_comp_ι le_rfl).symm
  let : LocallyOfFiniteType fU := by
    have : LocallyOfFiniteType (fU ≫ V.ι) := hsq ▸ inferInstance
    exact locallyOfFiniteType_of_comp fU V.ι
  have hkV : schemeDeltaDimension C (V.ι ≫ sW) = ((k + 1 : ℤ) : EInt) := by
    rw [← schemeDeltaDimension_eq_of_isOpenImmersion C V.ι sW (V.ι ≫ sW) rfl, hk]
  let : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  set αU := (restrictedFamily q fU U.ι V.ι hsq r α).1 with hαU_def
  have hαU : IsRelativeCycle fU r αU := isRelativeCycle_restrictedFamily q fU U.ι V.ι hsq r hα
  set fV := dominantFunctionFieldMap V.ι f with hfV_def
  have hfV : fV ≠ 0 := (map_ne_zero _).2 hf
  have hyU : y ∈ U := hvV
  set y' : U.toScheme := ⟨y, hyU⟩ with hy'
  have hA := capPrincipalIdentity_of_isAffine C (V.ι ≫ sW) fU r αU hαU hkV hfV y'
  unfold CapPrincipalIdentity at hA ⊢
  have hres := fun (e : ℤ) (β : CycleGroup C sW e) ↦
    cycleGroupRestrict_cap C sW (V.ι ≫ sW) q fU U.ι V.ι rfl hsq r e α β
  -- the principal divisor and the fundamental cycle restrict to their counterparts on `V`
  have hdiv : cycleGroupRestrict C sW (V.ι ≫ sW) V.ι rfl ((k + 1) - 1)
      (principalDivisorCycle C sW hk f) = principalDivisorCycle C (V.ι ≫ sW) hkV fV := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
    rw [cycleGroupRestrict_apply, principalDivisorCycle_apply, principalDivisorCycle_apply,
      hfV_def, ord_dominantFunctionFieldMap_of_isOpenImmersion]
  have hfund : cycleGroupRestrict C sW (V.ι ≫ sW) V.ι rfl (k + 1) (fundamentalCycle C sW (k + 1)) =
      fundamentalCycle C (V.ι ≫ sW) (k + 1) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
    rw [cycleGroupRestrict_apply]
    by_cases hv : v = genericPoint V.toScheme
    · subst hv
      rw [genericPoint_eq_of_isOpenImmersion V.ι, fundamentalCycle_apply_genericPoint C sW hk,
        fundamentalCycle_apply_genericPoint C (V.ι ≫ sW) hkV]
    · rw [fundamentalCycle_apply_eq_zero_of_ne (V.ι ≫ sW) (k + 1) hv,
        fundamentalCycle_apply_eq_zero_of_ne sW (k + 1)]
      intro h
      apply hv
      apply V.ι.isOpenEmbedding.injective
      rw [h, genericPoint_eq_of_isOpenImmersion V.ι]
  -- the left hand side
  have hLHS : Scheme.ord f (q.base y) * (α (q.base y)).1 (q.asFiber y) =
      (cap C sW q α (principalDivisorCycle C sW hk f)).1 y := rfl
  have hLHS' : Scheme.ord fV (fU.base y') * (αU (fU.base y')).1 (fU.asFiber y') =
      (cap C (V.ι ≫ sW) fU αU (principalDivisorCycle C (V.ι ≫ sW) hkV fV)).1 y' := rfl
  have hcapy : (cap C sW q α (principalDivisorCycle C sW hk f)).1 y =
      (cycleGroupRestrict C (q ≫ sW) (fU ≫ V.ι ≫ sW) U.ι
        (by rw [← Category.assoc, hsq, Category.assoc]) _
        (cap C sW q α (principalDivisorCycle C sW hk f))).1 y' := rfl
  rw [hLHS, hcapy, hres, hdiv, ← hLHS', hA]
  -- the coefficients `m_x`
  have hm : ∀ x' : U.toScheme, (cap C (V.ι ≫ sW) fU αU (fundamentalCycle C (V.ι ≫ sW) (k + 1))).1 x'
      = (cap C sW q α (fundamentalCycle C sW (k + 1))).1 (U.ι.base x') := by
    intro x'
    rw [← hfund, ← hres]
    rfl
  have hηV : genericPoint W ∈ V :=
    ((genericPoint_spec W).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hmem : ∀ x : capSupport C sW q r α k, x.1 ∈ U := fun x ↦ by
    change q.base x.1 ∈ V
    rw [capSupport.base_eq x]
    exact hηV
  let e : capSupport C (V.ι ≫ sW) fU r αU k ≃ capSupport C sW q r α k :=
    { toFun := fun x' ↦ ⟨U.ι.base x'.1, fun h ↦ x'.2 ((hm x'.1).trans h)⟩
      invFun := fun x ↦ ⟨⟨x.1, hmem x⟩, fun h ↦ x.2 ((hm ⟨x.1, hmem x⟩).symm.trans h)⟩
      left_inv := fun x' ↦ rfl
      right_inv := fun x ↦ rfl }
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun x' ↦ ?_
  rw [hm]
  congr 1
  let : IsDominant ((integralComponentAt x'.1).subschemeι ≫ fU) := x'.isDominant
  let : IsDominant ((integralComponentAt (e x').1).subschemeι ≫ q) := (e x').isDominant
  exact properPushforward_principalDivisorCycle_apply_of_isOpenImmersion C (q ≫ sW)
    (fU ≫ V.ι ≫ sW) U.ι (by rw [← Category.assoc, hsq, Category.assoc])
    (integralComponentAt (e x').1) (integralComponentAt x'.1)
    (comap_integralComponentAt_of_isOpenImmersion U.ι x'.1).symm
    (e x').schemeDeltaDimension_eq x'.schemeDeltaDimension_eq _ _
    (fun μ _ _ hμ ↦ by
      have hcomp : ∀ {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B] (g : A ⟶ B) (g' : B ⟶ W)
          [IsDominant g] [IsDominant g'],
          dominantFunctionFieldMap g (dominantFunctionFieldMap g' f) =
            dominantFunctionFieldMap (g ≫ g') f := by
        intros
        rw [dominantFunctionFieldMap_comp]
        rfl
      rw [hfV_def, hcomp, hcomp]
      have hmor : μ ≫ (integralComponentAt (e x').1).subschemeι ≫ q =
          ((integralComponentAt x'.1).subschemeι ≫ fU) ≫ V.ι :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ q) hμ).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hsq).trans
            (Category.assoc _ _ _).symm)))
      exact congrArg (fun φ ↦ φ f) (dominantFunctionFieldMap_congr _ _ hmor))
    y'

end Principal

/-! ### The coefficients of the divisor of a meromorphic section -/

/-- The coefficient at a point of the divisor of a meromorphic section is the order of vanishing
of any coordinate of the section at that point. -/
theorem chernComponentCycle_apply_of_isCoordinateAt (C : ChowSituation.{u}) {A : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] [IsIntegral A] [IsLocallyNoetherian A] {j : ℤ}
    (hj : schemeDeltaDimension C sA = ((j + 1 : ℤ) : EInt)) {M : A.Modules}
    (hM : ∀ a : A, IsTrivializedNear M a) (t : M.presheaf.stalk (genericPoint A))
    {z : A} {b : A.functionField} (hb : IsCoordinateAt M z t b) :
    (chernComponentCycle C sA hj hM t).1 z = A.ord b z := by
  by_cases hco : Order.coheight z = 1
  · have hgen : (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco).genericPoint = z :=
      Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne z hco
    have h1 := chernComponentCycle_genericPoint C sA hj hM t
      (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco)
    have hb' :
        IsCoordinateAt M (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco).genericPoint t b := by
      rw [hgen]; exact hb
    have h2 := orderOfVanishing_eq
      (hM (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco).genericPoint) hb'
    rw [hgen] at h1 h2
    exact h1.trans h2
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hco b]
    exact chernComponentCycle_eq_zero C sA hj hM t z
      fun Z hZ ↦ hco (hZ ▸ Stacks.Divisors.PrimeDivisor.coheight_genericPoint Z)

/-! ### The identity -/

section Identity

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  [IsIntegral W] (q : X ⟶ W) [LocallyOfFiniteType q] (r : ℕ) (α : FamilyOfCycles q r) {k : ℤ}
  (hk : schemeDeltaDimension C sW = ((k + 1 : ℤ) : EInt)) (M : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]

/-- The pushforward to `X` of the divisor of the pullback of `t` to the closure of a point of
`capSupport`. -/
def capComponentDivisor (t : M.presheaf.stalk (genericPoint W)) (x : capSupport C sW q r α k) :
    CycleGroup C (q ≫ sW) ((r : ℤ) + k) :=
  letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  letI : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
  letI : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
  properPushforward C ((integralComponentAt x.1).subschemeι ≫ q ≫ sW) (q ≫ sW)
    (integralComponentAt x.1).subschemeι rfl ((r : ℤ) + k)
    (chernComponentCycle C ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
      x.schemeDeltaDimension_eq
      (fun z ↦ (isTrivializedNear_of_isInvertible M
        (((integralComponentAt x.1).subschemeι ≫ q).base z)).pullback)
      (genericStalkPullback ((integralComponentAt x.1).subschemeι ≫ q) M t))

/-- **The action of a relative cycle on the divisor of a meromorphic section.** For a relative
`r`-cycle `α` on `X/W`, `W` integral of delta-dimension `k + 1`, an invertible `𝒪_W`-module `M`
and a nonzero meromorphic section `t` of `M`,
`α ∩ div_M(t) = ∑_x m_x (Z_x ⟶ X)_* div(t|_{Z_x})`, coefficientwise, where `x` runs over the
points of `X` at which `α ∩ [W]` has the nonzero coefficient `m_x` and `Z_x` is the closure
of `x`. -/
theorem cap_chernComponentCycle_apply
    (hα : letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
      IsRelativeCycle q r α)
    (t : M.presheaf.stalk (genericPoint W)) (ht : t ≠ 0) (y : X) :
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    (cap C sW q α (chernComponentCycle C sW hk (isTrivializedNear_of_isInvertible M) t)).1 y =
      ∑ᶠ x : capSupport C sW q r α k,
        (cap C sW q α (fundamentalCycle C sW (k + 1))).1 x.1 *
          (capComponentDivisor C sW q r α M t x).1 y := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  obtain ⟨b, hb⟩ := exists_isCoordinateAt (isTrivializedNear_of_isInvertible M (q.base y)) t
  have hb0 : b ≠ 0 := hb.ne_zero ht
  have hP := capPrincipalIdentity C sW q r α hα hk hb0 y
  unfold CapPrincipalIdentity at hP
  have hL : (cap C sW q α (chernComponentCycle C sW hk (isTrivializedNear_of_isInvertible M) t)).1 y
      = (chernComponentCycle C sW hk (isTrivializedNear_of_isInvertible M) t).1 (q.base y) *
        (α (q.base y)).1 (q.asFiber y) := rfl
  rw [hL, chernComponentCycle_apply_of_isCoordinateAt C sW hk _ t hb, hP]
  refine finsum_congr fun x ↦ ?_
  congr 1
  let : IsDominant ((integralComponentAt x.1).subschemeι ≫ q) := x.isDominant
  have : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ q ≫ sW)
  by_cases hy : y ∈ Set.range (integralComponentAt x.1).subschemeι.base
  · obtain ⟨z, rfl⟩ := hy
    simp only [capComponentPrincipal, capComponentDivisor]
    rw [properPushforward_apply_image_of_isClosedImmersion,
      properPushforward_apply_image_of_isClosedImmersion, principalDivisorCycle_apply]
    have hcoord : IsCoordinateAt M (((integralComponentAt x.1).subschemeι ≫ q).base z) t b := hb
    exact (chernComponentCycle_apply_of_isCoordinateAt C _ x.schemeDeltaDimension_eq _ _
      hcoord.pullback).symm
  · simp only [capComponentPrincipal, capComponentDivisor]
    rw [properPushforward_apply_eq_zero_of_notMem_range C _ _ _ rfl _ _ y hy,
      properPushforward_apply_eq_zero_of_notMem_range C _ _ _ rfl _ _ y hy]

end Identity

end Stacks.Chow

end
