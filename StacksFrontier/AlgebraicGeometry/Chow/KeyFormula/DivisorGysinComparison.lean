module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.KeyFormulaOnDivisor
import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible

/-!
# The Gysin pullback of a divisor cycle, compared on the divisor

Let `X` be integral, locally Noetherian and locally of finite type over the base scheme `S` of
chapter 42 of the Stacks Project, of delta-dimension `k + 2`. Let `L` be an invertible
`𝒪_X`-module with a nonzero global section `s`, with zero scheme `i : D = Z(s) ⟶ X`, and let `N`
be an invertible `𝒪_X`-module with a nonzero meromorphic section `t`.

This file proves the heart of Stacks 02TM: the Gysin cycle of `div_N(t)` on `D`, pushed forward
to `X`, differs from

  `∑_i ord_{B_i}(f_i) · (Z_i → X)_* div_{N|Z_i}(t_i|_{Z_i})`

by a cycle rationally equivalent to zero **with witnesses inside `D`**. Here `{Z_i}` is the family
of prime divisors of a situation of Stacks 0AYB for the pair `(L, s)` and `(N, t)` whose chosen
generator of `L` at `ξ_i` is the germ of `s` wherever that germ generates — the choice
`Stacks.Chow.gysinGenerator` already made for Stacks 02TO.

## The argument

Two inputs are combined.

* The key formula of Stacks 0AYC, `Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData`,
  exhibits

  `∑_i (Z_i → X)_* (ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i))`

  as a locally finite sum of principal divisors on the members `Z_i` along which `f_i ≠ 1`.
  With the generators chosen as above, `f_i = 1` at every member whose generic point lies off
  `D`, so the witnesses lie inside `D`; that is
  `Stacks.Chow.KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff`.

* The component comparison of Stacks 02T8,
  `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub`,
  compares the Gysin component cycle of `Z_i` with `div_{L|Z_i}(s_i|Z_i)` after pushing both
  forward to `X`, with witnesses inside `Z_i ∩ D`. Weighted by `ord_{B_i}(g_i)` and summed over
  the locally finite family, it says that the pushforward of the Gysin cycle differs from
  `∑_i ord_{B_i}(g_i) (Z_i → X)_* div_{L|Z_i}(s_i|Z_i)` by a cycle rationally equivalent to zero
  inside `D`.

Subtracting the first from the second leaves exactly the assertion above.

## Main definitions

* `Stacks.Chow.KeyFormulaSituation.withSectionGeneratorsL` — the situation of Stacks 0AYB whose
  generator of `L` at each member is `Stacks.Chow.gysinGenerator`, the germ of the global section
  `s` wherever that germ generates the stalk.

## Main results

* `Stacks.Chow.exists_cycleGroup_finsum` — a locally finite sum of `k`-cycles is a `k`-cycle.
* `Stacks.Chow.KeyFormulaSituation.withSectionGeneratorsL_ratioL_eq_one` — for that situation
  `f_i = 1` at every member whose generic point lies off `Z(s)`.
* `Stacks.Chow.KeyFormulaSituation.orderL_eq_zero_of_ratioL_eq_one` — and then the order of
  vanishing of `s` along that member is zero.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinCycle_sub` — the
  comparison above, the heart of Stacks 02TM.

## References

* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isIntegral_integralComponentAt

/-! ### Arithmetic and closure helpers -/

/-- A locally finite difference of sums splits. -/
private theorem finsum_sub_distrib {ι : Type*} {f g : ι → ℤ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i - g i) = (∑ᶠ i, f i) - ∑ᶠ i, g i := by
  simp only [sub_eq_add_neg]
  rw [finsum_add_distrib hf (hg.subset fun i hi ↦ by simpa using hi), finsum_neg_distrib]

/-! ### A locally finite sum of cycles -/

/-- **A locally finite sum of `k`-cycles is a `k`-cycle.** Each summand is supported inside a
member of a locally finite family of sets, so the sum has locally finite support, and a point
where the sum does not vanish is a point where one of the summands does not vanish, which fixes
its relative dimension. -/
theorem exists_cycleGroup_finsum (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) {J : Type u} (c : J → CycleGroup C p k) (E : J → Set X)
    (hE : LocallyFinite E) (hsub : ∀ j, Function.support (fun x ↦ (c j).1 x) ⊆ E j) :
    ∃ γ : CycleGroup C p k, ∀ x : X, γ.1 x = ∑ᶠ j : J, (c j).1 x := by
  have hloc := locallyFiniteSupport_finsum_of_locallyFinite E hE (fun j x ↦ (c j).1 x) hsub
    fun j ↦ (c j).1.locallyFiniteSupport
  refine ⟨⟨⟨fun x ↦ ∑ᶠ j : J, (c j).1 x, by simp, fun z _ ↦ hloc z⟩, ?_⟩, fun _ ↦ rfl⟩
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro x hx
  obtain ⟨j, hj⟩ : ∃ j : J, (c j).1 x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  exact (mem_cyclesOfDimension_iff_forall_point C p k _).1 (c j).2 x hj

/-! ### The situation adapted to a global section of the first module -/

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- **The situation of Stacks 0AYB with the generator of `L` adapted to a global section `s`.**
At each member the generator of `L` is `Stacks.Chow.gysinGenerator`: the germ of `s`, wherever
that germ generates the stalk, and an arbitrary generator elsewhere. Every other datum is
unchanged, so the orders of vanishing of the meromorphic section of `N` and the divisors
`div_{N|Z_i}(t_i|Z_i)` are too.

This is `Stacks.Chow.withGysinGenerators` with the second module left alone rather than replaced
by the structure sheaf. -/
def withSectionGeneratorsL (ℱ : KeyFormulaSituation L N) (s : Γ(L, ⊤)) :
    KeyFormulaSituation L N :=
  { ℱ with
    localGeneratorL := fun i ↦ gysinGenerator L s (ℱ.componentPoint i)
    isStalkBasis_localGeneratorL := fun i ↦
      isStalkBasis_gysinGenerator L s (ℱ.componentPoint i) }

variable (ℱ : KeyFormulaSituation L N) (s : Γ(L, ⊤))

omit [IsLocallyNoetherian X] in
/-- The adapted situation has the same meromorphic section of `L`. -/
@[simp]
theorem withSectionGeneratorsL_sectionL : (ℱ.withSectionGeneratorsL s).sectionL = ℱ.sectionL :=
  rfl

omit [IsLocallyNoetherian X] in
/-- The adapted situation has the same meromorphic section of `N`. -/
@[simp]
theorem withSectionGeneratorsL_sectionN : (ℱ.withSectionGeneratorsL s).sectionN = ℱ.sectionN :=
  rfl

omit [IsLocallyNoetherian X] in
/-- The adapted situation has the same family of prime divisors `Z_i`. -/
@[simp]
theorem withSectionGeneratorsL_component (i : ℱ.Index) :
    (ℱ.withSectionGeneratorsL s).component i = ℱ.component i := rfl

omit [IsLocallyNoetherian X] in
/-- The generator of `L` at the generic point of `Z_i` in the adapted situation is
`Stacks.Chow.gysinGenerator L s`. -/
@[simp]
theorem withSectionGeneratorsL_localGeneratorL (i : ℱ.Index) :
    (ℱ.withSectionGeneratorsL s).localGeneratorL i = gysinGenerator L s (ℱ.componentPoint i) :=
  rfl

omit [IsLocallyNoetherian X] in
/-- The adapted situation has the same local generators of `N`. -/
@[simp]
theorem withSectionGeneratorsL_localGeneratorN (i : ℱ.Index) :
    (ℱ.withSectionGeneratorsL s).localGeneratorN i = ℱ.localGeneratorN i := rfl

/-- **The adapted situation has `f_i = 1` at every member off the zero scheme of `s`.** There the
chosen generator is the germ of `s`, whose generic value is the meromorphic section itself. -/
theorem withSectionGeneratorsL_ratioL_eq_one (hs : s ≠ 0) (i : ℱ.Index)
    (hsection : ℱ.sectionL = L.presheaf.germ ⊤ (genericPoint X) trivial s)
    (hξ : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt (ℱ.componentPoint i)) :
    (ℱ.withSectionGeneratorsL s).ratioL i = 1 := by
  refine ((ℱ.withSectionGeneratorsL s).ratioL_eq_one_iff i).mpr ?_
  show toGenericStalk L (ℱ.componentPoint i) (gysinGenerator L s (ℱ.componentPoint i)) =
    ℱ.sectionL
  rw [gysinGenerator_eq_germ L s hs hξ,
    toGenericStalk_germ (Opens.mem_top (ℱ.componentPoint i)) (Opens.mem_top (genericPoint X))]
  exact hsection.symm

/-- **Where the chosen generator has the section for its generic value, the order of vanishing is
zero**: the order of the constant rational function `1`. -/
theorem orderL_eq_zero_of_ratioL_eq_one {i : ℱ.Index} (h : ℱ.ratioL i = 1) : ℱ.orderL i = 0 := by
  rw [ℱ.orderL_eq_ord_ratioL i, h,
    ← map_one (algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField)]
  exact Scheme.ord_algebraMap_of_isUnit (ℱ.coheight_componentPoint i) isUnit_one

end KeyFormulaSituation

/-! ### The comparison on the divisor -/

section Comparison

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}

/-- **The heart of Stacks 02TM.** Let `X` be integral, locally Noetherian, of delta-dimension
`k + 2` over the base, let `L` be invertible with a nonzero global section `s` and zero scheme
`D = Z(s)`, and let `N` be invertible with a nonzero meromorphic section `t`. Let `ℱ` be a
situation of Stacks 0AYB for `(L, s)` and `(N, t)` whose generator of `L` at each member off `D`
is the germ of `s`, so that `f_i = 1` there.

Let `β` be a cycle on `D` presented by the Gysin component cycles of the family with the orders
`ord_{B_i}(g_i)` — the Gysin cycle of `div_N(t)` — and let `δ` be the cycle
`∑_i ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i)` on `X`. Then `i_* β - δ` is rationally
equivalent to zero on `X` **with witnesses inside `D`**.

Both the key formula of Stacks 0AYC, whose witnesses lie inside `D` because `f_i = 1` off `D`,
and the component comparison of Stacks 02T8, whose witnesses lie inside `Z_i ∩ D`, contribute
only carriers inside `D`; see the module documentation. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinCycle_sub
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt))
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (ℱ : KeyFormulaSituation L N)
    (hratio : ∀ i, ¬ Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt (ℱ.componentPoint i) → ℱ.ratioL i = 1)
    (hgenL : ∀ i, ¬ Stacks.Divisors.zeroScheme X L s ≤
        integralComponentAt (ℱ.componentPoint i) →
      ℱ.localGeneratorL i = L.presheaf.germ ⊤ (ℱ.componentPoint i) trivial s)
    (β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)
    (hβ : ∀ z : (Stacks.Divisors.zeroScheme X L s).subscheme, β.1 z =
      ∑ᶠ i : ℱ.Index, ℱ.orderN i *
        (gysinComponentCycle C p k L s (firstChernComponentClass C p k L)
          (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
          (ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C p k hn i)).1 z)
    (δ : CycleGroup C p k)
    (hδ : ∀ x : X, δ.1 x = ∑ᶠ i : ℱ.Index, ℱ.orderL i *
      (properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
        (chernCycleOfRestrictedStalk C p k N (integralComponentAt (ℱ.componentPoint i))
          (isIntegral_integralComponentAt _)
          (ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C p k hn i)
          (genericPointOf_integralComponentAt _) (ℱ.localGeneratorN i))).1 x) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k β - δ)
      ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
  classical
  have hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt) :=
    ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C p k hn
  have hlocal : LocallyFinite fun i : ℱ.Index ↦
      ((integralComponentAt (ℱ.componentPoint i)).support : Set X) :=
    ℱ.locallyFinite_support_integralComponentAt
  -- the three families of `k`-cycles on `X`
  set gc : ℱ.Index → CycleGroup C p k := fun i ↦
    properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
      (gysinComponentCycle C p k L s (firstChernComponentClass C p k L)
        (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _) (hdim i))
    with hgc
  set dvL : ℱ.Index → CycleGroup C p k := fun i ↦
    properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (chernCycleOfRestrictedStalk C p k L (integralComponentAt (ℱ.componentPoint i))
        (isIntegral_integralComponentAt _) (hdim i) (genericPointOf_integralComponentAt _)
        (ℱ.localGeneratorL i))
    with hdvL
  set dvN : ℱ.Index → CycleGroup C p k := fun i ↦
    properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (chernCycleOfRestrictedStalk C p k N (integralComponentAt (ℱ.componentPoint i))
        (isIntegral_integralComponentAt _) (hdim i) (genericPointOf_integralComponentAt _)
        (ℱ.localGeneratorN i))
    with hdvN
  -- each family is supported on its own member
  have hsuppgc : ∀ i : ℱ.Index, Function.support (fun y ↦ (gc i).1 y) ⊆
      ((integralComponentAt (ℱ.componentPoint i)).support : Set X) := by
    intro i y hy
    simp only [hgc] at hy
    by_cases hr : y ∈ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base
    · obtain ⟨z, rfl⟩ := hr
      rw [Function.mem_support, properPushforward_apply_image_of_isClosedImmersion] at hy
      exact support_gysinComponentCycle_subset C p k L s (firstChernComponentClass C p k L)
        (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _) (hdim i) hy
    · exact absurd (properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _ hr) hy
  have hsuppdv : ∀ (i : ℱ.Index)
      (c : CycleGroup C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) k),
      Function.support (fun y ↦ (properPushforward C
        ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k c).1 y) ⊆
      ((integralComponentAt (ℱ.componentPoint i)).support : Set X) := by
    intro i c
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact support_properPushforward_subset C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k _
  have hfin : ∀ (w : ℱ.Index → ℤ) (c : ℱ.Index → CycleGroup C p k),
      (∀ i, Function.support (fun y ↦ (c i).1 y) ⊆
        ((integralComponentAt (ℱ.componentPoint i)).support : Set X)) →
      ∀ y : X, (Function.support fun i : ℱ.Index ↦ w i * (c i).1 y).Finite :=
    fun w c hc y ↦ finite_support_of_locallyFinite _ hlocal (fun i y ↦ w i * (c i).1 y)
      (fun i y hy ↦ hc i (right_ne_zero_of_mul (by exact hy))) y
  -- the Gysin cycle, pushed forward to `X`, is the weighted sum of the `gc i`
  have hpushβ : ∀ y : X,
      (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k β).1 y =
        ∑ᶠ i : ℱ.Index, ℱ.orderN i * (gc i).1 y := by
    intro y
    by_cases hr : y ∈ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base
    · obtain ⟨z, rfl⟩ := hr
      rw [properPushforward_apply_image_of_isClosedImmersion, hβ z]
      refine finsum_congr fun i ↦ ?_
      simp only [hgc]
      rw [properPushforward_apply_image_of_isClosedImmersion]
    · rw [properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _ hr]
      refine ((finsum_congr fun i ↦ ?_).trans finsum_zero).symm
      simp only [hgc]
      rw [properPushforward_apply_of_notMem_range C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _ hr, mul_zero]
  -- pushing forward an integer multiple
  have hzsmul : ∀ (i : ℱ.Index) (m : ℤ)
      (c : CycleGroup C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) k),
      properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
          (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k (m • c) =
        m • properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
          (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k c := fun i m c ↦
    map_zsmul (properPushforwardHom C
      ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k) m c
  -- the left hand side of the key formula, summand by summand
  have hcd : ∀ i : ℱ.Index, (ℱ.toKeyFormulaData C p).componentDifference i =
      ((ℱ.orderL i • chernCycleOfRestrictedStalk C p k N
          (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
          (hdim i) (genericPointOf_integralComponentAt _) (ℱ.localGeneratorN i) -
        ℱ.orderN i • chernCycleOfRestrictedStalk C p k L
          (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
          (hdim i) (genericPointOf_integralComponentAt _) (ℱ.localGeneratorL i))).1 :=
    fun _ ↦ rfl
  have hleft : ∀ y : X, (ℱ.toKeyFormulaData C p).leftCoeff C p y =
      ∑ᶠ i : ℱ.Index, (ℱ.orderL i * (dvN i).1 y - ℱ.orderN i * (dvL i).1 y) := by
    intro y
    show ∑ᶠ i : ℱ.Index, closedSubschemeCyclePushforward C p
      (integralComponentAt (ℱ.componentPoint i))
      ((ℱ.toKeyFormulaData C p).componentDifference i) y = _
    refine finsum_congr fun i ↦ ?_
    rw [hcd i]
    show (properPushforward C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) p
      (integralComponentAt (ℱ.componentPoint i)).subschemeι rfl k
      (ℱ.orderL i • chernCycleOfRestrictedStalk C p k N
          (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
          (hdim i) (genericPointOf_integralComponentAt _) (ℱ.localGeneratorN i) -
        ℱ.orderN i • chernCycleOfRestrictedStalk C p k L
          (integralComponentAt (ℱ.componentPoint i)) (isIntegral_integralComponentAt _)
          (hdim i) (genericPointOf_integralComponentAt _) (ℱ.localGeneratorL i))).1 y = _
    rw [properPushforward_sub, hzsmul i, hzsmul i]
    simp only [hdvL, hdvN]
    rfl
  -- the left hand side of the key formula, as a `k`-cycle
  have hmemα : (ℱ.toKeyFormulaData C p).leftCycle C p ∈ cyclesOfDimension C p k := by
    have h := (ℱ.toKeyFormulaData C p).leftCycle_mem_cyclesOfDimension C p hn
      (deltaDimensionFunction_apply C p)
    rwa [show (k + 2 - 2 : ℤ) = k from by ring] at h
  obtain ⟨α, hαval⟩ : ∃ α : CycleGroup C p k,
      ∀ y : X, α.1 y = (ℱ.toKeyFormulaData C p).leftCoeff C p y :=
    ⟨⟨(ℱ.toKeyFormulaData C p).leftCycle C p, hmemα⟩, fun _ ↦ rfl⟩
  -- the key formula: `α` is rationally equivalent to zero inside `D`
  have hαzero : IsRationallyEquivalentToZeroWithin C p k α
      ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
    refine (ℱ.isRationallyEquivalentToZeroWithin_leftCoeff C p
      (fun i ↦ ℱ.componentPoint i ∈ ((Stacks.Divisors.zeroScheme X L s).support : Set X))
      (fun i hi ↦ hratio i fun hle ↦ hi ((le_integralComponentAt_iff_mem_support _ _).1 hle))
      hdim α hαval).mono ?_
    refine Set.iUnion_subset fun j ↦ ?_
    have hcl : (((ℱ.toKeyFormulaData C p).component j.1).support : Set X) =
        closure {ℱ.componentPoint j.1} := coe_support_integralComponentAt _
    rw [hcl]
    exact ((Stacks.Divisors.zeroScheme X L s).support.isClosed.closure_subset_iff).mpr
      (Set.singleton_subset_iff.mpr j.2)
  -- the component comparisons, summed over the locally finite family
  have hsum : IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k β - δ + α)
      (⋃ i : ℱ.Index, ((integralComponentAt (ℱ.componentPoint i)).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L s).support : Set X)) := by
    refine rationallyEquivalentToZeroWithin_finsum C p k
      (fun i ↦ ℱ.orderN i • (gc i - dvL i))
      (fun i ↦ ((integralComponentAt (ℱ.componentPoint i)).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L s).support : Set X))
      (hlocal.subset fun i ↦ Set.inter_subset_left) (fun i ↦ ?_) fun y ↦ ?_
    · refine isRationallyEquivalentToZeroWithin_zsmul C p k
        (isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub C p L s k
          (ℱ.componentPoint i) (hdim i) (ℱ.isStalkBasis_localGeneratorL i) (hgenL i))
        (ℱ.orderN i) fun x ↦ ?_
      rfl
    · have hzs : ∀ i : ℱ.Index, ((ℱ.orderN i • (gc i - dvL i) : CycleGroup C p k)).1 y =
          ℱ.orderN i * ((gc i).1 y - (dvL i).1 y) := fun _ ↦ rfl
      show (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k β).1 y - δ.1 y + α.1 y = _
      have hdvsupp : ∀ i, Function.support (fun y ↦ (dvL i).1 y) ⊆
          ((integralComponentAt (ℱ.componentPoint i)).support : Set X) := fun i ↦ hsuppdv i _
      rw [hpushβ y, hδ y, hαval y, hleft y,
        finsum_sub_distrib (hfin ℱ.orderL dvN (fun i ↦ hsuppdv i _) y)
          (hfin ℱ.orderN dvL hdvsupp y),
        sub_add_sub_cancel,
        ← finsum_sub_distrib (hfin ℱ.orderN gc hsuppgc y) (hfin ℱ.orderN dvL hdvsupp y)]
      exact finsum_congr fun i ↦ by rw [hzs i]; ring
  have h := isRationallyEquivalentToZeroWithin_add C p k
    (hsum.mono (Set.iUnion_subset fun _ ↦ Set.inter_subset_right))
    (isRationallyEquivalentToZeroWithin_neg C p k hαzero)
  rwa [← sub_eq_add_neg, add_sub_cancel_right] at h

end Comparison

end Stacks.Chow

end
