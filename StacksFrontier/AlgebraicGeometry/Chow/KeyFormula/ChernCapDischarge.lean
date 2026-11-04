module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.IntegralFamilyCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationExists
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationKeyFormula

/-!
# Discharging the key formula in Stacks 02TH and the integral case of Stacks 02TI

`Stacks.Chow.firstChernClassCap_comm_of_keyFormula` and
`Stacks.Chow.firstChernClassCap_eq_zero_of_keyFormula` prove Stacks 02TH and the integral case of
Stacks 02TI for a term `D` of `Stacks.Chow.KeyFormulaData` *granting* the key formula
`D.KeyFormula C p` of Stacks 0AYC. The key formula holds unconditionally for the data of a
sheaf-level situation, `Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData`, so both
statements hold with no hypothesis about the key formula on an `X` that is integral and locally
Noetherian, for two invertible modules with nonzero meromorphic sections.

## The component rules

Both statements take the first Chern class component rules of Stacks 02SO as parameters, tied to
the data by the hypothesis that the value of the rule of `L` at the member `Z_i` is the cycle
`div_{L|Z_i}(s_i|Z_i)` of the generator the situation chose. The rule
`Stacks.Chow.firstChernComponentCycleRule` of an invertible module does not satisfy that
hypothesis: it is built from a nonzero meromorphic section of `L|_W` chosen with
`Classical.choice`, which need not be the restriction of `s_i`, and two choices differ by a
principal divisor. So a rule meeting it is built here — `Stacks.Chow.restrictedChernRule`, the
rule of `Stacks.Chow.firstChernComponentCycleRule` with its value at each `Z_i` replaced by
`div_{L|Z_i}(s_i|Z_i)` — and the two rules are then compared *up to rational equivalence*, which
is all the cap product sees: the class of the component cycle is the class of the divisor cycle of
every nonzero meromorphic section (`Stacks.Chow.firstChernComponentClass_eq_mk_of_ne_zero`,
Stacks 02SJ (2)), and the cap product depends on its rule only through those classes
(`Stacks.Chow.firstChernClassCap_congr`). The restriction `s_i|_{Z_i}` of a generator is a
generator of the stalk at the generic point of `Z_i`, hence nonzero, so the comparison applies.
The conclusions below are therefore stated for the canonical cap product
`Stacks.Chow.firstChernClassCapOfInvertible` of the invertible module itself, with no rule
parameter and no hypothesis tying a rule to the data.

The vanishing of the second restricted divisor, the hypothesis `hzeroN` of
`Stacks.Chow.firstChernClassCap_eq_zero_of_keyFormula`, is not needed either: with `N = 𝒪_X` the
cap product `c₁(𝒪_X) ∩ -` vanishes identically by
`Stacks.Chow.firstChernClassCapOfInvertible_unit`, the second half of Stacks 02SP, which is
stronger than what the trivial component rule gives.

## The two divisor cycles

The presentations `div_L(s) = ∑ ord_{B_i}(f_i) [Z_i]` and `div_N(t) = ∑ ord_{B_i}(g_i) [Z_i]` are
parameters of `Stacks.Chow.firstChernClassCap_comm_of_keyFormula`, as in the source statement.
Neither survives: both divisor cycles are presented by the family of the situation, because a
prime divisor outside it carries no order of vanishing — that is
`Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_apply_of_apply_eq_zero_of_notMem`,
applied to each of `div_L(s)` and `div_N(t)`. So the cycles of
`Stacks.Chow.divisorCycleOfInvertibleSection`, the divisors of the two sections themselves, may
be substituted, and the statement of Stacks 02TH is reached with no parameter left:
`Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm`.

In the vanishing statement the first cycle disappears altogether:
`Stacks.Chow.exists_integralFamilyCycle` produces one from the local finiteness of the family,
and the conclusion does not mention it.

## Main definitions

* `Stacks.Chow.chernCycleOfRestrictedStalk` — the cycle `div_{M|W}(m|_W)` of the restriction to
  `W` of an element of `M_x`, `x` the generic point of `W`, graded as a component rule value.
* `Stacks.Chow.restrictedChernRule` — a component rule of Stacks 02SO whose value along a given
  family of points is the divisor of a given family of restricted stalk generators.
* `Stacks.Chow.divisorCycleOfInvertibleSection` — the divisor cycle `div_L(s)` of Stacks 02SJ (1)
  on a scheme of delta-dimension `k + 2`, as a `(k+1)`-cycle.
* `Stacks.Chow.KeyFormulaSituation.weilDivisorCycleN` — the same for the section `t` of `N` of a
  situation.

## Main results

* `Stacks.Chow.rationallyEquivalent_restrictedChernRule` — that rule takes values rationally
  equivalent to those of `Stacks.Chow.firstChernComponentCycleRule`.
* `Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorL_apply` and
  `Stacks.Chow.KeyFormulaSituation.weilDivisorAlgebraicCycle_weilDivisorN_apply` —
  `div_L(s) = ∑ ord_{B_i}(f_i) [Z_i]` and `div_N(t) = ∑ ord_{B_i}(g_i) [Z_i]`.
* `Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm` — **Stacks 02TH**: for two
  invertible modules with nonzero meromorphic sections on an integral `X` of delta-dimension
  `k + 2`, `c₁(N) ∩ div_L(s) = c₁(L) ∩ div_N(t)` in `A_k(X)`, with no hypothesis beyond the
  source's.
* `Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_comm` — the same for a
  situation, with the two cycles given by presentations.
* `Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_eq_zero` and
  `Stacks.Chow.KeyFormulaSituation.firstChernClassCapOfInvertible_weilDivisorCycleN` — **the
  integral case of Stacks 02TI**, unconditionally: `c₁(L) ∩ div_{𝒪_X}(f) = 0` in `A_k(X)`.
* `Stacks.Chow.firstChernClassCapOfInvertible_weilDivisorCycle_eq_zero` — the same, with the
  situation produced from the two meromorphic sections.

## References

* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

open Stacks.Ample (unitModule)

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The restriction of a stalk generator is a nonzero meromorphic section -/

section Restrict

variable {X : Scheme.{u}} (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] in
/-- **The restriction of a generator of `M_x` to `W` is a nonzero meromorphic section of `M|_W`**,
`x` the generic point of `W`. It is a basis of the stalk of `M|_W` there, and zero generates no
module over a nontrivial ring. -/
theorem restrictStalk_ne_zero (W : X.IdealSheafData) [IsIntegral W.subscheme] {x : X}
    (hx : W.subschemeι.base (genericPoint W.subscheme) = x) {m : M.presheaf.stalk x}
    (hm : IsStalkBasis M x m) : restrictStalk W M hx m ≠ 0 := by
  intro h
  have h01 : (0 : W.subscheme.presheaf.stalk (genericPoint W.subscheme)) = 1 :=
    (isStalkBasis_restrictStalk W M hx hm).injective (by simp only [h, smul_zero])
  exact zero_ne_one (α := W.subscheme.functionField) h01

end Restrict

/-! ### The component cycle of a restricted stalk generator -/

section Rule

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]

/-- **`div_{M|W}(m|_W)` as a component rule value.** For an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1` with generic point `x` and an element `m` of `M_x`, this is the divisor
cycle on `W` of the restricted meromorphic section `m|_W` of `M|_W`, as a `k`-cycle. -/
def chernCycleOfRestrictedStalk (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    {x : X} (hx : genericPointOf W hW = x) (m : M.presheaf.stalk x) :
    CycleGroup C (W.subschemeι ≫ p) k :=
  haveI := hW
  haveI : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  chernComponentCycle C (W.subschemeι ≫ p) hDim (isTrivializedNear_restrictModule W M)
    (restrictStalk W M hx m)

/-- On the integral closed subscheme attached to a point the cycle of a restricted element is the
divisor `Stacks.Chow.restrictedWeilDivisorAt` records. -/
theorem val_chernCycleOfRestrictedStalk (x : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) (m : M.presheaf.stalk x) :
    (chernCycleOfRestrictedStalk C p k M (integralComponentAt x)
          (isIntegral_integralComponentAt x) hDim (genericPointOf_integralComponentAt x) m).1 =
      weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p x m) :=
  rfl

/-! ### A component rule prescribed along a family of points -/

variable {ι : Type u} (ξ : ι → X) (m : (i : ι) → M.presheaf.stalk (ξ i))

/-- **The value of the prescribed rule at an integral closed subscheme.** It is
`div_{M|W}(m_i|_W)` when the generic point of `W` is `ξ_i`, and in every case rationally
equivalent to the value of `Stacks.Chow.firstChernComponentCycleRule`: the class of a component
cycle is the class of the divisor cycle of any nonzero meromorphic section, Stacks 02SJ (2). -/
theorem exists_restrictedChernCycle (hξ : Function.Injective ξ)
    (hm : ∀ i, IsStalkBasis M (ξ i) (m i)) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    ∃ c : CycleGroup C (W.subschemeι ≫ p) k,
      (∀ (i : ι) (hi : genericPointOf W hW = ξ i),
          c = chernCycleOfRestrictedStalk C p k M W hW hDim hi (m i)) ∧
        RationallyEquivalent C (W.subschemeι ≫ p) k c
          (firstChernComponentCycleRule C p k M W hW hDim) := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  by_cases h : ∃ i : ι, genericPointOf W hW = ξ i
  · obtain ⟨i, hi⟩ := h
    refine ⟨chernCycleOfRestrictedStalk C p k M W hW hDim hi (m i), ?_, ?_⟩
    · intro j hj
      have hji : j = i := hξ (hj.symm.trans hi)
      subst hji
      rfl
    · exact QuotientAddGroup.eq_iff_sub_mem.1
        ((firstChernComponentClass_eq_mk_of_ne_zero C p k M W hDim
            (restrictStalk_ne_zero M W hi (hm i))).symm.trans
          (firstChernComponentClass_eq_mk C p k M W hW hDim))
  · refine ⟨firstChernComponentCycleRule C p k M W hW hDim, fun i hi ↦ absurd ⟨i, hi⟩ h, ?_⟩
    exact QuotientAddGroup.eq_iff_sub_mem.1 rfl

/-- **A first Chern class component rule of Stacks 02SO prescribed along a family of points.** On
the integral closed subscheme with generic point `ξ_i` it is the divisor cycle of the restriction
of the generator `m_i` of `M_{ξ_i}`, and elsewhere it is
`Stacks.Chow.firstChernComponentCycleRule`. -/
def restrictedChernRule (hξ : Function.Injective ξ) (hm : ∀ i, IsStalkBasis M (ξ i) (m i)) :
    FirstChernComponentCycleRule C p k := fun W hW hDim ↦
  (exists_restrictedChernCycle C p k M ξ m hξ hm W hW hDim).choose

/-- The prescribed rule has the prescribed value at the integral closed subscheme with generic
point `ξ_i`. -/
theorem restrictedChernRule_of_genericPointOf (hξ : Function.Injective ξ)
    (hm : ∀ i, IsStalkBasis M (ξ i) (m i)) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) (i : ι)
    (hi : genericPointOf W hW = ξ i) :
    restrictedChernRule C p k M ξ m hξ hm W hW hDim =
      chernCycleOfRestrictedStalk C p k M W hW hDim hi (m i) :=
  (exists_restrictedChernCycle C p k M ξ m hξ hm W hW hDim).choose_spec.1 i hi

/-- **The prescribed rule is rationally equivalent to the rule of the module.** Changing the
chosen nonzero meromorphic section of `M|_W` moves the component cycle inside its class, which is
Stacks 02SJ (2). -/
theorem rationallyEquivalent_restrictedChernRule (hξ : Function.Injective ξ)
    (hm : ∀ i, IsStalkBasis M (ξ i) (m i)) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C (W.subschemeι ≫ p) k
      (restrictedChernRule C p k M ξ m hξ hm W hW hDim)
      (firstChernComponentCycleRule C p k M W hW hDim) :=
  (exists_restrictedChernCycle C p k M ξ m hξ hm W hW hDim).choose_spec.2

/-- The cap product of the prescribed rule is the cap product of the module: the two rules take
rationally equivalent values on every integral closed subscheme. -/
theorem firstChernClassCap_restrictedChernRule (hξ : Function.Injective ξ)
    (hm : ∀ i, IsStalkBasis M (ξ i) (m i)) (α : CycleGroup C p (k + 1)) :
    firstChernClassCap C p k (restrictedChernRule C p k M ξ m hξ hm) α =
      firstChernClassCapOfInvertible C p k M α :=
  firstChernClassCap_congr C p k _ _
    (rationallyEquivalent_restrictedChernRule C p k M ξ m hξ hm) α

end Rule

/-! ### The divisor cycle of a nonzero meromorphic section -/

section DivisorCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] {k : ℤ}

/-- **The divisor cycle `div_L(s)` of Stacks 02SJ (1) on a scheme of delta-dimension `k + 2`.**
The Weil divisor `div_L(s) = ∑_Z ord_{Z, L}(s) [Z]` of a meromorphic section `s` of an invertible
module `L`, read as a cycle of delta-dimension `k + 1`.

This is `Stacks.Chow.meromorphicDivisorCycleOfInvertible` — the construction of Stacks 02SJ (1)
in the generic-stalk model — with its grading normalized from `(k + 2) - 1` to `k + 1`, so that it
is an argument of `Stacks.Chow.firstChernClassCapOfInvertible` at `k` with no transport. Local
Noetherianity of `X` is not a hypothesis: it follows from `p` being locally of finite type. -/
def divisorCycleOfInvertibleSection (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt))
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.presheaf.stalk (genericPoint X)) : CycleGroup C p (k + 1) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have := isInvertible_presheaf L
  ⟨weilDivisorAlgebraicCycle
      (weilDivisorOfMeromorphicSection (isTrivializedNear_of_isInvertible L) s), by
    have h := weilDivisorAlgebraicCycle_mem_cyclesOfDimension_sub_one C p hn
      (weilDivisorOfMeromorphicSection (isTrivializedNear_of_isInvertible L) s)
    rwa [show (k + 2 - 1 : ℤ) = k + 1 from by ring] at h⟩

variable [IsLocallyNoetherian X]

/-- The coefficient of `div_L(s)` at the generic point of a prime divisor `Z` is the order of
vanishing `ord_{Z, L}(s)` of Stacks 02SF: the cycle is the divisor cycle of Stacks 02SJ (1). -/
@[simp]
theorem divisorCycleOfInvertibleSection_genericPoint
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.presheaf.stalk (genericPoint X)) (Z : Stacks.Divisors.PrimeDivisor X) :
    (divisorCycleOfInvertibleSection C p hn L s).1 Z.genericPoint =
      orderOfVanishing L s Z :=
  weilDivisorCoeff_genericPoint _ Z

omit [IsLocallyNoetherian X] in
/-- `div_L(s)` vanishes at every point which is not the generic point of a prime divisor. -/
theorem divisorCycleOfInvertibleSection_eq_zero
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.presheaf.stalk (genericPoint X)) (x : X)
    (hx : ∀ Z : Stacks.Divisors.PrimeDivisor X, Z.genericPoint ≠ x) :
    (divisorCycleOfInvertibleSection C p hn L s).1 x = 0 :=
  weilDivisorCoeff_eq_zero _ x hx

/-- The cycle is `Stacks.Chow.meromorphicDivisorCycleOfInvertible`, the construction of
Stacks 02SJ (1) in the generic-stalk model, with its grading `(k + 2) - 1` read as `k + 1`. -/
theorem val_divisorCycleOfInvertibleSection
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.presheaf.stalk (genericPoint X)) :
    (divisorCycleOfInvertibleSection C p hn L s).1 =
      have := isInvertible_presheaf L
      (meromorphicDivisorCycleOfInvertible C p hn L s).val.1 :=
  rfl

end DivisorCycle

/-! ### Stacks 02TH for a situation, with the key formula discharged -/

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

omit [IsLocallyNoetherian X] in
/-- Distinct indices give distinct generic points: distinct members of the family. -/
theorem componentPoint_injective : Function.Injective ℱ.componentPoint := fun _ _ h ↦
  ℱ.component_injective (Stacks.Divisors.PrimeDivisor.genericPoint_injective h)

omit [IsLocallyNoetherian X] in
/-- The family of supports of the members of the family is locally finite, read on the integral
closed subschemes attached to the generic points. -/
theorem locallyFinite_support_integralComponentAt :
    LocallyFinite fun i : ℱ.Index ↦
      ((integralComponentAt (ℱ.componentPoint i)).support : Set X) := by
  simpa only [coe_support_integralComponentAt,
    Stacks.Divisors.PrimeDivisor.support_eq_closure] using ℱ.locallyFinite_component

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- The component rule of `L` with its value at each member `Z_i` of the family replaced by the
divisor `div_{L|Z_i}(s_i|Z_i)` of the chosen generator. -/
def chernRuleL : FirstChernComponentCycleRule C p k :=
  restrictedChernRule C p k L ℱ.componentPoint ℱ.localGeneratorL ℱ.componentPoint_injective
    ℱ.isStalkBasis_localGeneratorL

/-- The component rule of `N` with its value at each member `Z_i` of the family replaced by the
divisor `div_{N|Z_i}(t_i|Z_i)` of the chosen generator. -/
def chernRuleN : FirstChernComponentCycleRule C p k :=
  restrictedChernRule C p k N ℱ.componentPoint ℱ.localGeneratorN ℱ.componentPoint_injective
    ℱ.isStalkBasis_localGeneratorN

omit [IsLocallyNoetherian X] in
/-- The cap product of the prescribed rule of `L` is the cap product of `L`. -/
theorem firstChernClassCap_chernRuleL (α : CycleGroup C p (k + 1)) :
    firstChernClassCap C p k (ℱ.chernRuleL C p k) α =
      firstChernClassCapOfInvertible C p k L α :=
  firstChernClassCap_restrictedChernRule C p k L ℱ.componentPoint ℱ.localGeneratorL
    ℱ.componentPoint_injective ℱ.isStalkBasis_localGeneratorL α

omit [IsLocallyNoetherian X] in
/-- The cap product of the prescribed rule of `N` is the cap product of `N`. -/
theorem firstChernClassCap_chernRuleN (α : CycleGroup C p (k + 1)) :
    firstChernClassCap C p k (ℱ.chernRuleN C p k) α =
      firstChernClassCapOfInvertible C p k N α :=
  firstChernClassCap_restrictedChernRule C p k N ℱ.componentPoint ℱ.localGeneratorN
    ℱ.componentPoint_injective ℱ.isStalkBasis_localGeneratorN α

omit [IsLocallyNoetherian X] in
/-- Each member of the family has delta-dimension `k + 1` on a scheme of delta-dimension
`k + 2`: its generic point has codimension one. -/
theorem schemeDeltaDimension_integralComponentAt_componentPoint
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (i : ℱ.Index) :
    schemeDeltaDimension C ((integralComponentAt (ℱ.componentPoint i)).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt) := by
  have h := schemeDeltaDimension_integralComponentAt_of_coheight_one C p hn
    (deltaDimensionFunction_apply C p) (ℱ.coheight_componentPoint i)
  rwa [show (k + 2 - 1 : ℤ) = k + 1 from by ring] at h

omit [IsLocallyNoetherian X] in
/-- **A Weil divisor supported on the family is presented by it**: if `D` has coefficient zero
along every prime divisor outside the family, then `D = ∑_i D(Z_i) [Z_i]` as cycles. At the
generic point `ξ_i` of a member only the `i`-th term survives, the fundamental cycle of `Z_j`
having coefficient `1` at `ξ_j` and `0` elsewhere; at a point which is no `ξ_i` every term
vanishes, and so does `D`. -/
theorem weilDivisorAlgebraicCycle_apply_of_apply_eq_zero_of_notMem
    (D : Stacks.Divisors.WeilDivisor X)
    (hD : ∀ Z : Stacks.Divisors.PrimeDivisor X, (∀ i, ℱ.component i ≠ Z) → D.val Z = 0)
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (x : X) :
    weilDivisorAlgebraicCycle D x =
      ∑ᶠ i, D.val (ℱ.component i) * (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x := by
  have hterm : ∀ j : ℱ.Index, x ≠ ℱ.componentPoint j → D.val (ℱ.component j) *
      (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint j)).subschemeι (k + 1)).1 x = 0 := fun j hj ↦ by
    rw [cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p
      (integralComponentAt (ℱ.componentPoint j)) (isIntegral_integralComponentAt _) (k + 1)
      (by rwa [genericPointOf_integralComponentAt]), mul_zero]
  by_cases h : ∃ i : ℱ.Index, ℱ.componentPoint i = x
  · obtain ⟨i₀, rfl⟩ := h
    have hone : (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i₀)).subschemeι (k + 1)).1
          (ℱ.componentPoint i₀) = 1 := by
      have h1 := cycleAssociatedToClosedSubscheme_integral_apply C p
        (integralComponentAt (ℱ.componentPoint i₀)) (isIntegral_integralComponentAt _)
        (ℱ.schemeDeltaDimension_integralComponentAt_componentPoint C p k hn i₀)
      rwa [genericPointOf_integralComponentAt] at h1
    have hval : weilDivisorAlgebraicCycle D (ℱ.componentPoint i₀) =
        D.val (ℱ.component i₀) := weilDivisorCoeff_genericPoint D.val (ℱ.component i₀)
    rw [finsum_eq_single _ i₀ fun j hj ↦ hterm j fun he ↦ hj (ℱ.componentPoint_injective he.symm),
      hone, mul_one, hval]
  · have hnot : ∀ i : ℱ.Index, ℱ.componentPoint i ≠ x := fun i hi ↦ h ⟨i, hi⟩
    have hzero : weilDivisorAlgebraicCycle D x = 0 := by
      by_contra hx0
      obtain ⟨Z, hZ, hDZ⟩ := exists_primeDivisor_of_weilDivisorCoeff_ne_zero D.val hx0
      exact hDZ (hD Z fun i hi ↦ hnot i (by rw [← hZ, ← hi]))
    rw [hzero]
    exact (finsum_congr fun i ↦ hterm i fun he ↦ hnot i he.symm).trans finsum_zero |>.symm

/-- **`div_L(s) = ∑ ord_{B_i}(f_i) [Z_i]`.** The divisor of the section `s` of `L` is presented by
the family: its coefficient at the generic point `ξ_i` is `ord_{Z_i, L}(s)`, and at every other
point it vanishes, a prime divisor outside the family carrying no order of vanishing. -/
theorem weilDivisorAlgebraicCycle_weilDivisorL_apply
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (x : X) :
    weilDivisorAlgebraicCycle ℱ.weilDivisorL x =
      ∑ᶠ i, ℱ.orderL i * (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x :=
  ℱ.weilDivisorAlgebraicCycle_apply_of_apply_eq_zero_of_notMem C p k ℱ.weilDivisorL
    ℱ.weilDivisorL_apply_eq_zero_of_notMem hn x

/-- **`div_N(t) = ∑ ord_{B_i}(g_i) [Z_i]`.** The divisor of the section `t` of `N` is presented by
the family: its coefficient at the generic point `ξ_i` is `ord_{Z_i, N}(t)`, and at every other
point it vanishes, a prime divisor outside the family carrying no order of vanishing. -/
theorem weilDivisorAlgebraicCycle_weilDivisorN_apply
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (x : X) :
    weilDivisorAlgebraicCycle ℱ.weilDivisorN x =
      ∑ᶠ i, ℱ.orderN i * (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x :=
  ℱ.weilDivisorAlgebraicCycle_apply_of_apply_eq_zero_of_notMem C p k ℱ.weilDivisorN
    ℱ.weilDivisorN_apply_eq_zero_of_notMem hn x

variable {k}

/-- **The divisor cycle `div_N(t)` of Stacks 02SJ (1) on `X`**, a cycle of delta-dimension
`k + 1` on a scheme of delta-dimension `k + 2`. -/
def weilDivisorCycleN (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) :
    CycleGroup C p (k + 1) :=
  ⟨weilDivisorAlgebraicCycle ℱ.weilDivisorN, by
    have h := weilDivisorAlgebraicCycle_mem_cyclesOfDimension_sub_one C p hn ℱ.weilDivisorN
    rwa [show (k + 2 - 1 : ℤ) = k + 1 from by ring] at h⟩

/-- **Stacks 02TH, with no hypothesis about the key formula.** On an integral, locally Noetherian
scheme of delta-dimension `k + 2`, intersecting the divisor cycle of a nonzero meromorphic section
of one invertible module with the first Chern class of the other gives the same class in `A_k(X)`,
in either order.

The key formula of Stacks 0AYC is supplied by
`Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData`, and the two component rules are the
canonical ones: the rules prescribed by the chosen generators, which the key formula is stated
against, take rationally equivalent values, and the cap product does not see the difference. -/
theorem firstChernClassCapOfInvertible_comm
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (divL divN : CycleGroup C p (k + 1))
    (hdivL : ∀ x : X, divL.1 x = ∑ᶠ i, ℱ.orderL i *
      (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x)
    (hdivN : ∀ x : X, divN.1 x = ∑ᶠ i, ℱ.orderN i *
      (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x) :
    firstChernClassCapOfInvertible C p k N divL =
      firstChernClassCapOfInvertible C p k L divN := by
  have hcomm := firstChernClassCap_comm_of_keyFormula C p hn (ℱ.toKeyFormulaData C p)
    (ℱ.keyFormula_toKeyFormulaData C p) (ℱ.chernRuleL C p k) (ℱ.chernRuleN C p k)
    (fun i hW hDim ↦ congrArg Subtype.val
      (restrictedChernRule_of_genericPointOf C p k L ℱ.componentPoint ℱ.localGeneratorL
        ℱ.componentPoint_injective ℱ.isStalkBasis_localGeneratorL _ hW hDim i
        (genericPointOf_integralComponentAt _)))
    (fun i hW hDim ↦ congrArg Subtype.val
      (restrictedChernRule_of_genericPointOf C p k N ℱ.componentPoint ℱ.localGeneratorN
        ℱ.componentPoint_injective ℱ.isStalkBasis_localGeneratorN _ hW hDim i
        (genericPointOf_integralComponentAt _)))
    divL divN hdivL hdivN
  exact ((ℱ.firstChernClassCap_chernRuleN C p k divL).symm.trans hcomm).trans
    (ℱ.firstChernClassCap_chernRuleL C p k divN)

end KeyFormulaSituation

/-! ### Stacks 02TH -/

section Comm

variable {X : Scheme.{u}} [IsIntegral X] (C : ChowSituation.{u}) (p : X ⟶ C.S)
  [LocallyOfFiniteType p] {k : ℤ}

/-- **Stacks 02TH.** Let `X` be integral and locally of finite type over the base scheme `S` of
chapter 42, of delta-dimension `k + 2`, let `L` and `N` be invertible modules on `X` and let `s`
and `t` be nonzero meromorphic sections of `L` and `N`. Writing `α = div_L(s)` and
`β = div_N(t)` for their divisor cycles of Stacks 02SJ (1),

  `c₁(N) ∩ α = c₁(L) ∩ β`  in  `A_k(X)`.

Nothing is assumed beyond the source's hypotheses: the family of prime divisors and the local
generators of the situation of Stacks 0AYB are produced by
`Stacks.Chow.keyFormulaSituationOf`, the key formula of Stacks 0AYC for it is
`Stacks.Chow.KeyFormulaSituation.keyFormula_toKeyFormulaData`, the component rules of Stacks 02SO
are the canonical ones of `Stacks.Chow.firstChernClassCapOfInvertible`, and the two divisor
cycles are presented by the family because a prime divisor outside it carries no order of
vanishing. The source states the conclusion in `CH_{n-2}(X)` for `dim_δ(X) = n`; here
`n = k + 2`. -/
@[stacks 02TH]
theorem firstChernClassCapOfInvertible_divisorCycle_comm
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    {s : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0)
    {t : N.presheaf.stalk (genericPoint X)} (ht : t ≠ 0) :
    firstChernClassCapOfInvertible C p k N (divisorCycleOfInvertibleSection C p hn L s) =
      firstChernClassCapOfInvertible C p k L (divisorCycleOfInvertibleSection C p hn N t) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact (keyFormulaSituationOf L N s t hs ht).firstChernClassCapOfInvertible_comm C p hn _ _
    ((keyFormulaSituationOf L N s t hs ht).weilDivisorAlgebraicCycle_weilDivisorL_apply C p k hn)
    ((keyFormulaSituationOf L N s t hs ht).weilDivisorAlgebraicCycle_weilDivisorN_apply C p k hn)

end Comm

/-! ### The integral case of Stacks 02TI, with the key formula discharged -/

section Vanishing

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] {k : ℤ}

/-- **The integral case of Stacks 02TI, with no hypothesis about the key formula.** On an
integral, locally Noetherian scheme of delta-dimension `k + 2`, intersecting the divisor cycle of
a nonzero meromorphic section of `𝒪_X` with the first Chern class of an invertible module gives
zero in `A_k(X)`.

This is Stacks 02TH with the second invertible module the structure sheaf: the class
`c₁(𝒪_X) ∩ div_L(s)` vanishes by `Stacks.Chow.firstChernClassCapOfInvertible_unit`, the second
half of Stacks 02SP, and the presentation of `div_L(s)` by the family is supplied by
`Stacks.Chow.exists_integralFamilyCycle`. -/
theorem KeyFormulaSituation.firstChernClassCapOfInvertible_eq_zero
    (ℱ : KeyFormulaSituation L (unitModule X))
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) (divN : CycleGroup C p (k + 1))
    (hdivN : ∀ x : X, divN.1 x = ∑ᶠ i, ℱ.orderN i *
      (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt (ℱ.componentPoint i)).subschemeι (k + 1)).1 x) :
    firstChernClassCapOfInvertible C p k L divN = 0 := by
  obtain ⟨divL, hdivL⟩ := exists_integralFamilyCycle C p (k + 1)
    (fun i ↦ integralComponentAt (ℱ.componentPoint i))
    ℱ.locallyFinite_support_integralComponentAt ℱ.orderL
  rw [← ℱ.firstChernClassCapOfInvertible_comm C p hn divL divN hdivL hdivN]
  exact firstChernClassCapOfInvertible_unit C p k divL

/-- **The integral case of Stacks 02TI, for the divisor cycle of the rational function.** On an
integral, locally Noetherian scheme of delta-dimension `k + 2`,
`c₁(L) ∩ div_{𝒪_X}(f) = 0` in `A_k(X)` for the divisor cycle of a nonzero meromorphic section `f`
of the structure sheaf. -/
theorem KeyFormulaSituation.firstChernClassCapOfInvertible_weilDivisorCycleN
    (ℱ : KeyFormulaSituation L (unitModule X))
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt)) :
    firstChernClassCapOfInvertible C p k L (ℱ.weilDivisorCycleN C p hn) = 0 :=
  KeyFormulaSituation.firstChernClassCapOfInvertible_eq_zero C p ℱ hn _
    (ℱ.weilDivisorAlgebraicCycle_weilDivisorN_apply C p k hn)

/-- **The integral case of Stacks 02TI for a pair of nonzero meromorphic sections.** For a nonzero
meromorphic section `s` of an invertible module `L` and a nonzero meromorphic section `f` of
`𝒪_X` on an integral, locally Noetherian `X` of delta-dimension `k + 2`, intersecting the divisor
cycle `div_{𝒪_X}(f)` with the first Chern class of `L` gives zero in `A_k(X)`.

The family of prime divisors the key formula is applied to is the one of
`Stacks.Chow.keyFormulaSituationOf`; the conclusion does not mention it. -/
theorem firstChernClassCapOfInvertible_weilDivisorCycle_eq_zero
    (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt))
    {s : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0)
    {f : (unitModule X).presheaf.stalk (genericPoint X)} (hf : f ≠ 0) :
    firstChernClassCapOfInvertible C p k L
        ((keyFormulaSituationOf L (unitModule X) s f hs hf).weilDivisorCycleN C p hn) = 0 :=
  KeyFormulaSituation.firstChernClassCapOfInvertible_weilDivisorCycleN C p _ hn

end Vanishing

end Stacks.Chow

end
