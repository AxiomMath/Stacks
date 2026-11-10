module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.DivisorCycle

/-!
# The divisor class of a meromorphic section is independent of the section

Let `X` be an integral scheme of delta-dimension `n` locally of finite type over the base scheme
`S` of chapter 42 of the Stacks Project and let `L` be an invertible `𝒪_X`-module. Two nonzero
meromorphic sections `s`, `s'` of `L` have divisor cycles `div_L(s)`, `div_L(s')` of
delta-dimension `n - 1` which differ by the principal divisor of their ratio `f ∈ R(X)`
(Stacks 02SH), and the principal divisor of a rational function on `X` is rationally equivalent to
zero. So the *class* of `div_L(s)` in `A_{n-1}(X)` does not depend on `s`.

That is part (2) of [Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ), and it is the
one statement standing between `Stacks.Chow.firstChernComponentClass` and the first Chern class of
the source.

## The two steps

* `Stacks.Chow.isRationallyEquivalentToZero_of_eq_principalCycle` — a `k`-cycle on an integral
  scheme of delta-dimension `k + 1` whose underlying cycle is `div(f)` is rationally equivalent to
  zero. Stacks 02RW asks for a locally finite family of integral closed subschemes of
  delta-dimension `k + 1` carrying rational functions; the one-element family consisting of `X`
  itself is admissible, because `X` *is* a closed subscheme of itself: the trivial ideal sheaf
  `⊥ : X.IdealSheafData` has `IsIso (⊥).subschemeι`
  (`AlgebraicGeometry.Scheme.IdealSheafData.isIso_subschemeι_iff_eq_bot`), and transporting `f`
  along that isomorphism changes neither the principal divisor
  (`Stacks.Chow.map_principalCycle_rationalFunctions_of_iso`) nor the delta-dimension
  (`Stacks.Chow.schemeDeltaDimension_of_iso`).
* `Stacks.Chow.weilDivisorAlgebraicCycle_meromorphic_eq_add` — the cycle form of Stacks 02SH. It
  is stated for the underlying `AlgebraicGeometry.AlgebraicCycle`, with no grading, because its
  two consumers grade it differently: `Stacks.Chow.meromorphicDivisorCycle` produces an
  `(n-1)`-cycle from `dim_δ X = n` while `Stacks.Chow.chernComponentCycle` produces a `k`-cycle
  from `dim_δ X = k + 1`.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZero_principalDivisorCycle` — `div(f)` is rationally
  equivalent to zero, in the grading of Stacks 02RO.
* `Stacks.Chow.mk_eq_mk_of_coe_eq_add_principalCycle` — two `k`-cycles differing by `div(f)` have
  the same class in `A_k(X)`.
* `Stacks.Chow.mk_meromorphicDivisorCycle_eq` — **Stacks 02SJ (2)**: the class of `div_L(s)` in
  `A_{n-1}(X)` is independent of the nonzero meromorphic section `s`.
* `Stacks.Chow.mk_chernComponentCycle_eq` — the same in the grading the component rule of
  Stacks 02SO uses.
* `Stacks.Chow.mk_chernComponentCycleRule_eq`,
  `Stacks.Chow.firstChernComponentClass_eq_mk_of_ne_zero` — the component rule of Stacks 02SO
  evaluates, in the Chow group, to the class of the divisor cycle of *any* nonzero meromorphic
  section of `L|_W`, not only of the one it chose.
* `Stacks.Chow.mk_divisorOfMeromorphicSectionCycle_eq` — the same for the divisor cycle of a
  regular meromorphic section of Stacks 02SJ (1), `Stacks.Chow.divisorOfMeromorphicSectionCycle`.

## What this is not

The model of a meromorphic section used here is the one of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`: on an integral scheme the sheaf `𝒦_X(L)`
of meromorphic sections is the constant sheaf with value the generic stalk `L_η`, so a meromorphic
section is an element of `L_η` and regularity is nonvanishing. Identifying that model with the
source's sheaf of meromorphic sections is Stacks 01X5 (2), which this repository does not have, so
**no declaration here carries a Stacks attribute for Tag 02SJ**; composing with Stacks 01X5 (2) is
what recovers the source statement.

For the same reason `Stacks.Chow.mk_divisorOfMeromorphicSectionCycle_eq`, which *is* stated for a
regular global section of `𝒦_X(L)`, takes the nonvanishing of the generic values as an explicit
hypothesis rather than deriving it from regularity: regularity of a section of `𝒦_X(L)` is
injectivity of the map it induces from the total quotient sheaf, and that it forces the generic
value to be nonzero is part of the same comparison.

## References

* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The principal divisor of a rational function on `X` is rationally equivalent to zero -/

section Principal

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X]

/-- **The principal divisor of a rational function on `X` itself is rationally equivalent to
zero.**

Stacks 02RW presents rational equivalence by locally finite families of integral closed subschemes
`W ⊆ X` of delta-dimension `k + 1` carrying nonzero rational functions. The one-element family
`W = X` is such a family: `X` is a closed subscheme of itself, cut out by the trivial ideal sheaf
`⊥`, and `(⊥ : X.IdealSheafData).subschemeι` is an isomorphism. The statement is taken in the
flexible form "`α` is a `k`-cycle whose underlying cycle is `div(f)`" so that it applies in every
grading convention; the nonvanishing of `f` enters only through the units of `R(X)`. -/
theorem isRationallyEquivalentToZero_of_eq_principalCycle [IsLocallyNoetherian X] {k : ℤ}
    (hk : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) {f : X.functionField} (hf : f ≠ 0)
    (α : CycleGroup C p k) (hα : (α : AlgebraicCycle X ℤ) = principalCycle X f) :
    IsRationallyEquivalentToZero C p k α := by
  set I : X.IdealSheafData := ⊥ with hIdef
  let φ : I.subscheme ≅ X := asIso I.subschemeι
  have hI : IsIntegral I.subscheme := IsIntegral.of_isIso φ.inv
  have : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ p)
  have hφhom : φ.hom = I.subschemeι := rfl
  have hDim : schemeDeltaDimension C (I.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) := by
    rw [← schemeDeltaDimension_of_iso C (I.subschemeι ≫ p) p φ (by rw [hφhom]), hk]
  -- the rational function, transported to the trivial closed subscheme
  set e := (rationalFunctionsEquivFunctionField X).1 with hedef
  have hune : e.symm f ≠ 0 := fun h ↦ hf (by rw [← e.apply_symm_apply f, h, map_zero])
  set u : (rationalFunctions X)ˣ := Units.mk0 (e.symm f) hune with hudef
  set g : (rationalFunctions I.subscheme)ˣ := (rationalFunctionsUnitsMulEquivOfIso φ).symm u
    with hgdef
  have hgu : rationalFunctionsRingEquivOfIso φ (g : rationalFunctions I.subscheme) =
      (u : rationalFunctions X) := by
    rw [← rationalFunctionsUnitsMulEquivOfIso_coe φ g, hgdef, MulEquiv.apply_symm_apply]
  have hw : ∀ z : I.subscheme,
      relativeDimension C.dimensionFunction (I.subschemeι ≫ p) z =
        relativeDimension C.dimensionFunction p (φ.hom.base z) :=
    fun z ↦ relativeDimension_comp_closedImmersion C.dimensionFunction I.subschemeι p z
  have hpush : principalDivisorPushforward C p I hI g = principalCycle X f := by
    have h := map_principalCycle_rationalFunctions_of_iso φ
      (relativeDimension C.dimensionFunction (I.subschemeι ≫ p))
      (relativeDimension C.dimensionFunction p) hw (g : rationalFunctions I.subscheme)
    rw [hgu, hudef, Units.val_mk0, e.apply_symm_apply] at h
    exact h
  refine ⟨PUnit.{u + 1}, fun _ ↦ I, fun _ ↦ hI, fun _ ↦ hDim,
    fun x ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩, fun _ ↦ g, fun x ↦ ?_⟩
  change (α : AlgebraicCycle X ℤ) x = ∑ᶠ _ : PUnit.{u + 1}, _
  rw [finsum_unique, hα, ← hpush]

/-- **Stacks 02RW for a principal divisor on `X` itself.** On an integral scheme of
delta-dimension `n` the cycle `div(f)` of a nonzero rational function is rationally equivalent to
zero.

This is the named form of `Stacks.Chow.isRationallyEquivalentToZero_of_eq_principalCycle` at
`Stacks.Chow.principalDivisorCycle`, which is Stacks 02RO's reading of `div(f)` as an element of
`Z_{n-1}(X)`. -/
theorem isRationallyEquivalentToZero_principalDivisorCycle [IsLocallyNoetherian X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {f : X.functionField} (hf : f ≠ 0) :
    IsRationallyEquivalentToZero C p (n - 1) (principalDivisorCycle C p hn f) := by
  refine isRationallyEquivalentToZero_of_eq_principalCycle C p (k := n - 1) ?_ hf _ rfl
  rw [hn]
  norm_num

end Principal

/-! ### The class of a cycle is unchanged by adding a principal divisor -/

/-- Two `k`-cycles on an integral scheme of delta-dimension `k + 1` whose underlying cycles differ
by the principal divisor of a nonzero rational function have the same class in the Chow group
`A_k(X)`. -/
theorem mk_eq_mk_of_coe_eq_add_principalCycle (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] [IsLocallyNoetherian X] {k : ℤ}
    (hk : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) {f : X.functionField} (hf : f ≠ 0)
    (α β : CycleGroup C p k)
    (h : (α : AlgebraicCycle X ℤ) = (β : AlgebraicCycle X ℤ) + principalCycle X f) :
    (QuotientAddGroup.mk α : chowGroup C p k) = QuotientAddGroup.mk β := by
  refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
  refine isRationallyEquivalentToZero_of_eq_principalCycle C p hk hf (α - β) ?_
  change (α : AlgebraicCycle X ℤ) - (β : AlgebraicCycle X ℤ) = principalCycle X f
  rw [h, add_sub_cancel_left]

/-! ### The cycle form of Stacks 02SH -/

section Ratio

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L : X.Modules}

/-- **Stacks 02SH, as an identity of cycles.** The Weil divisor of a meromorphic section `s = f·s'`
of `L`, read as an algebraic cycle, is the cycle of the Weil divisor of `s'` plus the principal
divisor of `f`.

This is `Stacks.Divisors.orderOfVanishing_eq_add_ord_of_eq_smul` at the generic point of every
prime divisor, together with the vanishing of all three coefficient functions at every other
point. No grading is imposed: the consumers of this identity grade the two sides differently. -/
theorem weilDivisorAlgebraicCycle_meromorphic_eq_add (hL : ∀ x : X, IsTrivializedNear L x)
    {s s' : L.presheaf.stalk (genericPoint X)} (hs' : s' ≠ 0) {f : X.functionField} (hf : f ≠ 0)
    (hsf : s = f • s') :
    weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s) =
      weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s') + principalCycle X f := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  change weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s) x =
    weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s') x + principalCycle X f x
  rw [weilDivisorAlgebraicCycle_apply, weilDivisorAlgebraicCycle_apply, principalCycle_apply]
  by_cases hx : ∃ Z : PrimeDivisor X, Z.genericPoint = x
  · obtain ⟨Z, rfl⟩ := hx
    rw [weilDivisorCoeff_genericPoint, weilDivisorCoeff_genericPoint,
      weilDivisorOfMeromorphicSection_apply, weilDivisorOfMeromorphicSection_apply]
    exact orderOfVanishing_eq_add_ord_of_eq_smul (hL Z.genericPoint) hs' hf hsf
  · have hne : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x := fun Z hZ ↦ hx ⟨Z, hZ⟩
    have hcoh : coheight x ≠ 1 := fun h ↦
      hne (PrimeDivisor.ofCoheightOne x h) (PrimeDivisor.genericPoint_ofCoheightOne x h)
    rw [weilDivisorCoeff_eq_zero _ x hne, weilDivisorCoeff_eq_zero _ x hne,
      X.ord_eq_zero_of_coheight_neq_one hcoh, add_zero]

end Ratio

/-! ### Stacks 02SJ (2): the divisor class is independent of the section -/

section Independence

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] {L : X.Modules}

/-- Two nonzero meromorphic sections have Weil divisor cycles differing by `div(f)`, `f ≠ 0`. -/
private theorem exists_ne_zero_weilDivisorAlgebraicCycle_eq_add {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {L : X.Modules} (hL : ∀ x : X, IsTrivializedNear L x)
    {s s' : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0) (hs' : s' ≠ 0) :
    ∃ f : X.functionField, f ≠ 0 ∧
      weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s) =
      weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hL s') + principalCycle X f := by
  obtain ⟨f, hsf, -⟩ := existsUnique_smul_eq (s := s) (hL (genericPoint X)) hs'
  have hf : f ≠ 0 := fun h ↦ hs (by rw [hsf, h, zero_smul])
  exact ⟨f, hf, weilDivisorAlgebraicCycle_meromorphic_eq_add hL hs' hf hsf⟩

/-- **Stacks 02SJ (2), in the generic-stalk model of a meromorphic section.** On an integral scheme
of delta-dimension `n` the class in `A_{n-1}(X)` of the divisor cycle `div_L(s)` of a nonzero
meromorphic section of `L` does not depend on `s`.

Two nonzero meromorphic sections have a unique ratio `f ∈ R(X)`
(`Stacks.Divisors.existsUnique_smul_eq`), their divisor cycles differ by `div(f)`
(Stacks 02SH), and `div(f)` is rationally equivalent to zero.

No Stacks attribute is attached; see the module documentation. -/
theorem mk_meromorphicDivisorCycle_eq {n : ℤ} (hn : schemeDeltaDimension C p = (n : EInt))
    (hL : ∀ x : X, IsTrivializedNear L x) {s s' : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0)
    (hs' : s' ≠ 0) :
    (QuotientAddGroup.mk (meromorphicDivisorCycle C p hn hL s).val :
        chowGroup C p (n - 1)) =
      QuotientAddGroup.mk (meromorphicDivisorCycle C p hn hL s').val := by
  obtain ⟨f, hf, h⟩ := exists_ne_zero_weilDivisorAlgebraicCycle_eq_add hL hs hs'
  refine mk_eq_mk_of_coe_eq_add_principalCycle C p (k := n - 1) ?_ hf _ _ h
  rw [hn]
  norm_num

/-- **Stacks 02SJ (2) for an invertible module.** The rank-one hypothesis of
`Stacks.Chow.mk_meromorphicDivisorCycle_eq` discharged by
`Stacks.Divisors.isTrivializedNear_of_isInvertible`.

No Stacks attribute is attached; see the module documentation. -/
theorem mk_meromorphicDivisorCycleOfInvertible_eq {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {s s' : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0) (hs' : s' ≠ 0) :
    (QuotientAddGroup.mk (meromorphicDivisorCycleOfInvertible C p hn L s).val :
        chowGroup C p (n - 1)) =
      QuotientAddGroup.mk (meromorphicDivisorCycleOfInvertible C p hn L s').val :=
  mk_meromorphicDivisorCycle_eq C p hn (isTrivializedNear_of_isInvertible L) hs hs'

/-- **Stacks 02SJ (2) in the grading of the component rule of Stacks 02SO.** On an integral scheme
of delta-dimension `k + 1` the class in `A_k(X)` of the component cycle of a nonzero meromorphic
section of `L` does not depend on the section.

No Stacks attribute is attached; see the module documentation. -/
theorem mk_chernComponentCycle_eq {k : ℤ}
    (hk : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) (hL : ∀ x : X, IsTrivializedNear L x)
    {s s' : L.presheaf.stalk (genericPoint X)} (hs : s ≠ 0) (hs' : s' ≠ 0) :
    (QuotientAddGroup.mk (chernComponentCycle C p hk hL s) : chowGroup C p k) =
      QuotientAddGroup.mk (chernComponentCycle C p hk hL s') := by
  obtain ⟨f, hf, h⟩ := exists_ne_zero_weilDivisorAlgebraicCycle_eq_add hL hs hs'
  exact mk_eq_mk_of_coe_eq_add_principalCycle C p hk hf _ _ h

end Independence

/-! ### The component rule of Stacks 02SO is the class of any nonzero section -/

section ComponentRule

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules) (W : X.IdealSheafData) [IsIntegral W.subscheme]
  [IsLocallyNoetherian W.subscheme]

/-- **The component rule of Stacks 02SO does not depend on the section it chose.** In the Chow
group `A_k(W)` the value of `Stacks.Chow.chernComponentCycleRule` at an integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1` is the class of the divisor cycle of *every* nonzero meromorphic
section of `L|_W`, not only of the one the rule picked with
`Stacks.Divisors.exists_ne_zero_genericStalk`.

This is `Stacks.Chow.mk_chernComponentCycle_eq` at `W`; it is what makes the rule canonical as a
Chow-class-valued datum, which is Stacks 02SJ (2) in the generic-stalk model.

The integrality of `W.subscheme`, which `Stacks.Chow.chernComponentCycleRule` takes as an explicit
argument, is an instance hypothesis here because the type of `s` already needs it; a consumer
holding it as a plain hypothesis `hW` writes `have := hW` first. Its local Noetherianity is also an
instance hypothesis, implied by the other hypotheses through
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.

No Stacks attribute is attached; see the module documentation. -/
theorem mk_chernComponentCycleRule_eq
    (hL : ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
      ∀ x : W.subscheme, IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    {s : ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.stalk
      (genericPoint W.subscheme)} (hs : s ≠ 0) :
    (QuotientAddGroup.mk (chernComponentCycleRule C p k L hL W inferInstance hDim) :
        chowGroup C (W.subschemeι ≫ p) k) =
      QuotientAddGroup.mk
        (chernComponentCycle C (W.subschemeι ≫ p) hDim (hL W inferInstance) s) :=
  mk_chernComponentCycle_eq C (W.subschemeι ≫ p) hDim (hL W inferInstance)
    (exists_ne_zero_genericStalk (hL W inferInstance (genericPoint W.subscheme))).choose_spec hs

variable [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **`Stacks.Chow.firstChernComponentClass` is the class of the divisor cycle of any nonzero
meromorphic section.** The Chow-class-valued component rule of an invertible module is as canonical
as Stacks 02SJ (2) makes it: its value at `W` is the class of `div_{L|_W}(s)` for every nonzero
`s ∈ (L|_W)_η`.

No Stacks attribute is attached; see the module documentation. -/
theorem firstChernComponentClass_eq_mk_of_ne_zero
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    {s : ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.stalk
      (genericPoint W.subscheme)} (hs : s ≠ 0) :
    firstChernComponentClass C p k L W inferInstance hDim =
      QuotientAddGroup.mk
        (chernComponentCycle C (W.subschemeι ≫ p) hDim
          (fun x ↦
            have := isInvertible_presheaf_modulePullback L W.subschemeι
            isTrivializedNear_of_isInvertible _ x) s) :=
  mk_chernComponentCycleRule_eq C p k L W
    (fun W' _ x ↦
      have := isInvertible_presheaf_modulePullback L W'.subschemeι
      isTrivializedNear_of_isInvertible _ x) hDim hs

end ComponentRule

/-! ### The divisor cycle of a regular meromorphic section -/

/-- **Stacks 02SJ (2) for the divisor cycle of Stacks 02SJ (1).** The class in `A_{n-1}(X)` of
`Stacks.Chow.divisorOfMeromorphicSectionCycle`, the divisor cycle of a regular meromorphic section
of an invertible module, is the same for two sections with nonzero generic values.

The nonvanishing of the generic values is an explicit hypothesis rather than a consequence of
regularity; see the module documentation.

No Stacks attribute is attached; see the module documentation. -/
theorem mk_divisorOfMeromorphicSectionCycle_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s s' : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)
    (hs' : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s')
    (hv : genericValue L s ≠ 0) (hv' : genericValue L s' ≠ 0) :
    (QuotientAddGroup.mk (divisorOfMeromorphicSectionCycle C p n hn L s hs) :
        chowGroup C p (n - 1)) =
      QuotientAddGroup.mk (divisorOfMeromorphicSectionCycle C p n hn L s' hs') := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have := isInvertible_presheaf L
  exact mk_meromorphicDivisorCycleOfInvertible_eq C p hn L hv hv'

end Stacks.Chow

end
