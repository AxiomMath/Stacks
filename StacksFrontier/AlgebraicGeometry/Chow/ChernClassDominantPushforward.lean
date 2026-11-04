module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.RationalEquivalenceUnconditional

/-!
# The first Chern class of an invertible module under a proper dominant pushforward

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
integral and locally of finite type over `S` with `dim_δ(X) = dim_δ(Y) = n`, let `f : X ⟶ Y` be
a proper dominant morphism over `S` and let `L` be an invertible `𝒪_Y`-module. Then

  `f_*(c₁(f^*L) ∩ [X]) = [R(X) : R(Y)] c₁(L) ∩ [Y] = c₁(L) ∩ f_*[X]`

in `CH_{n-1}(Y)`. This is the second displayed equation of
[Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST); its first displayed equation, the
identity of cycles `f_*(div_{f^*L}(f^*s)) = [R(X) : R(Y)] div_L(s)`, is
`Stacks.Chow.properPushforward_meromorphicDivisorCycleOfInvertible`.

## The argument

The cap product of Stacks 02SO evaluates on the fundamental cycle `[X]` of the whole scheme as
the class of the divisor cycle of any nonzero meromorphic section of `L`, because `X` is a closed
subscheme of itself, cut out by the trivial ideal sheaf, and the choice of section is immaterial
by Stacks 02SJ (2); that is
`Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_mk`. So both outer members of the
displayed equation reduce to divisor cycles, where the first displayed equation of the tag
applies: the first equality is that equation read in `CH_{n-1}(Y)`. The second equality is the
first Chern class cap, an additive map, applied to `f_*[X] = [R(X) : R(Y)] [Y]`
(`Stacks.Chow.properPushforward_fundamentalCycle`), which holds because `[X]` is the prime cycle
of the generic point of `X` with coefficient one and the weight with which that point enters the
pushforward of Stacks 02R4 is the residue degree there, the degree of the extension of function
fields.

## Main results

* `Stacks.Chow.genericStalkPullback_ne_zero` — the pullback of a nonzero meromorphic section
  along a dominant morphism of integral schemes is nonzero.
* `Stacks.Chow.properPushforward_fundamentalCycle` — `f_*[X] = [R(X) : R(Y)] [Y]` as cycles.
* `Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_mk` — the cap product on the
  fundamental cycle is the class of the divisor cycle of a nonzero meromorphic section.
* `Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_fundamentalCycle` — **the
  second displayed equation of Stacks 02ST**, both of its equalities.

## Implementation notes

The module sits beside, rather than inside,
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicDivisorPushforward`, which holds the first
displayed equation: the third member of the second equation needs the identification of the degree
of an extension of function fields with the residue degree of Stacks 02R4
(`Stacks.Chow.finrank_functionField_eq_residueDegree`), and that lives in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree`, which imports the first
displayed equation.

A meromorphic section is an element of the generic stalk `L_η`, the model of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`; the identification of that model with a
global section of `𝒦_Y(L)` is Stacks 01X5 (2), which this library does not have. The statements
below do not mention a section, so this does not qualify the attribute: a nonzero element of the
generic stalk is produced internally by `Stacks.Divisors.exists_ne_zero_genericStalk`, and the
class of its divisor cycle is the cap product of Stacks 02SO whatever the section is.

## References

* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### A section with a nonzero coordinate is nonzero -/

/-- A meromorphic section with a nonzero coordinate at some point is nonzero: the generic value
of a stalk basis spans the generic stalk freely, so a nonzero multiple of it is nonzero.

This is the converse of `Stacks.Divisors.IsCoordinateAt.ne_zero`. -/
theorem ne_zero_of_isCoordinateAt {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {L : X.Modules} {x : X} (hL : IsTrivializedNear L x)
    {s : L.presheaf.stalk (genericPoint X)} {a : X.functionField}
    (ha : IsCoordinateAt L x s a) (ha0 : a ≠ 0) : s ≠ 0 := by
  obtain ⟨m, hm, hsa⟩ := ha
  intro h0
  have hzero : a • toGenericStalk L x m = (0 : X.functionField) • toGenericStalk L x m := by
    rw [zero_smul, ← hsa, h0]
  exact ha0 ((hm.toGenericStalk hL).injective hzero)

/-- **The pullback of a nonzero meromorphic section is nonzero.** Along a dominant morphism of
integral schemes a coordinate `a ∈ R(Y)` of `s` at the generic point pulls back to a coordinate
of `p^*s` (`Stacks.Divisors.IsCoordinateAt.pullback`), and the extension of function fields is
injective, so that coordinate is again nonzero. -/
theorem genericStalkPullback_ne_zero {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Y) [IsDominant p] {L : Y.Modules}
    (hL : ∀ y : Y, IsTrivializedNear L y) {s : L.presheaf.stalk (genericPoint Y)} (hs : s ≠ 0) :
    genericStalkPullback p L s ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_isCoordinateAt (hL (p.base (genericPoint X))) s
  have ha0 : a ≠ 0 := ha.ne_zero hs
  refine ne_zero_of_isCoordinateAt ((hL (p.base (genericPoint X))).pullback) ha.pullback ?_
  exact fun h ↦ ha0 ((map_eq_zero_iff _ (dominantFunctionFieldMap p).injective).1 h)

/-- An invertible module is trivialized near every point. -/
private theorem forall_isTrivializedNear_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) : IsTrivializedNear L x :=
  have := Stacks.Divisors.isInvertible_presheaf L
  isTrivializedNear_of_isInvertible L x

/-- A delta-dimension equal to `n` is also equal to `n - 1 + 1`. -/
private theorem eq_coe_sub_one_add_one {a : EInt} {n : ℤ} (h : a = (n : EInt)) :
    a = ((n - 1 + 1 : ℤ) : EInt) := by
  rwa [sub_add_cancel]

/-! ### The pushforward of the fundamental cycle of an integral scheme -/

/-- **`f_*[X] = [R(X) : R(Y)] [Y]`.** For a proper dominant morphism of integral schemes of the
same delta-dimension `n` over the base, the proper pushforward of Stacks 02R4 carries the
fundamental cycle of `X` to the degree of the extension of function fields times the fundamental
cycle of `Y`.

The fundamental cycle of an integral scheme is the prime cycle of its generic point with
coefficient one (`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_single`), the generic point of
`X` lies over that of `Y`, and the weight attached to it by Stacks 02R4 is the residue degree
there, which `Stacks.Chow.finrank_functionField_eq_residueDegree` identifies with
`[R(X) : R(Y)]`. -/
theorem properPushforward_fundamentalCycle (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] {n : ℤ} (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt)) (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hf : f ≫ sY = sX) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    properPushforward C sX sY f hf n (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n) =
      (Module.finrank Y.functionField X.functionField : ℤ) •
        cycleAssociatedToClosedSubscheme C sY (𝟙 Y) n := by
  classical
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  have hgen : f.base (genericPoint X) = genericPoint Y := base_genericPoint_of_isDominant f
  have hrelX : relativeDimension C.dimensionFunction sX (genericPoint X) = n :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sX).symm.trans hnX)
  have hrelY : relativeDimension C.dimensionFunction sY (genericPoint Y) = n :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sY).symm.trans hnY)
  have hXsingle : (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n).1 =
      @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ (genericPoint X) (1 : ℤ) :=
    cycleAssociatedToClosedSubscheme_eq_single C sX (𝟙 X) n hrelX
  have hYsingle : (cycleAssociatedToClosedSubscheme C sY (𝟙 Y) n).1 =
      @Function.locallyFinsuppWithin.single Y _ ℤ (Classical.decEq Y) _ (genericPoint Y) (1 : ℤ) :=
    cycleAssociatedToClosedSubscheme_eq_single C sY (𝟙 Y) n hrelY
  have hdeg : (f.residueDegree (genericPoint X) : ℤ) =
      (Module.finrank Y.functionField X.functionField : ℤ) :=
    congrArg _ (finrank_functionField_eq_residueDegree f).symm
  refine Subtype.ext ?_
  rw [properPushforward_single C sX sY f hf n (genericPoint X) _ hXsingle, hgen,
    ite_eq_left hrelY]
  change _ = (Module.finrank Y.functionField X.functionField : ℤ) •
    (cycleAssociatedToClosedSubscheme C sY (𝟙 Y) n).1
  rw [hYsingle]
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  by_cases hy : y = genericPoint Y <;> simp [hy, ← hdeg]

/-! ### The cap product on the fundamental cycle -/

/-- **The first Chern class cap product on the fundamental cycle of an integral scheme.** On an
integral scheme of delta-dimension `n`, `c₁(L) ∩ [X]` is the class in `CH_{n-1}(X)` of the divisor
cycle of any nonzero meromorphic section of the invertible module `L`.

The fundamental cycle `[X]` is the cycle of `X` as a closed subscheme of itself through the
identity, so the component formula of Stacks 02SO applies at the trivial ideal sheaf, and the
choice of section is immaterial by Stacks 02SJ (2). The grading is written `n - 1 + 1` so that the
cycle lies in the domain `Z_{(n-1)+1}(X)` of the cap product without a cast. -/
theorem firstChernClassCapOfInvertible_fundamentalCycle_eq_mk (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X]
    [IsLocallyNoetherian X] {n : ℤ} (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    firstChernClassCapOfInvertible C p (n - 1) L
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) (n - 1 + 1)) =
      QuotientAddGroup.mk (meromorphicDivisorCycle C p hn
        (fun x ↦
          have := Stacks.Divisors.isInvertible_presheaf L
          isTrivializedNear_of_isInvertible L x) s).val := by
  classical
  have hLX : ∀ x : X, IsTrivializedNear L x := forall_isTrivializedNear_of_isInvertible L
  have hIntW : IsIntegral (⊥ : X.IdealSheafData).subscheme :=
    IsIntegral.of_isIso (asIso (⊥ : X.IdealSheafData).subschemeι).inv
  have hLNW : IsLocallyNoetherian (⊥ : X.IdealSheafData).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((⊥ : X.IdealSheafData).subschemeι ≫ p)
  have hnW : schemeDeltaDimension C ((⊥ : X.IdealSheafData).subschemeι ≫ p) = (n : EInt) :=
    (schemeDeltaDimension_of_iso C ((⊥ : X.IdealSheafData).subschemeι ≫ p) p
      (asIso (⊥ : X.IdealSheafData).subschemeι) rfl).symm.trans hn
  have hDim := eq_coe_sub_one_add_one hnW
  have hLW : ∀ x : (⊥ : X.IdealSheafData).subscheme,
      IsTrivializedNear ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj L) x :=
    fun x ↦ (hLX _).pullback
  have hs' : genericStalkPullback (⊥ : X.IdealSheafData).subschemeι L s ≠ 0 :=
    genericStalkPullback_ne_zero (⊥ : X.IdealSheafData).subschemeι hLX hs
  have h1 : (QuotientAddGroup.mk (firstChernComponentCycleRule C p (n - 1) L
          (⊥ : X.IdealSheafData) hIntW hDim) :
        chowGroup C ((⊥ : X.IdealSheafData).subschemeι ≫ p) (n - 1)) =
      QuotientAddGroup.mk (chernComponentCycle C ((⊥ : X.IdealSheafData).subschemeι ≫ p) hDim hLW
        (genericStalkPullback (⊥ : X.IdealSheafData).subschemeι L s)) :=
    (firstChernComponentClass_eq_mk C p (n - 1) L (⊥ : X.IdealSheafData) hIntW hDim).symm.trans
      (firstChernComponentClass_eq_mk_of_ne_zero C p (n - 1) L (⊥ : X.IdealSheafData) hDim hs')
  have hcyc : chernComponentCycle C ((⊥ : X.IdealSheafData).subschemeι ≫ p) hDim hLW
      (genericStalkPullback (⊥ : X.IdealSheafData).subschemeι L s) =
      (meromorphicDivisorCycle C ((⊥ : X.IdealSheafData).subschemeι ≫ p) hnW hLW
        (genericStalkPullback (⊥ : X.IdealSheafData).subschemeι L s)).val := Subtype.ext rfl
  let _ : Algebra X.functionField (⊥ : X.IdealSheafData).subscheme.functionField :=
    (dominantFunctionFieldMap (⊥ : X.IdealSheafData).subschemeι).toAlgebra
  have hrank :
      Module.finrank X.functionField (⊥ : X.IdealSheafData).subscheme.functionField = 1 := by
    rw [finrank_functionField_eq_residueDegree (⊥ : X.IdealSheafData).subschemeι]
    exact residueDegree_eq_one_of_isClosedImmersion _ _
  have hpush : properPushforward C ((⊥ : X.IdealSheafData).subschemeι ≫ p) p
      (⊥ : X.IdealSheafData).subschemeι rfl (n - 1)
        (meromorphicDivisorCycle C ((⊥ : X.IdealSheafData).subschemeι ≫ p) hnW hLW
          (genericStalkPullback (⊥ : X.IdealSheafData).subschemeι L s)).val =
      (meromorphicDivisorCycle C p hn hLX s).val := by
    have h := properPushforward_meromorphicDivisorCycle C
      ((⊥ : X.IdealSheafData).subschemeι ≫ p) p hnW hn
      (⊥ : X.IdealSheafData).subschemeι rfl hLX s hs
    rw [h, hrank]
    exact one_smul _ _
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso C p (𝟙 X)
      (⊥ : X.IdealSheafData).subschemeι (asIso (⊥ : X.IdealSheafData).subschemeι).symm (by simp)
      (n - 1 + 1),
    firstChernClassCapOfInvertible_integral_cycle C p (n - 1) L (⊥ : X.IdealSheafData) hIntW hDim]
  refine (congrArg (chowPushforwardOfIsClosedImmersion C
    ((⊥ : X.IdealSheafData).subschemeι ≫ p) p (⊥ : X.IdealSheafData).subschemeι rfl (n - 1))
    h1).trans ?_
  rw [hcyc]
  exact congrArg QuotientAddGroup.mk hpush

/-! ### The second displayed equation of Stacks 02ST -/

/-- **The second displayed equation of Stacks 02ST.** Let `X` and `Y` be integral and locally of
finite type over the base with `dim_δ(X) = dim_δ(Y) = n`, let `f : X ⟶ Y` be proper and dominant
over the base and let `L` be an invertible `𝒪_Y`-module. Then

`f_*(c₁(f^*L) ∩ [X]) = [R(X) : R(Y)] c₁(L) ∩ [Y] = c₁(L) ∩ f_*[X]`

in `CH_{n-1}(Y)`, the two equalities being the two conjuncts below.

The proper pushforward on Chow groups carries no hypothesis: Stacks 02S2 is
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`. The invertibility of `f^*L` is
Stacks 0B8L, the instance `Stacks.Divisors.pullback_isInvertible`. -/
@[stacks 02ST "second displayed equation"]
theorem properChowPushforward_firstChernClassCapOfInvertible_fundamentalCycle
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hf : f ≫ sY = sX) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    properChowPushforward C sX sY f hf (n - 1)
          (properPushforwardFactorsThroughRationalEquivalence C sX sY f hf (n - 1))
          (firstChernClassCapOfInvertible C sX (n - 1) ((Scheme.Modules.pullback f).obj L)
            (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (n - 1 + 1))) =
        (Module.finrank Y.functionField X.functionField : ℤ) •
          firstChernClassCapOfInvertible C sY (n - 1) L
            (cycleAssociatedToClosedSubscheme C sY (𝟙 Y) (n - 1 + 1)) ∧
      firstChernClassCapOfInvertible C sY (n - 1) L
          (properPushforward C sX sY f hf (n - 1 + 1)
            (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (n - 1 + 1))) =
        (Module.finrank Y.functionField X.functionField : ℤ) •
          firstChernClassCapOfInvertible C sY (n - 1) L
            (cycleAssociatedToClosedSubscheme C sY (𝟙 Y) (n - 1 + 1)) := by
  classical
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  have hLNX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hLNY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hLY : ∀ y : Y, IsTrivializedNear L y := forall_isTrivializedNear_of_isInvertible L
  obtain ⟨s, hs⟩ := exists_ne_zero_genericStalk (hLY (genericPoint Y))
  have hs' : genericStalkPullback f L s ≠ 0 := genericStalkPullback_ne_zero f hLY hs
  -- both outer members are classes of divisor cycles
  have hY := firstChernClassCapOfInvertible_fundamentalCycle_eq_mk C sY hnY L s hs
  have hX := firstChernClassCapOfInvertible_fundamentalCycle_eq_mk C sX hnX
    ((Scheme.Modules.pullback f).obj L) (genericStalkPullback f L s) hs'
  refine ⟨?_, ?_⟩
  · rw [hX, hY]
    refine (properChowPushforward_mk C sX sY f hf (n - 1) _ _).trans ?_
    refine (congrArg QuotientAddGroup.mk
      (properPushforward_meromorphicDivisorCycle C sX sY hnX hnY f hf hLY s hs)).trans ?_
    exact map_zsmul (QuotientAddGroup.mk' (rationalEquivalences C sY (n - 1))) _ _
  · rw [properPushforward_fundamentalCycle C sX sY (eq_coe_sub_one_add_one hnX)
    (eq_coe_sub_one_add_one hnY) f hf, map_zsmul]

end Stacks.Chow

end
