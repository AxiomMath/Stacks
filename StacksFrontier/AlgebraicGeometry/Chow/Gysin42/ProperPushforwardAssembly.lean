module

import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardContained
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained

/-!
# The proof of Stacks 02TA for the Gysin map of an invertible module

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be proper over `S`, let `L` be an invertible module on `X` and let
`s ∈ Γ(X, L)` be a global section with zero scheme `i : D = Z(s) ⟶ X`. Writing `D' = Z(f^*s)` and
`g : D' ⟶ D` for the morphism of Remark 0B6Y, Stacks 02TA asserts

  `i^* f_* α' = g_* (i')^* α'`  in  `A_k(D)`,  for `α' ∈ Z_{k+1}(X')`.

This file proves the rational equivalence of the two cycles underlying those classes, with no
hypothesis beyond the properness of `f` and the commutativity of `f` over `S`. The tag itself is
carried by `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible` in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible`, which is this result
read on Chow groups.

## Main results

* `Stacks.Chow.properChowPushforward_firstChernComponentClass_eq_zero` — the contained
  dimension-drop branch of the source's first step: the pushforward of the first Chern class of
  a component whose image has smaller delta-dimension vanishes in the Chow group of the image.
* `Stacks.Chow.properPushforward_gysinComponentCycleAt_of_le` — on a component inside the zero
  scheme the Gysin component cycle, pushed along `g`, factors through the component restriction
  `W' ⟶ W`.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinComponentDifference` — **Stacks 02TA on a
  single integral component**, as a rational equivalence carried over that component.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward` —
  **the identity of Stacks 02TA**, as a rational equivalence of cycles on `D` carried over the
  part of `D` lying over the closure of the image of `f`.
* `Stacks.Chow.rationallyEquivalent_gysinRule_extendCycleGroup_properPushforward` — **the
  identity of Stacks 02TA**, as a rational equivalence of cycles on `D`.

## The argument

The two sides are classes of cycles on `D`, and the two cycles are compared coefficientwise over
the integral components of `α'`: `Stacks.Chow.ComponentRule.extendCoeff_map_apply` writes the left
side as `∑_{x'} α'(x') · w(x') · c(f x')` and
`Stacks.Chow.ComponentRule.map_extendCycle_apply` writes the right side as
`∑_{x'} α'(x') · g_*(c'(x'))`, both locally finite sums over the points of `X'`, with `w` the
pushforward weight of Stacks 02R4 and `c`, `c'` the Gysin component cycles of Stacks 02T8.

Term by term the two differ by a cycle rationally equivalent to zero, and never by more: this is
the first step of the source's proof, in four cases according as the component `W' = closure {x'}`
lies inside `D'` or not and as `f` preserves its delta-dimension or not.

* Not inside `D'`, delta-dimension preserved. Both component cycles are fundamental cycles of
  scheme-theoretic intersections and the identity holds already as cycles:
  `Stacks.Chow.properPushforward_gysinComponentCycle_of_not_le`.
* Inside `D'`, delta-dimension preserved. Both component cycles are pushforwards of
  representatives of first Chern classes, and the identity is the second displayed equation of
  Stacks 02ST, `Stacks.Chow.properChowPushforward_firstChernComponentClass`, which holds in
  `A_k(W)` and not on the nose; the discrepancy is a rational equivalence carried by `W`.
* Not inside `D'`, delta-dimension drops. The weight is zero and so is the pushforward of the
  component cycle, by
  `Stacks.Chow.properPushforward_gysinComponentCycleAt_eq_zero_of_relativeDimension_ne`.
* Inside `D'`, delta-dimension drops. The weight is zero and the pushed-forward first Chern class
  vanishes in `A_k(W)`, by the drop branch of the first displayed equation of Stacks 02ST.

The per-component equivalences are then summed. That is Stacks 02RZ, and it needs each of them to
be witnessed inside a member of a locally finite family of subsets of `D`: the member for `x'` is
the part of `D` lying over the integral component of `f x'`, and the family is locally finite
because `α'` is a cycle and `f` is proper. The summation itself is
`Stacks.Chow.rationallyEquivalentToZeroWithin_finsum`, which keeps the union of those members as
the carrier of the resulting equivalence; the union lies over the closure of the image of `f`.

## Implementation notes

The two contained cases cannot be proved as identities of cycles. In those cases
`Stacks.Chow.gysinComponentCycle` is the pushforward of `Quotient.out` of a first Chern class, an
unconstrained representative, and nothing relates the representatives chosen on `W` and on `W'`
coefficientwise. This is why the comparison is made at the level of classes and why
`Stacks.Chow.properPushforward_gysinRule_extendCycleGroup`, which matches the two cycles
coefficient by coefficient, is not used here: the hypothesis that theorem carries,
`Stacks.Chow.GysinCompatibleWithPushforward`, is an equality of cycle coefficients and is
independent of the axioms.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The contained dimension-drop branch -/

/-- **The drop branch of the second displayed equation of Stacks 02ST on an integral component.**
For a proper dominant `π : W' ⟶ W` between integral closed subschemes lying over `f : X' ⟶ X`,
with `W'` of delta-dimension `k + 1` and `W` of smaller delta-dimension,

  `π_*(c₁((f^*L)|_{W'}) ∩ [W']) = 0`  in  `A_k(W)`.

The first Chern class on `W'` is the class of the divisor cycle of the pullback along `π` of a
nonzero meromorphic section chosen on `W` (Stacks 02SJ (2)), carried across the identification
`π^*(L|_W) ≅ (f^*L)|_{W'}`, and the pushforward of such a divisor cycle vanishes when the
delta-dimension drops. -/
theorem properChowPushforward_firstChernComponentClass_eq_zero (C : ChowSituation.{u})
    {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (p' : X' ⟶ C.S)
    [LocallyOfFiniteType p'] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {f : X' ⟶ X} (hf : f ≫ p = p') (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hlt : schemeDeltaDimension C (W.subschemeι ≫ p) < ((k + 1 : ℤ) : EInt))
    (W' : X'.IdealSheafData) (hW' : IsIntegral W'.subscheme)
    (hDim' : schemeDeltaDimension C (W'.subschemeι ≫ p') = ((k + 1 : ℤ) : EInt))
    (π : W'.subscheme ⟶ W.subscheme) [IsProper π] [IsDominant π]
    (hπ : π ≫ W.subschemeι = W'.subschemeι ≫ f) :
    letI : IsIntegral W.subscheme := hW
    letI : IsIntegral W'.subscheme := hW'
    properChowPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
        (componentSquare_comp hf hπ) k
        (properPushforwardFactorsThroughRationalEquivalence C (W'.subschemeι ≫ p')
          (W.subschemeι ≫ p) π (componentSquare_comp hf hπ) k)
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L) W' hW' hDim') = 0 := by
  classical
  have := hW
  have := hW'
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have : IsLocallyNoetherian W'.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W'.subschemeι ≫ p')
  -- the restriction of `L` to `W` and to `W'`, and the pullback of the former along `π`
  set M : W.subscheme.Modules := (Scheme.Modules.pullback W.subschemeι).obj L with hMdef
  set Q : W'.subscheme.Modules :=
    (Scheme.Modules.pullback W'.subschemeι).obj ((Scheme.Modules.pullback f).obj L) with hQdef
  set R : W'.subscheme.Modules := (Scheme.Modules.pullback π).obj M with hRdef
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
      W.subscheme.ringCatSheaf.2 M := isInvertible_presheaf_modulePullback L W.subschemeι
  have hMinv' : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property M := hMinv
  have hQinv : AlgebraicGeometry.SheafOfModules.IsInvertible W'.subscheme.presheaf
      W'.subscheme.ringCatSheaf.2 Q :=
    isInvertible_presheaf_modulePullback ((Scheme.Modules.pullback f).obj L) W'.subschemeι
  have hRinv : AlgebraicGeometry.SheafOfModules.IsInvertible W'.subscheme.presheaf
      W'.subscheme.ringCatSheaf.2 R := isInvertible_presheaf_modulePullback M π
  have hMtriv : ∀ x : W.subscheme, IsTrivializedNear M x := fun x =>
    isTrivializedNear_of_isInvertible M x
  have hQtriv : ∀ x : W'.subscheme, IsTrivializedNear Q x := fun x =>
    isTrivializedNear_of_isInvertible Q x
  have hRtriv : ∀ x : W'.subscheme, IsTrivializedNear R x := fun x =>
    isTrivializedNear_of_isInvertible R x
  -- a nonzero meromorphic section of `L|_W`, pulled back to `W'` and carried to `(f^*L)|_{W'}`
  obtain ⟨σ, hσ⟩ := exists_ne_zero_genericStalk (hMtriv (genericPoint W.subscheme))
  set τ := genericStalkPullback π M σ with hτdef
  have hτ : τ ≠ 0 := genericStalkPullback_ne_zero π hMtriv hσ
  set e := componentPullbackModuleIso f L hπ with hedef
  set t := stalkLinearMap R Q e.hom (genericPoint W'.subscheme) τ with htdef
  have ht : t ≠ 0 := fun h =>
    hτ ((bijective_stalkLinearMap R Q e.hom (genericPoint W'.subscheme)).1
      (h.trans (map_zero _).symm))
  -- Stacks 02SJ (2): the rule on `W'` is the class of the divisor cycle of the chosen section
  have hstep1 :
      firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L) W' hW' hDim' =
        QuotientAddGroup.mk (chernComponentCycle C (W'.subschemeι ≫ p') hDim' hQtriv t) :=
    firstChernComponentClass_eq_mk_of_ne_zero C p' k ((Scheme.Modules.pullback f).obj L) W'
      hDim' ht
  -- the module isomorphism does not move the divisor cycle
  have hstep2 : chernComponentCycle C (W'.subschemeι ≫ p') hDim' hQtriv t =
      chernComponentCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ :=
    chernComponentCycle_mapStalkLinearMap C (W'.subschemeι ≫ p') hDim' R Q e.hom hRtriv hQtriv τ
  -- the drop branch of the first displayed equation of Stacks 02ST
  have h02ST := properPushforward_meromorphicDivisorCycleOfInvertible_eq_zero C
    (W'.subschemeι ≫ p') (W.subschemeι ≫ p) hDim' hlt π (componentSquare_comp hf hπ) M σ hσ
  have hvalτ := val_meromorphicDivisorCycle_eq_chernComponentCycle C (W'.subschemeι ≫ p') hDim'
    hRtriv τ
  have hstep3 : properPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
      (componentSquare_comp hf hπ) k
      (chernComponentCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ) = 0 := by
    refine Subtype.ext ?_
    rw [← val_properPushforward_eq_of_val_eq C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
        (componentSquare_comp hf hπ)
        (meromorphicDivisorCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ).val
        (chernComponentCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ) hvalτ,
      show (properPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
          (componentSquare_comp hf hπ) (k + 1 - 1)
          (meromorphicDivisorCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ).val :
            CycleGroup C (W.subschemeι ≫ p) (k + 1 - 1)) = 0 from h02ST]
    rfl
  rw [hstep1]
  refine (properChowPushforward_mk C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
    (componentSquare_comp hf hπ) k _ _).trans ?_
  rw [hstep2, hstep3]
  exact map_zero _

/-! ### The Gysin component cycle at a point -/

/-- At a point of relative dimension `k + 1` the point-indexed Gysin component cycle of
Stacks 02T8 is the Gysin component cycle of the integral component through that point. -/
theorem gysinComponentCycleAt_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k) {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 1) :
    gysinComponentCycleAt C p k L s chern x =
      gysinComponentCycle C p k L s chern (integralComponentAt x)
        (isIntegral_integralComponentAt x)
        (schemeDeltaDimension_integralComponentAt_of_eq C p hx) :=
  Subtype.ext ((gysinRule C p k L s chern).totalize_eq _ _ _)

/-- The Gysin component cycle at a point of `X` is supported over the closure of that point: the
component rule of Stacks 02T8 attaches to a point a cycle lying over its integral component. -/
theorem support_gysinComponentCycleAt_subset (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k) (x : X) :
    Function.support (gysinComponentCycleAt C p k L s chern x).1 ⊆
      (Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {x} := by
  have h := (gysinRule C p k L s chern).support_totalize_subset (integralComponentAt x)
  rw [coe_support_integralComponentAt] at h
  exact h

/-! ### Representatives of Chow classes -/

/-- The class of an integer multiple of a chosen representative of a Chow class is that multiple
of the class. -/
theorem mk_zsmul_out (C : ChowSituation.{u}) {A : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (m : ℤ) (j : ℤ) (c : chowGroup C sA m) :
    (QuotientAddGroup.mk (j • Quotient.out c) : chowGroup C sA m) = j • c :=
  (map_zsmul (QuotientAddGroup.mk' (rationalEquivalences C sA m)) j (Quotient.out c)).trans
    (congrArg (fun z : chowGroup C sA m ↦ j • z) (Quotient.out_eq c))

/-- The class of the proper pushforward of a chosen representative of a Chow class is the proper
pushforward of that class on Chow groups. -/
theorem mk_properPushforward_out (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (h : A ⟶ B) [IsProper h]
    (hh : h ≫ sB = sA) (m : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB h hh m)
    (c : chowGroup C sA m) :
    (QuotientAddGroup.mk (properPushforward C sA sB h hh m (Quotient.out c)) :
        chowGroup C sB m) =
      properChowPushforward C sA sB h hh m hfac c :=
  (properChowPushforward_mk C sA sB h hh m hfac (Quotient.out c)).symm.trans
    (congrArg (fun z : chowGroup C sA m ↦ properChowPushforward C sA sB h hh m hfac z)
      (Quotient.out_eq c))

/-- The image in the zero scheme `Z(s)` of a closed subscheme `W` containing it lies over `W`:
the inclusion composed with the closed immersion of `Z(s)` is the closed immersion of `W`. -/
theorem range_inclusion_subset_preimage_support {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {W : X.IdealSheafData} (hle : Divisors.zeroScheme X L s ≤ W) :
    Set.range (Scheme.IdealSheafData.inclusion hle).base ⊆
      (Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X) := by
  rintro y ⟨z, rfl⟩
  have hcomp : (Divisors.zeroScheme X L s).subschemeι.base
      ((Scheme.IdealSheafData.inclusion hle).base z) = W.subschemeι.base z :=
    congrArg (fun m : W.subscheme ⟶ X ↦ m.base z) (Scheme.IdealSheafData.inclusion_subschemeι hle)
  rw [Set.mem_preimage, hcomp, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- The closure of the image of a closed subscheme is its support: the image is already closed. -/
theorem closure_range_subschemeι {X : Scheme.{u}} (V : X.IdealSheafData) :
    closure (Set.range V.subschemeι.base) = (V.support : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact V.support.isClosed.closure_eq

/-- The image in the zero scheme `Z(s)` of the zero scheme of the restriction of `s` to a closed
subscheme `V` lies over `V`: the morphism of Remark 0B6Y for the closed immersion of `V` lies over
that closed immersion. -/
theorem range_zeroSchemePullbackMap_subset_preimage_support {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (V : X.IdealSheafData) :
    Set.range (zeroSchemePullbackMap V.subschemeι L s).base ⊆
      (Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (V.support : Set X) := by
  rintro y ⟨z, rfl⟩
  have hcomp : (Divisors.zeroScheme X L s).subschemeι.base
      ((zeroSchemePullbackMap V.subschemeι L s).base z) =
      V.subschemeι.base ((pullbackZeroScheme V.subschemeι L s).subschemeι.base z) :=
    congrArg (fun m : (pullbackZeroScheme V.subschemeι L s).subscheme ⟶ X ↦ m.base z)
      (zeroSchemePullbackMap_comp_subschemeι V.subschemeι L s)
  rw [Set.mem_preimage, hcomp, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, rfl⟩

/-- Proper pushforward of cycles commutes with integer multiples. -/
private theorem properPushforward_zsmul (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k : ℤ) (n : ℤ) (c : CycleGroup C sX k) :
    properPushforward C sX sY f hf k (n • c) = n • properPushforward C sX sY f hf k c :=
  map_zsmul (properPushforwardHom C sX sY f hf k) n c

/-- A cycle rationally equivalent to zero on a closed subscheme `W` containing the zero scheme
`Z(s)` pushes forward to a cycle on `Z(s)` rationally equivalent to zero within the part of `Z(s)`
lying over `W`. -/
private theorem isRationallyEquivalentToZeroWithin_properPushforward_inclusion
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {W : X.IdealSheafData} (hle : Divisors.zeroScheme X L s ≤ W)
    {c : CycleGroup C (W.subschemeι ≫ p) k}
    (hc : IsRationallyEquivalentToZero C (W.subschemeι ≫ p) k c) :
    IsRationallyEquivalentToZeroWithin C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (properPushforward C (W.subschemeι ≫ p) ((Divisors.zeroScheme X L s).subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion hle) (by simp) k c)
      ((Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X)) :=
  (properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C _ _
    (Scheme.IdealSheafData.inclusion hle) _ k hc).mono
    (range_inclusion_subset_preimage_support L s hle)

section Proper

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (p' : X' ⟶ C.S) [LocallyOfFiniteType p'] (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p')
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (k : ℤ)

/-- The pushforward along the morphism of Remark 0B6Y of the Gysin component cycle at a point of
`X'` is supported over the closure of the image of that point: the square `g ≫ i = i' ≫ f` carries
the integral component of `x'` into the integral component of `f x'`. -/
theorem support_properPushforward_gysinComponentCycleAt_subset
    (chern' : FirstChernComponentClassRule C p' k) (x' : X') :
    Function.support (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x')).1 ⊆
      (Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {f.base x'} := by
  intro y hy
  by_contra hny
  refine hy ?_
  rw [properPushforward_apply]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
  have hzy : (zeroSchemePullbackMap f L s).base z = y := hz
  refine mul_eq_zero_of_left ?_ _
  by_contra hc
  refine hny ?_
  have hmem := support_gysinComponentCycleAt_subset C p' k ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x' hc
  have hsq : (Divisors.zeroScheme X L s).subschemeι.base ((zeroSchemePullbackMap f L s).base z) =
      f.base ((pullbackZeroScheme f L s).subschemeι.base z) :=
    congrArg (fun m : (pullbackZeroScheme f L s).subscheme ⟶ X ↦ m.base z)
      (zeroSchemePullbackMap_comp_subschemeι f L s)
  rw [Set.mem_preimage, ← hzy, hsq]
  simpa using image_closure_subset_closure_image (f := f.base) f.continuous
    (Set.mem_image_of_mem _ hmem)

/-- **The contained case of Stacks 02TA, read on the integral components.** When the integral
component `W = closure {f x'}` contains the zero scheme `D = Z(s)`, the pushforward along the
morphism `g` of Remark 0B6Y of the Gysin component cycle at `x'` is the pushforward into `D` of
the pushforward along the component restriction `W' ⟶ W` of the representative of the first Chern
class on `W'`.

The square `i' ≫ g = π ≫ i` of the two inclusions and the component restriction commutes because
the closed immersion of `D` into `X` is a monomorphism. -/
theorem properPushforward_gysinComponentCycleAt_of_le
    (chern' : FirstChernComponentClassRule C p' k) (x' : X')
    (hx' : relativeDimension C.dimensionFunction p' x' = k + 1)
    (hle : Divisors.zeroScheme X L s ≤ integralComponentAt (f.base x')) :
    properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x') =
      properPushforward C ((integralComponentAt (f.base x')).subschemeι ≫ p)
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (Scheme.IdealSheafData.inclusion hle)
        (by simp) k
        (properPushforward C ((integralComponentAt x').subschemeι ≫ p')
          ((integralComponentAt (f.base x')).subschemeι ≫ p) (integralComponentMap f x')
          (integralComponentMap_comp_base C p' p f hf x') k
          (Quotient.out (chern' (integralComponentAt x') (isIntegral_integralComponentAt x')
            (schemeDeltaDimension_integralComponentAt_of_eq C p' hx')))) := by
  have hle' : pullbackZeroScheme f L s ≤ integralComponentAt x' :=
    (pullbackZeroScheme_le_integralComponentAt_iff f L s x').2 hle
  have hincl' : Scheme.IdealSheafData.inclusion hle' ≫
      ((pullbackZeroScheme f L s).subschemeι ≫ p') = (integralComponentAt x').subschemeι ≫ p' := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have hincl : Scheme.IdealSheafData.inclusion hle ≫
      ((Divisors.zeroScheme X L s).subschemeι ≫ p) =
      (integralComponentAt (f.base x')).subschemeι ≫ p := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have hkey : Scheme.IdealSheafData.inclusion hle' ≫ zeroSchemePullbackMap f L s =
      integralComponentMap f x' ≫ Scheme.IdealSheafData.inclusion hle := by
    have h1 : (Scheme.IdealSheafData.inclusion hle' ≫ zeroSchemePullbackMap f L s) ≫
        (Divisors.zeroScheme X L s).subschemeι = (integralComponentAt x').subschemeι ≫ f := by
      rw [Category.assoc, zeroSchemePullbackMap_comp_subschemeι, ← Category.assoc,
        Scheme.IdealSheafData.inclusion_subschemeι]
    have h2 : (integralComponentMap f x' ≫ Scheme.IdealSheafData.inclusion hle) ≫
        (Divisors.zeroScheme X L s).subschemeι = (integralComponentAt x').subschemeι ≫ f := by
      rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
        integralComponentMap_subschemeι]
    exact (cancel_mono (Divisors.zeroScheme X L s).subschemeι).1 (h1.trans h2.symm)
  rw [gysinComponentCycleAt_eq C p' k ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) chern' hx',
    gysinComponentCycle_of_le C p' k ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s) chern' (integralComponentAt x')
      (isIntegral_integralComponentAt x')
      (schemeDeltaDimension_integralComponentAt_of_eq C p' hx') hle',
    properPushforward_properPushforward C ((integralComponentAt x').subschemeι ≫ p')
      ((pullbackZeroScheme f L s).subschemeι ≫ p') ((Divisors.zeroScheme X L s).subschemeι ≫ p)
      (Scheme.IdealSheafData.inclusion hle') (zeroSchemePullbackMap f L s) hincl'
      (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k,
    properPushforward_properPushforward C ((integralComponentAt x').subschemeι ≫ p')
      ((integralComponentAt (f.base x')).subschemeι ≫ p)
      ((Divisors.zeroScheme X L s).subschemeι ≫ p)
      (integralComponentMap f x') (Scheme.IdealSheafData.inclusion hle)
      (integralComponentMap_comp_base C p' p f hf x') hincl k]
  exact congrFun (properPushforward_congr C ((integralComponentAt x').subschemeι ≫ p')
    ((Divisors.zeroScheme X L s).subschemeι ≫ p) _ _ hkey _ _ k) _

/-! ### Stacks 02TA on a single integral component -/

/-- **Stacks 02TA on a single integral component.** For a point `x'` of `X'` of relative dimension
`k + 1` and an integer `n`, the cycle

  `n · (w(x') · c(f x') - g_*(c'(x')))`

on the zero scheme `D = Z(s)` is rationally equivalent to zero, witnessed inside the part of `D`
lying over the integral component of `f x'`. Here `w` is the pushforward weight of Stacks 02R4 and
`c`, `c'` are the Gysin component cycles of Stacks 02T8 on `X` and on `X'`.

This is the first step of the source's proof. Its four cases are described in the module
documentation of `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardAssembly`. -/
theorem isRationallyEquivalentToZeroWithin_gysinComponentDifference (n : ℤ) (x' : X')
    (hx' : relativeDimension C.dimensionFunction p' x' = k + 1) :
    IsRationallyEquivalentToZeroWithin C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (n • (pushforwardWeight C p' p f x' •
          gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) (f.base x') -
        properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
          (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
          (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s)
            (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) x')))
      ((Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {f.base x'}) := by
  classical
  -- the zero cycle is rationally equivalent to zero inside the part of `D` over the component
  set T : (Divisors.zeroScheme X L s).subscheme.IdealSheafData :=
    (integralComponentAt (f.base x')).comap (Divisors.zeroScheme X L s).subschemeι with hT
  have hzero : IsRationallyEquivalentToZeroWithin C
      ((Divisors.zeroScheme X L s).subschemeι ≫ p) k 0
      ((Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {f.base x'}) := by
    have h := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
      (T.subschemeι ≫ ((Divisors.zeroScheme X L s).subschemeι ≫ p))
      ((Divisors.zeroScheme X L s).subschemeι ≫ p) T.subschemeι rfl k
      (rationallyEquivalentToZero_zero C _ k)
    rw [properPushforward_zero] at h
    refine h.mono ?_
    rw [Scheme.IdealSheafData.range_subschemeι, hT,
      Scheme.IdealSheafData.support_comap (integralComponentAt (f.base x'))
        (Divisors.zeroScheme X L s).subschemeι]
    exact Set.preimage_mono (le_of_eq (coe_support_integralComponentAt (f.base x')))
  by_cases hdim : relativeDimension C.dimensionFunction p (f.base x') = k + 1
  · by_cases hle : Divisors.zeroScheme X L s ≤ integralComponentAt (f.base x')
    · -- contained, delta-dimension preserved
      have hW := isIntegral_integralComponentAt (f.base x')
      have hW' := isIntegral_integralComponentAt x'
      have hDim := schemeDeltaDimension_integralComponentAt_of_eq C p hdim
      have hDim' := schemeDeltaDimension_integralComponentAt_of_eq C p' hx'
      let _ : Algebra (integralComponentAt (f.base x')).subscheme.functionField
          (integralComponentAt x').subscheme.functionField :=
        (dominantFunctionFieldMap (integralComponentMap f x')).toAlgebra
      have hwt : pushforwardWeight C p' p f x' =
          (Module.finrank (integralComponentAt (f.base x')).subscheme.functionField
            (integralComponentAt x').subscheme.functionField : ℤ) :=
        pushforwardWeight_eq_finrank_functionField C p' p f x' (by rw [hx', hdim])
      -- the two component cycles as pushforwards from the component `W` of `f x'`
      have hpushW : gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L)
            (f.base x') =
          properPushforward C ((integralComponentAt (f.base x')).subschemeι ≫ p)
            ((Divisors.zeroScheme X L s).subschemeι ≫ p)
            (Scheme.IdealSheafData.inclusion hle) (by simp) k
            (Quotient.out (firstChernComponentClass C p k L (integralComponentAt (f.base x'))
              hW hDim)) := by
        rw [gysinComponentCycleAt_eq C p k L s (firstChernComponentClass C p k L) hdim,
          gysinComponentCycle_of_le C p k L s (firstChernComponentClass C p k L)
            (integralComponentAt (f.base x')) hW hDim hle]
      have hpush := properPushforward_gysinComponentCycleAt_of_le C p p' f hf L s k
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) x' hx' hle
      -- the discrepancy on `W`, which the second equation of Stacks 02ST kills
      have hγ : IsRationallyEquivalentToZero C
          ((integralComponentAt (f.base x')).subschemeι ≫ p) k
          (n • (pushforwardWeight C p' p f x' •
              Quotient.out (firstChernComponentClass C p k L (integralComponentAt (f.base x'))
                hW hDim) -
            properPushforward C ((integralComponentAt x').subschemeι ≫ p')
              ((integralComponentAt (f.base x')).subschemeι ≫ p) (integralComponentMap f x')
              (integralComponentMap_comp_base C p' p f hf x') k
              (Quotient.out (firstChernComponentClass C p' k
                ((Scheme.Modules.pullback f).obj L) (integralComponentAt x') hW' hDim')))) := by
        refine (rationalEquivalences C
          ((integralComponentAt (f.base x')).subschemeι ≫ p) k).zsmul_mem ?_ n
        refine QuotientAddGroup.eq_iff_sub_mem.1 ?_
        rw [mk_zsmul_out, mk_properPushforward_out C _ _ _ _ k
          (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k), hwt]
        exact (properChowPushforward_firstChernComponentClass C p p' k L hf
          (integralComponentAt (f.base x')) hW hDim (integralComponentAt x') hW' hDim'
          (integralComponentMap f x') (integralComponentMap_subschemeι f x')).symm
      -- push the discrepancy into `D` along the closed immersion of `W`
      have hwithin :=
        isRationallyEquivalentToZeroWithin_properPushforward_inclusion C p k L s hle hγ
      rw [properPushforward_zsmul, properPushforward_sub, properPushforward_zsmul, ← hpushW,
        ← hpush] at hwithin
      rwa [coe_support_integralComponentAt] at hwithin
    · -- not contained, delta-dimension preserved
      rw [gysinComponentCycleAt_eq C p k L s (firstChernComponentClass C p k L) hdim,
        gysinComponentCycleAt_eq C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) hx',
        properPushforward_gysinComponentCycle_of_not_le C p p' f hf L s k
          (firstChernComponentClass C p k L)
          (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) x' hx' hdim hle,
        sub_self, smul_zero]
      exact hzero
  · -- the delta-dimension drops: the pushforward weight is zero
    have hw : pushforwardWeight C p' p f x' = 0 :=
      pushforwardWeight_eq_zero C p' p f (by rw [hx']; exact fun h ↦ hdim h.symm)
    rw [hw, zero_smul, zero_sub]
    by_cases hle : Divisors.zeroScheme X L s ≤ integralComponentAt (f.base x')
    · -- contained drop: the pushforward of the first Chern class vanishes in `A_k(W)`
      have hdrop : relativeDimension C.dimensionFunction p (f.base x') ≤ k := by
        have hadd := relativeDimension_comp_eq_add_trdeg C.dimensionFunction p f x'
        rw [hf, hx'] at hadd
        omega
      have hW := isIntegral_integralComponentAt (f.base x')
      have hW' := isIntegral_integralComponentAt x'
      have hDim' := schemeDeltaDimension_integralComponentAt_of_eq C p' hx'
      have hlt : schemeDeltaDimension C ((integralComponentAt (f.base x')).subschemeι ≫ p) <
          ((k + 1 : ℤ) : EInt) := by
        rw [schemeDeltaDimension_integralComponentAt]
        exact WithBotTop.coe_lt_coe.mpr (by omega)
      have hpush := properPushforward_gysinComponentCycleAt_of_le C p p' f hf L s k
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) x' hx' hle
      have hγ : IsRationallyEquivalentToZero C
          ((integralComponentAt (f.base x')).subschemeι ≫ p) k
          (n • (-properPushforward C ((integralComponentAt x').subschemeι ≫ p')
              ((integralComponentAt (f.base x')).subschemeι ≫ p) (integralComponentMap f x')
              (integralComponentMap_comp_base C p' p f hf x') k
              (Quotient.out (firstChernComponentClass C p' k
                ((Scheme.Modules.pullback f).obj L) (integralComponentAt x') hW' hDim')))) := by
        refine (rationalEquivalences C
          ((integralComponentAt (f.base x')).subschemeι ≫ p) k).zsmul_mem ?_ n
        refine (rationalEquivalences C
          ((integralComponentAt (f.base x')).subschemeι ≫ p) k).neg_mem ?_
        refine (QuotientAddGroup.eq_zero_iff _).1 ?_
        rw [mk_properPushforward_out C _ _ _ _ k
          (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k)]
        exact properChowPushforward_firstChernComponentClass_eq_zero C p p' k L hf
          (integralComponentAt (f.base x')) hW hlt (integralComponentAt x') hW' hDim'
          (integralComponentMap f x') (integralComponentMap_subschemeι f x')
      have hwithin :=
        isRationallyEquivalentToZeroWithin_properPushforward_inclusion C p k L s hle hγ
      rw [properPushforward_zsmul, properPushforward_neg, ← hpush] at hwithin
      rwa [coe_support_integralComponentAt] at hwithin
    · -- uncontained drop: the pushforward of the Gysin component cycle vanishes
      rw [properPushforward_gysinComponentCycleAt_eq_zero_of_relativeDimension_ne C p p' k L s f hf
          (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))
          (zeroSchemePullbackMap f L s) (zeroSchemePullbackMap_comp_subschemeι f L s)
          (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) x' hx' hdim
          (fun h ↦ hle ((pullbackZeroScheme_le_integralComponentAt_iff f L s x').1 h)),
        neg_zero, smul_zero]
      exact hzero

/-! ### Stacks 02TA -/

/-- **Stacks 02TA at the level of cycles modulo rational equivalence, carrying its support.** The
difference between the Gysin cycle of a proper pushforward and the pushforward along the morphism
`g` of Remark 0B6Y of the Gysin cycle is rationally equivalent to zero on the zero scheme `Z(s)`,
witnessed inside the part of `Z(s)` lying over the closure of the image of `f`.

The carrier is the union of the carriers of
`Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinComponentDifference`, one for each integral
component of the cycle `α`, each lying over the closure of a point of the image of `f`. -/
theorem isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward
    (α : CycleGroup C p' (k + 1)) :
    IsRationallyEquivalentToZeroWithin C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
          (properPushforward C p' p f hf (k + 1) α) -
        properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
          (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
          ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s)
            (firstChernComponentClass C p' k
              ((Scheme.Modules.pullback f).obj L))).extendCycleGroup α))
      ((Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure (Set.range f.base)) := by
  classical
  -- the difference of the two component cycles at a point of `X'`, weighted by `α'`
  set Δ : X' → CycleGroup C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k := fun x' ↦
    α.1 x' • (pushforwardWeight C p' p f x' •
        gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) (f.base x') -
      properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) x')) with hΔ
  -- the carriers: the parts of the zero scheme lying over the integral components of `α'`
  have hE : LocallyFinite fun i : ↥(Function.support (α.1 : X' → ℤ)) ↦
      (Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {f.base (i : X')} := by
    refine LocallyFinite.preimage_continuous ?_ (Divisors.zeroScheme X L s).subschemeι.continuous
    refine (locallyFinite_closure_image_of_isSpectralMap f.base f.isSpectralMap
      (fun i : ↥(Function.support (α.1 : X' → ℤ)) ↦ closure {(i : X')})
      (locallyFinite_closure_support α.1.locallyFiniteSupport)).subset fun i ↦ ?_
    exact closure_mono (Set.singleton_subset_iff.2 ⟨(i : X'), subset_closure rfl, rfl⟩)
  -- each term is rationally equivalent to zero inside its carrier
  have hD : ∀ i : ↥(Function.support (α.1 : X' → ℤ)),
      IsRationallyEquivalentToZeroWithin C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k
        (Δ (i : X'))
        ((Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {f.base (i : X')}) := fun i ↦
    isRationallyEquivalentToZeroWithin_gysinComponentDifference C p p' f hf L s k
      (α.1 (i : X')) (i : X')
      ((mem_cyclesOfDimension_iff_forall_point C p' (k + 1) α.1).1 α.2 (i : X') i.2)
  refine IsRationallyEquivalentToZeroWithin.mono
    (rationallyEquivalentToZeroWithin_finsum C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (fun i : ↥(Function.support (α.1 : X' → ℤ)) ↦ Δ (i : X'))
      (fun i ↦ (Divisors.zeroScheme X L s).subschemeι.base ⁻¹' closure {f.base (i : X')}) hE hD
      fun y ↦ ?_)
    (Set.iUnion_subset fun i ↦ Set.preimage_mono
      (closure_mono (Set.singleton_subset_iff.2 ⟨(i : X'), rfl⟩)))
  -- the left hand side: extending the Gysin rule of `X` over a pushforward along `f`
  have hcptf : IsCompact (f.base ⁻¹' {(Divisors.zeroScheme X L s).subschemeι.base y}) :=
    f.isProperMap.isCompact_preimage isCompact_singleton
  have hLHS : ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
      (properPushforward C p' p f hf (k + 1) α)).1 y =
      ∑ᶠ x' : X', α.1 x' * pushforwardWeight C p' p f x' *
        (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) (f.base x')).1 y := by
    rw [show ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C p' p f hf (k + 1) α)).1 y =
      (gysinRule C p k L s (firstChernComponentClass C p k L)).toComponentRule.extendCoeff
        (Function.locallyFinsupp.map f.base (pushforwardWeight C p' p f) f.isSpectralMap α.1)
        y from rfl,
      ComponentRule.extendCoeff_map_apply _ f.isSpectralMap f.isProperMap.isClosedMap _ _ y hcptf]
    exact finsum_congr fun _ ↦ rfl
  -- the right hand side: pushing the Gysin cycle of `X'` forward along `g`
  have hcptg : IsCompact ((zeroSchemePullbackMap f L s).base ⁻¹' {y}) :=
    (zeroSchemePullbackMap f L s).isProperMap.isCompact_preimage isCompact_singleton
  have hRHS : (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
      ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
      (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
      ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
          α)).1 y =
      ∑ᶠ x' : X', α.1 x' *
        (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
          ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
          (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
          (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
            (AlgebraicGeometry.pullbackGlobalSections f L s)
            (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) x')).1 y := by
    rw [properPushforward_apply_eq_map,
      show ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
            α).1 =
        (gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k
            ((Scheme.Modules.pullback f).obj L))).toComponentRule.extendCycle
          (pullbackZeroScheme f L s).subschemeι.continuous α.1 from rfl,
      ComponentRule.map_extendCycle_apply _ _ _ _ _ hcptg]
    exact finsum_congr fun _ ↦ rfl
  -- both sums have finite support at `y`, so they may be subtracted termwise
  have hfu : (Function.support fun i : ↥(Function.support (α.1 : X' → ℤ)) ↦
      α.1 (i : X') * pushforwardWeight C p' p f (i : X') *
        (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L)
          (f.base (i : X'))).1 y).Finite :=
    (hE.point_finite y).subset fun i hi ↦
      support_gysinComponentCycleAt_subset C p k L s (firstChernComponentClass C p k L)
        (f.base (i : X')) (right_ne_zero_of_mul (Function.mem_support.1 hi))
  have hfv : (Function.support fun i : ↥(Function.support (α.1 : X' → ℤ)) ↦
      α.1 (i : X') * (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L))
          (i : X'))).1 y).Finite :=
    (hE.point_finite y).subset fun i hi ↦
      support_properPushforward_gysinComponentCycleAt_subset C p p' f hf L s k
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L)) (i : X')
        (right_ne_zero_of_mul (Function.mem_support.1 hi))
  rw [show ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C p' p f hf (k + 1) α) -
      properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k
            ((Scheme.Modules.pullback f).obj L))).extendCycleGroup α)).1 y =
      ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C p' p f hf (k + 1) α)).1 y -
      (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k
            ((Scheme.Modules.pullback f).obj L))).extendCycleGroup α)).1 y from rfl,
    hLHS, hRHS,
    ← finsum_subtype_support_eq (α.1 : X' → ℤ) _ (fun z hz ↦ by rw [hz, zero_mul, zero_mul]),
    ← finsum_subtype_support_eq (α.1 : X' → ℤ) _ (fun z hz ↦ by rw [hz, zero_mul]),
    ← finsum_sub_distrib hfu hfv]
  refine finsum_congr fun i ↦ ?_
  rw [hΔ]
  simp only [AddSubgroupClass.coe_zsmul, AddSubgroupClass.coe_sub,
    Function.locallyFinsuppWithin.coe_zsmul, Function.locallyFinsuppWithin.coe_sub,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **Stacks 02TA at the level of cycles modulo rational equivalence.** The Gysin cycle of a
proper pushforward and the pushforward along the morphism `g` of Remark 0B6Y of the Gysin cycle
are rationally equivalent on the zero scheme `Z(s)`, both Gysin rules being the first Chern class
of an invertible module.

This is Stacks 02TA with both sides read as cycles: passing to classes gives the identity
`i^* f_* α' = g_* (i')^* α'` of the tag, which is
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible`. The two cycles
are *not* equal — see the implementation notes. -/
theorem rationallyEquivalent_gysinRule_extendCycleGroup_properPushforward
    (α : CycleGroup C p' (k + 1)) :
    RationallyEquivalent C ((Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
        (properPushforward C p' p f hf (k + 1) α))
      (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        ((gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (firstChernComponentClass C p' k
            ((Scheme.Modules.pullback f).obj L))).extendCycleGroup α)) :=
  (isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup_properPushforward
    C p p' f hf L s k α).isRationallyEquivalentToZero

end Proper

end Stacks.Chow

end
