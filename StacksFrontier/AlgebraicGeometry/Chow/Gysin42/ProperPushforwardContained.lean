module

import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# Proper dominant pushforward of the first Chern class on an integral component

Let `f : X' ⟶ X` be a morphism of schemes locally of finite type over the base scheme `S` of
chapter 42 of the Stacks Project, let `L` be an invertible `𝒪_X`-module, let `W ⊆ X` and
`W' ⊆ X'` be integral closed subschemes of delta-dimension `k + 1`, and let `π : W' ⟶ W` be a
proper dominant morphism with `π ≫ i_W = i_{W'} ≫ f`. Then

  `π_*(c₁((f^*L)|_{W'}) ∩ [W']) = [R(W') : R(W)] · c₁(L|_W) ∩ [W]`  in  `A_k(W)`.

This is the second displayed equation of
[Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST) transported along the identification
`π^*(L|_W) ≅ (f^*L)|_{W'}`, which the two factorizations `W' ⟶ W ⟶ X` and `W' ⟶ X' ⟶ X` of one
morphism provide.

It is the contained, equal-dimension case of the first step of the proof of
[Stacks, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA). When an integral component
`W' ⊆ X'` of delta-dimension `k + 1` lies inside the zero scheme of a global section of `f^*L`
and `f` does not drop its delta-dimension, the Gysin rule of Stacks 02T8 takes the value
`c₁((f^*L)|_{W'}) ∩ [W']` on `W'` and the value `c₁(L|_W) ∩ [W]` on `W`, so the identity above is
what Stacks 02TA asserts on that component — read in `A_k(W)`, which is the level at which the
source proves it.

## Main definitions

* `Stacks.Chow.componentPullbackModuleIso` — the identification `π^*(L|_W) ≅ (f^*L)|_{W'}`.

## Main results

* `Stacks.Chow.componentSquare_comp` — the square of components commutes over the base scheme.
* `Stacks.Chow.properChowPushforward_firstChernComponentClass` — the displayed identity, the
  multiplicity being the degree of the extension of function fields.
* `Stacks.Chow.properChowPushforward_firstChernComponentClass_residueDegree` — the same identity
  with the multiplicity read as the residue degree at the generic point of `W'`, the form in which
  the pushforward of cycles of Stacks 02R4 weights that point.

## Implementation notes

`Stacks.Chow.firstChernComponentClass` chooses a nonzero meromorphic section on each integral
component, and the rules of `f^*L` on `X'` and of `L` on `X` choose independently. The two are
compared through Stacks 02SJ (2), in the form
`Stacks.Chow.firstChernComponentClass_eq_mk_of_ne_zero`, which identifies the value of a rule at
`W'` with the class of the divisor cycle of *any* nonzero section of the restricted module. The
section used here is the pullback along `π` of the section chosen on `W`, carried across the
module isomorphism; carrying it across does not move its divisor cycle, by
`Stacks.Chow.chernComponentCycle_mapStalkLinearMap`.

Stacks 02ST is stated for `Stacks.Chow.meromorphicDivisorCycle`, graded `n - 1` on a scheme of
delta-dimension `n`, while the component rule of Stacks 02SO uses
`Stacks.Chow.chernComponentCycle`, graded `k` on a scheme of delta-dimension `k + 1`. The two have
the same underlying algebraic cycle and proper pushforward reads only that, so the two gradings
are crossed by `Stacks.Chow.val_meromorphicDivisorCycle_eq_chernComponentCycle` together with
`Stacks.Chow.val_properPushforward_eq_of_val_eq` rather than by a cast.

The hypothesis of Stacks 02S2 that `Stacks.Chow.properChowPushforward` carries is not a parameter:
it is supplied by `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`, which proves
it for an arbitrary proper morphism over the base.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The square of integral components -/

/-- A morphism `π : W' ⟶ W` of closed subschemes lying over `f : X' ⟶ X` lies over the base
scheme as well: the two squares compose. -/
theorem componentSquare_comp {S X X' : Scheme.{u}} {p : X ⟶ S} {p' : X' ⟶ S} {f : X' ⟶ X}
    (hf : f ≫ p = p') {W : X.IdealSheafData} {W' : X'.IdealSheafData}
    {π : W'.subscheme ⟶ W.subscheme} (hπ : π ≫ W.subschemeι = W'.subschemeι ≫ f) :
    π ≫ (W.subschemeι ≫ p) = W'.subschemeι ≫ p' := by
  rw [← Category.assoc, hπ, Category.assoc, hf]

/-- The pullback along `π : W' ⟶ W` of the restriction of `L` to `W` is isomorphic to the
restriction to `W'` of the pullback of `L` along `f`: both are the pullback of `L` along the one
morphism `W' ⟶ X`, written through its two factorizations. -/
def componentPullbackModuleIso {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
    {W : X.IdealSheafData} {W' : X'.IdealSheafData} {π : W'.subscheme ⟶ W.subscheme}
    (hπ : π ≫ W.subschemeι = W'.subschemeι ≫ f) :
    (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback W.subschemeι).obj L) ≅
      (Scheme.Modules.pullback W'.subschemeι).obj ((Scheme.Modules.pullback f).obj L) :=
  (Scheme.Modules.pullbackComp π W.subschemeι).app L ≪≫
    (Scheme.Modules.pullbackCongr hπ).app L ≪≫
    ((Scheme.Modules.pullbackComp W'.subschemeι f).app L).symm

/-! ### The contained, equal-dimension case of Stacks 02TA -/

/-- **The second displayed equation of Stacks 02ST on an integral component.** For a proper
dominant `π : W' ⟶ W` between integral closed subschemes of delta-dimension `k + 1` lying over
`f : X' ⟶ X`,

  `π_*(c₁((f^*L)|_{W'}) ∩ [W']) = [R(W') : R(W)] · c₁(L|_W) ∩ [W]`  in  `A_k(W)`.

This is the contained, equal-dimension case of the first step of the proof of Stacks 02TA. -/
theorem properChowPushforward_firstChernComponentClass (C : ChowSituation.{u})
    {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (p' : X' ⟶ C.S)
    [LocallyOfFiniteType p'] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {f : X' ⟶ X} (hf : f ≫ p = p') (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (W' : X'.IdealSheafData) (hW' : IsIntegral W'.subscheme)
    (hDim' : schemeDeltaDimension C (W'.subschemeι ≫ p') = ((k + 1 : ℤ) : EInt))
    (π : W'.subscheme ⟶ W.subscheme) [IsProper π] [IsDominant π]
    (hπ : π ≫ W.subschemeι = W'.subschemeι ≫ f) :
    letI : IsIntegral W.subscheme := hW
    letI : IsIntegral W'.subscheme := hW'
    letI : Algebra W.subscheme.functionField W'.subscheme.functionField :=
      (dominantFunctionFieldMap π).toAlgebra
    properChowPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
        (componentSquare_comp hf hπ) k
        (properPushforwardFactorsThroughRationalEquivalence C (W'.subschemeι ≫ p')
          (W.subschemeι ≫ p) π (componentSquare_comp hf hπ) k)
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L) W' hW' hDim') =
      (Module.finrank W.subscheme.functionField W'.subscheme.functionField : ℤ) •
        firstChernComponentClass C p k L W hW hDim := by
  classical
  have := hW
  have := hW'
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have : IsLocallyNoetherian W'.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W'.subschemeι ≫ p')
  let _ : Algebra W.subscheme.functionField W'.subscheme.functionField :=
    (dominantFunctionFieldMap π).toAlgebra
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
  have hMtriv := isTrivializedNear_of_isInvertible (L := M)
  have hQtriv := isTrivializedNear_of_isInvertible (L := Q)
  have hRtriv := isTrivializedNear_of_isInvertible (L := R)
  -- a nonzero meromorphic section of `L|_W`, pulled back to `W'` and carried to `(f^*L)|_{W'}`
  obtain ⟨σ, hσ⟩ := exists_ne_zero_genericStalk (hMtriv (genericPoint W.subscheme))
  set τ := genericStalkPullback π M σ with hτdef
  have hτ : τ ≠ 0 := genericStalkPullback_ne_zero π hMtriv hσ
  set e := componentPullbackModuleIso f L hπ with hedef
  set t := stalkLinearMap R Q e.hom (genericPoint W'.subscheme) τ with htdef
  have ht : t ≠ 0 := fun h =>
    hτ ((bijective_stalkLinearMap R Q e.hom (genericPoint W'.subscheme)).1
      (h.trans (map_zero _).symm))
  -- Stacks 02SJ (2): the two rules are the classes of the divisor cycles of the chosen sections
  have hstep1 :
      firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L) W' hW' hDim' =
        QuotientAddGroup.mk (chernComponentCycle C (W'.subschemeι ≫ p') hDim' hQtriv t) :=
    firstChernComponentClass_eq_mk_of_ne_zero C p' k ((Scheme.Modules.pullback f).obj L) W'
      hDim' ht
  have hstep4 :
      QuotientAddGroup.mk' (rationalEquivalences C (W.subschemeι ≫ p) k)
          (chernComponentCycle C (W.subschemeι ≫ p) hDim hMtriv σ) =
        firstChernComponentClass C p k L W hW hDim :=
    (firstChernComponentClass_eq_mk_of_ne_zero C p k L W hDim hσ).symm
  -- the module isomorphism does not move the divisor cycle
  have hstep2 : chernComponentCycle C (W'.subschemeι ≫ p') hDim' hQtriv t =
      chernComponentCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ :=
    chernComponentCycle_mapStalkLinearMap C (W'.subschemeι ≫ p') hDim' R Q e.hom hRtriv hQtriv τ
  -- Stacks 02ST, first displayed equation, read in the grading of the component rule
  have h02ST := properPushforward_meromorphicDivisorCycleOfInvertible C (W'.subschemeι ≫ p')
    (W.subschemeι ≫ p) hDim' hDim π (componentSquare_comp hf hπ) M σ hσ
  have hvalτ := val_meromorphicDivisorCycle_eq_chernComponentCycle C (W'.subschemeι ≫ p') hDim'
    hRtriv τ
  have hvalσ := val_meromorphicDivisorCycle_eq_chernComponentCycle C (W.subschemeι ≫ p) hDim
    hMtriv σ
  have hstep3 : properPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
        (componentSquare_comp hf hπ) k
        (chernComponentCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ) =
      (Module.finrank W.subscheme.functionField W'.subscheme.functionField : ℤ) •
        chernComponentCycle C (W.subschemeι ≫ p) hDim hMtriv σ := by
    refine Subtype.ext ?_
    rw [← val_properPushforward_eq_of_val_eq C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
      (componentSquare_comp hf hπ)
      (meromorphicDivisorCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ).val
      (chernComponentCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ) hvalτ]
    rw [show ((properPushforward C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
          (componentSquare_comp hf hπ) (k + 1 - 1)
          (meromorphicDivisorCycle C (W'.subschemeι ≫ p') hDim' hRtriv τ).val :
            CycleGroup C (W.subschemeι ≫ p) (k + 1 - 1)) :
          AlgebraicCycle W.subscheme ℤ) =
        (((Module.finrank W.subscheme.functionField W'.subscheme.functionField : ℤ) •
            (meromorphicDivisorCycle C (W.subschemeι ≫ p) hDim hMtriv σ).val :
              CycleGroup C (W.subschemeι ≫ p) (k + 1 - 1)) : AlgebraicCycle W.subscheme ℤ) from
      congrArg Subtype.val h02ST]
    rw [AddSubgroupClass.coe_zsmul, AddSubgroupClass.coe_zsmul, hvalσ]
  -- assembling the four steps
  rw [hstep1]
  refine (properChowPushforward_mk C (W'.subschemeι ≫ p') (W.subschemeι ≫ p) π
    (componentSquare_comp hf hπ) k _ _).trans ?_
  rw [hstep2, hstep3]
  refine (map_zsmul (QuotientAddGroup.mk' (rationalEquivalences C (W.subschemeι ≫ p) k)) _ _).trans
    ?_
  rw [hstep4]

/-- **The second displayed equation of Stacks 02ST on an integral component, with the multiplicity
read as a residue degree.** For a proper dominant `π : W' ⟶ W` between integral closed subschemes
of delta-dimension `k + 1` lying over `f : X' ⟶ X`, the pushforward along `π` of
`c₁((f^*L)|_{W'}) ∩ [W']` is `deg_{κ(η_{W'})/κ(η_W)} · c₁(L|_W) ∩ [W]` in `A_k(W)`. -/
theorem properChowPushforward_firstChernComponentClass_residueDegree (C : ChowSituation.{u})
    {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (p' : X' ⟶ C.S)
    [LocallyOfFiniteType p'] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {f : X' ⟶ X} (hf : f ≫ p = p') (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
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
        (firstChernComponentClass C p' k ((Scheme.Modules.pullback f).obj L) W' hW' hDim') =
      (π.residueDegree (genericPoint W'.subscheme) : ℤ) •
        firstChernComponentClass C p k L W hW hDim := by
  have := hW
  have := hW'
  let _ : Algebra W.subscheme.functionField W'.subscheme.functionField :=
    (dominantFunctionFieldMap π).toAlgebra
  have h := properChowPushforward_firstChernComponentClass C p p' k L hf W hW hDim W' hW' hDim'
    π hπ
  rwa [finrank_functionField_eq_residueDegree π] at h

end Stacks.Chow

end
