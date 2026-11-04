module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow

/-!
# The projection formula for the first Chern class along a proper morphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be locally
of finite type over `S`, let `p : X ⟶ Y` be proper and let `ℒ` be an invertible `𝒪_Y`-module.
[Stacks, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU) is the projection formula

  `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`  in  `A_k(Y)`,  for `α ∈ Z_{k+1}(X)`.

## The argument

`Stacks.Chow.properChowPushforward_firstChernClassCap` proves the formula for two arbitrary
component rules on `X` and on `Y` which are compatible with `p` on every integral component, and
`Stacks.Chow.firstChernClassCap_congr` shows that the cap product only depends on the classes of
the values of a component rule. So it suffices to exhibit a component rule on `X` which takes the
same classes as the rule of `p^*ℒ` and which is compatible with the rule of `ℒ` on `Y`.

That rule is `Stacks.Chow.pulledBackComponentRule`. On the integral component `W` of a point `x`
of `X` it is the divisor of the pullback, along the restriction `W ⟶ W'` of `p` to the integral
component `W'` of `p x`, of the meromorphic section of `ℒ|_{W'}` that the rule of `ℒ` chose on
`W'`. The pullback module is the restriction of `p^*ℒ` to `W`, so by Stacks 02SJ (2) this divisor
has the class the rule of `p^*ℒ` takes on `W`. Its compatibility with the rule of `ℒ` is the
source's reduction to `X`, `Y` integral and `p` dominant:

* if `W ⟶ W'` preserves the delta-dimension, the first displayed equation of Stacks 02ST
  (`Stacks.Chow.properPushforward_meromorphicDivisorCycleOfInvertible`) says that the divisor
  pushes forward to `[R(W) : R(W')]` times the divisor of the chosen section on `W'`, which is the
  value of the rule of `ℒ` there;
* if it drops the delta-dimension, the pushforward of the divisor vanishes: the chosen section is
  a basis of the generic stalk of `ℒ|_{W'}`, so its pullback is a basis of the stalk at every point
  of `W` over the generic point of `W'` and has order zero along every prime divisor of `W`
  dominating `W'`, while every other prime divisor of `W` maps to a point of delta-dimension
  smaller than `k`.

## Main definitions

* `Stacks.Chow.pulledBackComponentCycle` — the divisor of the pulled back section on the integral
  component of a point.
* `Stacks.Chow.pulledBackComponentRule` — the resulting component rule on `X`.

## Main results

* `Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_of_isProper` — **Stacks 02SU**.
* `Stacks.Chow.properChowPushforward_invCap_capOnChow` — the same formula on Chow groups.
* `Stacks.Chow.properChowPushforward_iteratedChernCapOnChow_ofFn` — its iterate for a finite family
  of invertible modules.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] isIntegral_integralComponentAt

/-! ### The pulled back component rule -/

section Rule

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : X ⟶ Y) (k : ℤ) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- The restriction of `L` to the integral component of `y` is invertible. -/
theorem isInvertible_restrictComponent (y : Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (integralComponentAt y).subscheme.sheaf.obj
      (integralComponentAt y).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (integralComponentAt y).subschemeι).obj L) :=
  isInvertible_presheaf_modulePullback L (integralComponentAt y).subschemeι

/-- The meromorphic section of `L` on the integral component of `y` that the component rule of
`L` chooses there: a nonzero element of the generic stalk of the restriction. -/
def chosenComponentSection (y : Y) :
    ((Scheme.Modules.pullback (integralComponentAt y).subschemeι).obj L).presheaf.stalk
      (genericPoint (integralComponentAt y).subscheme) :=
  (exists_ne_zero_genericStalk
    (have := isInvertible_presheaf_modulePullback L (integralComponentAt y).subschemeι
     isTrivializedNear_of_isInvertible
      ((Scheme.Modules.pullback (integralComponentAt y).subschemeι).obj L)
      (genericPoint (integralComponentAt y).subscheme))).choose

/-- The chosen section is nonzero. -/
theorem chosenComponentSection_ne_zero (y : Y) : chosenComponentSection L y ≠ 0 :=
  (exists_ne_zero_genericStalk
    (have := isInvertible_presheaf_modulePullback L (integralComponentAt y).subschemeι
     isTrivializedNear_of_isInvertible
      ((Scheme.Modules.pullback (integralComponentAt y).subschemeι).obj L)
      (genericPoint (integralComponentAt y).subscheme))).choose_spec

/-- The chosen section is a basis of the generic stalk of the restriction of `L`. -/
private theorem isStalkBasis_chosenComponentSection (y : Y) :
    IsStalkBasis ((Scheme.Modules.pullback (integralComponentAt y).subschemeι).obj L)
      (genericPoint (integralComponentAt y).subscheme) (chosenComponentSection L y) :=
  isStalkBasis_genericPoint_of_ne_zero _ _ (chosenComponentSection_ne_zero L y)

/-- The pullback of `L|_{W'}` along the restriction `W ⟶ W'` of `p` to the integral components
of `x` and of `p x`. -/
abbrev integralComponentMapPullbackModule (x : X) : (integralComponentAt x).subscheme.Modules :=
  (Scheme.Modules.pullback (integralComponentMap p x)).obj
    ((Scheme.Modules.pullback (integralComponentAt (p.base x)).subschemeι).obj L)

/-- The pullback of `L|_{W'}` along `W ⟶ W'` is invertible, by Stacks 0B8L twice. -/
theorem isInvertible_integralComponentMapPullbackModule (x : X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (integralComponentAt x).subscheme.presheaf
      (integralComponentAt x).subscheme.ringCatSheaf.2 (integralComponentMapPullbackModule p L x) :=
  have := isInvertible_restrictComponent L (p.base x)
  isInvertible_presheaf_modulePullback _ (integralComponentMap p x)

/-- The pullback along `W ⟶ W'` of the chosen section on `W'`. -/
def integralComponentMapPullbackSection (x : X) :
    (integralComponentMapPullbackModule p L x).presheaf.stalk
      (genericPoint (integralComponentAt x).subscheme) :=
  genericStalkPullback (integralComponentMap p x) _ (chosenComponentSection L (p.base x))

/-- **The divisor of the pulled back section.** On the integral component `W` of a point `x`, the
divisor of the pullback along `W ⟶ W'` of the meromorphic section chosen on the integral component
`W'` of `p x`. -/
def pulledBackComponentCycle (x : X)
    (hk : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ sX) =
      ((k + 1 : ℤ) : EInt)) :
    CycleGroup C ((integralComponentAt x).subschemeι ≫ sX) k :=
  haveI : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ sX)
  chernComponentCycle C ((integralComponentAt x).subschemeι ≫ sX) hk
    (fun z => have := isInvertible_integralComponentMapPullbackModule p L x
      isTrivializedNear_of_isInvertible _ z)
    (integralComponentMapPullbackSection p L x)

/-- Transport of a cycle on an integral closed subscheme along an equality of ideal sheaves. -/
def integralComponentCycleTransport {W W' : X.IdealSheafData} (h : W = W')
    (c : CycleGroup C (W.subschemeι ≫ sX) k) : CycleGroup C (W'.subschemeι ≫ sX) k :=
  h ▸ c

/-- **The pulled back component rule** of an invertible `𝒪_Y`-module `L` along `p : X ⟶ Y`. On
an integral closed subscheme `W` of `X` with generic point `x` it is
`Stacks.Chow.pulledBackComponentCycle` at `x`, read on `W = closure {x}`. -/
def pulledBackComponentRule (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (p : X ⟶ Y) (k : ℤ) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    FirstChernComponentCycleRule C sX k := fun W hW hDim =>
  integralComponentCycleTransport C sX k (integralComponentAt_genericPointOf W hW)
    (pulledBackComponentCycle C sX p k L (genericPointOf W hW)
      (by rw [integralComponentAt_genericPointOf W hW]; exact hDim))

/-- Transporting the pulled back cycle along an equality of points does nothing. -/
theorem integralComponentCycleTransport_pulledBackComponentCycle (x y : X) (hyx : y = x)
    (h : integralComponentAt y = integralComponentAt x)
    (hk : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ sX) =
      ((k + 1 : ℤ) : EInt))
    (hk' : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ sX) =
      ((k + 1 : ℤ) : EInt)) :
    integralComponentCycleTransport C sX k h (pulledBackComponentCycle C sX p k L y hk) =
      pulledBackComponentCycle C sX p k L x hk' := by
  subst hyx
  rfl

/-- On the integral component of a point the pulled back rule is the divisor of the pulled back
section. -/
theorem pulledBackComponentRule_integralComponentAt (x : X)
    (hW : IsIntegral (integralComponentAt x).subscheme)
    (hk : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ sX) =
      ((k + 1 : ℤ) : EInt)) :
    pulledBackComponentRule C sX p k L (integralComponentAt x) hW hk =
      pulledBackComponentCycle C sX p k L x hk :=
  integralComponentCycleTransport_pulledBackComponentCycle C sX p k L x _
    (genericPointOf_integralComponentAt x)
    _ _ _

end Rule

/-! ### The pulled back rule takes the classes of the rule of `p^*ℒ` -/

section Classes

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : X ⟶ Y) (k : ℤ) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- The pullback of `L|_{W'}` along `W ⟶ W'` is the restriction of `p^*L` to `W`: both are the
pullback of `L` along the one morphism `W ⟶ Y`, written through its two factorizations. -/
def integralComponentMapPullbackIso (x : X) :
    integralComponentMapPullbackModule p L x ≅
      (Scheme.Modules.pullback (integralComponentAt x).subschemeι).obj
        ((Scheme.Modules.pullback p).obj L) :=
  (Scheme.Modules.pullbackComp (integralComponentMap p x)
      (integralComponentAt (p.base x)).subschemeι).app L ≪≫
    (Scheme.Modules.pullbackCongr (integralComponentMap_subschemeι p x)).app L ≪≫
    ((Scheme.Modules.pullbackComp (integralComponentAt x).subschemeι p).app L).symm

/-- **The pulled back component cycle has the class of the component rule of `p^*L`.** The
pulled back section is nonzero, the pullback module is isomorphic to the restriction of `p^*L`,
which does not move the divisor cycle, and the divisor cycles of two nonzero sections of one
invertible module have the same class, by Stacks 02SJ (2). -/
theorem rationallyEquivalent_firstChernComponentCycleRule_pulledBackComponentCycle (x : X)
    (hk : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ sX) =
      ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C ((integralComponentAt x).subschemeι ≫ sX) k
      (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L)
        (integralComponentAt x) (isIntegral_integralComponentAt x) hk)
      (pulledBackComponentCycle C sX p k L x hk) := by
  classical
  have := isLocallyNoetherian_integralComponentAt C sX x
  have hMinv := isInvertible_integralComponentMapPullbackModule p L x
  have hτbasis : IsStalkBasis (integralComponentMapPullbackModule p L x)
      (genericPoint (integralComponentAt x).subscheme)
      (integralComponentMapPullbackSection p L x) :=
    (isStalkBasis_chosenComponentSection L (p.base x)).genericStalkPullback
  have hτ : integralComponentMapPullbackSection p L x ≠ 0 :=
    hτbasis.ne_zero
      (exists_ne_zero_genericStalk_of_isInvertible (integralComponentMapPullbackModule p L x))
  set e := integralComponentMapPullbackIso p L x with hedef
  have hPinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (integralComponentAt x).subscheme.presheaf (integralComponentAt x).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (integralComponentAt x).subschemeι).obj
        ((Scheme.Modules.pullback p).obj L)) :=
    isInvertible_presheaf_modulePullback ((Scheme.Modules.pullback p).obj L) _
  set t := stalkLinearMap (integralComponentMapPullbackModule p L x)
    ((Scheme.Modules.pullback (integralComponentAt x).subschemeι).obj
      ((Scheme.Modules.pullback p).obj L)) e.hom
    (genericPoint (integralComponentAt x).subscheme) (integralComponentMapPullbackSection p L x)
    with htdef
  have ht : t ≠ 0 := fun h =>
    hτ ((bijective_stalkLinearMap _ _ e.hom (genericPoint (integralComponentAt x).subscheme)).1
      (h.trans (map_zero _).symm))
  have hstep1 : (QuotientAddGroup.mk
        (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L)
          (integralComponentAt x) (isIntegral_integralComponentAt x) hk) :
      chowGroup C ((integralComponentAt x).subschemeι ≫ sX) k) =
      QuotientAddGroup.mk (chernComponentCycle C ((integralComponentAt x).subschemeι ≫ sX) hk
        (fun z => isTrivializedNear_of_isInvertible _ z) t) := by
    have h := firstChernComponentClass_eq_mk_of_ne_zero C sX k
      ((Scheme.Modules.pullback p).obj L) (integralComponentAt x) hk ht
    exact (firstChernComponentClass_eq_mk C sX k ((Scheme.Modules.pullback p).obj L)
      (integralComponentAt x) (isIntegral_integralComponentAt x) hk).symm.trans h
  have hstep2 : chernComponentCycle C ((integralComponentAt x).subschemeι ≫ sX) hk
        (fun z => isTrivializedNear_of_isInvertible _ z) t =
      pulledBackComponentCycle C sX p k L x hk :=
    chernComponentCycle_mapStalkLinearMap C ((integralComponentAt x).subschemeι ≫ sX) hk _ _
      e.hom (fun z => isTrivializedNear_of_isInvertible _ z)
      (fun z => isTrivializedNear_of_isInvertible _ z) (integralComponentMapPullbackSection p L x)
  exact QuotientAddGroup.eq_iff_sub_mem.1 (hstep1.trans (congrArg QuotientAddGroup.mk hstep2))

/-- **The pulled back rule and the rule of `p^*L` agree in the Chow group of every integral
component.** -/
theorem rationallyEquivalent_firstChernComponentCycleRule_pulledBackComponentRule
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C (W.subschemeι ≫ sX) k
      (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L) W hW hDim)
      (pulledBackComponentRule C sX p k L W hW hDim) := by
  obtain ⟨x, rfl⟩ : ∃ x, integralComponentAt x = W :=
    ⟨_, integralComponentAt_genericPointOf W hW⟩
  rw [pulledBackComponentRule_integralComponentAt]
  exact rationallyEquivalent_firstChernComponentCycleRule_pulledBackComponentCycle C sX p k L x hDim

end Classes

/-! ### The pullback of a section along a morphism to the generic point -/

/-- At a point lying over the generic point, the pullback of a stalk element of the generic stalk
has generic value the pulled back meromorphic section. -/
theorem toGenericStalk_pullbackStalkAt_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (q : X ⟶ Y) [IsDominant q] (M : Y.Modules) (z : X)
    (h : q.base z = genericPoint Y) (s : M.presheaf.stalk (genericPoint Y)) :
    toGenericStalk ((Scheme.Modules.pullback q).obj M) z (pullbackStalkAt q M z h s) =
      genericStalkPullback q M s := by
  obtain ⟨V, hηV, a, rfl⟩ := M.presheaf.exists_germ_eq s
  have hzV : q.base z ∈ V := h ▸ hηV
  have hηV' : q.base (genericPoint X) ∈ V := by
    rw [base_genericPoint_of_isDominant q]; exact hηV
  rw [pullbackStalkAt_germ q M z h V hzV a, genericStalkPullback_germ q M V hηV' a,
    toGenericStalk_germ (L := (Scheme.Modules.pullback q).obj M) (W := q ⁻¹ᵁ V) hzV hηV']

/-! ### Compatibility of the pulled back rule with the rule of `ℒ` -/

section Compatibility

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
  (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

include hp in
/-- **The dimension-preserving case**, from the first displayed equation of Stacks 02ST: when
`W ⟶ W'` preserves the delta-dimension, the divisor of the pulled back section pushes forward to
`[R(W) : R(W')]` times the divisor of the chosen section on `W'`. -/
theorem properPushforward_pulledBackComponentCycle_of_eq (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + 1)
    (hy : relativeDimension C.dimensionFunction sY (p.base x) = k + 1) :
    properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
        ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
        (integralComponentMap_comp_base C sX sY p hp x) k
        (pulledBackComponentCycle C sX p k L x
          (schemeDeltaDimension_integralComponentAt_of_eq C sX hx)) =
      pushforwardWeight C sX sY p x •
        firstChernComponentCycleRule C sY k L (integralComponentAt (p.base x))
          (isIntegral_integralComponentAt (p.base x))
          (schemeDeltaDimension_integralComponentAt_of_eq C sY hy) := by
  classical
  have := isLocallyNoetherian_integralComponentAt C sX x
  have := isLocallyNoetherian_integralComponentAt C sY (p.base x)
  have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (integralComponentAt (p.base x)).subscheme.presheaf
      (integralComponentAt (p.base x)).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (integralComponentAt (p.base x)).subschemeι).obj L) :=
    isInvertible_restrictComponent L (p.base x)
  let _ : Algebra (integralComponentAt (p.base x)).subscheme.functionField
      (integralComponentAt x).subscheme.functionField :=
    (dominantFunctionFieldMap (integralComponentMap p x)).toAlgebra
  have hDimX := schemeDeltaDimension_integralComponentAt_of_eq C sX hx
  have hDimY := schemeDeltaDimension_integralComponentAt_of_eq C sY hy
  have h02ST := properPushforward_meromorphicDivisorCycleOfInvertible C
    ((integralComponentAt x).subschemeι ≫ sX) ((integralComponentAt (p.base x)).subschemeι ≫ sY)
    hDimX hDimY (integralComponentMap p x) (integralComponentMap_comp_base C sX sY p hp x)
    ((Scheme.Modules.pullback (integralComponentAt (p.base x)).subschemeι).obj L)
    (chosenComponentSection L (p.base x)) (chosenComponentSection_ne_zero L (p.base x))
  rw [← pushforwardWeight_eq_finrank_functionField C sX sY p x (hx.trans hy.symm)] at h02ST
  have hMinv := isInvertible_integralComponentMapPullbackModule p L x
  have hX := val_meromorphicDivisorCycle_eq_chernComponentCycle C
    ((integralComponentAt x).subschemeι ≫ sX) hDimX
    (fun z => isTrivializedNear_of_isInvertible (integralComponentMapPullbackModule p L x) z)
    (integralComponentMapPullbackSection p L x)
  have hY := val_meromorphicDivisorCycle_eq_chernComponentCycle C
    ((integralComponentAt (p.base x)).subschemeι ≫ sY) hDimY
    (fun z => isTrivializedNear_of_isInvertible
      ((Scheme.Modules.pullback (integralComponentAt (p.base x)).subschemeι).obj L) z)
    (chosenComponentSection L (p.base x))
  refine Subtype.ext ?_
  refine (val_properPushforward_eq_of_val_eq C ((integralComponentAt x).subschemeι ≫ sX)
    ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
    (integralComponentMap_comp_base C sX sY p hp x) _ _ hX.symm).trans ?_
  refine (congrArg Subtype.val h02ST).trans ?_
  show pushforwardWeight C sX sY p x • _ = pushforwardWeight C sX sY p x • _
  exact congrArg _ hY

include hp in
/-- **The dimension-dropping case**: when `p` drops the delta-dimension at `x`, the component
cycle of the pulled back rule at `x` pushes forward to zero. -/
theorem properPushforward_firstChernComponentCycleAt_pulledBackComponentRule_eq_zero (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + 1)
    (hy : relativeDimension C.dimensionFunction sY (p.base x) ≠ k + 1) :
    properPushforward C sX sY p hp k
      (firstChernComponentCycleAt C sX k (pulledBackComponentRule C sX p k L) x) = 0 := by
  classical
  have := isLocallyNoetherian_integralComponentAt C sX x
  rw [properPushforward_firstChernComponentCycleAt C sX sY p hp k _ hx,
    pulledBackComponentRule_integralComponentAt]
  set c := pulledBackComponentCycle C sX p k L x
    (schemeDeltaDimension_integralComponentAt_of_eq C sX hx) with hcdef
  -- the relative dimension of the generic point of `W'` is at most `k`
  have hηV : (integralComponentAt (p.base x)).subschemeι.base
      (genericPoint (integralComponentAt (p.base x)).subscheme) = p.base x :=
    genericPointOf_integralComponentAt (p.base x)
  have hrelη : relativeDimension C.dimensionFunction
      ((integralComponentAt (p.base x)).subschemeι ≫ sY)
      (genericPoint (integralComponentAt (p.base x)).subscheme) ≤ k := by
    rw [relativeDimension_comp_closedImmersion, hηV]
    have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY p x
    rw [hp, hx] at hstep
    omega
  -- every term of the pushforward vanishes
  have hterm : ∀ z : (integralComponentAt x).subscheme, c.1 z *
      (if relativeDimension C.dimensionFunction ((integralComponentAt x).subschemeι ≫ sX) z =
          relativeDimension C.dimensionFunction
            ((integralComponentAt (p.base x)).subschemeι ≫ sY) ((integralComponentMap p x).base z)
        then ((integralComponentMap p x).residueDegree z : ℤ) else 0) = 0 := by
    intro z
    by_cases hc : c.1 z = 0
    · rw [hc, zero_mul]
    have hzk := (mem_cyclesOfDimension_iff_forall_point C _ k c.1).1 c.2 z hc
    by_cases hd : relativeDimension C.dimensionFunction ((integralComponentAt x).subschemeι ≫ sX)
        z = relativeDimension C.dimensionFunction
          ((integralComponentAt (p.base x)).subschemeι ≫ sY) ((integralComponentMap p x).base z)
    swap
    · rw [ite_eq_right hd, mul_zero]
    exfalso
    by_cases hgz : (integralComponentMap p x).base z =
        genericPoint (integralComponentAt (p.base x)).subscheme
    · -- the pulled back section is a basis of the stalk at `z`
      apply hc
      have hMinv := isInvertible_integralComponentMapPullbackModule p L x
      by_cases hZ : ∃ Z : Stacks.Divisors.PrimeDivisor (integralComponentAt x).subscheme,
          Z.genericPoint = z
      · obtain ⟨Z, rfl⟩ := hZ
        rw [hcdef, pulledBackComponentCycle, chernComponentCycle_genericPoint]
        have hcoord : IsCoordinateAt (integralComponentMapPullbackModule p L x) Z.genericPoint
            (integralComponentMapPullbackSection p L x) 1 :=
          ⟨pullbackStalkAt (integralComponentMap p x) _ Z.genericPoint hgz
              (chosenComponentSection L (p.base x)),
            (isStalkBasis_chosenComponentSection L (p.base x)).pullbackStalkAt
              (integralComponentMap p x) _ Z.genericPoint hgz, by
              rw [one_smul, toGenericStalk_pullbackStalkAt_genericPoint]
              rfl⟩
        rw [orderOfVanishing_eq (isTrivializedNear_of_isInvertible _ _) hcoord,
          ← map_one (algebraMap ((integralComponentAt x).subscheme.presheaf.stalk Z.genericPoint)
            (integralComponentAt x).subscheme.functionField)]
        exact Scheme.ord_algebraMap_of_isUnit Z.coheight_genericPoint isUnit_one
      · push Not at hZ
        rw [hcdef, pulledBackComponentCycle]
        exact chernComponentCycle_eq_zero C _ _ _ _ z hZ
    · -- the image of `z` is a proper specialization of the generic point of `W'`
      obtain ⟨d, hd'⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
        C.dimensionFunction ((integralComponentAt (p.base x)).subschemeι ≫ sY)
      have hlt := d.strictAnti_specializes
        (genericPoint_specializes ((integralComponentMap p x).base z)) (Ne.symm hgz)
      rw [hd', hd'] at hlt
      omega
  have hinner : properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
      ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
      (integralComponentMap_comp_base C sX sY p hp x) k c = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w => ?_)
    rw [properPushforward_apply]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun z _ => hterm z
  rw [hinner, properPushforward_zero]

include hp in
/-- **The pulled back rule is compatible with the rule of `ℒ` along `p`**, on every integral
component of `X`. -/
theorem firstChernCapCompatibleWithPushforward_pulledBackComponentRule :
    FirstChernCapCompatibleWithPushforward C sX sY p hp k (pulledBackComponentRule C sX p k L)
      (firstChernComponentCycleRule C sY k L) :=
  firstChernCapCompatibleWithPushforward_of_integralComponentMap C sX sY p hp k _ _
    (fun x hx hy => by
      rw [pulledBackComponentRule_integralComponentAt]
      exact properPushforward_pulledBackComponentCycle_of_eq C sX sY p hp k L x hx hy)
    (fun x hx hy =>
      properPushforward_firstChernComponentCycleAt_pulledBackComponentRule_eq_zero C sX sY p hp k L
        x hx hy)

end Compatibility


/-! ### Stacks 02SU -/

section ProjectionFormula

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
  (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- **Stacks 02SU.** Let `p : X ⟶ Y` be a proper morphism of schemes locally of finite type over
the base scheme of chapter 42, and let `ℒ` be an invertible `𝒪_Y`-module. Then for every
`(k+1)`-cycle `α` on `X`

  `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`  in  `A_k(Y)`.

The invertibility of `p^*ℒ` is Stacks 0B8L (`Stacks.Divisors.pullback_isInvertible`), and proper
pushforward on Chow groups is defined by Stacks 02S2
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`). -/
@[stacks 02SU]
theorem properChowPushforward_firstChernClassCapOfInvertible_of_isProper
    (α : CycleGroup C sX (k + 1)) :
    properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k)
        (firstChernClassCapOfInvertible C sX k ((Scheme.Modules.pullback p).obj L) α) =
      firstChernClassCapOfInvertible C sY k L (properPushforward C sX sY p hp (k + 1) α) := by
  rw [show firstChernClassCapOfInvertible C sX k ((Scheme.Modules.pullback p).obj L) α =
      firstChernClassCap C sX k
        (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L)) α from rfl,
    firstChernClassCap_congr C sX k _ (pulledBackComponentRule C sX p k L)
      (rationallyEquivalent_firstChernComponentCycleRule_pulledBackComponentRule C sX p k L) α]
  exact properChowPushforward_firstChernClassCap C sX sY p hp k _ _ _
    (firstChernCapCompatibleWithPushforward_pulledBackComponentRule C sX sY p hp k L) α

/-- **Stacks 02SU on Chow groups.** Proper pushforward carries `c₁(p^*ℒ) ∩ -` on `A_{k+1}(X)` to
`c₁(ℒ) ∩ -` on `A_{k+1}(Y)`. -/
theorem properChowPushforward_invCap_capOnChow (a : chowGroup C sX (k + 1)) :
    properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k)
        ((invCap C sX ((Scheme.Modules.pullback p).obj L)).capOnChow C sX k a) =
      (invCap C sY L).capOnChow C sY k
        (properChowPushforward C sX sY p hp (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp (k + 1))
          a) := by
  induction a using QuotientAddGroup.induction_on with
  | H α =>
    show properChowPushforward C sX sY p hp k _
        ((invCap C sX ((Scheme.Modules.pullback p).obj L)).capOnChow C sX k
          (QuotientAddGroup.mk' _ α)) =
      (invCap C sY L).capOnChow C sY k
        (properChowPushforward C sX sY p hp (k + 1) _ (QuotientAddGroup.mk' _ α))
    rw [invCap_capOnChow_mk, properChowPushforward_mk, invCap_capOnChow_mk]
    exact properChowPushforward_firstChernClassCapOfInvertible_of_isProper C sX sY p hp k L α

end ProjectionFormula

/-! ### Iterated caps -/

section Iterated

variable (C : ChowSituation.{u})

/-- The defining equation of an iterated cap at a nonempty list: the head is applied last. -/
theorem iteratedChernCapOnChow_cons_eq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (O : ChernCapOperator C sP) (Os : List (ChernCapOperator C sP)) (d : ℤ)
    (x : chowGroup C sP (d + ((O :: Os).length : ℤ)))
    (y : chowGroup C sP (d + 1 + (Os.length : ℤ))) (hxy : x ≍ y) :
    iteratedChernCapOnChow C sP (O :: Os) d x =
      O.capOnChow C sP d (iteratedChernCapOnChow C sP Os (d + 1) y) := by
  show chowGroupDegreeCast C sP _ ((O.capOnChow C sP d).comp
    (iteratedChernCapOnChow C sP Os (d + 1))) x = _
  rw [chowGroupDegreeCast_apply]
  show O.capOnChow C sP d (iteratedChernCapOnChow C sP Os (d + 1) _) = _
  congr 2
  exact chowGroup_eq_of_heq C sP ((chowGroupCast_heq C sP _ x).trans hxy)

/-- An iterated cap at the empty list is heterogeneously the identity. -/
theorem iteratedChernCapOnChow_nil_heq {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (d : ℤ) (x : chowGroup C sP (d + (([] : List (ChernCapOperator C sP)).length : ℤ))) :
    iteratedChernCapOnChow C sP [] d x ≍ x := by
  show chowGroupDegreeCast C sP _ (AddMonoidHom.id _) x ≍ x
  rw [chowGroupDegreeCast_apply]
  exact chowGroupCast_heq C sP _ x

/-- **Iterated caps commute with proper pushforward**, for two lists of cap operators which commute
with the pushforward termwise. -/
theorem properChowPushforward_iteratedChernCapOnChow_of_forall₂ {PQ PG : Scheme.{u}}
    (sPQ : PQ ⟶ C.S) [LocallyOfFiniteType sPQ] (sPG : PG ⟶ C.S) [LocallyOfFiniteType sPG]
    (ι : PQ ⟶ PG) [IsProper ι] (hι : ι ≫ sPG = sPQ)
    {OQs : List (ChernCapOperator C sPQ)} {OGs : List (ChernCapOperator C sPG)}
    (hcap : List.Forall₂ (fun (OQ : ChernCapOperator C sPQ) (OG : ChernCapOperator C sPG) =>
      ∀ (d : ℤ) (y : chowGroup C sPQ (d + 1)),
        properChowPushforward C sPQ sPG ι hι d
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
            (OQ.capOnChow C sPQ d y) =
          OG.capOnChow C sPG d (properChowPushforward C sPQ sPG ι hι (d + 1)
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y))
      OQs OGs)
    (d : ℤ) (y : chowGroup C sPQ (d + (OQs.length : ℤ)))
    (y' : chowGroup C sPG (d + (OGs.length : ℤ)))
    (hy : y' ≍ properChowPushforward C sPQ sPG ι hι _
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι _) y) :
    properChowPushforward C sPQ sPG ι hι d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPQ sPG ι hι d)
        (iteratedChernCapOnChow C sPQ OQs d y) =
      iteratedChernCapOnChow C sPG OGs d y' := by
  induction hcap generalizing d with
  | nil =>
    refine chowGroup_eq_of_heq C sPG ?_
    refine HEq.trans ?_ (iteratedChernCapOnChow_nil_heq C sPG d y').symm
    refine HEq.trans ?_ hy.symm
    exact properChowPushforward_heq C sPQ sPG ι hι (by simp)
      (iteratedChernCapOnChow_nil_heq C sPQ d y)
  | @cons OQ OG OQs OGs hOO _ ih =>
    rw [iteratedChernCapOnChow_cons_eq C sPQ OQ OQs d y
      (chowGroupCast C sPQ (by simp; ring) y) (chowGroupCast_heq C sPQ _ y).symm,
      iteratedChernCapOnChow_cons_eq C sPG OG OGs d y'
      (chowGroupCast C sPG (by simp; ring) y') (chowGroupCast_heq C sPG _ y').symm, hOO]
    congr 1
    refine ih (d + 1) _ _ ((chowGroupCast_heq C sPG _ y').trans (hy.trans ?_))
    exact properChowPushforward_heq C sPQ sPG ι hι (by simp; ring)
      (chowGroupCast_heq C sPQ _ y).symm

/-- Two families related termwise give lists related termwise. -/
theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} {n : ℕ} {f : Fin n → α} {g : Fin n → β}
    (h : ∀ j, R (f j) (g j)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih fun j => h j.succ)

/-- **Stacks 02SU, iterated.** For a proper morphism `p : X ⟶ Y` over the base and invertible
`𝒪_Y`-modules `ℒ_1, …, ℒ_n`,

  `p_*(c₁(p^*ℒ_1) ∩ ⋯ ∩ c₁(p^*ℒ_n) ∩ y) = c₁(ℒ_1) ∩ ⋯ ∩ c₁(ℒ_n) ∩ p_*y`

for `y ∈ A_{d+n}(X)`; the class `y'` stands for `p_*y` read in the degree the right-hand side
iterates from. -/
theorem properChowPushforward_iteratedChernCapOnChow_ofFn {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) {n : ℕ} (L : Fin n → Y.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property (L j)]
    (d : ℤ)
    (y : chowGroup C sX
      (d + ((List.ofFn fun j => invCap C sX ((Scheme.Modules.pullback p).obj (L j))).length : ℤ)))
    (y' : chowGroup C sY (d + ((List.ofFn fun j => invCap C sY (L j)).length : ℤ)))
    (hy : y' ≍ properChowPushforward C sX sY p hp _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp _) y) :
    properChowPushforward C sX sY p hp d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp d)
        (iteratedChernCapOnChow C sX
          (List.ofFn fun j => invCap C sX ((Scheme.Modules.pullback p).obj (L j))) d y) =
      iteratedChernCapOnChow C sY (List.ofFn fun j => invCap C sY (L j)) d y' :=
  properChowPushforward_iteratedChernCapOnChow_of_forall₂ C sX sY p hp
    (forall₂_ofFn fun j e z => properChowPushforward_invCap_capOnChow C sX sY p hp e (L j) z) d y y'
    hy

end Iterated

end Stacks.Chow

end
