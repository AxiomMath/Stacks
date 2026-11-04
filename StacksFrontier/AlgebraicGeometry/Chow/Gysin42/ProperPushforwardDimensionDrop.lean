module

import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicDivisorPushforward
import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# The dimension-drop branch of Stacks 02TA

Let `f : X' ⟶ X` be proper over the base scheme `S` of chapter 42 of the Stacks Project, let `L`
be an invertible module on `X` with a global section `s` and zero schemes `i : D = Z(s) ⟶ X` and
`i' : D' = Z(f^*s) ⟶ X'`, and let `g : D' ⟶ D` be the morphism of Remark 0B6Y. Let `W' ⊆ X'` be an
integral closed subscheme of delta-dimension `k + 1` whose image `W = f(W')` has *strictly
smaller* delta-dimension. Then `f_*[W'] = 0` in `Z_{k+1}(X)`, so the compatibility of Stacks 02TA
at `W'` reads

  `g_* (i')^* [W'] = 0`  in  `A_k(D)`.

This file proves the two statements that dispose of that branch, one for each case of the
component formula of Stacks 02T8.

## Main results

* `Stacks.Chow.properPushforward_gysinComponentCycleAt_eq_zero_of_relativeDimension_ne` — the
  **uncontained** case: when `W'` is not contained in `Z(f^*s)` the pushforward along `g` of the
  Gysin component cycle of `W'` vanishes already as a cycle.
* `Stacks.Chow.properPushforward_meromorphicDivisorCycle_eq_zero_of_schemeDeltaDimension_lt` —
  the **contained** case, in the shape of the drop branch of the first displayed equation of
  Stacks 02ST: for a proper dominant morphism `π : V ⟶ T` of integral schemes over the base with
  `dim_δ(V) = n` and `dim_δ(T) < n`, the pushforward of the divisor cycle of a pulled-back
  nonzero meromorphic section vanishes. Its invertible-module form, which is what the contained
  case of Stacks 02TA consumes, is
  `Stacks.Chow.properPushforward_meromorphicDivisorCycleOfInvertible_eq_zero`.

## The two arguments

### The uncontained case is a dimension count

In the uncontained case the Gysin component cycle of `W'` is the fundamental cycle of
`W' ∩ D'`, whose support lies over `W'`; so the support of its pushforward along `g` lies over
`W ∩ D`, the square `g ≫ i = i' ≫ f` being commutative. Now `W` is *not* contained in `D`:
`Z(f^*s) = f^{-1}(Z(s))` by Stacks 0B6Y, so `W ⊆ D` would give `W' ⊆ D'`. Hence the generic point
of `W` avoids `D`, and every point of `W ∩ D` is a nontrivial specialization of it, so has
relative dimension strictly below `dim_δ(W) ≤ k` by Stacks 02JW. A `k`-cycle vanishes wherever
the relative dimension is not `k`, which is everywhere on `W ∩ D`.

### The contained case is Stacks 02RU

In the contained case the source invokes the first displayed equation of Stacks 02ST, whose
statement `π_*(div_{π^*N}(π^*t)) = [R(V) : R(T)] div_N(t)` presupposes `dim_δ(V) = dim_δ(T)`;
the drop branch replaces the right hand side by zero. Its proof is the one of
`Stacks.Chow.properPushforward_meromorphicDivisorCycle` with the norm formula of Stacks 02RT
replaced by Stacks 02RU. The pushforward is an `(n-1)`-cycle on the integral scheme `T`, so when
`dim_δ(T) < n - 1` it is zero outright, and when `dim_δ(T) = n - 1` it can be nonzero only at the
generic point `η` of `T`, where its coefficient is the generic-fibre sum

  `∑_{x ↦ η} ord_x(a) · [κ(x) : κ(η)]`

for `a` the image in `R(V)` of a coordinate of `t` at `η` — the coordinates of a meromorphic
section pull back to coordinates of its pullback — and that sum vanishes by
`Stacks.Chow.genericFibreDegreeVanishes`.

## What is not here

No Stacks attribute is placed in this file: these are two branches of the covering set of
Stacks 02TA, and the tag belongs on the statement of the tag itself. The other branches — the
compatibility at a component whose image *keeps* the delta-dimension — are not here either.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The uncontained case -/

/-- **The uncontained dimension-drop branch of Stacks 02TA.** Let `f : X' ⟶ X` be proper over the
base, let `(L, s)` have zero schemes `i : D = Z(s) ⟶ X` and `i' : D' = Z(f^*s) ⟶ X'`, and let
`g : D' ⟶ D` be proper and fill the square `g ≫ i = i' ≫ f` of Remark 0B6Y. If the integral
component `W' = closure {x'}` has delta-dimension `k + 1`, is not contained in `D'`, and has
image of smaller delta-dimension, then the pushforward along `g` of its Gysin component cycle is
the zero cycle.

The hypothesis that `W'` is not contained in `D'` forces the generic point of `W = f(W')` to
avoid `D`, so every point of `D` in the support of the pushforward is a nontrivial
specialization of that generic point and therefore has relative dimension below `k`; a `k`-cycle
vanishes there. -/
theorem properPushforward_gysinComponentCycleAt_eq_zero_of_relativeDimension_ne
    (C : ChowSituation.{u}) {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (p' : X' ⟶ C.S) [LocallyOfFiniteType p'] (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p')
    (chern' : FirstChernComponentClassRule C p' k)
    (g : (pullbackZeroScheme f L s).subscheme ⟶ (zeroScheme X L s).subscheme) [IsProper g]
    (hgi : g ≫ (zeroScheme X L s).subschemeι = (pullbackZeroScheme f L s).subschemeι ≫ f)
    (hg : g ≫ ((zeroScheme X L s).subschemeι ≫ p) =
      (pullbackZeroScheme f L s).subschemeι ≫ p')
    (x' : X') (hx' : relativeDimension C.dimensionFunction p' x' = k + 1)
    (hdrop : relativeDimension C.dimensionFunction p (f.base x') ≠ k + 1)
    (hnotle : ¬ pullbackZeroScheme f L s ≤ integralComponentAt x') :
    properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((zeroScheme X L s).subschemeι ≫ p) g hg k
        (gysinComponentCycleAt C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s) chern' x') = 0 := by
  -- the generic point of the image avoids the zero scheme, because `W'` is not contained in `D'`
  have hx'mem : x' ∉ ((pullbackZeroScheme f L s).support : Set X') := by
    intro hmem
    refine hnotle ?_
    rw [integralComponentAt, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    refine SetLike.coe_subset_coe.mp ?_
    rw [Closeds.coe_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
      (pullbackZeroScheme f L s).support.isClosed
  have hfmem : f.base x' ∉ ((zeroScheme X L s).support : Set X) := by
    intro hmem
    refine hx'mem ?_
    rw [show pullbackZeroScheme f L s = (zeroScheme X L s).comap f from
      zeroScheme_pullback f L s]
    simpa using hmem
  -- the image has delta-dimension at most `k`
  have hle : relativeDimension C.dimensionFunction p (f.base x') ≤ k := by
    have hadd := relativeDimension_comp_eq_add_trdeg C.dimensionFunction p f x'
    rw [hf, hx'] at hadd
    omega
  -- the support of the Gysin component cycle lies over `W'`
  have hsupp := (gysinRule C p' k ((Scheme.Modules.pullback f).obj L)
    (AlgebraicGeometry.pullbackGlobalSections f L s) chern').support_totalize_subset
    (integralComponentAt x')
  rw [coe_support_integralComponentAt] at hsupp
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  by_cases hdim : relativeDimension C.dimensionFunction
      ((zeroScheme X L s).subschemeι ≫ p) y = k
  · -- every point of the fibre of `g` above `y` carries a zero coefficient
    rw [properPushforward_apply]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
    have hzy : g.base z = y := hz
    refine mul_eq_zero_of_left ?_ _
    by_contra hc
    -- `i y` is the image of a point of `W'`, hence lies in the closure of the image of `x'`
    have hmemW : (pullbackZeroScheme f L s).subschemeι.base z ∈ closure {x'} := hsupp (by exact hc)
    have hsq : (zeroScheme X L s).subschemeι.base (g.base z) =
        f.base ((pullbackZeroScheme f L s).subschemeι.base z) :=
      congrArg (fun m : (pullbackZeroScheme f L s).subscheme ⟶ X ↦ m.base z) hgi
    have hclos : (zeroScheme X L s).subschemeι.base y ∈ closure {f.base x'} := by
      rw [← hzy, hsq]
      have himg := image_closure_subset_closure_image (f := f.base) f.continuous
        (Set.mem_image_of_mem _ hmemW)
      simpa using himg
    -- and it lies in the zero scheme, which the image of `x'` does not
    have hne : (zeroScheme X L s).subschemeι.base y ≠ f.base x' := by
      intro heq
      refine hfmem ?_
      rw [← heq, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y, rfl⟩
    -- so its relative dimension is strictly below that of the image of `x'`
    have hlt := relativeDimension_lt_of_mem_closure_of_ne C p hclos hne
    rw [relativeDimension_comp_closedImmersion C.dimensionFunction
      (zeroScheme X L s).subschemeι p y] at hdim
    omega
  · exact properPushforward_apply_eq_zero_of_relativeDimension_ne C
      ((pullbackZeroScheme f L s).subschemeι ≫ p')
      ((zeroScheme X L s).subschemeι ≫ p) g hg k _ y hdim

/-! ### The contained case: the drop branch of the first equation of Stacks 02ST -/

/-- **The drop branch of the first displayed equation of Stacks 02ST.** Let `p : V ⟶ T` be a
proper dominant morphism of integral schemes locally of finite type over the base with
`dim_δ(V) = n` and `dim_δ(T) < n`, let `L` be a rank-one `𝒪_T`-module and let `t` be a nonzero
meromorphic section of `L`. Then the proper pushforward of the divisor cycle of `p^*t` is the
zero cycle.

This is the dimension-drop counterpart of
`Stacks.Chow.properPushforward_meromorphicDivisorCycle`, whose right hand side
`[R(V) : R(T)] div_L(t)` only makes sense when the delta-dimension is preserved. For
`dim_δ(T) < n - 1` there are no `(n-1)`-cycles on `T` at all; for `dim_δ(T) = n - 1` the only
point that can carry a coefficient is the generic point of `T`, and the coefficient there is the
generic-fibre sum of Stacks 02RU. -/
theorem properPushforward_meromorphicDivisorCycle_eq_zero_of_schemeDeltaDimension_lt
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hlt : schemeDeltaDimension C sY < (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX)
    {L : Y.Modules} (hL : ∀ y : Y, IsTrivializedNear L y)
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) :
    properPushforward C sX sY p hp (n - 1)
        (meromorphicDivisorCycle C sX hnX
          (fun x ↦ (hL (p.base x)).pullback) (genericStalkPullback p L s)).val = 0 := by
  classical
  set hL' : ∀ x : X, IsTrivializedNear ((Scheme.Modules.pullback p).obj L) x :=
    fun x ↦ (hL (p.base x)).pullback with hhL'
  show properPushforward C sX sY p hp (n - 1)
      (meromorphicDivisorCycle C sX hnX hL' (genericStalkPullback p L s)).val = 0
  -- the delta-dimension of the target, read at its generic point
  set d : ℤ := relativeDimension C.dimensionFunction sY (genericPoint Y) with hd
  have hnY : schemeDeltaDimension C sY = (d : EInt) := schemeDeltaDimension_eq_genericPoint C sY
  have hdlt : d < n := by
    rw [hnY] at hlt
    exact WithBotTop.coe_lt_coe.mp hlt
  rcases lt_or_eq_of_le (show d ≤ n - 1 by omega) with hdd | hdd
  · -- below `n - 1` there is no nonzero `(n-1)`-cycle on `T`
    exact eq_zero_of_schemeDeltaDimension_lt C sY (n - 1)
      (by rw [hnY]; exact WithBotTop.coe_lt_coe.mpr hdd) _
  · have hnY' : schemeDeltaDimension C sY = ((n - 1 : ℤ) : EInt) := by rw [hnY, hdd]
    -- the delta-dimension of the source, read through the composite
    have hnXc : schemeDeltaDimension C (p ≫ sY) = (n : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint C (p ≫ sY), hp,
        ← schemeDeltaDimension_eq_genericPoint C sX, hnX]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    by_cases hy : y = genericPoint Y
    · subst hy
      -- a coordinate of `t` at the generic point, which the whole generic fibre will use
      obtain ⟨a, ha⟩ := exists_isCoordinateAt (hL (genericPoint Y)) s
      have ha0 : a ≠ 0 := ha.ne_zero hs
      have hb0 : dominantFunctionFieldMap p a ≠ 0 := fun h ↦
        ha0 ((dominantFunctionFieldMap p).injective (by rw [h, map_zero]))
      have hgen : relativeDimension C.dimensionFunction sY (genericPoint Y) = n - 1 := by
        rw [← hd]
        exact hdd
      -- above the generic point the divisor cycle of `p^*t` is the divisor of the coordinate
      have hfib : ∀ x : X, p.base x = genericPoint Y →
          ((meromorphicDivisorCycle C sX hnX hL' (genericStalkPullback p L s)).val :
              AlgebraicCycle X ℤ) x = X.ord (dominantFunctionFieldMap p a) x := by
        intro x hxy
        have ha' : IsCoordinateAt L (p.base x) s a := by rw [hxy]; exact ha
        by_cases hx : ∃ Z : PrimeDivisor X, Z.genericPoint = x
        · obtain ⟨Z, rfl⟩ := hx
          rw [meromorphicDivisorCycle_genericPoint]
          exact orderOfVanishing_eq (hL' Z.genericPoint) ha'.pullback
        · have hne : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x := fun Z hZ ↦ hx ⟨Z, hZ⟩
          have hcoh : coheight x ≠ 1 := fun h ↦
            hne (PrimeDivisor.ofCoheightOne x h) (PrimeDivisor.genericPoint_ofCoheightOne x h)
          rw [meromorphicDivisorCycle_eq_zero C sX hnX hL' _ x hne,
            X.ord_eq_zero_of_coheight_neq_one hcoh]
      rw [properPushforward_apply_of_relativeDimension_eq C sX sY p hp (n - 1) _ _ hgen,
        show (∑ᶠ x ∈ p.base ⁻¹' {genericPoint Y},
              ((meromorphicDivisorCycle C sX hnX hL' (genericStalkPullback p L s)).val :
                AlgebraicCycle X ℤ) x * (p.residueDegree x : ℤ)) =
            ∑ᶠ x ∈ p.base ⁻¹' {genericPoint Y},
              X.ord (dominantFunctionFieldMap p a) x * (p.residueDegree x : ℤ) from
          finsum_congr fun x ↦ finsum_congr fun hx ↦ by rw [hfib x hx]]
      exact genericFibreDegreeVanishes C sY p hnXc hnY' _ hb0
    · exact properPushforward_apply_eq_zero_of_relativeDimension_ne C sX sY p hp (n - 1) _ y
        (by have := relativeDimension_le_sub_one_of_ne_genericPoint C sY hnY' hy; omega)

/-- **The drop branch of the first displayed equation of Stacks 02ST, for an invertible module.**
For a proper dominant morphism `p : V ⟶ T` of integral schemes locally of finite type over the
base with `dim_δ(V) = n` and `dim_δ(T) < n`, an invertible `𝒪_T`-module `L` and a nonzero
meromorphic section `t` of `L`, the proper pushforward of the divisor cycle of `p^*t` vanishes.

These are the hypotheses the source states the tag under; the rank-one hypothesis of
`Stacks.Chow.properPushforward_meromorphicDivisorCycle_eq_zero_of_schemeDeltaDimension_lt` is
discharged by `Stacks.Divisors.isTrivializedNear_of_isInvertible`. This is the form the contained
case of Stacks 02TA consumes, `L` being the restriction of an invertible module to an integral
component. -/
theorem properPushforward_meromorphicDivisorCycleOfInvertible_eq_zero
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hlt : schemeDeltaDimension C sY < (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) :
    properPushforward C sX sY p hp (n - 1)
        (meromorphicDivisorCycle C sX hnX
          (fun x ↦ (isTrivializedNear_of_isInvertible L (p.base x)).pullback)
          (genericStalkPullback p L s)).val = 0 :=
  properPushforward_meromorphicDivisorCycle_eq_zero_of_schemeDeltaDimension_lt C sX sY hnX hlt p hp
    (isTrivializedNear_of_isInvertible L) s hs

end Stacks.Chow

end
