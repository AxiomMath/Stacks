module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback

/-!
# The restriction of a divisor to a prime divisor

In the situation preceding the key formula Stacks 0AYC one picks, for each member `Z_i` of the
family of codimension-one subsets, a generator `t_i` of the stalk `N_{ξ_i}` at the generic point
`ξ_i` of `Z_i`, and observes that its image in the fibre `N_{ξ_i} ⊗ κ(ξ_i)` is a nonzero
meromorphic section `t_i|_{Z_i}` of the restriction `N|_{Z_i}`. The left hand side of the key
formula is built from the divisors `div_{N|_{Z_i}}(t_i|_{Z_i})` of those sections, cycles on
`Z_i` of delta-dimension `dim_δ(Z_i) - 1`.

This file constructs that divisor from three ingredients:

* the restriction `N|_Z` is the module pullback along the closed immersion `Z → X`, and it is
  **trivialized near every point** of `Z`, which is what the order-of-vanishing calculus asks of
  it — `Stacks.Divisors.IsTrivializedNear.pullback` proves this with no invertibility hypothesis
  on the pullback, from invertibility of `N` on `X`;
* the restriction `t|_Z` of a stalk element is `Stacks.Divisors.pullbackStalkAt` at the generic
  point of `Z`, which lands in the stalk of `N|_Z` there — the base change
  `N_ξ ⊗_{𝒪_{X, ξ}} 𝒪_{Z, ξ}`, and `𝒪_{Z, ξ} = κ(ξ)` is the fibre the source names;
* the divisor of a meromorphic section in that model is `Stacks.Chow.meromorphicDivisorCycle`,
  Stacks 02SJ (1) in the generic-stalk model.

The compatibility that makes the construction usable is the one the key formula's first paragraph
uses: replacing the generator `t` by `u · t` for a unit `u` of `𝒪_{X, ξ}` replaces
`div_{N|_Z}(t|_Z)` by `div_{N|_Z}(t|_Z) + div(u|_Z)`, where `u|_Z` is the image of `u` in
`𝒪_{Z, ξ} = R(Z)`. That is
`Stacks.Chow.orderOfVanishing_restrictStalk_smul` coefficientwise, and it is Stacks 02SH applied
on `Z`.

Everything is stated for an arbitrary integral closed subscheme `Z ⊆ X` recorded by its ideal
sheaf, with its generic point named through an equality `ι(η_Z) = ξ`. That is the shape in which
`Stacks.Chow.KeyFormulaData` carries the members of its family, so no transport is needed at the
point of use. For `Z = Stacks.Chow.integralComponentAt ξ` the equality is
`Stacks.Chow.genericPointOf_integralComponentAt`.

## Main definitions

* `Stacks.Chow.restrictModule` — the restriction `N|_Z` of an `𝒪_X`-module to a closed
  subscheme.
* `Stacks.Chow.restrictStalk` — the restriction `t|_Z` of an element of `N_ξ` to the stalk of
  `N|_Z` at the generic point of `Z`.
* `Stacks.Chow.restrictedDivisor` — **`div_{N|_Z}(t|_Z)`**, the divisor cycle of the restricted
  section, with its coefficient specification.

## Main results

* `Stacks.Chow.isTrivializedNear_restrictModule` — `N|_Z` is trivialized near every point of
  `Z`.
* `Stacks.Chow.isStalkBasis_restrictStalk` — the restriction of a generator of `N_ξ` is a
  generator of `(N|_Z)_{η_Z}`, hence a nonzero meromorphic section of `N|_Z`.
* `Stacks.Chow.restrictedDivisor_genericPoint` and `Stacks.Chow.restrictedDivisor_eq_zero` — the
  coefficients of the restricted divisor.
* `Stacks.Chow.restrictStalk_smul` and `Stacks.Chow.orderOfVanishing_restrictStalk_smul` — the
  change-of-generator rule.

## References

* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable {X : Scheme.{u}} (W : X.IdealSheafData) [IsIntegral W.subscheme] (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-! ### The restricted module -/

/-- **The restriction `N|_Z` of an `𝒪_X`-module to a closed subscheme**, the module pullback
along the closed immersion `Z → X`. -/
abbrev restrictModule : W.subscheme.Modules :=
  (Scheme.Modules.pullback W.subschemeι).obj N

omit [IsIntegral W.subscheme] in
/-- **The restriction of an invertible module is trivialized near every point.** `N` is
trivialized near every point of `X` by Stacks 0B8M, and
`Stacks.Divisors.IsTrivializedNear.pullback` carries that to the pullback.

This is the rank-one hypothesis of `Stacks.Chow.meromorphicDivisorCycle`, discharged. Nothing is
assumed about the pullback itself. -/
theorem isTrivializedNear_restrictModule (z : W.subscheme) :
    IsTrivializedNear (restrictModule W N) z :=
  have := isInvertible_presheaf N
  (isTrivializedNear_of_isInvertible N _).pullback

/-! ### The restricted section -/

section Restrict

variable {ξ : X} (hξ : W.subschemeι.base (genericPoint W.subscheme) = ξ)

/-- **The restriction `t|_Z` of an element of `N_ξ`.** The stalk of `N|_Z` at the generic point
`η_Z` of `Z` is the base change `N_ξ ⊗_{𝒪_{X, ξ}} 𝒪_{Z, η_Z}` of Stacks 0098, and `𝒪_{Z, η_Z}` is
the residue field `κ(ξ)` of `𝒪_{X, ξ}`; so this is the image of `t` in the fibre
`N_ξ ⊗ κ(ξ)` that the source calls `t|_Z`, read as a meromorphic section of `N|_Z` in the
generic-stalk model. -/
def restrictStalk (t : N.presheaf.stalk ξ) :
    (restrictModule W N).presheaf.stalk (genericPoint W.subscheme) :=
  pullbackStalkAt W.subschemeι N (genericPoint W.subscheme) hξ t

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] in
/-- **The restriction of a generator of `N_ξ` is a generator of `(N|_Z)_{η_Z}`.** The base change
of a free rank-one module is free of rank one, so `t|_Z` is a basis of the stalk of `N|_Z` at the
generic point of `Z`; in particular it is a *nonzero* meromorphic section of `N|_Z`, which is
what the source asserts of `t_i|_{Z_i}`. -/
theorem isStalkBasis_restrictStalk {t : N.presheaf.stalk ξ} (ht : IsStalkBasis N ξ t) :
    IsStalkBasis (restrictModule W N) (genericPoint W.subscheme) (restrictStalk W N hξ t) :=
  ht.pullbackStalkAt W.subschemeι N (genericPoint W.subscheme) hξ

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] in
/-- **The change-of-generator rule on stalks.** Rescaling `t` by `r ∈ 𝒪_{X, ξ}` rescales `t|_Z`
by the image `r|_Z` of `r` in `𝒪_{Z, η_Z} = R(Z)`, the germ map of the closed immersion at the
generic point of `Z`. -/
theorem restrictStalk_smul (r : X.presheaf.stalk ξ) (t : N.presheaf.stalk ξ) :
    restrictStalk W N hξ (r • t) =
      (hξ ▸ W.subschemeι.stalkMap (genericPoint W.subscheme)).hom r •
        restrictStalk W N hξ t :=
  pullbackStalkAt_smul W.subschemeι N (genericPoint W.subscheme) hξ r t

/-- **The image `u|_Z` in `R(Z)` of a unit of `𝒪_{X, ξ}` is nonzero.** The germ map of the closed
immersion carries units to units, and `R(Z)` is a field. -/
theorem restrictScalar_ne_zero_of_isUnit {r : X.presheaf.stalk ξ} (hr : IsUnit r) :
    (hξ ▸ W.subschemeι.stalkMap (genericPoint W.subscheme)).hom r ≠ 0 :=
  (hr.map (hξ ▸ W.subschemeι.stalkMap (genericPoint W.subscheme)).hom).ne_zero

/-- **The change-of-generator rule on orders of vanishing, Stacks 02SH on `Z`.** Replacing the
generator `t` of `N_ξ` by `u · t` for a unit `u` of `𝒪_{X, ξ}` adds to the order of vanishing of
`t|_Z` along a prime divisor `Y` of `Z` the order of vanishing of `u|_Z` there.

This is the computation the first paragraph of the proof of Stacks 0AYC performs: it is why the
key formula is unchanged by a change of the chosen generators, up to the term
`div(u|_{Z_i})` which the bilinearity of the tame symbol reproduces. -/
theorem orderOfVanishing_restrictStalk_smul [IsLocallyNoetherian W.subscheme]
    {Y : PrimeDivisor W.subscheme} {r : X.presheaf.stalk ξ} (hr : IsUnit r)
    {t : N.presheaf.stalk ξ} (ht : IsStalkBasis N ξ t)
    (ht0 : restrictStalk W N hξ t ≠ 0) :
    orderOfVanishing (restrictModule W N) (restrictStalk W N hξ (r • t)) Y =
      W.subscheme.ord ((hξ ▸ W.subschemeι.stalkMap (genericPoint W.subscheme)).hom r)
          Y.genericPoint +
        orderOfVanishing (restrictModule W N) (restrictStalk W N hξ t) Y := by
  have _ := ht
  rw [restrictStalk_smul W N hξ r t]
  exact orderOfVanishing_smul (isTrivializedNear_restrictModule W N Y.genericPoint)
    (restrictScalar_ne_zero_of_isUnit W hξ hr) ht0

/-! ### The restricted divisor -/

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsLocallyNoetherian W.subscheme] {n : ℤ}
  (hn : schemeDeltaDimension C (W.subschemeι ≫ p) = (n : EInt))

/-- **`div_{N|_Z}(t|_Z)`, the restriction to a prime divisor of the divisor of a
meromorphic-section generator.** For an integral closed subscheme `Z ⊆ X` of delta-dimension `n`
with generic point `ξ`, an invertible `𝒪_X`-module `N` and an element `t` of `N_ξ`, this is the
divisor cycle of the restricted section `t|_Z`: a cycle of delta-dimension `n - 1` on `Z`,
specified by its coefficients.

The coefficient at the generic point of a prime divisor `Y` of `Z` is
`ord_{Y, N|_Z}(t|_Z)` and the coefficient at a point which is no prime divisor's generic point is
zero; they are available as `Stacks.Chow.restrictedDivisor_genericPoint` and
`Stacks.Chow.restrictedDivisor_eq_zero`.

For `t` a *generator* of `N_ξ` — the case the key formula uses — the restricted section is a
nonzero meromorphic section of `N|_Z` by `Stacks.Chow.isStalkBasis_restrictStalk`. -/
def restrictedDivisor (t : N.presheaf.stalk ξ) :
    { c : CycleGroup C (W.subschemeι ≫ p) (n - 1) //
      IsWeilDivisorCycle C (W.subschemeι ≫ p) n
        (fun Y : PrimeDivisor W.subscheme =>
          orderOfVanishing (restrictModule W N) (restrictStalk W N hξ t) Y) c } :=
  meromorphicDivisorCycle C (W.subschemeι ≫ p) hn (isTrivializedNear_restrictModule W N)
    (restrictStalk W N hξ t)

/-- The coefficient of `div_{N|_Z}(t|_Z)` at the generic point of a prime divisor `Y` of `Z` is
the order of vanishing of `t|_Z` along `Y`. -/
@[simp]
theorem restrictedDivisor_genericPoint (t : N.presheaf.stalk ξ) (Y : PrimeDivisor W.subscheme) :
    ((restrictedDivisor W N hξ C p hn t).val : AlgebraicCycle W.subscheme ℤ) Y.genericPoint =
      orderOfVanishing (restrictModule W N) (restrictStalk W N hξ t) Y :=
  (restrictedDivisor W N hξ C p hn t).property.1 Y

/-- `div_{N|_Z}(t|_Z)` vanishes at every point of `Z` which is not the generic point of a prime
divisor of `Z`. -/
theorem restrictedDivisor_eq_zero (t : N.presheaf.stalk ξ) (z : W.subscheme)
    (hz : ∀ Y : PrimeDivisor W.subscheme, Y.genericPoint ≠ z) :
    ((restrictedDivisor W N hξ C p hn t).val : AlgebraicCycle W.subscheme ℤ) z = 0 :=
  (restrictedDivisor W N hξ C p hn t).property.2 z hz

/-- **The restricted divisor changes by the principal divisor of `u|_Z`.** Coefficientwise, the
divisor of `(u · t)|_Z` is the divisor of `t|_Z` plus the divisor of the rational function `u|_Z`
on `Z`, for a unit `u` of `𝒪_{X, ξ}`.

This is `Stacks.Chow.orderOfVanishing_restrictStalk_smul` read on the cycle, and it is the
invariance the key formula needs of its left hand side under a change of the chosen
generators. -/
theorem restrictedDivisor_smul_genericPoint {r : X.presheaf.stalk ξ} (hr : IsUnit r)
    {t : N.presheaf.stalk ξ} (ht : IsStalkBasis N ξ t) (ht0 : restrictStalk W N hξ t ≠ 0)
    (Y : PrimeDivisor W.subscheme) :
    ((restrictedDivisor W N hξ C p hn (r • t)).val : AlgebraicCycle W.subscheme ℤ)
          Y.genericPoint =
      W.subscheme.ord ((hξ ▸ W.subschemeι.stalkMap (genericPoint W.subscheme)).hom r)
          Y.genericPoint +
        ((restrictedDivisor W N hξ C p hn t).val : AlgebraicCycle W.subscheme ℤ)
          Y.genericPoint := by
  rw [restrictedDivisor_genericPoint, restrictedDivisor_genericPoint]
  exact orderOfVanishing_restrictStalk_smul W N hξ hr ht ht0

end Restrict

end Stacks.Chow

end
