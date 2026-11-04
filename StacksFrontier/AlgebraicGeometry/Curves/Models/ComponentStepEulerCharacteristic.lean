module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalComponentsMeet
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Adding a component of the special fibre to a divisor

In the situation of [Stacks, Tag 0C61] let `X` be a regular proper model over a discrete
valuation ring with residue field `k`, let `C₁, …, Cₙ` be the irreducible components of the
special fibre `X_k`, and let `D, D' ⊂ X` be effective Cartier divisors with `D' = D + Cᵢ` and
`D' ⊂ X_k`. [Stacks, Tag 0CA2] computes the change in the Euler characteristic of the structure
sheaf of the divisor:

`χ(X_k, 𝒪_{D'}) - χ(X_k, 𝒪_D) = χ(X_k, 𝒪_X(-D)|_{Cᵢ}) = -(D · Cᵢ) + χ(Cᵢ, 𝒪_{Cᵢ})`.

## Main definitions

* `Stacks.Models.RegularModelSituation.specialFiberDivisorCoeff` — the coefficient `bⱼ` of the
  component `Cⱼ` in a divisor `D`: the order of `D` at the generic point of `Cⱼ`.

## Main results

* `Stacks.Models.RegularModelSituation.eq_prod_specialFiberDivisorCoeff` — an effective Cartier
  divisor contained in `X_k` is `D = ∑ⱼ bⱼCⱼ`.
* `RegularProperModelSituation.eulerCharacteristic_sub_eq_eulerCharacteristic_restrict`
  — the first equality.
* `Stacks.Models.RegularProperModelSituation.eulerCharacteristic_addComponent` —
  **[Stacks, Tag 0CA2]**, both equalities.

## The argument

*The first equality.* The divisors are Cartier on `X`, and the short exact sequence
`0 ⟶ 𝒪_X(-D)|_{Cᵢ} ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0` of [Stacks, Tag 0C4T] is a sequence of
`𝒪_X`-modules. All three terms are direct images of modules on closed subschemes of `X_k`,
because `Cᵢ`, `D` and `D'` lie in `X_k`, so additivity of the Euler characteristic on the proper
`k`-scheme `X_k` ([Stacks, Tag 08AA]) applies to it:
`Stacks.Models.eulerCharacteristic_add_of_shortExact_pushforward`. The subschemes are mapped into
`X_k` by `Stacks.Models.RegularProperModelSituation.fibreSubschemeι`.

*The second equality.* The Euler characteristic on `X_k` of a module on `Cᵢ` is its Euler
characteristic on `Cᵢ`. There `χ(𝒪_X(-D)|_{Cᵢ}) - χ(𝒪_{Cᵢ})` is by definition the degree of
`𝒪_X(-D)|_{Cᵢ}`, which is `-deg(𝒪_X(D)|_{Cᵢ})` by additivity of the degree
([Stacks, Tag 0AYX]). Writing `D = ∑ⱼ bⱼCⱼ`, additivity again gives
`deg(𝒪_X(D)|_{Cᵢ}) = ∑ⱼ bⱼ deg(𝒪_X(Cⱼ)|_{Cᵢ})`, while
`(D · Cᵢ) = ⟨b, 𝒪_X(Cᵢ)⟩ = ∑ⱼ bⱼ deg(𝒪_X(Cᵢ)|_{Cⱼ})` by the definition of the intersection
product ([Stacks, Tag 0C65]). The two agree termwise by the symmetry of [Stacks, Tag 0C64].

## References

* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0BCP](https://stacks.math.columbia.edu/tag/0BCP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- **The coefficient of a component `Cᵢ` in a divisor `D` supported on the special fibre**: the
order of `D` at the generic point of `Cᵢ`, i.e. the coefficient of `Cᵢ` in the Weil divisor of
`D`. -/
public def specialFiberDivisorCoeff (D : S.X.IdealSheafData)
    (Z : irreducibleComponents S.specialFiber) : ℕ :=
  (effectiveCartierMultiplicity D (S.specialFiberComponentPrimeDivisor Z)).toNat

/-- **An effective Cartier divisor contained in the special fibre is the sum of the components
with its coefficients**, `D = ∑ᵢ bᵢCᵢ` with `bᵢ` the order of `D` along `Cᵢ`; divisor sums are
written multiplicatively. The components are integral effective Cartier divisors covering `D`, so
[Stacks, Tag 0BCP] writes `D` as some nonnegative combination of them, and the order at the
generic point of each `Cᵢ`, a discrete valuation ring, reads off the coefficients. -/
public theorem eq_prod_specialFiberDivisorCoeff (D : S.X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hk : S.specialFiberIdeal ≤ D) :
    D = ∏ Z, S.specialFiberComponentIdeal Z ^ S.specialFiberDivisorCoeff D Z := by
  classical
  obtain ⟨a, ha⟩ := exists_finsupp_eq_prod_of_support_cover D hD
    (fun Z => S.specialFiberComponentIdeal Z)
    (fun Z => ⟨inferInstance, S.isEffectiveCartierDivisor_specialFiberComponent Z⟩)
    (by
      intro x hx
      have hx' : x ∈ (((S.specialFiberIdeal.support : TopologicalSpace.Closeds S.X) :
          Set S.X)) := Scheme.IdealSheafData.support_antitone hk hx
      rw [S.coe_support_specialFiberIdeal] at hx'
      obtain ⟨y, rfl⟩ := hx'
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        ({y} : Set S.specialFiber) isIrreducible_singleton
      refine ⟨⟨Z, hZ⟩, ?_⟩
      show S.specialFiberι.base y ∈
        (((S.specialFiberComponentIdeal ⟨Z, hZ⟩).support : TopologicalSpace.Closeds S.X) :
          Set S.X)
      rw [S.coe_support_specialFiberComponentIdeal]
      exact ⟨y, hyZ rfl, rfl⟩)
  have hprod : (a.prod fun Z n => S.specialFiberComponentIdeal Z ^ n) =
      ∏ Z, S.specialFiberComponentIdeal Z ^ a Z :=
    Finsupp.prod_fintype _ _ fun _ => pow_zero _
  have hm : ∀ W, S.specialFiberDivisorCoeff D W = a W := by
    intro W
    rw [specialFiberDivisorCoeff, ha, hprod,
      S.effectiveCartierMultiplicity_prod_specialFiberComponentIdeal_pow, ite_eq_left
        (Finset.mem_univ W)]
    simp
  conv_lhs => rw [ha, hprod]
  exact Finset.prod_congr rfl fun W _ => by rw [hm W]

end RegularModelSituation

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- The special fibre of a regular proper model is locally Noetherian, being proper over the
residue field. -/
public instance isLocallyNoetherian_specialFiber : IsLocallyNoetherian S.specialFiber :=
  Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field S.k
    S.specialFiberToSpec

/-- The structure sheaf `𝒪_E` of a closed subscheme `E ⊆ X_k`, as a module on `X_k`, is
coherent. -/
public instance isCoherent_pushforward_fibreSubschemeι_unit {E : S.X.IdealSheafData}
    (h : S.specialFiberIdeal ≤ E) :
    ((Scheme.Modules.pushforward (S.fibreSubschemeι E h)).obj
      (SheafOfModules.unit E.subscheme.ringCatSheaf)).IsCoherent :=
  haveI : IsLocallyNoetherian E.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (S.fibreSubschemeι E h)
  haveI := Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent E.subscheme
  isCoherent_pushforward_of_isClosedImmersion _ _

/-- The restriction `𝒪_X(-D)|_{Cᵢ}` of the ideal sheaf of an effective Cartier divisor to a
component of the special fibre is coherent on the component. -/
public instance isCoherent_pullback_negativeTwist_specialFiberComponent
    (Z : irreducibleComponents S.specialFiber) (D : S.X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
      (Stacks.Divisors.negativeTwist D)).IsCoherent :=
  haveI := isInvertible_restrict (S.specialFiberComponentIdeal Z) _
    (Stacks.Divisors.isTensorInvertible_negativeTwist D)
  Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k
    (S.specialFiberComponentToSpec Z) _ 1

/-- `𝒪_X(-D)|_{Cᵢ}`, as a module on `X_k`, is coherent. -/
public instance isCoherent_pushforward_pullback_negativeTwist_specialFiberComponent
    (Z : irreducibleComponents S.specialFiber) (D : S.X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    ((Scheme.Modules.pushforward (S.specialFiberComponentι Z)).obj
      ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
        (Stacks.Divisors.negativeTwist D))).IsCoherent :=
  isCoherent_pushforward_of_isClosedImmersion _ _

/-- The Euler characteristic on `X_k` of `𝒪_X(-D)|_{Cᵢ}` is its Euler characteristic on `Cᵢ`. -/
private theorem eulerCharacteristic_pushforward_pullback_negativeTwist
    (Z : irreducibleComponents S.specialFiber) (D : S.X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.specialFiberComponentι Z)).obj
          ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
            (Stacks.Divisors.negativeTwist D))) =
      eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
        ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
          (Stacks.Divisors.negativeTwist D)) :=
  eulerCharacteristic_pushforward_of_isClosedImmersion S.k (S.specialFiberComponentι Z)
    S.specialFiberToSpec _ inferInstance inferInstance

/-- **The first equality of [Stacks, Tag 0CA2]**,
`χ(X_k, 𝒪_{D'}) - χ(X_k, 𝒪_D) = χ(X_k, 𝒪_X(-D)|_{Cᵢ})` for effective Cartier divisors
`D' = D + Cᵢ ⊂ X_k`: the short exact sequence of [Stacks, Tag 0C4T] on `X`, brought to `X_k`, and
additivity of the Euler characteristic there. -/
public theorem eulerCharacteristic_sub_eq_eulerCharacteristic_restrict
    (Z : irreducibleComponents S.specialFiber) (D D' : S.X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hsum : D' = D * S.specialFiberComponentIdeal Z) (hk : S.specialFiberIdeal ≤ D') :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι D' hk)).obj
          (SheafOfModules.unit D'.subscheme.ringCatSheaf)) -
      eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι D
          (hk.trans (hsum ▸ Scheme.IdealSheafData.mul_le_left D _)))).obj
          (SheafOfModules.unit D.subscheme.ringCatSheaf)) =
      eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.specialFiberComponentι Z)).obj
          ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
            (Stacks.Divisors.negativeTwist D))) := by
  have hC := S.isEffectiveCartierDivisor_specialFiberComponent Z
  have hD' : Stacks.Divisors.IsEffectiveCartierDivisor D' :=
    hsum ▸ AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _ hD hC
  have hsub : D' ≤ D := hsum ▸ Scheme.IdealSheafData.mul_le_left D _
  have hZ := S.specialFiberIdeal_le_specialFiberComponentIdeal Z
  obtain ⟨f, zero, hex⟩ := Stacks.Divisors.addEffectiveCartierDivisor_shortExact D D'
    (S.specialFiberComponentIdeal Z) hD hD' hC hsub hsum
  have hcE : ∀ (E : S.X.IdealSheafData) (h : S.specialFiberIdeal ≤ E),
      (SheafOfModules.unit E.subscheme.ringCatSheaf).IsCoherent := fun E h =>
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k (S.fibreSubschemeToSpec E h)
  have hE : ∀ (E : S.X.IdealSheafData) (h : S.specialFiberIdeal ≤ E),
      eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι E h)).obj
          (SheafOfModules.unit E.subscheme.ringCatSheaf)) =
      @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec E h) _
        (SheafOfModules.unit E.subscheme.ringCatSheaf) (hcE E h) := fun E h =>
    eulerCharacteristic_pushforward_of_isClosedImmersion S.k (S.fibreSubschemeι E h)
      S.specialFiberToSpec _ (hcE E h) inferInstance
  have key := eulerCharacteristic_add_of_shortExact_pushforward S hZ hk (hk.trans hsub) hex
    (Iso.refl _) (Iso.refl _) (Iso.refl _) inferInstance (hcE D' hk) (hcE D (hk.trans hsub))
  have e3 := (S.eulerCharacteristic_pushforward_pullback_negativeTwist Z D).trans
    (eulerCharacteristic_congr_morphism _ inferInstance _ inferInstance
      (S.fibreSubschemeToSpec_specialFiberComponentIdeal Z).symm)
  rw [hE D' hk, hE D (hk.trans hsub), e3, key]
  ring

/-- The structure sheaf of a component of the special fibre is coherent. -/
public instance isCoherent_unit_specialFiberComponent (Z : irreducibleComponents S.specialFiber) :
    (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf).IsCoherent :=
  Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k (S.specialFiberComponentToSpec Z)

/-- **`χ(X_k, 𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ}) + χ(Cᵢ, 𝒪_{Cᵢ})`** for an effective Cartier
divisor `D` and a component `Cᵢ` of the special fibre. The Euler characteristic on `X_k` of a
module on `Cᵢ` is its Euler characteristic on `Cᵢ`, and there it is the degree plus `χ(𝒪_{Cᵢ})`;
the degree of `𝒪_X(-D)` is minus that of `𝒪_X(D)`. -/
public theorem eulerCharacteristic_restrict_negativeTwist_eq
    (Z : irreducibleComponents S.specialFiber) (D : S.X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.specialFiberComponentι Z)).obj
          ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
            (Stacks.Divisors.negativeTwist D))) =
      -S.specialFiberComponentDegree Z (Stacks.Divisors.invertibleSheaf' D)
          (Stacks.Divisors.isTensorInvertible_invertibleSheaf D) +
        eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) := by
  have h1 := componentDegree_eq_eulerCharacteristic_restrict_sub S.k
    (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
    (S.isProper_specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (Stacks.Divisors.negativeTwist' D) (Stacks.Divisors.isTensorInvertible_negativeTwist D)
    inferInstance inferInstance
  have hneg := componentDegree_negativeTwist_eq_neg S
    (fun Y => S.specialFiberComponentIdeal Y) (fun Y => S.specialFiberComponentToSpec Y)
    (fun Y => S.isProper_specialFiberComponentToSpec Y)
    (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y) Z D hD
  rw [S.eulerCharacteristic_pushforward_pullback_negativeTwist Z D]
  change componentDegree _ _ _ _ _ _ _ = _ at hneg
  unfold specialFiberComponentDegree
  linarith

/-- The degree on a component of `𝒪_X(∏ⱼ Cⱼ ^ cⱼ)` is `∑ⱼ cⱼ deg(𝒪_X(Cⱼ)|_{Cᵢ})`. -/
private theorem specialFiberComponentDegree_prod_pow
    (Z : irreducibleComponents S.specialFiber) (c : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberComponentDegree Z
        (Stacks.Divisors.invertibleSheaf' (∏ Y, S.specialFiberComponentIdeal Y ^ c Y))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ _ _
            fun W _ => S.isEffectiveCartierDivisor_specialFiberComponent W)) =
      ∑ Y, (c Y : ℤ) * S.specialFiberComponentDegree Z
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Y))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Y)) :=
  componentDegree_invertibleSheaf_prod S (fun W => S.specialFiberComponentIdeal W)
    (fun W => S.specialFiberComponentToSpec W) (fun W => S.isProper_specialFiberComponentToSpec W)
    (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) Z
    (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W) Finset.univ c _
    (fun W => @Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
      (S.isEffectiveCartierDivisor_specialFiberComponent W))

/-- **The intersection product against a single component**, on the canonical family of
components of the special fibre: `(∑ⱼ aⱼCⱼ · Cᵢ) = ⟨a, 𝒪_X(Cᵢ)⟩ = ∑ⱼ aⱼ deg(𝒪_X(Cᵢ)|_{Cⱼ})`. -/
public theorem intersectionProduct_single_right [DecidableEq (irreducibleComponents S.specialFiber)]
    (a : irreducibleComponents S.specialFiber → ℤ) (Z : irreducibleComponents S.specialFiber) :
    intersectionProduct S Finset.univ (fun Y => S.specialFiberComponentIdeal Y)
        (fun Y => S.specialFiberComponentToSpec Y)
        (fun Y => S.isProper_specialFiberComponentToSpec Y)
        (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y) a
        (Pi.single Z 1) (fun Y _ => S.isEffectiveCartierDivisor_specialFiberComponent Y) =
      ∑ Y, a Y * S.specialFiberComponentDegree Y
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Z)) := by
  rw [intersectionProduct_eq_degreePairing]
  unfold degreePairing
  refine Finset.sum_congr rfl fun Y _ => ?_
  congr 1
  refine (S.specialFiberComponentDegree_prod_pow Y (Pi.single Z 1)).trans ?_
  rw [Finset.sum_eq_single_of_mem Z (Finset.mem_univ Z)
      (fun W _ hW => by rw [Pi.single_eq_of_ne hW]; simp),
    Pi.single_eq_same]
  simp [specialFiberComponentDegree]

/-- **The degree of `𝒪_X(D)` on a component, for `D` supported on the special fibre**:
`deg(𝒪_X(D)|_{Cᵢ}) = ∑ⱼ bⱼ deg(𝒪_X(Cⱼ)|_{Cᵢ})` with `bⱼ` the coefficients of `D`. -/
public theorem specialFiberComponentDegree_invertibleSheaf_eq_sum
    (Z : irreducibleComponents S.specialFiber) (D : S.X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] (hk : S.specialFiberIdeal ≤ D) :
    S.specialFiberComponentDegree Z (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf D) =
      ∑ Y, (S.specialFiberDivisorCoeff D Y : ℤ) * S.specialFiberComponentDegree Z
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Y))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Y)) := by
  have hDeq := S.eq_prod_specialFiberDivisorCoeff D hD hk
  rw [← S.specialFiberComponentDegree_prod_pow Z]
  unfold specialFiberComponentDegree
  exact componentDegree_eq_of_iso _ _ _ _ _ _ _ _ _ (eqToIso (by rw [← hDeq]))

/-- **Stacks Project, Tag 0CA2.** In the situation of [Stacks, Tag 0C61] let `Cᵢ` be an
irreducible component of the special fibre `X_k` and let `D, D' ⊂ X` be effective Cartier
divisors with `D' = D + Cᵢ` and `D' ⊂ X_k`. Then

`χ(X_k, 𝒪_{D'}) - χ(X_k, 𝒪_D) = χ(X_k, 𝒪_X(-D)|_{Cᵢ}) = -(D · Cᵢ) + χ(Cᵢ, 𝒪_{Cᵢ})`.

Divisor sums are products of ideal sheaves, so `D' = D + Cᵢ` is `D' = D * Cᵢ`, and `D' ⊂ X_k` is
the containment `ℐ_{X_k} ⊆ ℐ_{D'}`. The modules `𝒪_{D'}`, `𝒪_D` and `𝒪_X(-D)|_{Cᵢ}` are taken on
`X_k` as direct images along the closed immersions into `X_k`. The intersection number
`(D · Cᵢ)` is the intersection product `Stacks.Models.intersectionProduct` of [Stacks, Tag 0C65]
on the components of `X_k`, with `D` read as the formal sum `∑ⱼ bⱼCⱼ` of its coefficients
`bⱼ = Stacks.Models.RegularModelSituation.specialFiberDivisorCoeff D Cⱼ`, which is `D` by
`Stacks.Models.RegularModelSituation.eq_prod_specialFiberDivisorCoeff`.

The first equality is additivity of the Euler characteristic ([Stacks, Tag 08AA]) on the short
exact sequence `0 ⟶ 𝒪_X(-D)|_{Cᵢ} ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0` of [Stacks, Tag 0C4T], brought from `X`
to `X_k` along the closed immersion `X_k ⟶ X`. The second is the definition of the degree,
`deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})`, and the symmetry of [Stacks, Tag 0C64]. -/
@[stacks 0CA2 "χ(X_k, O_D') - χ(X_k, O_D) = χ(X_k, O_X(-D)|_Cᵢ) = -(D · Cᵢ) + χ(Cᵢ, O_Cᵢ)"]
public theorem eulerCharacteristic_addComponent
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (Z : irreducibleComponents S.specialFiber) (D D' : S.X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hsum : D' = D * S.specialFiberComponentIdeal Z) (hk : S.specialFiberIdeal ≤ D') :
    eulerCharacteristic S.k S.specialFiberToSpec
          ((Scheme.Modules.pushforward (S.fibreSubschemeι D' hk)).obj
            (SheafOfModules.unit D'.subscheme.ringCatSheaf)) -
        eulerCharacteristic S.k S.specialFiberToSpec
          ((Scheme.Modules.pushforward (S.fibreSubschemeι D
            (hk.trans (hsum ▸ Scheme.IdealSheafData.mul_le_left D _)))).obj
            (SheafOfModules.unit D.subscheme.ringCatSheaf)) =
      eulerCharacteristic S.k S.specialFiberToSpec
          ((Scheme.Modules.pushforward (S.specialFiberComponentι Z)).obj
            ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
              (Stacks.Divisors.negativeTwist D))) ∧
    eulerCharacteristic S.k S.specialFiberToSpec
          ((Scheme.Modules.pushforward (S.specialFiberComponentι Z)).obj
            ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
              (Stacks.Divisors.negativeTwist D))) =
      -intersectionProduct S Finset.univ (fun Y => S.specialFiberComponentIdeal Y)
          (fun Y => S.specialFiberComponentToSpec Y)
          (fun Y => S.isProper_specialFiberComponentToSpec Y)
          (fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y)
          (fun Y => (S.specialFiberDivisorCoeff D Y : ℤ)) (Pi.single Z 1)
          (fun Y _ => S.isEffectiveCartierDivisor_specialFiberComponent Y) +
        eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
          (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) := by
  have hDk : S.specialFiberIdeal ≤ D :=
    hk.trans (hsum ▸ Scheme.IdealSheafData.mul_le_left D _)
  refine ⟨S.eulerCharacteristic_sub_eq_eulerCharacteristic_restrict Z D D' hsum hk, ?_⟩
  rw [S.eulerCharacteristic_restrict_negativeTwist_eq Z D, S.intersectionProduct_single_right,
    S.specialFiberComponentDegree_invertibleSheaf_eq_sum Z D hDk]
  have hsymm : ∀ Y, S.specialFiberComponentDegree Y
      (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
      (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
        (S.isEffectiveCartierDivisor_specialFiberComponent Z)) =
      S.specialFiberComponentDegree Z
      (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Y))
      (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
        (S.isEffectiveCartierDivisor_specialFiberComponent Y)) := fun Y =>
    S.componentDegree_specialFiberComponent_comm Y Z
  simp only [hsymm]

end RegularProperModelSituation

end Stacks.Models

end
