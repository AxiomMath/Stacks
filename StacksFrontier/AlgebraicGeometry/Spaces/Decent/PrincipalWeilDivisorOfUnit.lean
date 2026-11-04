module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldMeromorphic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RegularMeromorphicSectionDivisorLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection

/-!
# The principal Weil divisor of a rational function

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let
`f ∈ R(X)^*`. **Stacks 0ENP** defines the *principal Weil divisor associated to `f`*,

`div(f) = div_X(f) = ∑_Z ord_Z(f) [Z]`,

the sum over the prime divisors `Z ⊂ X` of the order of vanishing of Stacks 0ENL, and observes
that the sum makes sense by Stacks 0ENN: the prime divisors with `ord_Z(f) ≠ 0` are locally
finite in `|X|`.

The order of vanishing `ord_Z(f)` is `AlgebraicGeometry.Space.GenericFractionEmbedding.ord` at the
canonical embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK,
`AlgebraicGeometry.Space.genericFractionEmbedding`.

## Main results

* `AlgebraicGeometry.Space.genericFractionEmbedding_ord_eq_sub`: `ord_Z(f)` is the difference of
  the orders of vanishing of two regular meromorphic sections of `𝒪_X`.
* `AlgebraicGeometry.Space.genericFractionEmbedding_ord_mem_weilDivisor`: **Stacks 0ENN, the
  second set** — the prime divisors with `ord_Z(f) ≠ 0` are locally finite.
* `AlgebraicGeometry.Space.principalWeilDivisorOfUnit`: **Stacks 0ENP**, `div(f)` in `Div(X)`.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hInt : IsIntegralSpace B S hS X)
variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- The generic Henselian local rings of the prime divisors are nontrivial Noetherian rings of
Krull dimension at most one. -/
private theorem genericHenselianLocalRing_properties (hdec : IsDecentSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    (∀ W : PrimeDivisor B S hS X, Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)) ∧
      (∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)) ∧
      ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) :=
  ⟨fun W => W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN,
    fun W => W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN,
    fun W => W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN⟩

include hInt hN in
/-- **`ord_Z(f)` as a difference of orders of vanishing of sections of `𝒪_X`.** For an invertible
rational function `f` on a locally Noetherian integral algebraic space there are two regular
meromorphic sections `s`, `t` of `𝒪_X` with `ord_Z(f) = ord_{Z,𝒪_X}(s) - ord_{Z,𝒪_X}(t)` at
every prime divisor `Z`, the orders of vanishing of the sections being read at the canonical
ratios of Stacks 0EPR. -/
theorem genericFractionEmbedding_ord_eq_sub (f : (rationalFunctions B S hS hX)ˣ) :
    haveI hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
    haveI : ∀ W : PrimeDivisor B S hS X,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
    ∃ s t : MeromorphicSection.{u, u} B S hS X hX (structureModule ⟨X, hX⟩),
      IsRegularMeromorphicSection.{u, u} B S hS X hX (structureModule ⟨X, hX⟩) s ∧
      IsRegularMeromorphicSection.{u, u} B S hS X hX (structureModule ⟨X, hX⟩) t ∧
      (genericFractionEmbedding B S hS hX hdec hInt hN).ord f =
        divisorCoefficients.{u, u} B S hS hX hdec (structureModule ⟨X, hX⟩) s
            (canonicalLocalRatioFamily B S hS hX hdec (structureModule ⟨X, hX⟩)
              (isInvertibleModule_structureModule ⟨X, hX⟩) hInt hN) -
          divisorCoefficients.{u, u} B S hS hX hdec (structureModule ⟨X, hX⟩) t
            (canonicalLocalRatioFamily B S hS hX hdec (structureModule ⟨X, hX⟩)
              (isInvertibleModule_structureModule ⟨X, hX⟩) hInt hN) := by
  have hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_properties B S hS hX hdec hInt hN
  have hL := isInvertibleModule_structureModule ⟨X, hX⟩
  obtain ⟨t, ht, hrat⟩ := exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul
    B S hS hX hdec hInt hN (structureModule ⟨X, hX⟩) hL f
  refine ⟨regularMeromorphicSection B S hS hX hInt hN (structureModule ⟨X, hX⟩) hL, t,
    isRegularMeromorphicSection_regularMeromorphicSection B S hS hX hInt hN _ hL, ht,
    funext fun W => ?_⟩
  have h := orderOfVanishingSection_eq_add_ord_of_ratio_eq B S hS hX hdec
    (genericFractionEmbedding B S hS hX hdec hInt hN) W (structureModule ⟨X, hX⟩)
    (structureModule ⟨X, hX⟩) _ t
    (canonicalLocalRatioFamily B S hS hX hdec (structureModule ⟨X, hX⟩) hL hInt hN W)
    (canonicalLocalRatioFamily B S hS hX hdec (structureModule ⟨X, hX⟩) hL hInt hN W) f (hrat W)
  simp only [Pi.sub_apply, divisorCoefficients]
  lia

include hInt hN in
/-- **Stacks 0ENN, the second set.** On a locally Noetherian integral algebraic space the prime
divisors `Z` along which an invertible rational function `f` has `ord_Z(f) ≠ 0` are locally finite
in `|X|`; that is, the coefficient family `Z ↦ ord_Z(f)` is a Weil divisor. The order of vanishing
is the one of Stacks 0ENL along the canonical embedding of Stacks 0ENK. -/
theorem genericFractionEmbedding_ord_mem_weilDivisor (f : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hX (hInt.isDecentSpace B S hS X) hInt hN).ord f ∈
      WeilDivisor B S hS X := by
  have hdec : IsDecentSpace B S hS X := hInt.isDecentSpace B S hS X
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_properties B S hS hX hdec hInt hN
  have hL := isInvertibleModule_structureModule ⟨X, hX⟩
  obtain ⟨s, t, hs, ht, heq⟩ := genericFractionEmbedding_ord_eq_sub B S hS hX hInt hN f
  rw [heq]
  exact sub_mem
    (locallyFinite_canonicalDivisorCoefficients_ne_zero B S hS hX hdec hInt hN _ hL s hs)
    (locallyFinite_canonicalDivisorCoefficients_ne_zero B S hS hX hdec hInt hN _ hL t ht)

/-- The *principal Weil divisor associated to `f ∈ R(X)^*`*,
`div(f) = div_X(f) = ∑_Z ord_Z(f) [Z]`, as an element of `Div(X)`, for `X` a locally Noetherian
integral algebraic space over `S`.

The sum is over the prime divisors of `X`, and `ord_Z(f)` is the order of vanishing of Stacks
0ENL, taken along the canonical embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK
(`AlgebraicGeometry.Space.genericFractionEmbedding`). -/
@[stacks 0ENP "div(f) = ∑ ord_Z(f) [Z] as an element of Div(X), for X a locally Noetherian \
integral algebraic space over S and f ∈ R(X)^*: the order of vanishing of Stacks 0ENL along the \
canonical embedding R(X) → Q(O^h_{X,ξ}) of Stacks 0ENK, whose ring-theoretic properties are \
proved; the local finiteness of Stacks 0ENN is proved, nothing is carried"]
def principalWeilDivisorOfUnit (f : (rationalFunctions B S hS hX)ˣ) :
    ↥(WeilDivisor B S hS X) :=
  (genericFractionEmbedding B S hS hX (hInt.isDecentSpace B S hS X) hInt hN).principalDivisor
    (genericFractionEmbedding_ord_mem_weilDivisor B S hS hX hInt hN) f

/-- The coefficient of `div(f)` at a prime divisor `Z` is `ord_Z(f)`, the order of vanishing of
Stacks 0ENL of the image of `f` under the canonical embedding of Stacks 0ENK. -/
@[simp]
theorem coe_principalWeilDivisorOfUnit (f : (rationalFunctions B S hS hX)ˣ) :
    ((principalWeilDivisorOfUnit B S hS hX hInt hN f : ↥(WeilDivisor B S hS X)) :
        PrimeDivisor B S hS X → ℤ) =
      (genericFractionEmbedding B S hS hX (hInt.isDecentSpace B S hS X) hInt hN).ord f :=
  rfl

/-- `div(f)` is a principal Weil divisor in the sense of the class group of Stacks 0ENR. -/
theorem isPrincipal_principalWeilDivisorOfUnit (f : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hX (hInt.isDecentSpace B S hS X) hInt hN).IsPrincipal
      (principalWeilDivisorOfUnit B S hS hX hInt hN f) :=
  ⟨f, rfl⟩

end AlgebraicGeometry.Space

end
