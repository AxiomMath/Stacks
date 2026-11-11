module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product as a cycle

Let `X` be a nonsingular variety and let `V`, `W ⊆ X` be closed subvarieties of dimensions `r`
and `s` which intersect properly. Section 43.14 of the source defines their intersection product
to be the cycle

`W · V = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_{r + s - dim X}`,

an alternating sum of the cycles associated to the `Tor` sheaves. This file constructs that
alternating sum, for any two coherent `𝒪_X`-modules and any dimension index: the source's
`W · V` is the case of the two structure sheaves with `k = r + s - dim X`.

The sum makes sense because of two facts proved elsewhere. Each `Torᵢ^{𝒪_X}(ℱ, 𝒢)` is coherent
on a regular scheme, so it has an associated cycle once its support has delta-dimension at most
`k` — and that bound is where the source's hypothesis of proper intersection enters, since it is
exactly what makes the supports small enough. And the sum has only finitely many nonzero terms,
because the `Tor` sheaves vanish above the dimension of `X`.

## Main definitions

* `AlgebraicGeometry.TorFormula.intersectionProductCycle` — the alternating sum, given the
  support bounds. The intersection product of Tag 0AZR, with the bounds proved from proper
  intersection, is `AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct` in
  `StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SubvarietyIntersectionProduct`.

## Main results

* `AlgebraicGeometry.TorFormula.coherentSheafCycle_eq_zero_of_isZero` — the cycle of a zero
  sheaf is zero.
* `AlgebraicGeometry.TorFormula.torSheafCycle_eq_zero_of_lt` — above the dimension of `X` the
  summands vanish.
* `AlgebraicGeometry.TorFormula.finite_support_torSheafCycle` — hence the alternating sum is a
  finite sum.

## Implementation notes

The alternating sum is a `finsum` over `ℕ`. That is total whatever the summands do, and
`finite_support_torSheafCycle` is what says the value is the honest finite alternating sum of
the source rather than an artefact of the convention: on a regular scheme of dimension at most
`d` every summand with `i > d` is zero, by the vanishing clause of Tag 0AZT.

The delta-dimension bounds on the supports are a parameter `hFk`, one for each `i`, in the same
style as `Stacks.Chow.cycleAssociatedToCoherentSheaf`, since for two arbitrary coherent modules
they need not hold. For the structure sheaves of two properly intersecting closed subvarieties
they are proved by `schemeDeltaDimension_torSheaf_subvariety_le_sub`.

## References

* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- The cycle of a zero sheaf is the zero cycle: a zero sheaf has empty support, so every
coefficient vanishes. -/
theorem coherentSheafCycle_eq_zero_of_isZero (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules)
    [SheafOfModules.IsCoherent F] (k : ℤ)
    (hFk : Stacks.Chow.schemeDeltaDimension C ((Stacks.Chow.reducedSupport F).subschemeι ≫ f)
      ≤ WithBotTop.coe k)
    (h : IsZero F) :
    Stacks.Chow.coherentSheafCycle C f F k hFk = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hx : x ∉ SheafOfModules.supp F :=
    (Scheme.Modules.notMem_supp_iff_isZero_stalk F x).mpr
      (Functor.map_isZero (Scheme.Modules.stalkFunctor X x) h)
  change Stacks.Chow.sheafCycleCoeff C f F k x = 0
  simp [Stacks.Chow.sheafCycleCoeff, hx]

/-- **The Tor-formula alternating sum.** For coherent `𝒪_X`-modules `ℱ` and `𝒢` on a regular
scheme, the alternating sum `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(ℱ, 𝒢)]_k` of the cycles of the `Tor` sheaves,
for a given bound `hFk` on the supports. For `ℱ = 𝒪_W` and `𝒢 = 𝒪_V` the structure sheaves of two
closed subvarieties of dimensions `s` and `r` which intersect properly, and `k = r + s - dim X`,
the bound is proved and this is the intersection product `W · V` of Tag 0AZR,
`AlgebraicGeometry.TorFormula.subvarietyIntersectionProduct`. -/
def intersectionProductCycle (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k) :
    AlgebraicCycle X ℤ :=
  ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i) •
    (haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
     Stacks.Chow.coherentSheafCycle C f (torSheaf X F G i) k (hFk i))

/-- Above the dimension of `X` the summands of the alternating sum vanish: the `Tor` sheaf is
zero there, and the cycle of a zero sheaf is zero. -/
theorem torSheafCycle_eq_zero_of_lt (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (i : ℕ) (hdi : d < i) :
    ((-1 : ℤ) ^ i) •
      (haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
       Stacks.Chow.coherentSheafCycle C f (torSheaf X F G i) k (hFk i)) = 0 := by
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  rw [coherentSheafCycle_eq_zero_of_isZero C f (torSheaf X F G i) k (hFk i)
    (isZero_torSheaf_of_lt X hreg F G d i hd hdi)]
  simp

/-- **The alternating sum defining the intersection product is finite.** On a regular scheme of
dimension at most `d` only the summands with `i ≤ d` contribute. -/
theorem finite_support_torSheafCycle (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf X F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    (Function.support fun i : ℕ => ((-1 : ℤ) ^ i) •
      (haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
       Stacks.Chow.coherentSheafCycle C f (torSheaf X F G i) k (hFk i))).Finite := by
  refine Set.Finite.subset (Set.finite_Iic d) fun i hi => ?_
  by_contra hle
  exact hi (torSheafCycle_eq_zero_of_lt C f hX F G hF hG k hFk hreg d hd i (by simpa using hle))

end AlgebraicGeometry.TorFormula

end
