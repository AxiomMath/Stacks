module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness
public import StacksCore.Tactic.StacksAttribute

/-!
# Centrality of the characteristic classes of a perfect object of the derived category

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `E` be a perfect object of `D(𝒪_X)` whose Chern
classes are defined in the sense of Stacks 0F9E (1). **Stacks 0FAC (1)** says that `c_p(E)` lies
in the centre of the ring `A^*(X)` of Stacks 0B7E.

This file proves that clause for the **power sums** `P_p(E)`, the classes of Stacks 0ESZ, by
descent along an envelope.

## Main results

* `Stacks.Chow.chowCohomologyTotalRestriction_injective` — the graded restriction map
  `res : A^*(Y) ⟶ A^*(Y')` of Stacks 0B7F is injective as soon as it is injective in each degree.
* `Stacks.Chow.mem_center_of_chowCohomologyTotalRestriction_mem_center` — centrality descends
  along a degreewise injective restriction map: `res` is a ring map, so a class whose restriction
  is central is central.
* `Stacks.Chow.mem_center_of_isEnvelope` — the same along an envelope, where the degreewise
  injectivity is automatic.
* `Stacks.Chow.powerSumClassComplex_mem_center` — the class `P_p(ℰ^•)` of a complex is central
  whenever the classes `P_p` of modules are, the former being an alternating sum of the latter.
* `Stacks.Chow.powerSum_mem_center_of_envelopePresentation` — centrality of the power
  sums by descent along an envelope (Stacks 0FAC itself is
  `Stacks.Chow.perfectPowerSumComponent_mem_center`). A family of classes on `X` restricting along
  an envelope presentation of `E` to the power sums of the presenting complex is central in
  `A^*(X)`.

## Implementation notes

### What stands in for `c_p(E)`

This repository does not construct the Chern classes of a perfect object; the existence half of
Stacks 0GUD is not available. A family `c` of classes on `X` together with the hypothesis that
its restriction along the envelope of an envelope presentation is the corresponding class of the
presenting complex is the only expression this repository has for "`c` **is** the family of
characteristic classes of `E`", and it is the hypothesis taken here, in exactly the shape
`Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded` takes it. See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness`.

### Why the power sums here, and where the total Chern class reading is

`P_p` of a complex is an element of `A^p(X)` and the alternating **sum** of the `P_p` of its
terms, so the centre, being an additive subgroup, swallows it as soon as it swallows the classes
of modules. The total Chern class of a complex is the alternating **product** of Stacks 0ESZ, so
it needs a ring in which a total Chern class is invertible, and which ring that is decides whether
the clause has content.

It must not be a `Stacks.Chow.ChowCohomologySeriesRing` built on the product of Stacks 0B7E, and
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCenterUnderCommutativity` proves why. By
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction` such a ring exists if
and only if `Stacks.Chow.GradedChowProductRule.IsComm` holds for that product, and then:

* if the commutativity assumed is that of the ring `A^*(X)` — equivalently, degreewise in every
  pair of degrees of `ℤ` — the clause is **vacuous**, by
  `Stacks.Chow.forall_mem_center_of_heq_comm`: its conclusion then holds of *every* family of
  classes `c p ∈ A^p(X)`, with no hypothesis relating the family to anything;
* `Stacks.Chow.GradedChowProductRule.IsComm` itself is less than that, since it quantifies over
  the degrees in `ℕ` while `A^*(X)` is graded by `ℤ`
  (`Stacks.Chow.chowCohomologyMul_heq_comm_of_isComm`); under it the clause is **not** vacuous,
  but by `Stacks.Chow.mem_center_of_isComm_of_heq_comm_neg` what is left to prove is exactly the
  commutation with the classes of the negative degrees, which the source does not address.

The ring it must be is the one the source itself works in:
`Stacks.Chow.CentralUnitalSeries` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries`, the series with **central**
coefficients, which is a commutative group with no hypothesis on `A^*(X)` at all. The total Chern
class reading of the clause is proved there, as
`Stacks.Chow.totalChernClass_mem_center_of_envelopePresentation` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CentralTotalChernClass`, by the same descent
along an envelope as below. The power sum reading remains the one that needs no series ring at
all, and it is the reading below.

### Why centrality descends along an envelope

Restriction of Chow cohomology along an envelope is injective, by
`Stacks.Chow.chowCohomologyRestriction_injective_of_isEnvelope`, the uniqueness half of
Stacks 0GUC; and the graded restriction map is a ring homomorphism, by Stacks 0B7F. An injective
ring map reflects centrality: from `res(x · y) = res(x) · res(y) = res(y) · res(x) = res(y · x)`
and injectivity one gets `x · y = y · x`. No multiplicativity in the other direction and no
surjectivity is needed, which is why the clause descends from the envelope even though almost
nothing else does.

The degreewise restriction maps assemble into the graded one as `DirectSum.map`, whose value at a
degree is the value of that degree's map; so injectivity in each degree gives injectivity of the
graded map.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-! ### Injectivity of the graded restriction map -/

section Injective

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- The graded restriction map `res : A^*(Y) ⟶ A^*(Y')` of Stacks 0B7F evaluated at a degree is
the degreewise restriction map of that degree evaluated at the corresponding component: the graded
map is `DirectSum.map` of the degreewise ones. -/
theorem chowCohomologyTotalRestriction_apply (x : chowCohomology C G sY) (p : ℤ) :
    chowCohomologyTotalRestriction C G sY f hgys x p =
      chowCohomologyRestriction C G sY f p hgys (x p) :=
  DFinsupp.mapRange_apply _ (fun _ => map_zero _) x p

/-- **The graded restriction map is injective as soon as every degreewise one is.** The graded map
is `DirectSum.map` of the degreewise maps, so its value at a degree is the value of that degree's
map, and two classes with the same restriction have the same components. -/
theorem chowCohomologyTotalRestriction_injective
    (hinj : ∀ p : ℤ, Function.Injective (chowCohomologyRestriction C G sY f p hgys)) :
    Function.Injective (chowCohomologyTotalRestriction C G sY f hgys) := by
  intro x y hxy
  refine DFinsupp.ext fun p => hinj p ?_
  rw [← chowCohomologyTotalRestriction_apply C G sY f hgys x p,
    ← chowCohomologyTotalRestriction_apply C G sY f hgys y p, hxy]

end Injective

/-! ### Centrality descends along the restriction map -/

section Center

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso) (hiso : G.IsNaturalUnderInverseIso)

/-- **Centrality descends along a degreewise injective restriction map.** The graded restriction
map of Stacks 0B7F is a homomorphism of the rings of Stacks 0B7E, so a class whose restriction is
central is itself central: `res(x · y) = res(x) · res(y) = res(y) · res(x) = res(y · x)`, and
`res` is injective. The ring structure of Stacks 0B7E is an `@[instance_reducible] def` and not
an `instance`, which is why it is supplied by hand. -/
theorem mem_center_of_chowCohomologyTotalRestriction_mem_center
    (hinj : ∀ p : ℤ, Function.Injective (chowCohomologyRestriction C G sY f p hgys))
    (x : chowCohomology C G sY)
    (hx : letI := chowCohomologyRing C G (f ≫ sY) hiso
      chowCohomologyTotalRestriction C G sY f hgys x ∈
        Subring.center (chowCohomology C G (f ≫ sY))) :
    letI := chowCohomologyRing C G sY hiso
    x ∈ Subring.center (chowCohomology C G sY) := by
  let := chowCohomologyRing C G sY hiso
  let := chowCohomologyRing C G (f ≫ sY) hiso
  rw [Subring.mem_center_iff] at hx ⊢
  intro y
  refine chowCohomologyTotalRestriction_injective C G sY f hgys hinj ?_
  have h := hx (chowCohomologyTotalRestriction C G sY f hgys y)
  rw [chowCohomologyTotalRestriction_mul C G sY f hgys hiso,
    chowCohomologyTotalRestriction_mul C G sY f hgys hiso]
  exact h

/-- **Centrality descends along an envelope.** Restriction of Chow cohomology along an envelope is
injective in every degree, by `Stacks.Chow.chowCohomologyRestriction_injective_of_isEnvelope`, so
a class of `A^*(Y)` whose restriction to the source of an envelope is central is central. -/
theorem mem_center_of_isEnvelope (hfE : IsEnvelope f) (x : chowCohomology C G sY)
    (hx : letI := chowCohomologyRing C G (f ≫ sY) hiso
      chowCohomologyTotalRestriction C G sY f hgys x ∈
        Subring.center (chowCohomology C G (f ≫ sY))) :
    letI := chowCohomologyRing C G sY hiso
    x ∈ Subring.center (chowCohomology C G sY) :=
  mem_center_of_chowCohomologyTotalRestriction_mem_center C G sY f hgys hiso
    (fun p => chowCohomologyRestriction_injective_of_isEnvelope C G sY f p hgys hfE) x hx

end Center

/-! ### The power sums of a complex are central -/

section Complex

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso)

/-- **The class `P_p(ℰ^•)` of a complex is central whenever the classes `P_p` of modules are.**
The class of a complex is the alternating sum `∑_n (-1)^n P_p(ℰ^n)` of Stacks 0ESZ and the centre
is a subring, hence closed under sums and integer multiples. -/
theorem powerSumClassComplex_mem_center (W : PowerSumClassRule C G sX)
    (hW : ∀ (M : X.Modules) (p : ℕ),
      letI := chowCohomologyRing C G sX hiso
      DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (p : ℤ) (W.cls M p) ∈
        Subring.center (chowCohomology C G sX))
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) (p : ℕ) :
    letI := chowCohomologyRing C G sX hiso
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (p : ℤ)
        (powerSumClassComplex C G sX W P a k p) ∈
      Subring.center (chowCohomology C G sX) := by
  let := chowCohomologyRing C G sX hiso
  rw [powerSumClassComplex_eq_sum, map_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  exact Subring.zsmul_mem _ (hW (P.X (a + (i : ℤ))) p) _

end Complex

/-! ### Centrality of the power sums of an envelope presentation -/

section Derived

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)
  (hiso : G.IsNaturalUnderInverseIso) {E : DerivedCategory X.Modules}

/-- **Centrality of the power sums, by descent along an envelope.** Stacks 0FAC (1) for the
classes `P_p(E)` is `Stacks.Chow.perfectPowerSumComponent_mem_center`. Let `E` be an object of
`D(𝒪_X)` and let `H` be an envelope presentation of it, Stacks 0F9E (1), whose source is
quasi-compact. Let `c` be a family of Chow cohomology classes of `X` whose restrictions along
the envelope of `H` are the classes `P_p(ℰ_Y^•)` of the presenting complex — the repository's
expression for "`c` is the family of power sums of `E`", exactly as in
`Stacks.Chow.eq_of_restriction_eq_powerSumClassComplexLocallyBounded`. Then each `c p` lies in the
centre of the ring `A^*(X)` of Stacks 0B7E, provided the classes `P_p` of modules on the source of
the envelope do.

The hypothesis `hW` is the centrality clause of Stacks 02UA for the power sums of a *module*; it
is carried because `Stacks.Chow.PowerSumClassRule` is a bare family of classes, the evaluated
power sums of Stacks 0F9B not being constructed in this repository. Nothing about `E`, about the
presentation or about the complex is assumed beyond it: the descent along the envelope is
unconditional. -/
theorem powerSum_mem_center_of_envelopePresentation
    (H : EnvelopePresentation E) [LocallyOfFiniteType H.f] [CompactSpace H.Y]
    (W : PowerSumClassRule C G (H.f ≫ sX))
    (hW : ∀ (M : H.Y.Modules) (q : ℕ),
      letI := chowCohomologyRing C G (H.f ≫ sX) hiso
      DirectSum.of (fun n : ℤ ↦ chowCohomologyComponent C G (H.f ≫ sX) n) (q : ℤ) (W.cls M q) ∈
        Subring.center (chowCohomology C G (H.f ≫ sX)))
    (c : ∀ p : ℕ, chowCohomologyComponent C G sX (p : ℤ))
    (hc : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      powerSumClassComplexLocallyBounded C G (H.f ≫ sX) W H.P H.locallyBounded p)
    (p : ℕ) :
    letI := chowCohomologyRing C G sX hiso
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (p : ℤ) (c p) ∈
      Subring.center (chowCohomology C G sX) := by
  let := chowCohomologyRing C G sX hiso
  let := chowCohomologyRing C G (H.f ≫ sX) hiso
  refine mem_center_of_isEnvelope C G sX H.f hgys hiso H.envelope _ ?_
  rw [chowCohomologyTotalRestriction_of, hc p, powerSumClassComplexLocallyBounded]
  exact powerSumClassComplex_mem_center C G (H.f ≫ sX) hiso W hW H.P _ _ p

end Derived

end Stacks.Chow

end
