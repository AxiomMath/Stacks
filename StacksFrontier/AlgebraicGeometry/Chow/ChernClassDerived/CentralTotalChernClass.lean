module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Centrality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeExistenceTotalChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ChernClassCentral
public import StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries
public import StacksCore.Tactic.StacksAttribute

/-!
# The total Chern class in the centre, and Stacks 0FAC (1) for it

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes
are defined in the sense of Stacks 0F9E (1). **Stacks 0FAC (1)** says that `c_p(E)` lies in the
centre of the ring `A^*(X)` of Stacks 0B7E.

This file proves that clause **for the total Chern class**, by descent along an envelope. The
reading for the power sums `P_p(E)` is
`Stacks.Chow.powerSum_mem_center_of_envelopePresentation` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Centrality`; the implementation notes there
record that the total Chern class reading was out of reach, for a reason that the commutative
series ring of `StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCentralSeries` removes.

## What changed, and why the clause is now provable and not vacuous

The total Chern class of a complex is the alternating **product** `∏_n c(ℰ^n)^{(-1)^n}` of Stacks
0ESZ, so it needs a ring in which a total Chern class is invertible. The ring used until now,
`Stacks.Chow.ChowCohomologySeriesRing`, has the whole of `A^i(X)` in each degree, and by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` one exists on the product of Stacks
0B7E if and only if that product is commutative in every pair of non-negative degrees. Carrying
that hypothesis destroys the clause: with commutativity of `A^*(X)` the clause is vacuous, by
`Stacks.Chow.forall_mem_center_of_heq_comm`, and with its non-negative form it is unproved, by
`Stacks.Chow.mem_center_of_isComm_of_heq_comm_neg`.

`Stacks.Chow.CentralUnitalSeries` is the same alternating product formed in the **centre**, where
the Cauchy product is commutative for free. It needs no hypothesis on `A^*(X)`, and the
centrality of each coefficient of the class of a complex is not a theorem about it but its
defining property. So the clause below:

* assumes **nothing** about commutativity of `A^*(X)` or of `A^*(Y)`, and is therefore not an
  instance of the vacuity of `Stacks.Chow.forall_mem_center_of_heq_comm`;
* assumes centrality of the total Chern classes of the **modules** on the source of the envelope,
  which is the conclusion of Stacks 02UA clause (1) — proved here as
  `Stacks.Chow.chernClassBivariant_mem_center`, a proof of `Stacks.Chow.IsCentralComponent`
  verbatim, with no bridge in between — and deduces it for the classes on `X`, which it is not;
* has content exactly because restriction along an envelope is *injective*, Stacks 0GUC, while
  nothing identifies the centre of `A^*(X)` with anything on `Y`.

The degrees: the centre is taken in the ring `A^*(X)`, which is graded by `ℤ`, so the conclusion
is commutation with the classes of **every** degree, the negative ones included. Nothing is left
over in the negative degrees as it would be under
`Stacks.Chow.GradedChowProductRule.IsComm`.

## Main definitions

* `Stacks.Chow.centralChernClassKGroupHom`, `Stacks.Chow.centralChernClassKGroup` — **Stacks
  0FEL in the centre**: the Chern class map `c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` with values in
  the commutative group of central unital series, for a total Chern class datum whose series are
  central. No `Stacks.Chow.ChowCohomologySeriesRing`, hence no commutativity hypothesis, appears.
* `Stacks.Chow.centralTotalChernClassComplex`,
  `Stacks.Chow.centralTotalChernClassComplexLocallyBounded` — **Stacks 0ESZ in the centre**: the
  total Chern class `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` of a complex, and of a locally bounded complex
  on a quasi-compact scheme.

## Main results

* `Stacks.Chow.centralChernClassKGroup_val_eq_chernClassKGroup` — the central Chern class map
  computes the **same series** as the carried one of Stacks 0FEL wherever the latter is defined:
  the two agree on the classes of modules and both are homomorphisms. So nothing is a different
  object; the centre is where the construction needs no hypothesis, not where it changes value.
* `Stacks.Chow.chowCohomologyRestriction_centralChernClassKGroup`,
  `Stacks.Chow.chowCohomologyRestriction_centralTotalChernClassComplex` — **step 2 of the
  source's proof of Stacks 0GUD**, in the centre: `res(c_p(ℰ^•)) = c_p(f^*ℰ^•)`.
* `existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplex`,
  `existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplexLocallyBounded`
  (in `Stacks.Chow`) — **Stacks 0GUD, existence for the total Chern class**, with the
  commutativity hypothesis that
  `existsUnique_chowCohomologyRestriction_eq_totalChernClassComplexLocallyBounded` carries
  removed.
* `Stacks.Chow.totalChernClass_mem_center_of_envelopePresentation` — centrality of the
  total Chern class by descent along an envelope; Stacks 0FAC itself is
  `Stacks.Chow.perfectChernClass_mem_center`.

## Why restriction is the only hard step

Restriction of Chow cohomology along a morphism is a ring map `A^*(X) ⟶ A^*(X')`, and a ring map
carries the centre into the centre only when it is surjective; so there is **no** homomorphism
from the central unital series of `X` to those of `X'`, and the comparison of the two Chern class
maps across a base change cannot be made by composing one. What makes it work is that the
restrictions of the total Chern classes *are* central downstairs — by Stacks 02UA on `X'`, the
hypothesis `pbCh`, and, for a module that is not finite locally free, because both sides are the
unit series. `Stacks.Chow.centralUnitalSeriesRestrictionSubgroup` is the subgroup of series for
which this holds and `Stacks.Chow.centralUnitalSeriesRestrictionHom` the homomorphism on it; the
Chern class map lands there, and the comparison is then two applications of the universal property
of `K_0(Vect(X))` into commutative groups.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

/-! ### The Chern class map of Stacks 0FEL in the centre -/

section KGroup

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso)
  (D : GradedTotalChernClassSeries C G sX (chowCohomologyGradedProductRule hiso)
    (chowCohomologySeriesOne hiso))
  (hcentral : ∀ E : X.Modules, IsCentralSeries C G sX hiso (D.ch E))

/-- The total Chern class of a module, as an element of the commutative group of central unital
series. -/
def centralTotalChernClassModule (E : X.Modules) : CentralUnitalSeries C G sX hiso where
  val := D.ch E
  central := hcentral E
  val_apply_zero := D.ch_apply_zero E

/-- **Stacks 0FEL in the centre, as a homomorphism of groups.** The Chern class map
`c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`, read as a homomorphism from `K_0(Vect(X))` to the group of
*central* series with constant term `1` written additively. The universal property of
`K_0(Vect(X))` applies for the same reason as in `Stacks.Chow.chernClassKGroupHom` — the Whitney
sum formula of Stacks 02UI makes `ℰ ↦ c(ℰ)` additive once the target is written additively — and
the target is a commutative group with **no hypothesis** on `A^*(X)`, by
`Stacks.Chow.CentralUnitalSeries.instCommGroup`, rather than only when a
`Stacks.Chow.ChowCohomologySeriesRing` exists. -/
def centralChernClassKGroupHom :
    AlgebraicGeometry.VectorBundleKZero X →+ Additive (CentralUnitalSeries C G sX hiso) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom
    (fun E => Additive.ofMul (centralTotalChernClassModule C G sX hiso D hcentral E))
    (fun E hE => congrArg Additive.ofMul
      (CentralUnitalSeries.ext (D.ch_eq_one_of_not_isFiniteLocallyFree E hE)))
    (fun f g w h₁ h₂ h₃ _ _ hex => by
      rw [← ofMul_mul]
      exact congrArg Additive.ofMul
        (CentralUnitalSeries.ext (D.ch_shortExact f g w h₁ h₂ h₃ inferInstance inferInstance hex)))

/-- **Stacks 0FEL in the centre.** The Chern class map
`c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)`, sending `[ℰ]` to `c(ℰ)` and extended multiplicatively, with
values in the central unital series. -/
def centralChernClassKGroup (α : AlgebraicGeometry.VectorBundleKZero X) :
    CentralUnitalSeries C G sX hiso :=
  Additive.toMul (centralChernClassKGroupHom C G sX hiso D hcentral α)

/-- The homomorphism sends the generator `[ℰ]` to the total Chern class `c(ℰ)`. -/
@[simp] theorem centralChernClassKGroupHom_classOf (E : X.Modules) :
    centralChernClassKGroupHom C G sX hiso D hcentral
        (AlgebraicGeometry.VectorBundleKZero.classOf X E)
      = Additive.ofMul (centralTotalChernClassModule C G sX hiso D hcentral E) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom_classOf _ _ _ E

/-- The central Chern class map sends the generator `[ℰ]` to the total Chern class `c(ℰ)`. -/
@[simp] theorem centralChernClassKGroup_classOf (E : X.Modules) :
    centralChernClassKGroup C G sX hiso D hcentral
        (AlgebraicGeometry.VectorBundleKZero.classOf X E)
      = centralTotalChernClassModule C G sX hiso D hcentral E :=
  congrArg Additive.toMul (centralChernClassKGroupHom_classOf C G sX hiso D hcentral E)

/-- **The central Chern class map is multiplicative**, which is what "extending multiplicatively"
means: the sum in `K_0(Vect(X))` goes to the Cauchy product of series. -/
theorem centralChernClassKGroup_add (α β : AlgebraicGeometry.VectorBundleKZero X) :
    centralChernClassKGroup C G sX hiso D hcentral (α + β)
      = centralChernClassKGroup C G sX hiso D hcentral α *
        centralChernClassKGroup C G sX hiso D hcentral β :=
  (congrArg Additive.toMul
    (map_add (centralChernClassKGroupHom C G sX hiso D hcentral) α β)).trans (toMul_add _ _)

/-- **The central Chern class map computes the same series as the carried map of Stacks 0FEL.**
Let `R` be a series ring whose degreewise product and unit are those of Stacks 0B7E and let `D'`
be a total Chern class datum for it with the same total Chern classes as `D`. Then the two maps
agree on every class of `K_0(Vect(X))`.

So the construction in the centre is not a different construction: it takes the same values
wherever the carried one is defined at all, and the point of it is that it needs no hypothesis on
`A^*(X)`, not that it computes something else. Both sides are homomorphisms from `K_0(Vect(X))`
into the group of unital series of `R`, the first through the inclusion
`Stacks.Chow.CentralUnitalSeries.toUnitalSeries`, so they agree as soon as they agree on the
classes of modules. -/
theorem centralChernClassKGroup_val_eq_chernClassKGroup {R : ChowCohomologySeriesRing C G sX}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hone : R.one = chowCohomologySeriesOne hiso) (D' : TotalChernClassSeries C G sX R)
    (hch : D'.ch = D.ch) (α : AlgebraicGeometry.VectorBundleKZero X) :
    (centralChernClassKGroup C G sX hiso D hcentral α).val = chernClassKGroup D' α := by
  have key : (MonoidHom.toAdditive (CentralUnitalSeries.toUnitalSeries hmul hone)).comp
        (centralChernClassKGroupHom C G sX hiso D hcentral)
      = chernClassKGroupHom D' := by
    refine AlgebraicGeometry.VectorBundleKZero.addHom_ext fun E hE => ?_
    rw [AddMonoidHom.comp_apply, chernClassKGroupHom_classOf, centralChernClassKGroupHom_classOf]
    exact congrArg Additive.ofMul (Subtype.ext (congrFun hch E).symm)
  exact congrArg Subtype.val (congrArg Additive.toMul
    (congrArg (fun φ : AlgebraicGeometry.VectorBundleKZero X →+
      Additive (ChowCohomologySeriesRing.UnitalSeries R) => φ α) key))

end KGroup

/-! ### The total Chern class of a complex in the centre -/

section Complex

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso)
  (D : GradedTotalChernClassSeries C G sX (chowCohomologyGradedProductRule hiso)
    (chowCohomologySeriesOne hiso))
  (hcentral : ∀ E : X.Modules, IsCentralSeries C G sX hiso (D.ch E))

/-- **Stacks 0ESZ in the centre.** The total Chern class `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` of a
complex of finite locally free modules bounded in the degrees `a, …, a + k`, as an element of the
commutative group of *central* series with constant term `1`; the negative exponents are the
formal inverses of Stacks 0FEL, and the product is formed in the centre of `A^*(X)`, which is
where Remark 0ESW puts it and where no commutativity of `A^*(X)` is needed to form it. -/
def centralTotalChernClassComplex (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) :
    CentralUnitalSeries C G sX hiso :=
  centralChernClassKGroup C G sX hiso D hcentral (alternatingKClass X P a k)

/-- **Stacks 0ESZ in the centre.** The total Chern class of a complex is the alternating product
`∏_n c(ℰ^n)^{(-1)^n}` of the total Chern classes of its terms, which is the formula of the source;
the product is an honest `Finset.prod` because the central series commute. -/
theorem centralTotalChernClassComplex_eq_prod (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) :
    centralTotalChernClassComplex C G sX hiso D hcentral P a k =
      ∏ i ∈ Finset.range (k + 1),
        centralTotalChernClassModule C G sX hiso D hcentral (P.X (a + (i : ℤ))) ^
          ((a + (i : ℤ)).negOnePow : ℤ) := by
  rw [show centralTotalChernClassComplex C G sX hiso D hcentral P a k
        = Additive.toMul (centralChernClassKGroupHom C G sX hiso D hcentral
            (alternatingKClass X P a k)) from rfl, alternatingKClass, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, toMul_zsmul, centralChernClassKGroupHom_classOf]
  rfl

/-- **Stacks 0ESZ in the centre, the locally bounded case.** The total Chern class of a locally
bounded complex of finite locally free modules on a quasi-compact scheme: such a complex vanishes
outside a single global window of degrees, and the class is the bounded-window class on one. -/
def centralTotalChernClassComplexLocallyBounded [CompactSpace X]
    (P : CochainComplex X.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) :
    CentralUnitalSeries C G sX hiso :=
  centralTotalChernClassComplex C G sX hiso D hcentral P
    (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose.1
    (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose.2

/-- **The total Chern class of a locally bounded complex does not depend on the window.** For any
window `a, …, a + k` outside which the terms of the complex vanish, the class of the locally
bounded case is the bounded-window class computed from that window. -/
theorem centralTotalChernClassComplexLocallyBounded_eq [CompactSpace X]
    (P : CochainComplex X.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) :
    centralTotalChernClassComplexLocallyBounded C G sX hiso D hcentral P hP =
      centralTotalChernClassComplex C G sX hiso D hcentral P a k :=
  congrArg (centralChernClassKGroup C G sX hiso D hcentral)
    (alternatingKClass_eq_of_isZero_outside_both P
      (exists_window_of_isLocallyBoundedFiniteLocallyFree hP).choose_spec hvanish)

/-- **Every coefficient of the total Chern class of a complex is central.** This is not a theorem
about the class but its defining property: the alternating product of Stacks 0ESZ is formed in
`Stacks.Chow.CentralUnitalSeries`, whose elements are the series with central coefficients. It is
recorded as a lemma because it is the hypothesis that the descent along an envelope consumes. -/
theorem isCentralComponent_centralTotalChernClassComplex (P : CochainComplex X.Modules ℤ) (a : ℤ)
    (k : ℕ) (p : ℕ) :
    IsCentralComponent C G sX hiso
      ((centralTotalChernClassComplex C G sX hiso D hcentral P a k).val p) :=
  (centralTotalChernClassComplex C G sX hiso D hcentral P a k).central p

end Complex

/-! ### The central Chern class map restricts -/

section BaseChange

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso) (f : X' ⟶ X)
  [LocallyOfFiniteType f] (hgys : G.IsNaturalUnderBaseChangeIso)
  (D : GradedTotalChernClassSeries C G sX (chowCohomologyGradedProductRule hiso)
    (chowCohomologySeriesOne hiso))
  (hcentral : ∀ E : X.Modules, IsCentralSeries C G sX hiso (D.ch E))
  (D' : GradedTotalChernClassSeries C G (f ≫ sX) (chowCohomologyGradedProductRule hiso)
    (chowCohomologySeriesOne hiso))
  (hcentral' : ∀ E : X'.Modules, IsCentralSeries C G (f ≫ sX) hiso (D'.ch E))
  (pbCh : ∀ E : X.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      ∀ i : ℕ, chowCohomologyRestriction C G sX f (i : ℤ) hgys (D.ch E i)
        = D'.ch ((Scheme.Modules.pullback f).obj E) i)

include D' hcentral' pbCh in
/-- **The total Chern class of a module restricts into the centre.** For a finite locally free
module this is the base change clause of Stacks 0ESZ, the hypothesis `pbCh`, together with
centrality downstairs; for a module that is not finite locally free both sides are the unit
series. So the total Chern class of a module lies in the subgroup on which restriction is a
homomorphism of the central series groups. -/
theorem centralTotalChernClassModule_mem_restrictionSubgroup (E : X.Modules) :
    centralTotalChernClassModule C G sX hiso D hcentral E
      ∈ centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys := by
  intro i
  change IsCentralComponent C G (f ≫ sX) hiso
    (chowCohomologyRestriction C G sX f (i : ℤ) hgys (D.ch E i))
  by_cases hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E
  · rw [pbCh E hE i]
    exact hcentral' ((Scheme.Modules.pullback f).obj E) i
  · rw [D.ch_eq_one_of_not_isFiniteLocallyFree E hE,
      chowCohomologyRestriction_chowCohomologySeriesOne]
    exact isCentralSeries_chowCohomologySeriesOne C G (f ≫ sX) hiso i

/-- The Chern class map of Stacks 0FEL in the centre, read in the subgroup of central unital
series whose restriction is again central. Its existence is the whole of the work: `res` is not a
map of centres, so a homomorphism `K_0(Vect(X)) ⟶` central series of `X'` cannot be had by
composing, and the total Chern classes are exactly the elements for which the composite is
defined. -/
def centralChernClassKGroupHomRestriction :
    AlgebraicGeometry.VectorBundleKZero X →+
      Additive (centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom
    (fun E => Additive.ofMul
      (⟨centralTotalChernClassModule C G sX hiso D hcentral E,
        centralTotalChernClassModule_mem_restrictionSubgroup C G sX hiso f hgys D hcentral D'
          hcentral' pbCh E⟩ :
        centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys))
    (fun E hE => congrArg Additive.ofMul (Subtype.ext
      (CentralUnitalSeries.ext (D.ch_eq_one_of_not_isFiniteLocallyFree E hE))))
    (fun g h w h₁ h₂ h₃ _ _ hex => by
      rw [← ofMul_mul]
      exact congrArg Additive.ofMul (Subtype.ext (CentralUnitalSeries.ext
        (D.ch_shortExact g h w h₁ h₂ h₃ inferInstance inferInstance hex))))

/-- `centralChernClassKGroupHomRestriction` sends the class of a module `E` to its central total
Chern class `c(E)`, viewed in the subgroup of central unital series whose restriction is
central. -/
@[simp] theorem centralChernClassKGroupHomRestriction_classOf (E : X.Modules) :
    centralChernClassKGroupHomRestriction C G sX hiso f hgys D hcentral D' hcentral' pbCh
        (AlgebraicGeometry.VectorBundleKZero.classOf X E)
      = Additive.ofMul
        (⟨centralTotalChernClassModule C G sX hiso D hcentral E,
          centralTotalChernClassModule_mem_restrictionSubgroup C G sX hiso f hgys D hcentral D'
            hcentral' pbCh E⟩ :
          centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys) :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom_classOf _ _ _ E

include pbCh in
/-- **The base change clause of Stacks 0ESZ for the total Chern class, in the centre and with no
commutativity hypothesis.** The restriction map of Stacks 0B7F carries the degree-`i` component of
`c(α)` to the degree-`i` component of `c(p(α))`, for every class `α ∈ K_0(Vect(X))`:

  `res(c_i(α)) = c_i(p(α))`.

Taken at the alternating class of a complex, Stacks 0ESZ, this is step 2 of the source's proof of
Stacks 0GUD for the total Chern class, which
`Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex` proves in a carried
`Stacks.Chow.ChowCohomologySeriesRing` — hence under commutativity of `A^*(X)` in every pair of
non-negative degrees, by `Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`. Here no such
hypothesis appears.

Both sides are homomorphisms out of `K_0(Vect(X))` into the **commutative** group of central
unital series of `X'`: the left one through
`Stacks.Chow.centralUnitalSeriesRestrictionHom`, which is defined on the subgroup that
`Stacks.Chow.centralChernClassKGroupHomRestriction` lands in, and the right one through the ring
map `pK` on `K_0(Vect)`. So they agree as soon as they agree on the classes of finite locally free
modules, which is `pbCh`. -/
theorem chowCohomologyRestriction_centralChernClassKGroup
    (pK : AlgebraicGeometry.VectorBundleKZero X →+* AlgebraicGeometry.VectorBundleKZero X')
    (pKClassOf : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        pK (AlgebraicGeometry.VectorBundleKZero.classOf X E)
          = AlgebraicGeometry.VectorBundleKZero.classOf X'
            ((Scheme.Modules.pullback f).obj E))
    (α : AlgebraicGeometry.VectorBundleKZero X) (i : ℕ) :
    chowCohomologyRestriction C G sX f (i : ℤ) hgys
        ((centralChernClassKGroup C G sX hiso D hcentral α).val i)
      = (centralChernClassKGroup C G (f ≫ sX) hiso D' hcentral' (pK α)).val i := by
  have hsub : (MonoidHom.toAdditive
        (centralUnitalSeriesRestrictionSubgroup C G sX hiso f hgys).subtype).comp
        (centralChernClassKGroupHomRestriction C G sX hiso f hgys D hcentral D' hcentral' pbCh)
      = centralChernClassKGroupHom C G sX hiso D hcentral := by
    refine AlgebraicGeometry.VectorBundleKZero.addHom_ext fun E _ => ?_
    rw [AddMonoidHom.comp_apply, centralChernClassKGroupHomRestriction_classOf,
      centralChernClassKGroupHom_classOf]
    rfl
  have hres : (MonoidHom.toAdditive
        (centralUnitalSeriesRestrictionHom C G sX hiso f hgys)).comp
        (centralChernClassKGroupHomRestriction C G sX hiso f hgys D hcentral D' hcentral' pbCh)
      = (centralChernClassKGroupHom C G (f ≫ sX) hiso D' hcentral').comp
        (pK : AlgebraicGeometry.VectorBundleKZero X →+
          AlgebraicGeometry.VectorBundleKZero X') := by
    refine AlgebraicGeometry.VectorBundleKZero.addHom_ext fun E hE => ?_
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      centralChernClassKGroupHomRestriction_classOf]
    erw [pKClassOf E hE, centralChernClassKGroupHom_classOf]
    exact congrArg Additive.ofMul (CentralUnitalSeries.ext (funext fun j => pbCh E hE j))
  have h1 : (Additive.toMul (centralChernClassKGroupHomRestriction C G sX hiso f hgys D hcentral
        D' hcentral' pbCh α)).1
      = centralChernClassKGroup C G sX hiso D hcentral α :=
    congrArg Additive.toMul (DFunLike.congr_fun hsub α)
  have h2 : centralUnitalSeriesRestrictionHom C G sX hiso f hgys
        (Additive.toMul (centralChernClassKGroupHomRestriction C G sX hiso f hgys D hcentral D'
          hcentral' pbCh α))
      = centralChernClassKGroup C G (f ≫ sX) hiso D' hcentral' (pK α) :=
    congrArg Additive.toMul (DFunLike.congr_fun hres α)
  rw [← h1]
  exact congrFun (congrArg CentralUnitalSeries.val h2) i

include pbCh in
/-- **Step 2 of the source's proof of Stacks 0GUD for the total Chern class, in the centre and
with no commutativity hypothesis.** The restriction map of Stacks 0B7F carries the degree-`p`
component of the total Chern class `c(ℰ^•)` of a complex of finite locally free modules to the
degree-`p` component of the total Chern class of the pulled back complex:

  `f^*(c_p(ℰ^•)) = c_p(f^*ℰ^•)`.

`Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex` is the same statement in a carried
`Stacks.Chow.ChowCohomologySeriesRing`, and therefore under commutativity of `A^*(X)` and of
`A^*(X')` in every pair of non-negative degrees by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm`. Here the alternating product is formed
in the centre and that hypothesis is gone; what remains carried is what that theorem also carries,
namely the two total Chern class data, their base change compatibility `pbCh`, and the ring map
`pK` on `K_0(Vect)` with its compatibility `pKClassOf`, no such map being constructed in this
repository. -/
theorem chowCohomologyRestriction_centralTotalChernClassComplex
    (pK : AlgebraicGeometry.VectorBundleKZero X →+* AlgebraicGeometry.VectorBundleKZero X')
    (pKClassOf : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        pK (AlgebraicGeometry.VectorBundleKZero.classOf X E)
          = AlgebraicGeometry.VectorBundleKZero.classOf X'
            ((Scheme.Modules.pullback f).obj E))
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ)))) (p : ℕ) :
    chowCohomologyRestriction C G sX f (p : ℤ) hgys
        ((centralTotalChernClassComplex C G sX hiso D hcentral P a k).val p)
      = (centralTotalChernClassComplex C G (f ≫ sX) hiso D' hcentral'
          (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          a k).val p :=
  (chowCohomologyRestriction_centralChernClassKGroup C G sX hiso f hgys D hcentral D' hcentral'
      pbCh pK pKClassOf (alternatingKClass X P a k) p).trans
    (congrFun (congrArg CentralUnitalSeries.val
      (congrArg (centralChernClassKGroup C G (f ≫ sX) hiso D' hcentral')
        (map_alternatingKClass f pK pKClassOf P a k hflf))) p)

end BaseChange

/-! ### Stacks 0GUD, existence for the total Chern class, in the centre -/

section RingCongr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z : Scheme.{u}} {s s' : Z ⟶ C.S}
  [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (hiso : G.IsNaturalUnderInverseIso)

/-- **A central total Chern class datum read against an equal presentation of the structure
morphism.** A datum for `s : Z ⟶ S` is a datum for any `s'` equal to it: the two are the same
type, presented differently, and the transport is the substitution of the equality. This is
`Stacks.Chow.totalChernClassSeriesCongr` for the data of the centre, where the degreewise product
and the unit series are those of Stacks 0B7E and move with the presentation. -/
def centralTotalChernClassSeriesCongr (h : s = s')
    (D : GradedTotalChernClassSeries C G s (chowCohomologyGradedProductRule hiso)
      (chowCohomologySeriesOne hiso)) :
    GradedTotalChernClassSeries C G s' (chowCohomologyGradedProductRule hiso)
      (chowCohomologySeriesOne hiso) := by
  subst h
  exact D

/-- The series of a transported datum are central as soon as those of the original one are. -/
theorem isCentralSeries_centralTotalChernClassSeriesCongr (h : s = s')
    {D : GradedTotalChernClassSeries C G s (chowCohomologyGradedProductRule hiso)
      (chowCohomologySeriesOne hiso)}
    (hcentral : ∀ E : Z.Modules, IsCentralSeries C G s hiso (D.ch E)) (E : Z.Modules) :
    IsCentralSeries C G s' hiso
      ((centralTotalChernClassSeriesCongr C G hiso h D).ch E) := by
  subst h
  exact hcentral E

/-- The component of the total Chern class of a complex computed with a transported datum is the
component computed with the original one, read through the transport of the Chow cohomology
groups. -/
theorem bivariantClassCongrBase_centralTotalChernClassComplex (h : s = s')
    {D : GradedTotalChernClassSeries C G s (chowCohomologyGradedProductRule hiso)
      (chowCohomologySeriesOne hiso)}
    (hcentral : ∀ E : Z.Modules, IsCentralSeries C G s hiso (D.ch E))
    (P : CochainComplex Z.Modules ℤ) (a : ℤ) (k : ℕ) (p : ℕ) :
    bivariantClassCongrBase C G (𝟙 Z) h.symm h.symm (hv := Category.id_comp s')
        (hv' := Category.id_comp s) (p : ℤ)
        ((centralTotalChernClassComplex C G s' hiso
          (centralTotalChernClassSeriesCongr C G hiso h D)
          (fun E => isCentralSeries_centralTotalChernClassSeriesCongr C G hiso h hcentral E)
          P a k).val p) =
      (centralTotalChernClassComplex C G s hiso D hcentral P a k).val p := by
  subst h
  rfl

end RingCongr

section Descent

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hiso : G.IsNaturalUnderInverseIso) (g : Y ⟶ X)
  [LocallyOfFiniteType g] (hgys : G.IsNaturalUnderBaseChangeIso)
  (D : GradedTotalChernClassSeries C G (g ≫ sX) (chowCohomologyGradedProductRule hiso)
    (chowCohomologySeriesOne hiso))
  (hcentral : ∀ E : Y.Modules, IsCentralSeries C G (g ≫ sX) hiso (D.ch E))
  (DZ : GradedTotalChernClassSeries C G (pullback.fst g g ≫ (g ≫ sX))
    (chowCohomologyGradedProductRule hiso) (chowCohomologySeriesOne hiso))
  (hcentralZ : ∀ E : (pullback g g).Modules,
    IsCentralSeries C G (pullback.fst g g ≫ (g ≫ sX)) hiso (DZ.ch E))
  (pbChfst : ∀ E : Y.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      ∀ i : ℕ, chowCohomologyRestriction C G (g ≫ sX) (pullback.fst g g) (i : ℤ) hgys (D.ch E i)
        = DZ.ch ((Scheme.Modules.pullback (pullback.fst g g)).obj E) i)
  (pbChsnd : ∀ E : Y.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      ∀ i : ℕ, chowCohomologyRestriction C G (g ≫ sX) (pullback.snd g g) (i : ℤ) hgys (D.ch E i)
        = (centralTotalChernClassSeriesCongr C G hiso
            (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm DZ).ch
          ((Scheme.Modules.pullback (pullback.snd g g)).obj E) i)
  (pKfst pKsnd : AlgebraicGeometry.VectorBundleKZero Y →+*
    AlgebraicGeometry.VectorBundleKZero (pullback g g))
  (pKClassOffst : ∀ E : Y.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      pKfst (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
        = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
          ((Scheme.Modules.pullback (pullback.fst g g)).obj E))
  (pKClassOfsnd : ∀ E : Y.Modules,
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
      pKsnd (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
        = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
          ((Scheme.Modules.pullback (pullback.snd g g)).obj E))

include pbChfst pbChsnd pKClassOffst pKClassOfsnd in
/-- **The two restrictions of `c_p(ℰ^•)` to `Y ×_X Y` agree, in the centre.** This is
`Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex_eq` with the alternating product
formed in `Stacks.Chow.CentralUnitalSeries`, so that no
`Stacks.Chow.ChowCohomologySeriesRing` — and hence no commutativity of `A^*(Y)` or of
`A^*(Y ×_X Y)` in any pair of degrees — appears. Each restriction is the corresponding component
of the total Chern class of the pulled back complex by
`Stacks.Chow.chowCohomologyRestriction_centralTotalChernClassComplex`, and the transport between
the two presentations of the structure morphism of `Y ×_X Y` is absorbed into the datum by
`Stacks.Chow.bivariantClassCongrBase_centralTotalChernClassComplex`, which is why one datum on
`Y ×_X Y` suffices for both projections. -/
theorem chowCohomologyRestriction_centralTotalChernClassComplex_eq
    (P : CochainComplex Y.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (a + (i : ℤ)))) (p : ℕ)
    (hPP : (centralTotalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) hiso DZ hcentralZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).val p =
        (centralTotalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) hiso DZ hcentralZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).val p) :
    chowCohomologyRestriction C G (g ≫ sX) (pullback.fst g g) (p : ℤ) hgys
        ((centralTotalChernClassComplex C G (g ≫ sX) hiso D hcentral P a k).val p)
      = bivariantClassCongrBase C G (𝟙 (pullback g g))
        (selfPullbackSnd_comp_structureMorphism_eq C sX g)
        (selfPullbackSnd_comp_structureMorphism_eq C sX g) (hv := Category.id_comp _)
        (hv' := Category.id_comp _) (p : ℤ)
        (chowCohomologyRestriction C G (g ≫ sX) (pullback.snd g g) (p : ℤ) hgys
          ((centralTotalChernClassComplex C G (g ≫ sX) hiso D hcentral P a k).val p)) := by
  rw [chowCohomologyRestriction_centralTotalChernClassComplex C G (g ≫ sX) hiso
      (pullback.fst g g) hgys D hcentral DZ hcentralZ pbChfst pKfst pKClassOffst P a k hflf p,
    chowCohomologyRestriction_centralTotalChernClassComplex C G (g ≫ sX) hiso
      (pullback.snd g g) hgys D hcentral
      (centralTotalChernClassSeriesCongr C G hiso
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm DZ)
      (fun E => isCentralSeries_centralTotalChernClassSeriesCongr C G hiso
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm hcentralZ E)
      pbChsnd pKsnd pKClassOfsnd P a k hflf p,
    bivariantClassCongrBase_centralTotalChernClassComplex C G hiso
      (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm hcentralZ]
  exact hPP

variable (hgysP : G.IsNaturalUnderProperPushforward)
  (hgysC : G.IsNaturalUnderPullbackCompPushforward) (hgE : IsEnvelope g)

include hgysP hgysC hgE pbChfst pbChsnd pKClassOffst pKClassOfsnd in
/-- **Stacks 0GUD, existence for the total Chern class, with no commutativity hypothesis.** Let
`g : Y ⟶ X` be an envelope and let `ℰ^•` be a complex of finite locally free modules on `Y`
bounded in the degrees `a, …, a + k` whose total Chern class is compatible with restriction to
`Y ×_X Y`. Then there is a **unique** class in `A^p(X)` whose restriction of Stacks 0B7F along `g`
is the degree-`p` component of `c(ℰ^•)`.

This is
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_totalChernClassComplex` with the
alternating product of Stacks 0ESZ formed in the centre. What that theorem carries and this one
does not is a `Stacks.Chow.ChowCohomologySeriesRing` on `Y` and on `Y ×_X Y`, which by
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` is commutativity of `A^*(Y)` and of
`A^*(Y ×_X Y)` in every pair of non-negative degrees — a hypothesis the source does not make. -/
theorem existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplex
    (P : CochainComplex Y.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (a + (i : ℤ)))) (p : ℕ)
    (hPP : (centralTotalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) hiso DZ hcentralZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).val p =
        (centralTotalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) hiso DZ hcentralZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).val p) :
    ∃! c : chowCohomologyComponent C G sX (p : ℤ),
      chowCohomologyRestriction C G sX g (p : ℤ) hgys c =
        (centralTotalChernClassComplex C G (g ≫ sX) hiso D hcentral P a k).val p :=
  existsUnique_chowCohomologyRestriction_eq_of_restriction_eq C G sX g (p : ℤ)
    hgys hgysP hgysC hgE _
    (chowCohomologyRestriction_centralTotalChernClassComplex_eq C G sX hiso g hgys D hcentral
      DZ hcentralZ pbChfst pbChsnd pKfst pKsnd pKClassOffst pKClassOfsnd P a k hflf p hPP)

include hgysP hgysC hgE pbChfst pbChsnd pKClassOffst pKClassOfsnd in
/-- **Stacks 0GUD, existence for the total Chern class of a locally bounded complex, with no
commutativity hypothesis.** The locally bounded case of
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplex`: a window of
degrees outside which the complex vanishes identifies the class of
`Stacks.Chow.centralTotalChernClassComplexLocallyBounded` with the bounded-window class, by
`Stacks.Chow.centralTotalChernClassComplexLocallyBounded_eq`. -/
theorem existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplexLocallyBounded
    [CompactSpace Y] (P : CochainComplex Y.Modules ℤ)
    (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) (p : ℕ)
    (hPP : (centralTotalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) hiso DZ hcentralZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).val p =
        (centralTotalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) hiso DZ hcentralZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).val p) :
    ∃! c : chowCohomologyComponent C G sX (p : ℤ),
      chowCohomologyRestriction C G sX g (p : ℤ) hgys c =
        (centralTotalChernClassComplexLocallyBounded C G (g ≫ sX) hiso D hcentral P hP).val p := by
  rw [centralTotalChernClassComplexLocallyBounded_eq C G (g ≫ sX) hiso D hcentral P hP hvanish]
  exact existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplex C G sX hiso g hgys
    D hcentral DZ hcentralZ pbChfst pbChsnd pKfst pKsnd pKClassOffst pKClassOfsnd hgysP hgysC hgE
    P a k (fun i _ => isFiniteLocallyFree_X_of_isLocallyBounded hP _) p hPP

end Descent

/-! ### Centrality of the total Chern class of an envelope presentation -/

section Derived

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)
  (hiso : G.IsNaturalUnderInverseIso) {E : DerivedCategory X.Modules}

/-- **Centrality of the total Chern class, by descent along an envelope.** Stacks 0FAC (1) is
`Stacks.Chow.perfectChernClass_mem_center`. Let `E` be an object of `D(𝒪_X)` and let `H` be
an envelope presentation of it, Stacks 0F9E (1), whose source is quasi-compact. Let `c` be a
family of Chow cohomology classes of `X` whose restrictions along the envelope of `H` are the
components of the total Chern class `c(ℰ_Y^•)` of the presenting complex — the repository's
expression for "`c` is the family of Chern classes of `E`", exactly as in
`Stacks.Chow.eq_of_restriction_eq_totalChernClassComplexLocallyBounded`. Then each `c p` lies in
the centre of the ring `A^*(X)` of Stacks 0B7E, provided the total Chern classes of the modules on
the source of the envelope do.

The proof is the one the source's clause has no need of and this repository does: the total Chern
class of the complex is formed in `Stacks.Chow.CentralUnitalSeries`, so each of its coefficients
is central on `Y` by construction, and centrality descends along an envelope by
`Stacks.Chow.mem_center_of_isEnvelope`, restriction along an envelope being injective by the
uniqueness half of Stacks 0GUC and a ring map by Stacks 0B7F.

Nothing about commutativity of `A^*(X)` or of `A^*(Y)` is assumed, which is what makes the clause
informative; see the implementation notes of this file and of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCenterUnderCommutativity`. -/
theorem totalChernClass_mem_center_of_envelopePresentation
    (H : EnvelopePresentation E) [LocallyOfFiniteType H.f] [CompactSpace H.Y]
    (D : GradedTotalChernClassSeries C G (H.f ≫ sX) (chowCohomologyGradedProductRule hiso)
      (chowCohomologySeriesOne hiso))
    (hcentral : ∀ M : H.Y.Modules, IsCentralSeries C G (H.f ≫ sX) hiso (D.ch M))
    (c : ∀ p : ℕ, chowCohomologyComponent C G sX (p : ℤ))
    (hc : ∀ p : ℕ, chowCohomologyRestriction C G sX H.f (p : ℤ) hgys (c p) =
      (centralTotalChernClassComplexLocallyBounded C G (H.f ≫ sX) hiso D hcentral H.P
        H.locallyBounded).val p)
    (p : ℕ) :
    IsCentralComponent C G sX hiso (c p) := by
  let := chowCohomologyRing C G sX hiso
  let := chowCohomologyRing C G (H.f ≫ sX) hiso
  refine mem_center_of_isEnvelope C G sX H.f hgys hiso H.envelope _ ?_
  rw [chowCohomologyTotalRestriction_of, hc p]
  exact (centralTotalChernClassComplexLocallyBounded C G (H.f ≫ sX) hiso D hcentral H.P
    H.locallyBounded).central p

end Derived

end Stacks.Chow

end
