module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineProductDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.GeometricRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleLocalConditions
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePushforward
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 parts (1)(b) and (2): the fibre cycle as a pushforward, and rational equivalence

Let `W ⊆ X ×_S ℙ¹_S` be a closed subvariety meeting the image of the zero section properly.
Part (1)(a) of Tag 0B07 identifies the cycle of the scheme-theoretic intersection
`W ∩ (X × a)` with the Section 43.14 intersection product `W · (X × a)` on `X ×_S ℙ¹_S`. Part
(1)(b) reads the same cycle on `X`: the fibre `W_a`, viewed as a closed subscheme of `X`
through the section, has cycle the proper pushforward of `W · (X × a)` along the projection
`pr : X ×_S ℙ¹_S ⟶ X`. Part (2) follows for a prime cycle: the difference of the two fibre
cycles is a basic rational equivalence in the sense of Tag 0AZG, and by Tag 0AZI those generate
the cycles rationally equivalent to zero.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle_of_isIntegral` —
  **Tag 0B07 part (1)(a)**, `[W_a]_k = W · (X × a)` as cycles on `X ×_S ℙ¹_S`.
* `Stacks.Chow.properPushforward_intersectionProductCycle_eq_zeroFiberCycle` and its infinity
  twin — **Tag 0B07 part (1)(b)**, `[W_a]_k = pr_{X,*}(W · X × a)`.
* `Stacks.Chow.properPushforward_intersectionProductCycle_integralComponentAt_eq_zeroFiberCycle`
  and its infinity twin — the same for `W = closure {x}`, presented by its generic point.
* `Stacks.Chow.sub_properPushforward_intersectionProductCycle_mem_rationalEquivalences` — **Tag
  0B07 part (2) for a prime cycle**.
* `sub_properPushforward_intersectionProductCycle_integralComponentAt_mem_rationalEquivalences`
  (in `Stacks.Chow`) — the same for `W = closure {x}`.
* `AlgebraicGeometry.TorFormula.schemeDeltaDimension_reducedSupport_torSheaf_le` — the `Tor`
  sheaves of two subscheme structure sheaves are supported on the scheme-theoretic intersection,
  so proper intersection bounds the delta-dimension of every one of their supports. This is what
  the Section 43.14 product of Tag 0AZR asks of proper intersection, and it is never assumed
  below.

## Implementation notes

Nothing pointwise is assumed anywhere in this file. The hypotheses are those of the source: `W`
is a closed subvariety of delta-dimension `k + 1` meeting the image of the section properly. The
local conditions of part (1)(a) are derived from that by
`Stacks.Chow.localConditions_ker_zeroSection` and its infinity twin, the image of a
distinguished section being an effective Cartier divisor.

Neither are the delta-dimension bounds on the supports of the `Tor` sheaves that the Section
43.14 product of Tag 0AZR needs in its own definition: they are
`AlgebraicGeometry.TorFormula.schemeDeltaDimension_reducedSupport_torSheaf_le`, proved at the top
of this file, and derived from proper intersection alone. What the part (1)(a) and part (1)(b)
statements here do carry about the ambient family `X ×_S ℙ¹_S` is its regularity `hY` and a
bound `hd` on its Krull dimension, because they are stated over an arbitrary Chow situation:
over an arbitrary base neither regularity of the ambient family follows from anything assumed
about `X`, nor is the family of finite dimension, and the bound is what makes the alternating
`Tor` sum of the Section 43.14 product finite. Neither clause is in the source, whose `X` is a
nonsingular variety over an algebraically closed field; in that setting both are theorems —
`Stacks.Chow.isRegular_projectiveLineProduct_of_eq` and
`Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le` — and
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleNonsingularVariety` carries
all of parts (1)(a), (1)(b), (2) and (3) there, with both derived and neither assumed. The two
part (2) statements of this file, which are stated for a variety over an algebraically closed
field already, carry no dimension bound: they obtain it from that existence theorem.

The general `(k + 1)`-cycle `α` of part (2) is the `ℤ`-linear extension of the prime case over
the components of `α`, through the bilinear extension
`AlgebraicGeometry.TorFormula.cycleIntersectionProduct` of Tag 0B08. That extension and part
(3), the converse, are carried in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalenceCycle`.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZG](https://stacks.math.columbia.edu/tag/0AZG)
* [Stacks Project, Tag 0AZI](https://stacks.math.columbia.edu/tag/0AZI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- **The Tor-support bound from proper intersection.** The `Tor` sheaves of the structure
sheaves of two closed subschemes are supported on their scheme-theoretic intersection, so a
bound on the delta-dimension of that intersection bounds the delta-dimension of the support of
every one of them.

This is what the Section 43.14 product of Tag 0AZR asks of proper intersection in the shape its
own definition consumes: the hypothesis `hFk` of
`AlgebraicGeometry.TorFormula.intersectionProductCycle` is never assumed in this file, it is
this term. -/
theorem schemeDeltaDimension_reducedSupport_torSheaf_le (C : Stacks.Chow.ChowSituation.{u})
    {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (hY : IsRegular Y) (W D : Y.IdealSheafData) (k : ℤ)
    (hWD : Stacks.Chow.schemeDeltaDimension C ((W ⊔ D).subschemeι ≫ f) ≤ (k : EInt)) :
    ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf W)
        (subschemeStructureSheaf D) (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf D) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf Y (subschemeStructureSheaf W)
          (subschemeStructureSheaf D) i)).subschemeι ≫ f) ≤ WithBotTop.coe k := by
  intro i
  have := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf W)
    (subschemeStructureSheaf D) (isCoherent_subschemeStructureSheaf W)
    (isCoherent_subschemeStructureSheaf D) i
  refine Stacks.Chow.schemeDeltaDimension_reducedSupport_le C f _ fun z hz => ?_
  obtain ⟨hzW, hzD⟩ := supp_torSheaf_subset_inter Y _ _ i hz
  rw [supp_subschemeStructureSheaf] at hzW
  rw [supp_subschemeStructureSheaf] at hzD
  have hzmem : z ∈ Set.range (W ⊔ D).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_sup]
    exact ⟨hzW, hzD⟩
  obtain ⟨w, rfl⟩ := hzmem
  exact Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le C f (W ⊔ D).subschemeι hWD w

end AlgebraicGeometry.TorFormula

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### The cycle of the scheme-theoretic intersection is the intersection product -/

variable {Y : Scheme.{u}}

/-- The cycle of the scheme-theoretic intersection `W ∩ D` is the Tor-formula intersection
product of `W` and `D`: this is Tag 0B07 part (1)(a) together with the identification
`[Z]_k = [𝒪_Z]_k` of Tag 02QY. -/
theorem cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle (f : Y ⟶ C.S)
    [LocallyOfFiniteType f] (hY : IsRegular Y) (W D : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hWD : schemeDeltaDimension C ((W ⊔ D).subschemeι ≫ f) ≤ (k : EInt))
    (hpt : ∀ z : Y, relativeDimension C.dimensionFunction f z = k →
      z ∈ (W ⊔ D).support →
        IsDomain (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        (∃ g : Fin 1 → Y.presheaf.stalk z,
          RingTheory.Sequence.IsRegular (Y.presheaf.stalk z) (List.ofFn g) ∧
            IdealSheafData.stalk D z = Ideal.span (Set.range g)) ∧
        ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk (D ⊔ W) z) = 0 ∧
        ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) = 1) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    (cycleAssociatedToClosedSubscheme C f (W ⊔ D).subschemeι k).1 =
      intersectionProductCycle C f hY (subschemeStructureSheaf W) (subschemeStructureSheaf D)
        (isCoherent_subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf D) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C f hY W D k hWD) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hWD' : schemeDeltaDimension C
      ((reducedSupport (subschemeStructureSheaf (W ⊔ D))).subschemeι ≫ f) ≤ WithBotTop.coe k :=
    schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C f (W ⊔ D).subschemeι hWD
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C f
    (W ⊔ D).subschemeι k hWD]
  exact subschemeCycle_sup_eq_intersectionProductCycle_of_mem_support C f hY W D k d hd hWD'
    (schemeDeltaDimension_reducedSupport_torSheaf_le C f hY W D k hWD) hpt

/-- The Tor-formula intersection product of `W` and `D` is a `k`-cycle. Nothing beyond the
delta-dimension bound `hWD` on the scheme-theoretic intersection is needed: every summand of the
alternating sum is a `k`-cycle and the `k`-cycles form a subgroup, which is
`AlgebraicGeometry.TorFormula.intersectionProductCycle_mem_cyclesOfDimension` read in the
sheaf-of-ideals idiom. In particular no bound on the dimension of `Y` is assumed. -/
theorem intersectionProductCycle_mem_cyclesOfDimension (f : Y ⟶ C.S)
    [LocallyOfFiniteType f] (hY : IsRegular Y) (W D : Y.IdealSheafData) (k : ℤ)
    (hWD : schemeDeltaDimension C ((W ⊔ D).subschemeι ≫ f) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    intersectionProductCycle C f hY (subschemeStructureSheaf W) (subschemeStructureSheaf D)
        (isCoherent_subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf D) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C f hY W D k hWD) ∈
      cyclesOfDimension C f k :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  AlgebraicGeometry.TorFormula.intersectionProductCycle_mem_cyclesOfDimension C f hY
    (subschemeStructureSheaf W) (subschemeStructureSheaf D)
    (isCoherent_subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf D) k
    (schemeDeltaDimension_reducedSupport_torSheaf_le C f hY W D k hWD)

/-- **Stacks 0B07, part (1)(a), as an identity of cycles.** Let `W ⊆ Y` be a closed subvariety
of delta-dimension `k + 1` and let `D ⊆ Y` be an effective Cartier divisor meeting it properly,
in the sense that the scheme-theoretic intersection `W ∩ D` has delta-dimension at most `k`.
Then the cycle `[W ∩ D]_k` is the Section 43.14 intersection product of `W` and `D`.

Nothing pointwise is assumed: the local conditions of the clause are read off `hDim`, `hD` and
`hWD` by `Stacks.Chow.localConditions_of_isEffectiveCartierDivisor`. -/
theorem cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle_of_isIntegral
    (f : Y ⟶ C.S) [LocallyOfFiniteType f] (hY : IsRegular Y) (W D : Y.IdealSheafData)
    [IsIntegral W.subscheme] (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (W.subschemeι ≫ f) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ D).subschemeι ≫ f) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    (cycleAssociatedToClosedSubscheme C f (W ⊔ D).subschemeι k).1 =
      intersectionProductCycle C f hY (subschemeStructureSheaf W) (subschemeStructureSheaf D)
        (isCoherent_subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf D) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C f hY W D k hWD) :=
  cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C f hY W D k d hd hWD
    (localConditions_of_isEffectiveCartierDivisor C f W D inferInstance hD hDim hWD)

/-! ### Part (1)(b) -/

section PartOneB

variable (W : (projectiveLineProduct p).IdealSheafData) (k : ℤ) (d : ℕ)

/-- **Stacks 0B07, part (1)(b), for the zero section.** The cycle `[W_a]_k` of the fibre of `W`
over the section, viewed as a closed subscheme of `X`, is the proper pushforward along
`pr : X ×_S ℙ¹_S ⟶ X` of the Section 43.14 intersection product `W · (X × a)`.

Nothing pointwise is assumed: `W` is a closed subvariety of delta-dimension `k + 1` meeting the
image of the section properly, and `Stacks.Chow.localConditions_ker_zeroSection` derives the
local conditions of part (1)(a) from that. -/
theorem properPushforward_intersectionProductCycle_eq_zeroFiberCycle
    [IsIntegral W.subscheme] (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (zeroSection p).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (zeroSection p).ker k
            hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (zeroFiber p W).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have : IsReduced W.subscheme := inferInstance
  have hbundle : (⟨_, intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (zeroSection p).ker k hWD⟩ :
      CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
      cycleAssociatedToClosedSubscheme C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (zeroSection p).ker).subschemeι k :=
    Subtype.ext (cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (zeroSection p).ker k d hd
      hWD (localConditions_ker_zeroSection C p W hDim hWD)).symm
  rw [hbundle]
  exact properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_zeroSection C p W k

/-- **Stacks 0B07, part (1)(b), for the infinity section.** Nothing pointwise is assumed; see
`Stacks.Chow.properPushforward_intersectionProductCycle_eq_zeroFiberCycle`. -/
theorem properPushforward_intersectionProductCycle_eq_infinityFiberCycle
    [IsIntegral W.subscheme] (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (infinitySection p).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (infinitySection p).ker k
            hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (infinityFiber p W).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have : IsReduced W.subscheme := inferInstance
  have hbundle : (⟨_, intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (infinitySection p).ker k hWD⟩ :
      CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
      cycleAssociatedToClosedSubscheme C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (infinitySection p).ker).subschemeι k :=
    Subtype.ext (cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (infinitySection p).ker k d hd
      hWD (localConditions_ker_infinitySection C p W hDim hWD)).symm
  rw [hbundle]
  exact properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_infinitySection C p W k

end PartOneB

/-! ### Part (2) for a prime cycle -/

section PartTwoPrime

variable (W : (projectiveLineProduct p).IdealSheafData) (k : ℤ) (d : ℕ)

/-- **Stacks 0B07 part (2) for a prime cycle.** Let `W ⊆ X ×_S ℙ¹_S` be a closed subvariety of
delta-dimension `k + 1` meeting the images of both distinguished sections properly. Then
`pr_{X,*}(W · X × 0 - W · X × ∞)` is rationally equivalent to zero: by part (1)(b) it is the
difference `[W₀]_k - [W_∞]_k` of the two fibre cycles, which is a basic rational equivalence in
the sense of Tag 0AZG. -/
theorem sub_properPushforward_intersectionProductCycle_mem_rationalEquivalencesByFibres
    [IsIntegral W.subscheme] (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (hWD₀ : schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWDinf : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (zeroSection p).ker k hWD₀),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (zeroSection p).ker k
            hWD₀⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (infinitySection p).ker k
            hWDinf⟩ ∈
      rationalEquivalencesByFibres C p k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  rw [properPushforward_intersectionProductCycle_eq_zeroFiberCycle C p W k d hY hd hDim hWD₀,
    properPushforward_intersectionProductCycle_eq_infinityFiberCycle C p W k d hY hd hDim hWDinf]
  exact sub_cycleAssociatedToFibres_mem_rationalEquivalencesByFibres C p k W inferInstance
    hDim h₀ hInf

/-- **Stacks 0B07, part (2) for a prime cycle.** Let `X` be a variety over an algebraically
closed field whose projective line family is regular, and let `W ⊆ X ×_S ℙ¹_S` be a closed
subvariety of delta-dimension `k + 1` meeting the images of both distinguished sections
properly. Then `pr_{X,*}(W · X × 0 - W · X × ∞)` is rationally equivalent to zero: by part
(1)(b) it is the difference `[W₀]_k - [W_∞]_k` of the two fibre cycles, which is a basic
rational equivalence, and by Tag 0AZI those generate the cycles rationally equivalent to
zero. -/
theorem sub_properPushforward_intersectionProductCycle_mem_rationalEquivalences
    (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
    [IsIntegral W.subscheme] (hY : IsRegular (projectiveLineProduct p))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (hWD₀ : schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWDinf : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (zeroSection p).ker k hWD₀),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (zeroSection p).ker k
            hWD₀⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (infinitySection p).ker k
            hWDinf⟩ ∈
      rationalEquivalences C p k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  rw [rationalEquivalences_eq_rationalEquivalencesByFibres Kf C hC p k]
  exact sub_properPushforward_intersectionProductCycle_mem_rationalEquivalencesByFibres C p W k d
    hY hd hDim h₀ hInf hWD₀ hWDinf

end PartTwoPrime

/-! ### The delta-dimension of `closure {x}` -/

section IntegralComponentDimension

variable (x : projectiveLineProduct p)

/-- The delta-dimension hypothesis of Tag 0AZG for `closure {x}`, read off the relative
dimension of `x`: the only generic point of an irreducible component of `closure {x}` is `x`
itself. -/
theorem relativeDimension_familyBase_integralComponentAt_genericPoints {k : ℤ}
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (ξ : genericPoints (integralComponentAt x).subscheme) :
    relativeDimension C.dimensionFunction (familyBase p (integralComponentAt x)) ξ.1 = k + 1 := by
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hmem : ξ.1 ∈ ({genericPoint (integralComponentAt x).subscheme} :
      Set (integralComponentAt x).subscheme) := by
    rw [← genericPoints_eq_singleton]
    exact ξ.2
  have hξ : ξ.1 = genericPoint (integralComponentAt x).subscheme := Set.eq_of_mem_singleton hmem
  rw [hξ, show familyBase p (integralComponentAt x) =
      (integralComponentAt x).subschemeι ≫
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) from rfl,
    relativeDimension_comp_closedImmersion,
    show (integralComponentAt x).subschemeι.base (genericPoint (integralComponentAt x).subscheme) =
      genericPointOf (integralComponentAt x) (isIntegral_integralComponentAt x) from rfl,
    genericPointOf_integralComponentAt]
  exact hx

end IntegralComponentDimension

/-! ### Part (1)(b) with the pointwise hypotheses discharged -/

section PartOneBClean

variable (x : projectiveLineProduct p) (k : ℤ) (d : ℕ)

/-- **Stacks 0B07 part (1)(b) for a closed subvariety, with the pointwise hypotheses of part
(1)(a) discharged.** For `W = closure {x}` the integral closed subscheme of delta-dimension
`k + 1` spanned by a point `x`, meeting the image of the zero section properly — which is the
hypothesis `hWD₀` that `W ∩ (X × 0)` has delta-dimension at most `k` — the fibre cycle
`[W₀]_k` on `X` is the proper pushforward of the Section 43.14 product `W · (X × 0)`.

Nothing pointwise is assumed: the image of the zero section is an effective Cartier divisor, so
`Stacks.Chow.localConditions_integralComponentAt_of_isEffectiveCartierDivisor` supplies the
local conditions of part (1)(a) from `hx` and `hWD₀`. -/
theorem properPushforward_intersectionProductCycle_integralComponentAt_eq_zeroFiberCycle
    (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hWD₀ : schemeDeltaDimension C ((integralComponentAt x ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    haveI : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
    haveI : IsReduced (integralComponentAt x).subscheme := inferInstance
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf (integralComponentAt x))
            (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf (integralComponentAt x))
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
              (zeroSection p).ker k hWD₀),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
            (zeroSection p).ker k hWD₀⟩ =
      cycleAssociatedToClosedSubscheme C p
        (zeroFiber p (integralComponentAt x)).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have : IsReduced (integralComponentAt x).subscheme := inferInstance
  exact properPushforward_intersectionProductCycle_eq_zeroFiberCycle C p (integralComponentAt x)
    k d hY hd (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) hWD₀

/-- **Stacks 0B07 part (1)(b) for a closed subvariety, at the infinity section**, with the
pointwise hypotheses of part (1)(a) discharged. -/
theorem properPushforward_intersectionProductCycle_integralComponentAt_eq_infinityFiberCycle
    (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hWDinf : schemeDeltaDimension C
      ((integralComponentAt x ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    haveI : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
    haveI : IsReduced (integralComponentAt x).subscheme := inferInstance
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf (integralComponentAt x))
            (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf (integralComponentAt x))
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
            (infinitySection p).ker k hWDinf⟩ =
      cycleAssociatedToClosedSubscheme C p
        (infinityFiber p (integralComponentAt x)).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have : IsReduced (integralComponentAt x).subscheme := inferInstance
  exact properPushforward_intersectionProductCycle_eq_infinityFiberCycle C p
    (integralComponentAt x) k d hY hd
    (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) hWDinf

end PartOneBClean

/-! ### Part (2) for a prime cycle, with the pointwise hypotheses discharged -/

section PartTwoClean

variable (x : projectiveLineProduct p) (k : ℤ) (d : ℕ)

/-- **Stacks 0B07, part (2) for a prime cycle, with the pointwise hypotheses of part (1)(a)
discharged.** Let `X` be a variety over an algebraically closed field whose projective line
family is regular, and let `W = closure {x}` be a closed subvariety of `X ×_S ℙ¹_S` of
delta-dimension `k + 1` contained in neither distinguished section and meeting both of them
properly. Then `pr_{X,*}(W · X × 0 - W · X × ∞)` is rationally equivalent to zero. -/
theorem sub_properPushforward_intersectionProductCycle_integralComponentAt_mem_rationalEquivalences
    (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
    (hY : IsRegular (projectiveLineProduct p))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p))
    (hWD₀ : schemeDeltaDimension C ((integralComponentAt x ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWDinf : schemeDeltaDimension C
      ((integralComponentAt x ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    haveI : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf (integralComponentAt x))
            (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf (integralComponentAt x))
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
              (zeroSection p).ker k hWD₀),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
            (zeroSection p).ker k hWD₀⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf (integralComponentAt x))
            (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf (integralComponentAt x))
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
            (infinitySection p).ker k hWDinf⟩ ∈
      rationalEquivalences C p k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  exact sub_properPushforward_intersectionProductCycle_mem_rationalEquivalences C p
    (integralComponentAt x) k Kf hC hY
    (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) h₀ hInf hWD₀ hWDinf

end PartTwoClean

end Stacks.Chow

end
