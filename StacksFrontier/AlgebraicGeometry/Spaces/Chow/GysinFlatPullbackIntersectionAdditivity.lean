module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# The intersection additivity carried by Stacks 0ER6, discharged

In Situation 0EDT let `X/B` and `X'/B` be good, let `f : X' ⟶ X` be flat of relative dimension
`r`, and let `(ℒ, s, i : E → X)` be a triple as in Definition 0ER1, so `ℒ` is invertible on `X`,
`s` is a global section of it and `E = Z(s)` is its vanishing locus.  Remark 0ER3 forms
`ℒ' = f^*ℒ`, `s' = f^*s` and `E' = f^{-1}(E) = Z(s')`.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackPreimage` proves Stacks 0ER6 from two
inputs.  One of them, `hadd`, is the additivity on `X'` of the cycles of Stacks 0EE9 under
intersection with `E'`, applied at the closed subspace `f^{-1}(W)`; the source of Stacks 0ER6
uses it silently in applying the Gysin map of Definition 0ER1, which that definition gives on
prime cycles, to the cycle `f^*[W] = [f^{-1}(W)]_{k+1+r}` of a closed subspace that need not be
integral.  **This file discharges it**, so Stacks 0ER6 carries only the contained branch.

What `hadd` needs beyond Stacks 0EQL on `X'` — which this library has as
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum` — is that
`E' ∩ f^{-1}(W)` be an effective Cartier divisor on `f^{-1}(W)`.  Two things supply it: that
`E ∩ W` is one on the *integral* `W`, which is Stacks 0846 part (4) on an integral space and is
proved here; and the invariance of the effective Cartier property under flat inverse image, which
for algebraic spaces is part (2) of Stacks 083Z — the analogue for spaces of Stacks 02OO (6) —
and is already in this library as
`AlgebraicGeometry.Space.isPullbackDefined_of_isFlat`.  The flat morphism it is applied to is the
projection `f^{-1}(W) ⟶ W` of the cartesian square of Stacks 083Q, which is flat by base change;
note that `f^{-1}(W)` is *not* integral in general, so `E' ∩ f^{-1}(W)` cannot be obtained the
way `E ∩ W` is.

## Main results

* `AlgebraicGeometry.Space.zeroSchemeSubfunctor_zero`: part of Stacks 0846 — the zero scheme of
  the zero section is the whole space.
* `AlgebraicGeometry.Space.closedSubspaceRestrictSection_ne_zero_of_not_le`: a closed subspace
  not contained in `Z(s)` does not kill the section.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_of_not_le`:
  **clause (1)(a) of Stacks 0ER1 is an effective Cartier divisor.**  On an integral closed
  subspace `W ⊆ X` not contained in `E` the intersection `E ∩ W` is an effective Cartier divisor
  on `W`.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_preimage`:
  the same for `E' ∩ f^{-1}(W)` on `f^{-1}(W)`, which is **not** assumed integral; this is
  part (2) of Stacks 083Z along the flat projection of the square of Stacks 083Q.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_gysinPreimageIntersection_eq_finsum`:
  **the `hadd` of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackPreimage`,
  proved.**
* `AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq_of_chernComparison`: **Stacks 0ER6
  at the triple `(ℒ, s, i : E → X)` of Definition 0ER1, with `hadd` no longer carried.**  Only
  the contained branch remains, which is Stacks 0EQR read coefficientwise at clause (1)(b) of
  Stacks 0ER1 and is not derivable here: `chernCycle` is a free parameter of
  `AlgebraicGeometry.Space.GysinComponentRule` on each side, so the two are unrelated data.

## Implementation notes

### Why the pulled-back divisor must be presented as a vanishing locus

`AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity_of_isPullback`
states Stacks 0ER6 for an *arbitrary* closed subspace `E' ⊆ X'` completing the square, which is
more general than Remark 0ER3 but gives no handle on `E' ∩ f^{-1}(W)`.  Stacks 0EQL is a
statement about the vanishing locus of a section, so to use it `E'` has to be `Z(s')`; by
`AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus` — Stacks 0ER3 — that is the same
closed subspace as `f^{-1}(E)`, and taking it as `Z(s')` from the start avoids transporting
anything along that equality.  The projection `g : E' ⟶ E` and the cartesian square are
hypotheses, exactly as they are there; they are the content of Remark 0ER3, which is proved.

### The δ-dimension index

Stacks 0EQL is applied on `X'` at `k + r`, so the cycle it weights by is `[f^{-1}(W)]_{k+r+1}`,
while `AlgebraicGeometry.Space.flatPullbackMult` is by construction the coefficient family of
`[f^{-1}(W)]_{dim_δ(W)+r}`.  The two indices agree because `dim_δ(W) = k + 1`, and the
coefficient family of Stacks 0EE9 depends on its index only through the test
`dim_δ(T) = index`, so the identification is the rewrite of one integer.

### The note on Stacks 02OO for spaces is out of date

Nothing of part (6) of Stacks 02OO is re-proved here.  For schemes it is
`Stacks.Divisors.isPullbackDefined_of_flat`, and for algebraic spaces it is part (2) of
Stacks 083Z, `AlgebraicGeometry.Space.isPullbackDefined_of_isFlat` of
`StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierPullbackCriteria.lean`, whose own proof
descends to a surjective étale scheme chart and uses the scheme case there.

## References

* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 083Z](https://stacks.math.columbia.edu/tag/083Z)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The zero scheme of the zero section -/

section ZeroSection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Part of Stacks 0846: the zero scheme of the zero section is the whole space.**  The
evaluation ideal of Stacks 0845 of the zero section is the zero ideal on every chart, and the
defining ideal of the whole of `X` as a closed subspace of itself is the zero ideal too, so the
maximality half of Stacks 0846 puts `X` inside the zero scheme. -/
theorem zeroSchemeSubfunctor_zero (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) :
    zeroSchemeSubfunctor B S hS X L 0 = ⊤ := by
  refine le_antisymm le_top ?_
  have hret : (ObjectProperty.homMk (inv (⊤ : Subfunctor X.1).ι) :
      X ⟶ (⟨(⊤ : Subfunctor X.1).toFunctor, (isClosedSubspace_top B S hS X).1⟩ :
        AlgebraicSpaces B S hS)) ≫ ObjectProperty.homMk (⊤ : Subfunctor X.1).ι = 𝟙 X :=
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)
  refine le_zeroSchemeSubfunctor B S hS X L 0 ⟨⊤, isClosedSubspace_top B S hS X⟩ fun U hU => ?_
  rw [definingIdealAt_eq_bot_of_retraction B S hS X ⟨⊤, isClosedSubspace_top B S hS X⟩ _ hret
    (op U), le_bot_iff, sectionEvaluationIdealAt, Ideal.span_eq_bot]
  rintro - ⟨l, rfl⟩
  exact map_zero l

end ZeroSection

/-! ### Clause (1)(a) of Stacks 0ER1 is an effective Cartier divisor -/

section Restriction

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-- **A closed subspace not contained in the vanishing locus does not kill the section.**  If
`s|_Z = 0` then `E ∩ Z = Z(s|_Z)` is the whole of `Z`, by
`AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme` and
`AlgebraicGeometry.Space.zeroSchemeSubfunctor_zero`, so the inclusion of `Z` lands in `E` and
`Z ⊆ E`. -/
theorem closedSubspaceRestrictSection_ne_zero_of_not_le (hL : IsInvertibleSheaf D p hp L)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)
    (hZE : ¬ Z.1 ≤ (vanishingLocus D p hp L s).1) :
    closedSubspaceRestrictSection D p hp L s Z ≠ 0 := by
  intro h0
  refine hZE ?_
  have htop : (vanishingLocus D p hp L s).1.preimage Z.1.ι = ⊤ := by
    have h : (vanishingLocus D p hp L s).1.preimage Z.1.ι =
        zeroSchemeSubfunctor D.site D.base D.base_mem
          (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
          (closedSubspaceRestrictSheaf D p hp L Z)
          (closedSubspaceRestrictSection D p hp L s Z) :=
      congrArg Subtype.val (interOnClosedSubspace_eq_zeroScheme D p hp L s Z hL)
    rw [h, h0]
    exact zeroSchemeSubfunctor_zero D.site D.base D.base_mem
      (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
      (closedSubspaceRestrictSheaf D p hp L Z)
  have hrange := (Subfunctor.preimage_eq_top_iff (vanishingLocus D p hp L s).1 Z.1.ι).1 htop
  rwa [Subfunctor.range_ι] at hrange

/-- **Clause (1)(a) of Stacks 0ER1 is an effective Cartier divisor.**  For an integral closed
subspace `W ⊆ X` not contained in `E = Z(s)` the intersection `E ∩ W` is an effective Cartier
divisor on `W`.

The restriction `ℒ|_W` is invertible by Stacks 0B8P, `W` is an integral algebraic space, and
`s|_W ≠ 0` by
`AlgebraicGeometry.Space.closedSubspaceRestrictSection_ne_zero_of_not_le`; so `s|_W` is a
regular section by the geometric half of Stacks 0DMZ,
`AlgebraicGeometry.Space.isRegularSection_of_ne_zero`, and part (4) of Stacks 0846 turns that
into the effective Cartier property, through
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection`. -/
theorem isEffectiveCartierDivisor_interOnClosedSubspace_of_not_le
    (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    IsEffectiveCartierDivisor D.site D.base D.base_mem
      (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩
        ⟨W.subspace, W.isClosedSubspace⟩)
      (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩) :=
  (isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection D p hp L s
      ⟨W.subspace, W.isClosedSubspace⟩ hL).2
    (isRegularSection_of_ne_zero D.site D.base D.base_mem
      (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ ⟨W.subspace, W.isClosedSubspace⟩)
      (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
      (isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL)
      W.isIntegralSpace
      (closedSubspaceRestrictSection_ne_zero_of_not_le D p hp L s hL
        ⟨W.subspace, W.isClosedSubspace⟩ hWE))

end Restriction

/-! ### The same downstairs, by part (2) of Stacks 083Z -/

section Pullback

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-- Shorthand for the vanishing locus `Z(s')` of the pulled-back section, the `E'` of Remark
0ER3 presented the way Stacks 0EQL needs it.  By
`AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus` — Stacks 0ER3 — this is the same
closed subspace as `AlgebraicGeometry.Space.pullbackDivisor`, which is the inverse image
`f^{-1}(E)`; the two presentations are not definitionally equal, and this is the one whose
intersections Stacks 0EQL computes. -/
abbrev pullbackSectionVanishingLocus : ClosedSubspaces D.site D.base D.base_mem X' :=
  vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
    (pullbackGlobalSection D p hp p' hp' f L s)

/-- **`E' ∩ f^{-1}(W)` is an effective Cartier divisor on `f^{-1}(W)`.**  This is what Stacks
0EQL on `X'` needs at the closed subspace `f^{-1}(W)`, for `f` flat and `W` an integral closed
subspace of `X` not contained in `E = Z(s)`.

`f^{-1}(W)` is **not** assumed integral — it need not be, which is why the argument that gives
`E ∩ W` upstairs,
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_of_not_le`, has no
analogue downstairs.  What carries it down is part (2) of Stacks 083Z,
`AlgebraicGeometry.Space.isPullbackDefined_of_isFlat` — the analogue for algebraic spaces of
part (6) of Stacks 02OO — applied to the projection `f^{-1}(W) ⟶ W` of the cartesian square of
Stacks 083Q, which is flat by base change.

The two readings of the resulting closed subspace are matched by
`AlgebraicGeometry.Space.preimage_preimage_of_comm` for the commuting square, and by
`AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus` — Stacks 0ER3 — which identifies
`f^{-1}(E)` with `Z(s')`. -/
theorem isEffectiveCartierDivisor_interOnClosedSubspace_preimage
    (hflat : IsFlat D.site D.base D.base_mem f.hom) (hL : IsInvertibleSheaf D p hp L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    IsEffectiveCartierDivisor D.site D.base D.base_mem
      (closedSubspaceToSpace D.site D.base D.base_mem ⟨X', hp'.1⟩
        ⟨W.subspace.preimage f.hom,
          isClosedSubspace_preimage D.site D.base D.base_mem f.hom W.subspace hp.1 hp'.1
            W.isClosedSubspace⟩)
      (interOnClosedSubspace D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)
        ⟨W.subspace.preimage f.hom,
          isClosedSubspace_preimage D.site D.base D.base_mem f.hom W.subspace hp.1 hp'.1
            W.isClosedSubspace⟩) := by
  have hsq : IsPullback (W.subspace.fromPreimage f.hom) (W.subspace.preimage f.hom).ι
      W.subspace.ι f.hom :=
    Subfunctor.isPullback_preimage f.hom W.subspace
  -- the projection `f^{-1}(W) ⟶ W` of the square of Stacks 083Q, as a morphism of spaces
  have hpull := isPullbackDefined_of_isFlat D.site D.base D.base_mem
    (X := closedSubspaceToSpace D.site D.base D.base_mem ⟨X', hp'.1⟩
      ⟨W.subspace.preimage f.hom,
        isClosedSubspace_preimage D.site D.base D.base_mem f.hom W.subspace hp.1 hp'.1
          W.isClosedSubspace⟩)
    (Y := closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩
      ⟨W.subspace, W.isClosedSubspace⟩)
    (ObjectProperty.homMk (W.subspace.fromPreimage f.hom))
    (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)
    (isEffectiveCartierDivisor_interOnClosedSubspace_of_not_le D p hp L s hL W hWE)
    (isFlat_of_isPullback_of_isAlgebraicSpace D.site D.base D.base_mem hsq hp'.1 hp.1 hflat)
  -- the two readings of `E' ∩ f^{-1}(W)` agree
  refine (show interOnClosedSubspace D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s)
      ⟨W.subspace.preimage f.hom,
        isClosedSubspace_preimage D.site D.base D.base_mem f.hom W.subspace hp.1 hp'.1
          W.isClosedSubspace⟩ = _ from Subtype.ext ?_) ▸ hpull
  have hE' : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s)).1 =
      (vanishingLocus D p hp L s).1.preimage f.hom :=
    congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D p hp p' hp' f L s hL).symm
  rw [show (interOnClosedSubspace D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)
        ⟨W.subspace.preimage f.hom, isClosedSubspace_preimage D.site D.base D.base_mem f.hom
          W.subspace hp.1 hp'.1 W.isClosedSubspace⟩).1 =
      (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
        (pullbackGlobalSection D p hp p' hp' f L s)).1.preimage
          (W.subspace.preimage f.hom).ι from rfl, hE']
  exact (preimage_preimage_of_comm hsq.w (vanishingLocus D p hp L s).1).symm

/-! ### The intersection additivity on `X'`, proved -/

/-- **The `hadd` that `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackPreimage`
carries, proved.**  In Situation 0EDT let `f : X' ⟶ X` be flat of relative dimension `r` between
good algebraic spaces over `B`, let `(ℒ, s)` be as in Definition 0ER1 with `E = Z(s)`, and let
`W ⊆ X` be an integral closed subspace of δ-dimension `k + 1` not contained in `E`.  Then the
multiplicity of an integral closed subspace `T' ⊆ E' = Z(s')` in `E' ∩ f^{-1}(W)` is the sum,
over the integral closed subspaces `W' ⊆ X'`, of their multiplicities in `f^*[W]` times the
component cycle of clause (1) of Stacks 0ER1 at `W'`.

This is Lemma 0EQL on `X'` for the triple `(f^{-1}(W), ℒ'|_{f^{-1}(W)}, s'|_{f^{-1}(W)})`,
transported into `X'`, which is
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum`.  Its two
hypotheses are supplied here: the δ-dimension bound `dim_δ(f^{-1}(W)) ≤ k + r + 1` is part (1)
of Stacks 0EPB, and the effective Cartier condition on `E' ∩ f^{-1}(W)` is
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_preimage`.  The weights
match because `AlgebraicGeometry.Space.flatPullbackMult` is by construction the coefficient
family of `[f^{-1}(W)]_{dim_δ(W)+r}` and `dim_δ(W) = k + 1`. -/
theorem cycleCoeffOfClosedSubspace_gysinPreimageIntersection_eq_finsum
    (hfbase : f.hom ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)
    (chern' : FirstChernComponentCycleRule D p' (k + (r : ℤ)))
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem
      (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.toFunctor) :
    cycleCoeffOfClosedSubspace D
        ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s))
        (gysinPreimageIntersectionSubspace D p hp p' hp' f.hom
          (pullbackSectionVanishingLocus D p hp p' hp' f L s)
          (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s)) W).1
        (gysinPreimageIntersectionSubspace D p hp p' hp' f.hom
          (pullbackSectionVanishingLocus D p hp p' hp' f L s)
          (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s)) W).2 (k + (r : ℤ))
        (canonicalGeometricPoint D.site D.base D.base_mem
          (gysinPreimageIntersectionSubspace D p hp p' hp' f.hom
            (pullbackSectionVanishingLocus D p hp p' hp' f L s)
            (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
              (pullbackGlobalSection D p hp p' hp' f L s)) W).1.toFunctor) T' =
      ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W W' *
          (gysinComponentCycle D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
            (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
              (pullbackGlobalSection D p hp p' hp' f L s)) (k + (r : ℤ))
            (canonicalGysinComponentRule D p' hp'
              (pullbackSectionVanishingLocus D p hp p' hp' f L s)
              (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
                (pullbackGlobalSection D p hp p' hp' f L s)) (k + (r : ℤ)) chern') W').1 T' := by
  have hcl : IsClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f.hom) :=
    isClosedSubspace_preimage D.site D.base D.base_mem f.hom W.subspace hp.1 hp'.1
      W.isClosedSubspace
  have hdeg : k + (r : ℤ) + 1 = deltaDimension D p W + (r : ℤ) := by omega
  have hZdim : deltaDimensionSubspace D p' hp' (W.subspace.preimage f.hom) hcl ≤
      ((k + (r : ℤ) + 1 : ℤ) : EInt) := by
    rw [hdeg]
    exact deltaDimensionSubspace_preimage_integralClosedSubspace_le D p' hp' p hp f.hom hfbase r
      hflat hr W
  have hmult : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
      (closedSubspaceCycle D p' hp' (W.subspace.preimage f.hom) hcl (k + (r : ℤ) + 1)
          hZdim).1 W' =
        flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W W' := by
    intro W'
    rw [closedSubspaceCycle_coe]
    show cycleCoeffOfClosedSubspace D p' hp' (W.subspace.preimage f.hom) hcl (k + (r : ℤ) + 1)
        (canonicalGeometricPoint D.site D.base D.base_mem
          (W.subspace.preimage f.hom).toFunctor) W' =
      (closedSubspaceCycle D p' hp' (W.subspace.preimage f.hom) _
        (deltaDimension D p W + (r : ℤ)) _).1 W'
    rw [closedSubspaceCycle_coe, hdeg]
  exact (cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum D p' hp'
    (pullbackSheaf D p hp p' hp' f L) (pullbackGlobalSection D p hp p' hp' f L s)
    (k + (r : ℤ)) ⟨W.subspace.preimage f.hom, hcl⟩
    (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL)
    (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s))
    chern' hZdim
    (isEffectiveCartierDivisor_interOnClosedSubspace_preimage D p hp p' hp' f L s hflat hL W hWE)
    T').trans (finsum_congr fun W' => by rw [hmult W'])

/-! ### Stacks 0ER6 with only the contained branch carried -/

/-- **Stacks 0ER6 at the triple `(ℒ, s, i : E → X)` of Definition 0ER1, with the intersection
additivity no longer carried.**  In Situation 0EDT let `f : X' ⟶ X` be a flat morphism of
relative dimension `r` of good algebraic spaces over `B` — so locally of finite type, by
Definition 06LR — let `ℒ` be invertible on `X` with a global section `s` and vanishing locus
`E = Z(s)`, and form the cartesian square of Remark 0ER3 with `E' = Z(s')` for `s' = f^*s`,
`g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every `(k+1)`-cycle `α` on `X`

  `(i')^* f^* α = g^* i^* α`,

an identity of `(k+r)`-cycles on `E'`, hence of classes in `CH_{k+r}(E')`.

This is
`AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity_of_isPullback`
with `E'` presented as `Z(s')` and its `hadd` discharged by
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_gysinPreimageIntersection_eq_finsum`.
Everything the square gives is still derived rather than carried: that `g` is a morphism over
`B`, that it is flat, and that it has relative dimension `r`.

**One input is carried**, `hchern`: the contained branch `W ⊆ E`, which is Stacks 0EQR read
coefficientwise at clause (1)(b) of Stacks 0ER1.  It is not derivable in this library and is not
hidden: clause (1)(b) is the free parameter
`AlgebraicGeometry.Space.GysinComponentRule.chernCycle`, which
`AlgebraicGeometry.Space.canonicalGysinComponentRule` passes along unchanged, so `chern` on `X`
and `chern'` on `X'` are unrelated data and nothing relates the two cap products.  Stacks 0EQR
is itself conditional here; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackPreimage`. -/
theorem gysinCycleMap_flatPullbackMap_eq_of_chernComparison
    (hfbase : f.hom ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hft : IsLocallyOfFiniteType D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' (k + (r : ℤ)))
    (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    {g : (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.toFunctor ⟶
      (vanishingLocus D p hp L s).1.toFunctor}
    (hsq : IsPullback g (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι
      (vanishingLocus D p hp L s).1.ι f.hom)
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → W.subspace ≤ (vanishingLocus D p hp L s).1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem
        (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.toFunctor,
        (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f.hom hfbase r hflat hr W W' *
              (gysinComponentCycle D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
                (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
                  (pullbackGlobalSection D p hp p' hp' f L s)) (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp'
                  (pullbackSectionVanishingLocus D p hp p' hp' f L s)
                  (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
                    (pullbackGlobalSection D p hp p' hp' f L s)) (k + (r : ℤ)) chern')
                W').1 T') =
          ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem
              (vanishingLocus D p hp L s).1.toFunctor,
            (gysinComponentCycle D p (vanishingLocus D p hp L s)
                (isGood_vanishingLocus D p hp L s) k
                (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
                  (isGood_vanishingLocus D p hp L s) k chern) W).1 T *
              flatPullbackMult D
                ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
                (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
                  (pullbackGlobalSection D p hp p' hp' f L s))
                ((vanishingLocus D p hp L s).1.ι ≫ p) (isGood_vanishingLocus D p hp L s) g
                (comp_structure_of_isPullback D p p' hfbase hsq) r
                (isFlat_gysinBaseChange D p hp p' hp' hsq hflat)
                (hasRelativeDimension_gysinBaseChange D p hp p' hp'
                  (isGood_vanishingLocus D p hp L s) r hsq hft hr) T T')
    (α : CycleGroup D p (k + 1)) :
    gysinCycleMap D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
        (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)) (k + (r : ℤ))
        (canonicalGysinComponentRule D p' hp'
          (pullbackSectionVanishingLocus D p hp p' hp' f L s)
          (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s)) (k + (r : ℤ)) chern')
        (flatPullbackMap D p' hp' p hp f.hom hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
          hkr α) =
      flatPullbackMap D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s))
        ((vanishingLocus D p hp L s).1.ι ≫ p) (isGood_vanishingLocus D p hp L s) g
        (comp_structure_of_isPullback D p p' hfbase hsq) r
        (isFlat_gysinBaseChange D p hp p' hp' hsq hflat)
        (hasRelativeDimension_gysinBaseChange D p hp p' hp'
          (isGood_vanishingLocus D p hp L s) r hsq hft hr) k (k + (r : ℤ)) rfl
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
            (isGood_vanishingLocus D p hp L s) k chern) α) :=
  gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity_of_isPullback D p hp p' hp'
    hfbase r hflat hft hr (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
    (pullbackSectionVanishingLocus D p hp p' hp' f L s)
    (isGood_vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s))
    hsq k chern chern' hkr
    (fun W hW hWE T' => cycleCoeffOfClosedSubspace_gysinPreimageIntersection_eq_finsum
      D p hp p' hp' f L s hfbase r hflat hr hL k chern' W hW hWE T')
    hchern α

end Pullback

end AlgebraicGeometry.Space

end
