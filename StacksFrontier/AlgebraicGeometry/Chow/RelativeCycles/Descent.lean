module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SeparableMultiplicityOne

/-!
# Descent of families of cycles on fibres

The ingredients for part (2) of [Stacks, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X):
a family `α'` of `r`-cycles on the fibres of `X' / S'`, where `X' = X ×_S S'`, whose two
pullbacks to the double overlap `S' ×_S S'` agree descends uniquely along a `g : S' ⟶ S` every
point of whose target has a preimage with separable residue field extension.

This file carries the construction of the descended family and the elementary argument that
makes it work; the comparison of the two pullbacks on the double overlap is in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeComposition` and the
multiplicity-one statement at a separable point in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SeparableMultiplicityOne`.

## Main definitions

* `Stacks.Chow.chosenLiftCoeff` and `Stacks.Chow.cycleFromChosenLifts` — the cycle on `Y`
  obtained from a cycle on `Y'` by choosing, at each point of relative dimension `r`, a lift of
  that relative dimension and reading the coefficient there.

## Main results

* `Stacks.Chow.existsUnique_weightedDescent` — the set-theoretic skeleton of part (2): a weighted
  descent problem with a weight-one lift over every point and a multiplicativity relation across
  the overlap has a unique solution.
* `Stacks.Chow.locallyFiniteSupport_of_support_control` — the local finiteness the descended
  cycle inherits from the cycle upstairs, which is the "small detail omitted" of the source.
* `Stacks.Chow.closedSubschemeCycleCoeff_comap_eq_one_of_geometricallyReduced` — the source's
  `m(x', g) = 1`, in the form the descent uses.
* `Stacks.Chow.exists_fieldCycle_matching_lifts` and
  `Stacks.Chow.exists_fiberCycle_matching_lifts` — the descended cycle on a fibre, and the lifts
  witnessing that the base change of any family carrying it agrees with `α'`.

## Implementation notes

Local finiteness of the descended cycle is the only place where the geometry of the morphism is
used rather than its points: a point of `Y` has a compact open neighbourhood, its inverse image
under the quasi-compact morphism of fibres is compact, and a cycle has finite support on a
compact set. The morphism of fibres is quasi-compact because it is a base change of a morphism
of affine schemes.

The comparison between a family on the fibres of `X / S` and one on the fibres of a base change
is made through `Stacks.Chow.familyCoeff`, the coefficients read as a function on `X`; this is
what removes the transport along `g t = s`, which otherwise appears because the fibres of `f`
over `s` and over `g t` are equal types only propositionally. The one place where that equation
still has to be used is `Stacks.Chow.exists_fiberCycle_matching_lifts`, and there it is
discharged by `subst` on the chosen separable preimage rather than by transporting a cycle.

## References

* [Stacks Project, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Tag 0H4W](https://stacks.math.columbia.edu/tag/0H4W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The weighted descent problem, as an identity of functions -/

/-- **The elementary argument of the proof of Stacks Project, Tag 0H4X (2).** Let `p : B → A` be
a map of sets equipped with a weight `m : B → R` in a domain, and let `p₁, p₂ : D → B` be a pair
of maps which realizes every coincidence `p y₁ = p y₂` and carries weights `m₁, m₂` satisfying
the multiplicativity `m (p₁ z) m₁ z = m (p₂ z) m₂ z`. If every point of `A` has a lift of weight
one, and `m₁` never vanishes, then a function `b` on `B` satisfying the same multiplicativity is
the weighted pullback of a unique function on `A`.

This is the set-theoretic skeleton of part (2): `p` is the map of points of `X' / S'` to points
of `X / S`, `m` is the base change multiplicity, `p₁` and `p₂` are the two projections of the
double overlap, the lift of weight one is the separable point, and the multiplicativity of the
weights is `Stacks.Chow.flatPullbackWeight_mul_comp`. -/
theorem existsUnique_weightedDescent {A B D R : Type*} [CommRing R] [IsDomain R]
    (p : B → A) (p₁ p₂ : D → B) (m : B → R) (m₁ m₂ : D → R)
    (hunit : ∀ x, ∃ y, p y = x ∧ m y = 1)
    (hcommon : ∀ y₁ y₂, p y₁ = p y₂ → ∃ z, p₁ z = y₁ ∧ p₂ z = y₂)
    (hne : ∀ z, m₁ z ≠ 0) (hm : ∀ z, m (p₁ z) * m₁ z = m (p₂ z) * m₂ z)
    (b : B → R) (hb : ∀ z, b (p₁ z) * m₁ z = b (p₂ z) * m₂ z) :
    ∃! a : A → R, ∀ y, a (p y) * m y = b y := by
  classical
  choose σ hσ hσm using hunit
  refine ⟨fun x ↦ b (σ x), fun y ↦ ?_, ?_⟩
  · obtain ⟨z, hz₁, hz₂⟩ := hcommon y (σ (p y)) (hσ (p y)).symm
    have hmz := hm z
    have hbz := hb z
    rw [hz₁, hz₂, hσm, one_mul] at hmz
    rw [hz₁, hz₂] at hbz
    refine mul_right_cancel₀ (hne z) ?_
    rw [mul_assoc, hmz, hbz]
  · intro a ha
    funext x
    simpa only [hσ, hσm, mul_one] using ha (σ x)

/-! ### A cycle built from chosen lifts -/

/-- A coefficient function on `Y` whose support is controlled, along a quasi-compact morphism,
by that of a cycle on `Y'` has locally finite support: a point of `Y` has a compact open
neighbourhood, its inverse image is compact, so only finitely many points of the support of the
cycle lie over the neighbourhood. -/
theorem locallyFiniteSupport_of_support_control {Y Y' : Scheme.{u}} (m : Y' ⟶ Y)
    [QuasiCompact m] (c : AlgebraicCycle Y' ℤ) (d : Y → ℤ)
    (h : ∀ y : Y, d y ≠ 0 → ∃ y' : Y', m y' = y ∧ c y' ≠ 0) :
    LocallyFiniteSupport d := by
  classical
  intro y
  obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  refine ⟨U, IsOpen.mem_nhds hU.1.1 hU.2.1, ?_⟩
  have hfinite : (m ⁻¹' U ∩ Function.support c).Finite :=
    (Function.locallyFinsupp.locallyFiniteSupport c).finite_inter_support_of_isCompact
      (QuasiCompact.isCompact_preimage (f := m) U hU.1.1 hU.1.2)
  refine (hfinite.image m).subset ?_
  intro z hz
  obtain ⟨z', hz', hc'⟩ := h z hz.2
  exact ⟨z', ⟨by rw [Set.mem_preimage, hz']; exact hz.1, hc'⟩, hz'⟩

section ChosenLifts

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
  (C' : ChowSituation.{u}) {Y' : Scheme.{u}} (q' : Y' ⟶ C'.S) [LocallyOfFiniteType q']
  (m : Y' ⟶ Y) (r : ℤ) (c' : CycleGroup C' q' r)
  (hLift : ∀ y : Y, relativeDimension C.dimensionFunction q y = r →
    ∃ y' : Y', m y' = y ∧ relativeDimension C'.dimensionFunction q' y' = r)

/-- The coefficient at `y` of the cycle built from chosen lifts: at a point of relative
dimension `r` the coefficient of the cycle upstairs at a chosen lift of the same relative
dimension, and zero elsewhere. -/
def chosenLiftCoeff (y : Y) : ℤ :=
  open Classical in
  if hy : relativeDimension C.dimensionFunction q y = r then
    (c' : AlgebraicCycle Y' ℤ) (Classical.choose (hLift y hy))
  else 0

omit [LocallyOfFiniteType q] in
/-- Off relative dimension `r` the coefficient built from chosen lifts vanishes. -/
theorem chosenLiftCoeff_eq_zero_of_relativeDimension_ne (y : Y)
    (hy : relativeDimension C.dimensionFunction q y ≠ r) :
    chosenLiftCoeff C q C' q' m r c' hLift y = 0 :=
  dite_eq_right hy

omit [LocallyOfFiniteType q] in
/-- At relative dimension `r` the coefficient built from chosen lifts is the coefficient of the
cycle upstairs at the chosen lift. -/
theorem chosenLiftCoeff_of_relativeDimension_eq (y : Y)
    (hy : relativeDimension C.dimensionFunction q y = r) :
    chosenLiftCoeff C q C' q' m r c' hLift y =
      (c' : AlgebraicCycle Y' ℤ) (Classical.choose (hLift y hy)) :=
  dite_eq_left hy

omit [LocallyOfFiniteType q] [LocallyOfFiniteType q'] in
/-- The chosen lift of a point of relative dimension `r` lies over it and has relative
dimension `r`. -/
theorem chosenLift_spec (y : Y) (hy : relativeDimension C.dimensionFunction q y = r) :
    m (Classical.choose (hLift y hy)) = y ∧
      relativeDimension C'.dimensionFunction q' (Classical.choose (hLift y hy)) = r :=
  Classical.choose_spec (hLift y hy)

omit [LocallyOfFiniteType q] in
/-- A point carrying a nonzero coefficient built from chosen lifts has a lift carrying a nonzero
coefficient of the cycle upstairs. -/
theorem exists_lift_of_chosenLiftCoeff_ne_zero (y : Y)
    (hy : chosenLiftCoeff C q C' q' m r c' hLift y ≠ 0) :
    ∃ y' : Y', m y' = y ∧ (c' : AlgebraicCycle Y' ℤ) y' ≠ 0 := by
  by_cases hdim : relativeDimension C.dimensionFunction q y = r
  · rw [chosenLiftCoeff_of_relativeDimension_eq C q C' q' m r c' hLift y hdim] at hy
    exact ⟨Classical.choose (hLift y hdim),
      (chosenLift_spec C q C' q' m r hLift y hdim).1, hy⟩
  · exact absurd (chosenLiftCoeff_eq_zero_of_relativeDimension_ne C q C' q' m r c' hLift y hdim)
      hy

/-- The cycle on `Y` built from chosen lifts of the points of relative dimension `r`. -/
def cycleFromChosenLifts [QuasiCompact m] : CycleGroup C q r :=
  ⟨⟨chosenLiftCoeff C q C' q' m r c' hLift, fun _ _ ↦ trivial, fun y _ ↦
      locallyFiniteSupport_of_support_control m (c' : AlgebraicCycle Y' ℤ)
        (chosenLiftCoeff C q C' q' m r c' hLift)
        (exists_lift_of_chosenLiftCoeff_ne_zero C q C' q' m r c' hLift) y⟩,
    (mem_cyclesOfDimension_iff_forall_point C q r _).2 fun y hy ↦ by
      by_contra hne
      exact hy (chosenLiftCoeff_eq_zero_of_relativeDimension_ne C q C' q' m r c' hLift y hne)⟩

/-- The coefficients of `Stacks.Chow.cycleFromChosenLifts`. -/
theorem cycleFromChosenLifts_apply [QuasiCompact m] (y : Y) :
    (cycleFromChosenLifts C q C' q' m r c' hLift : AlgebraicCycle Y ℤ) y =
      chosenLiftCoeff C q C' q' m r c' hLift y :=
  rfl

end ChosenLifts

/-! ### Matching lifts over a geometrically reduced base change -/

/-- In a cartesian square of schemes over fields, a point `y` of relative dimension `r` whose
image has the same residue transcendence degree enters the base change of the reduced closure of
that image with nonzero multiplicity. -/
private theorem closedSubschemeCycleCoeff_comap_ne_zero {k K : Type u} [Field k] [Field K]
    {Y Y' : Scheme.{u}} (q : Y ⟶ Spec (.of k)) (q' : Y' ⟶ Spec (.of K))
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (m : Y' ⟶ Y)
    (φ : Spec (.of K) ⟶ Spec (.of k)) (hPB : IsPullback m q' q φ) (r : ℕ) (y : Y')
    (hx : residueTrdeg q (m y) = r) (hy : residueTrdeg q' y = r) :
    closedSubschemeCycleCoeff (fieldChowSituation K) q'
        (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({m y} : Set Y))).comap m).subschemeι) (r : ℤ) y ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := pullbackPoint_generic_in_pointClosure q q' m φ hPB (m y) y rfl
    (hx.trans hy.symm)
  have hne := closedSubschemeCycleCoeff_ne_zero_of_genericPoint (fieldChowSituation K) q'
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({m y} : Set Y))).comap m).subschemeι) (r : ℤ) ξ
    (by rw [hξ]; exact relativeDimension_eq_of_trdeg q' r y hy)
  rwa [hξ] at hne

/-- **The step "`m(x', g) = 1` because `Z_{s'}` is reduced in this case" of the proof of Stacks
Project, Tag 0H4X (2), in the form the descent uses.** In a cartesian square of schemes over a
field whose lower edge is geometrically reduced, a point of relative dimension `r` whose image
also has relative dimension `r` enters the base change of the reduced closure of that image with
multiplicity one. -/
theorem closedSubschemeCycleCoeff_comap_eq_one_of_geometricallyReduced {k K : Type u} [Field k]
    [Field K] {Y Y' : Scheme.{u}} (q : Y ⟶ Spec (.of k)) (q' : Y' ⟶ Spec (.of K))
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (m : Y' ⟶ Y)
    (φ : Spec (.of K) ⟶ Spec (.of k)) (hPB : IsPullback m q' q φ)
    (hφ : GeometricallyReduced φ) (r : ℕ) (y : Y')
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction q (m y) = (r : ℤ))
    (hy : relativeDimension (fieldChowSituation K).dimensionFunction q' y = (r : ℤ)) :
    closedSubschemeCycleCoeff (fieldChowSituation K) q'
        (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({m y} : Set Y))).comap m).subschemeι) (r : ℤ) y = 1 := by
  have := isReduced_comap_of_isPullback_of_geometricallyReduced hPB hφ
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({m y} : Set Y)))
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _)
  have hne := closedSubschemeCycleCoeff_comap_ne_zero q q' m φ hPB r y
    (trdeg_eq_of_relativeDimension q inferInstance r (m y) hx)
    (trdeg_eq_of_relativeDimension q' inferInstance r y hy)
  exact closedSubschemeCycleCoeff_eq_one_of_isReduced (fieldChowSituation K) q' _ (r : ℤ) y hne

/-- **The construction of the descended cycle on a fibre, Stacks Project, Tag 0H4X (2).** In a
cartesian square of schemes over a field whose lower edge is surjective and geometrically
reduced, every `r`-cycle upstairs is matched by an `r`-cycle downstairs: every point of `Y` has a
lift of the same residue transcendence degree at which the base change formula for the cycle
downstairs returns the coefficient of the cycle upstairs.

At a point of relative dimension `r` the lift is one of the same relative dimension, which exists
by Tag 0H4W part (1), and there the multiplicity is one by geometric reducedness, so the matching
coefficient is the coefficient upstairs. Off relative dimension `r` both coefficients vanish, the
lift being chosen of the same residue transcendence degree as the point. -/
theorem exists_fieldCycle_matching_lifts {k K : Type u} [Field k] [Field K]
    {Y Y' : Scheme.{u}} (q : Y ⟶ Spec (.of k)) (q' : Y' ⟶ Spec (.of K))
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (m : Y' ⟶ Y)
    (φ : Spec (.of K) ⟶ Spec (.of k)) (hPB : IsPullback m q' q φ)
    (hφ : GeometricallyReduced φ) [Surjective φ] [QuasiCompact m] (r : ℕ)
    (c' : CycleGroup (fieldChowSituation K) q' (r : ℤ)) :
    ∃ c : CycleGroup (fieldChowSituation k) q (r : ℤ),
      ∀ x : Y, ∃ y : Y', m y = x ∧ residueTrdeg q' y = residueTrdeg q x ∧
        (c : AlgebraicCycle Y ℤ) x * closedSubschemeCycleCoeff (fieldChowSituation K) q'
            (((Scheme.IdealSheafData.vanishingIdeal
              (Closeds.closure ({m y} : Set Y))).comap m).subschemeι) (r : ℤ) y =
          (c' : AlgebraicCycle Y' ℤ) y := by
  classical
  have hlift : ∀ x : Y,
      relativeDimension (fieldChowSituation k).dimensionFunction q x = (r : ℤ) →
      ∃ y : Y', m y = x ∧
        relativeDimension (fieldChowSituation K).dimensionFunction q' y = (r : ℤ) := by
    intro x hx
    obtain ⟨y, hy, hydim⟩ := AlgebraicGeometry.exists_preimage_preserving_residueField_trdeg
      hPB r x (trdeg_eq_of_relativeDimension q inferInstance r x hx)
    exact ⟨y, hy, relativeDimension_eq_of_trdeg q' r y hydim⟩
  refine ⟨cycleFromChosenLifts (fieldChowSituation k) q (fieldChowSituation K) q' m (r : ℤ) c'
    hlift, fun x ↦ ?_⟩
  by_cases hx : relativeDimension (fieldChowSituation k).dimensionFunction q x = (r : ℤ)
  · obtain ⟨hmy, hydim⟩ := chosenLift_spec (fieldChowSituation k) q (fieldChowSituation K) q' m
      (r : ℤ) hlift x hx
    refine ⟨Classical.choose (hlift x hx), hmy, ?_, ?_⟩
    · exact (trdeg_eq_of_relativeDimension q' inferInstance r _ hydim).trans
        (trdeg_eq_of_relativeDimension q inferInstance r x hx).symm
    · rw [closedSubschemeCycleCoeff_comap_eq_one_of_geometricallyReduced q q' m φ hPB hφ r _
          (by rwa [hmy]) hydim, mul_one, cycleFromChosenLifts_apply,
        chosenLiftCoeff_of_relativeDimension_eq (fieldChowSituation k) q (fieldChowSituation K)
          q' m (r : ℤ) c' hlift x hx]
  · obtain ⟨n, hn⟩ := exists_residueTrdeg_eq_natCast q x
    obtain ⟨y, hy, hydim⟩ :=
      AlgebraicGeometry.exists_preimage_preserving_residueField_trdeg hPB n x hn
    refine ⟨y, hy, hydim.trans hn.symm, ?_⟩
    have hc : (cycleFromChosenLifts (fieldChowSituation k) q (fieldChowSituation K) q' m (r : ℤ)
        c' hlift : AlgebraicCycle Y ℤ) x = 0 :=
      (cycleFromChosenLifts_apply (fieldChowSituation k) q (fieldChowSituation K) q' m (r : ℤ)
          c' hlift x).trans
        (chosenLiftCoeff_eq_zero_of_relativeDimension_ne (fieldChowSituation k) q
          (fieldChowSituation K) q' m (r : ℤ) c' hlift x hx)
    have hc' : (c' : AlgebraicCycle Y' ℤ) y = 0 := by
      by_contra hne
      exact hx (relativeDimension_eq_of_trdeg q r x (hn.trans
        (hydim.symm.trans (trdeg_eq_of_cycle_coeff_ne_zero q' inferInstance r y c' hne))))
    rw [hc, hc', zero_mul]

/-! ### Matching lifts on the fibres of a base change with separable residue extensions -/

/-- **The construction of the descended family, Stacks Project, Tag 0H4X (2).** Let `g : S' ⟶ S`
be such that every point of `S` has a preimage with separable residue field extension. Then over
each point `s` of `S` there is a cycle on the fibre of `f` over `s` which every point of that
fibre witnesses: the point has a lift to a fibre of the base change, of the same residue
transcendence degree, at which the base change of any family taking that cycle over `s` agrees
with `α'`.

The chosen preimage `t` of `s` is a separable one, so the multiplicity entering the base change
formula over `t` is one and `Stacks.Chow.exists_fieldCycle_matching_lifts` applies to the
cartesian square of fibres. -/
theorem exists_fiberCycle_matching_lifts {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (hg : HasSeparableResidueFieldPoints g) (r : ℕ)
    (α' : FamilyOfCycles (pullback.snd f g) r) (s : S) :
    ∃ c : FiberCycleGroup f s r,
      ∀ x : f.fiber s, ∃ (t : S') (y : (pullback.snd f g).fiber t),
        pullback.fst f g ((pullback.snd f g).fiberι t y) = f.fiberι s x ∧
        residueTrdeg (pullback.snd f g) ((pullback.snd f g).fiberι t y) =
          residueTrdeg f (f.fiberι s x) ∧
        ∀ α : FamilyOfCycles f r, α s = c →
          (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) y =
            (α' t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) y := by
  obtain ⟨t, ht, hsep⟩ := hg s
  subst s
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (g t)) := inferInstance
  let : LocallyOfFiniteType ((pullback.snd f g).fiberToSpecResidueField t) := inferInstance
  have hPB : IsPullback (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t) ((pullback.snd f g).fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g :=
    isPullback_restrictedFiberMap_baseChange f g t
  have hφ : GeometricallyReduced (residueFieldBaseChangeSituation g t).g :=
    @geometricallyReduced_specMap_algebraMap_of_isSeparableExtension
      ↥(S.residueField (g t)) ↥(S'.residueField t) _ _ (g.residueFieldMap t).hom.toAlgebra hsep
  have : Surjective (residueFieldBaseChangeSituation g t).g :=
    ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have : QuasiCompact (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t) :=
    MorphismProperty.of_isPullback hPB.flip (P := @QuasiCompact) inferInstance
  obtain ⟨c, hc⟩ := @exists_fieldCycle_matching_lifts ↥(S.residueField (g t))
    ↥(S'.residueField t) _ _ (f.fiber (g t)) ((pullback.snd f g).fiber t)
    (f.fiberToSpecResidueField (g t)) ((pullback.snd f g).fiberToSpecResidueField t)
    inferInstance inferInstance
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
    (residueFieldBaseChangeSituation g t).g hPB hφ inferInstance inferInstance r (α' t)
  refine ⟨c, fun x ↦ ?_⟩
  obtain ⟨y, hy, hydim, hcy⟩ := hc x
  refine ⟨t, y, ?_, ?_, ?_⟩
  · change ((pullback.snd f g).fiberι t ≫ pullback.fst f g) y = _
    rw [← restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t]
    exact congrArg (f.fiberι (g t)) hy
  · exact (residueTrdeg_fiberToSpecResidueField (pullback.snd f g) t y).symm.trans
      (hydim.trans (residueTrdeg_fiberToSpecResidueField f (g t) x))
  · intro α hα
    rw [baseChangeFamily_apply, hα]
    subst x
    exact hcy

/-! ### Vanishing of a family satisfying the overlap condition -/

variable {X S S' : Scheme.{u}}

/-- A base-changed family vanishes at a point exactly when the family does at the image of that
point in `X`, provided both the point and its image have residue transcendence degree `r`: the
multiplicity entering the base change formula is then nonzero, the point being a generic point of
the base change of the reduced closure of its image. -/
theorem baseChangeFamily_coeff_eq_zero_iff (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (r : ℕ) (α : FamilyOfCycles f r) (t : S') (y : (pullback.snd f g).fiber t)
    (hx : residueTrdeg f (pullback.fst f g ((pullback.snd f g).fiberι t y)) = r)
    (hy : residueTrdeg (pullback.snd f g) ((pullback.snd f g).fiberι t y) = r) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) y = 0 ↔
      familyCoeff f r α (pullback.fst f g ((pullback.snd f g).fiberι t y)) = 0 := by
  have hPB := isPullback_restrictedFiberMap_baseChange f g t
  have hmx : residueTrdeg (f.fiberToSpecResidueField (g t))
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t y)
      = r := by
    rw [residueTrdeg_fiberToSpecResidueField]
    change residueTrdeg f ((restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t ≫ f.fiberι (g t)) y) = r
    rwa [restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t]
  have hmy : residueTrdeg ((pullback.snd f g).fiberToSpecResidueField t) y = r :=
    (residueTrdeg_fiberToSpecResidueField (pullback.snd f g) t y).trans hy
  have hc := @closedSubschemeCycleCoeff_comap_ne_zero ↥(S.residueField (g t))
    ↥(S'.residueField t) _ _ (f.fiber (g t)) ((pullback.snd f g).fiber t)
    (f.fiberToSpecResidueField (g t)) ((pullback.snd f g).fiberToSpecResidueField t)
    inferInstance inferInstance
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
    (residueFieldBaseChangeSituation g t).g hPB r y hmx hmy
  rw [baseChangeFamily_apply, familyCoeff_restrictedFiberMap]
  exact mul_eq_zero.trans (or_iff_left hc)

/-- A family on the fibres of `X' / S'` satisfying the overlap condition and vanishing at one
lift of every point of `X` of matching residue transcendence degree has all coefficients zero. -/
theorem familyCoeff_eq_zero_of_overlap_of_zero_lifts (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (β : FamilyOfCycles (pullback.snd f g) r)
    (hβ : ∀ (t : (pullback g g : Scheme.{u}))
      (v : (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t),
      (baseChangeFamily (pullback.snd f g) (pullback.fst g g) r β t :
          AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) ℤ) v =
        (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r β t :
            AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
          ((overlapFiberComparison f g t).hom v))
    (hzero : ∀ x : X, ∃ (n : ℕ) (y : (pullback f g : Scheme.{u})),
      residueTrdeg f x = n ∧ pullback.fst f g y = x ∧
        residueTrdeg (pullback.snd f g) y = n ∧
        familyCoeff (pullback.snd f g) r β y = 0) :
    ∀ z : (pullback f g : Scheme.{u}), familyCoeff (pullback.snd f g) r β z = 0 := by
  classical
  intro z
  by_contra hnz
  have hzdim := residueTrdeg_eq_of_familyCoeff_ne_zero (pullback.snd f g) r β z hnz
  obtain ⟨n, y, hn, hy, hydim, hyzero⟩ := hzero (pullback.fst f g z)
  obtain ⟨w, hw₁, hw₂, hwdim⟩ := AlgebraicGeometry.exists_common_preimage_of_preserved_trdeg
    (IsPullback.of_hasPullback f g) (IsPullback.of_hasPullback g g)
    (IsPullback.of_hasPullback (pullback.snd f g) (pullback.fst g g))
    (overlap_isPullback_snd f g) (overlap_isPullback_fst f g) n r
    (pullback.fst f g z) y z hn hy rfl hydim hzdim
  set t := pullback.snd (pullback.snd f g) (pullback.fst g g) w
  set v := (pullback.snd (pullback.snd f g) (pullback.fst g g)).asFiber w
  have hv : (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiberι t v = w :=
    Scheme.Hom.fiberι_asFiber _ w
  have hv' : (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberι t
      ((overlapFiberComparison f g t).hom v) = (overlapComparison f g).hom w := by
    change ((overlapFiberComparison f g t).hom ≫
      (pullback.snd (pullback.snd f g) (pullback.snd g g)).fiberι t) v = _
    rw [overlapFiberComparison_hom_fiberι]
    exact congrArg (overlapComparison f g).hom hv
  have hfirst := baseChangeFamily_apply_eq_zero_of_familyCoeff_eq_zero
    (pullback.snd f g) (pullback.fst g g) r β t v (by rwa [hv, hw₁])
  have hsecond : (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r β t :
      AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
      ((overlapFiberComparison f g t).hom v) = 0 := (hβ t v).symm.trans hfirst
  have hz' := (baseChangeFamily_coeff_eq_zero_iff (pullback.snd f g) (pullback.snd g g) r β t
    ((overlapFiberComparison f g t).hom v)
    (by rw [hv']
        change residueTrdeg (pullback.snd f g) (((overlapComparison f g).hom ≫
          pullback.fst (pullback.snd f g) (pullback.snd g g)) w) = r
        rwa [hw₂])
    (by rwa [hv', residueTrdeg_overlap])).mp hsecond
  rw [hv'] at hz'
  change familyCoeff (pullback.snd f g) r β (((overlapComparison f g).hom ≫
    pullback.fst (pullback.snd f g) (pullback.snd g g)) w) = 0 at hz'
  rw [hw₂] at hz'
  exact hnz hz'

/-- **The injectivity step of the proof of Stacks Project, Tag 0H4X (2).** A family of `r`-cycles
on the fibres of `X' / S'` whose two pullbacks to the double overlap agree, and which vanishes at
one lift of every point of `X` of matching residue transcendence degree, is zero.

Given a point `z` of `X'` carrying a nonzero coefficient, the hypothesis supplies a lift `y` of
its image in `X` at which the family vanishes, of the same residue transcendence degree `n` as
that image. `AlgebraicGeometry.exists_common_preimage_of_preserved_trdeg` then produces a point
`w` of the double overlap lying over `y` and over `z` whose residue transcendence degree is that
of `z`; the overlap condition at `w` equates a vanishing coefficient with a nonvanishing one. -/
theorem family_eq_zero_of_overlap_of_zero_lifts (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (β : FamilyOfCycles (pullback.snd f g) r)
    (hβ : ∀ (t : (pullback g g : Scheme.{u}))
      (v : (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t),
      (baseChangeFamily (pullback.snd f g) (pullback.fst g g) r β t :
          AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) ℤ) v =
        (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r β t :
            AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
          ((overlapFiberComparison f g t).hom v))
    (hzero : ∀ x : X, ∃ (n : ℕ) (y : (pullback f g : Scheme.{u})),
      residueTrdeg f x = n ∧ pullback.fst f g y = x ∧
        residueTrdeg (pullback.snd f g) y = n ∧
        familyCoeff (pullback.snd f g) r β y = 0) :
    β = 0 := by
  have hz := familyCoeff_eq_zero_of_overlap_of_zero_lifts f g r β hβ hzero
  funext t
  exact Subtype.ext <| Function.locallyFinsuppWithin.ext fun y ↦
    (familyCoeff_fiberι (pullback.snd f g) r β t y).symm.trans (hz ((pullback.snd f g).fiberι t y))

/-! ### Part (2) of Tag 0H4X -/

/-- **Stacks Project, Tag 0H4X (2).** Let `f : X ⟶ S` be locally of finite type, let `r ≥ 0`, let
`g : S' ⟶ S` be a morphism such that every point of `S` has a preimage in `S'` whose residue
field extension is separable, and let `X' = X ×_S S'`. Given a family `α'` of `r`-cycles on the
fibres of `X' / S'` whose two pullbacks to the double overlap `S'' = S' ×_S S'` agree as families
of `r`-cycles on the fibres of `S'' ×_S X / S''`, there is a unique family `α` of `r`-cycles on
the fibres of `X / S` with `g^*α = α'`. -/
@[stacks 0H4X "descent of a family of cycles on fibres along a morphism with separable residue
  field extensions"]
theorem existsUnique_familyOfCycles_baseChangeFamily_eq (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (hg : HasSeparableResidueFieldPoints g) (r : ℕ)
    (α' : FamilyOfCycles (pullback.snd f g) r)
    (hα' : ∀ (t : (pullback g g : Scheme.{u}))
      (x : (pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t),
      (baseChangeFamily (pullback.snd f g) (pullback.fst g g) r α' t :
          AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) ℤ) x =
        (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r α' t :
            AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
          ((overlapFiberComparison f g t).hom x)) :
    ∃! α : FamilyOfCycles f r, baseChangeFamily f g r α = α' := by
  classical
  let : Surjective g := surjective_of_hasSeparableResidueFieldPoints hg
  choose α hα using exists_fiberCycle_matching_lifts f g hg r α'
  have hzero : baseChangeFamily f g r α - α' = 0 := by
    refine family_eq_zero_of_overlap_of_zero_lifts f g r _ (fun t v ↦ ?_) (fun x ↦ ?_)
    · rw [baseChangeFamily_sub, baseChangeFamily_sub]
      change (baseChangeFamily (pullback.snd f g) (pullback.fst g g) r
            (baseChangeFamily f g r α) t :
          AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) ℤ) v -
          (baseChangeFamily (pullback.snd f g) (pullback.fst g g) r α' t :
            AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.fst g g)).fiber t) ℤ) v =
        (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r
              (baseChangeFamily f g r α) t :
            AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
            ((overlapFiberComparison f g t).hom v) -
          (baseChangeFamily (pullback.snd f g) (pullback.snd g g) r α' t :
              AlgebraicCycle ((pullback.snd (pullback.snd f g) (pullback.snd g g)).fiber t) ℤ)
            ((overlapFiberComparison f g t).hom v)
      rw [baseChangeFamily_apply_overlapFiberComparison f g r t α v, hα' t v]
    · obtain ⟨n, hn⟩ := exists_residueTrdeg_eq_natCast f x
      obtain ⟨t, y, hy, hydim, hcy⟩ := hα (f x) (f.asFiber x)
      rw [Scheme.Hom.fiberι_asFiber] at hy hydim
      refine ⟨n, (pullback.snd f g).fiberι t y, hn, hy, hydim.trans hn, ?_⟩
      rw [familyCoeff_fiberι]
      change (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) y -
        (α' t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) y = 0
      exact sub_eq_zero.mpr (hcy α rfl)
  have hbase : baseChangeFamily f g r α = α' := sub_eq_zero.mp hzero
  exact ⟨α, hbase, fun γ hγ ↦ baseChangeFamily_injective f g r γ α (hγ.trans hbase.symm)⟩

end Stacks.Chow

end
