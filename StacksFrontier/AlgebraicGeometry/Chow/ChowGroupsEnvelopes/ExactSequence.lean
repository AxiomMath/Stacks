module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.FibreCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.PrincipalDivisorLift
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropApplications
public import StacksCore.Tactic.StacksAttribute

/-!
# The exact sequence of Chow groups of an envelope

Let `S` be the base scheme of chapter 42 of the Stacks Project, let `X` be a scheme locally of
finite type over `S` and let `f : Y ⟶ X` be an envelope (Stacks 0GU5). Writing `p, q` for the two
projections of the fibre square `Y ×_X Y`, the sequence

  `A_k(Y ×_X Y) --(p_* - q_*)--> A_k(Y) --f_*--> A_k(X) ⟶ 0`

is exact for every `k ∈ ℤ`. This is Stacks 0GU8.

## Main results

* `Stacks.Chow.envelope_chow_comp_eq_zero` — the composite `f_* ∘ (p_* - q_*)` is zero.
* `Stacks.Chow.envelope_chow_exact` — exactness at the middle term: a class on `Y` pushes
  forward to zero on `X` exactly when it is `p_* γ - q_* γ` for a class `γ` on `Y ×_X Y`.
* `Stacks.Chow.envelope_chow_exactSequence` — the three statements together: the composite is
  zero, the sequence is exact at the middle term, and `f_*` is surjective.

## References

* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Preliminaries -/

/-- A double `finsum` of a family supported in a product of two finite sets may be taken in
either order. -/
theorem finsum_finsum_comm_of_support_subset_prod {A B : Type u} (G : A × B → ℤ) (s : Finset A)
    (t : Finset B) (hsupp : Function.support G ⊆ (s : Set A) ×ˢ (t : Set B)) :
    (∑ᶠ a, ∑ᶠ b, G (a, b)) = ∑ᶠ b, ∑ᶠ a, G (a, b) := by
  classical
  have hrow (a : A) : Function.support (fun b ↦ G (a, b)) ⊆ (t : Set B) := fun b hb ↦
    (Set.mem_prod.mp (hsupp (by simpa [Function.mem_support] using hb))).2
  have hcol (b : B) : Function.support (fun a ↦ G (a, b)) ⊆ (s : Set A) := fun a ha ↦
    (Set.mem_prod.mp (hsupp (by simpa [Function.mem_support] using ha))).1
  have hleft : Function.support (fun a ↦ ∑ᶠ b, G (a, b)) ⊆ (s : Set A) := by
    intro a ha
    by_contra has
    exact ha (finsum_eq_zero_of_forall_eq_zero fun b ↦ by
      by_contra hne
      exact has (Set.mem_prod.mp (hsupp (by simpa [Function.mem_support] using hne))).1)
  have hright : Function.support (fun b ↦ ∑ᶠ a, G (a, b)) ⊆ (t : Set B) := by
    intro b hb
    by_contra hbt
    exact hb (finsum_eq_zero_of_forall_eq_zero fun a ↦ by
      by_contra hne
      exact hbt (Set.mem_prod.mp (hsupp (by simpa [Function.mem_support] using hne))).2)
  rw [finsum_eq_sum_of_support_subset _ hleft]
  simp_rw [fun a ↦ finsum_eq_sum_of_support_subset (f := fun b ↦ G (a, b)) (s := t) (hrow a)]
  rw [finsum_eq_sum_of_support_subset _ hright]
  simp_rw [fun b ↦ finsum_eq_sum_of_support_subset (f := fun a ↦ G (a, b)) (s := s) (hcol b)]
  rw [Finset.sum_comm]

/-- The coefficient of the weighted pushforward of an algebraic cycle, in the form taken by
proper pushforward of `k`-cycles but with no reference to the grading. -/
theorem algebraicCycle_map_relativeDimension_apply (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsProper f] (c : AlgebraicCycle X ℤ) (y : Y) :
    AlgebraicCycle.map f (relativeDimension C.dimensionFunction sX)
        (relativeDimension C.dimensionFunction sY) c y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, c x *
        (if relativeDimension C.dimensionFunction sX x =
            relativeDimension C.dimensionFunction sY (f.base x)
          then (f.residueDegree x : ℤ) else 0) := by
  simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff]

/-- Two equal proper morphisms over the base induce the same proper pushforward on Chow
groups. -/
theorem properChowPushforward_congr_of_eq (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {p p' : X ⟶ Y} [IsProper p]
    [IsProper p'] (h : p = p') (hp : p ≫ sY = sX) (hp' : p' ≫ sY = sX) (k : ℤ)
    (hrat : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (hrat' : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p' hp' k) :
    properChowPushforward C sX sY p hp k hrat = properChowPushforward C sX sY p' hp' k hrat' := by
  subst h
  rfl

/-! ### Lifting a rational equivalence along a completely decomposed morphism -/

/-- The lifts along a completely decomposed `f : Y ⟶ X` of a locally finite family of integral
closed subschemes of `X` form a locally finite family on `Y`. -/
theorem locallyFinite_envelopeSubschemeLift {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) :
    LocallyFinite fun j ↦ ((envelopeSubschemeLift f hcd (W j) (hW j)).support : Set Y) := by
  intro y
  obtain ⟨U, hU, hfin⟩ := hLocal (f.base y)
  refine ⟨f.base ⁻¹' U, f.continuous.continuousAt.preimage_mem_nhds hU, hfin.subset ?_⟩
  rintro j ⟨z, hzV, hzU⟩
  exact ⟨f.base z,
    mem_support_of_mem_support_envelopeSubschemeLift f hcd (W j) (hW j) hzV, hzU⟩

/-- The pushforward to `X` of the cycle on `Y` presented by the lifted family of principal
divisors is the cycle presented by the original family. -/
theorem properPushforward_apply_of_envelopeSubschemeLift_family (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (δ : CycleGroup C (f ≫ sX) k)
    (hδ : ∀ y : Y, δ.1 y = principalDivisorFamilyCoefficient C (f ≫ sX)
      (fun j ↦ envelopeSubschemeLift f hcd (W j) (hW j))
      (fun j ↦ isIntegral_envelopeSubschemeLift f hcd (W j) (hW j))
      (fun j ↦ envelopeRationalFunctionLift f hcd (W j) (hW j) (g j)) y)
    (x : X) :
    (properPushforward C (f ≫ sX) sX f rfl k δ).1 x =
      principalDivisorFamilyCoefficient C sX W hW g x := by
  classical
  rw [properPushforward_apply]
  set fibre : Set Y := f.base ⁻¹' ({x} : Set X) with hfibre
  have hcompact : IsCompact fibre := f.isProperMap.isCompact_preimage isCompact_singleton
  set wt : Y → ℤ := fun y ↦
    if relativeDimension C.dimensionFunction (f ≫ sX) y =
        relativeDimension C.dimensionFunction sX (f.base y)
      then (f.residueDegree y : ℤ) else 0 with hwt
  set a : J → AlgebraicCycle Y ℤ := fun j ↦
    principalDivisorPushforward C (f ≫ sX) (envelopeSubschemeLift f hcd (W j) (hW j))
      (isIntegral_envelopeSubschemeLift f hcd (W j) (hW j))
      (envelopeRationalFunctionLift f hcd (W j) (hW j) (g j)) with ha
  have hδ' : ∀ y : Y, δ.1 y = ∑ᶠ j, a j y := hδ
  have hVlocal := locallyFinite_envelopeSubschemeLift f hcd W hW hLocal
  set t : Finset J := (hVlocal.finite_nonempty_inter_compact hcompact).toFinset with ht
  set s : Finset Y := t.attach.biUnion fun j ↦
    ((a j).locallyFiniteSupport.finite_inter_support_of_isCompact hcompact).toFinset with hs
  set G : Y × J → ℤ := fun yj ↦ if f.base yj.1 = x then a yj.2 yj.1 * wt yj.1 else 0 with hG
  have hGsupp : Function.support G ⊆ (s : Set Y) ×ˢ (t : Set J) := by
    intro yj hyj
    have hterm : G yj ≠ 0 := by simpa only [Function.mem_support] using hyj
    have hfy : f.base yj.1 = x := by
      by_contra h
      exact hterm (by simp [hG, h])
    have hcoeff : a yj.2 yj.1 ≠ 0 := by
      have hmul : a yj.2 yj.1 * wt yj.1 ≠ 0 := by simpa [hG, hfy] using hterm
      exact (mul_ne_zero_iff.mp hmul).1
    have hyfibre : yj.1 ∈ fibre := by simpa [hfibre] using hfy
    have hjt : yj.2 ∈ t := by
      refine (Set.Finite.mem_toFinset _).mpr ⟨yj.1, ?_, hyfibre⟩
      exact support_principalDivisorPushforward_subset C (f ≫ sX) _ _ _
        (Function.mem_support.mpr hcoeff)
    refine Set.mem_prod.mpr ⟨?_, hjt⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨yj.2, hjt⟩, Finset.mem_attach _ _, ?_⟩)
    exact (Set.Finite.mem_toFinset _).mpr ⟨hyfibre, Function.mem_support.mpr hcoeff⟩
  have hleft : (∑ᶠ y ∈ fibre, δ.1 y * wt y) = ∑ᶠ y, ∑ᶠ j, G (y, j) := by
    rw [finsum_mem_def]
    refine finsum_congr fun y ↦ ?_
    by_cases hy : y ∈ fibre
    · have hyx : f.base y = x := by simpa [hfibre] using hy
      rw [Set.indicator_of_mem hy, hδ' y, finsum_mul]
      exact finsum_congr fun j ↦ by simp [hG, hyx]
    · have hyx : f.base y ≠ x := by simpa [hfibre] using hy
      simp [Set.indicator_of_notMem hy, hG, hyx]
  have hright : (∑ᶠ j, ∑ᶠ y, G (y, j)) = ∑ᶠ j, ∑ᶠ y ∈ fibre, a j y * wt y := by
    refine finsum_congr fun j ↦ ?_
    rw [finsum_mem_def]
    refine finsum_congr fun y ↦ ?_
    by_cases hy : y ∈ fibre
    · have hyx : f.base y = x := by simpa [hfibre] using hy
      rw [Set.indicator_of_mem hy]
      simp [hG, hyx]
    · have hyx : f.base y ≠ x := by simpa [hfibre] using hy
      simp [Set.indicator_of_notMem hy, hG, hyx]
  have hterm : ∀ j, (∑ᶠ y ∈ fibre, a j y * wt y) =
      principalDivisorPushforward C sX (W j) (hW j) (g j) x := by
    intro j
    rw [← properPushforward_principalDivisorPushforward_envelopeSubschemeLift f hcd (W j)
      (hW j) C sX (hDim j) (g j),
      algebraicCycle_map_relativeDimension_apply C (f ≫ sX) sX f (a j) x]
  calc (∑ᶠ y ∈ fibre, δ.1 y * wt y)
      = ∑ᶠ y, ∑ᶠ j, G (y, j) := hleft
    _ = ∑ᶠ j, ∑ᶠ y, G (y, j) := finsum_finsum_comm_of_support_subset_prod G s t hGsupp
    _ = ∑ᶠ j, ∑ᶠ y ∈ fibre, a j y * wt y := hright
    _ = principalDivisorFamilyCoefficient C sX W hW g x := finsum_congr hterm

/-- **Replacing a cycle by one in the same class with vanishing pushforward.** If the pushforward
to `X` of a `k`-cycle `α` on `Y` is rationally equivalent to zero, then `α` is rationally
equivalent to a `k`-cycle whose pushforward to `X` is zero. -/
theorem exists_rationallyEquivalent_properPushforward_eq_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (α : CycleGroup C (f ≫ sX) k)
    (hα : properPushforward C (f ≫ sX) sX f rfl k α ∈ rationalEquivalences C sX k) :
    ∃ α' : CycleGroup C (f ≫ sX) k, α - α' ∈ rationalEquivalences C (f ≫ sX) k ∧
      properPushforward C (f ≫ sX) sX f rfl k α' = 0 := by
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  have hVdim : ∀ j, schemeDeltaDimension C
      ((envelopeSubschemeLift f hcd (W j) (hW j)).subschemeι ≫ f ≫ sX) =
      ((k + 1 : ℤ) : EInt) := fun j ↦
    (schemeDeltaDimension_envelopeSubschemeLift f hcd (W j) (hW j) C sX).trans (hDim j)
  obtain ⟨δ, hδ⟩ := exists_principalDivisorFamilySum C (f ≫ sX) k
    (fun j ↦ envelopeSubschemeLift f hcd (W j) (hW j))
    (fun j ↦ isIntegral_envelopeSubschemeLift f hcd (W j) (hW j)) hVdim
    (locallyFinite_envelopeSubschemeLift f hcd W hW hLocal)
    (fun j ↦ envelopeRationalFunctionLift f hcd (W j) (hW j) (g j))
  have hδmem : δ ∈ rationalEquivalences C (f ≫ sX) k :=
    ⟨J, _, _, hVdim, locallyFinite_envelopeSubschemeLift f hcd W hW hLocal, _, hδ⟩
  have hpushδ : properPushforward C (f ≫ sX) sX f rfl k δ =
      properPushforward C (f ≫ sX) sX f rfl k α :=
    Subtype.ext <| Function.locallyFinsuppWithin.ext fun x ↦
      (properPushforward_apply_of_envelopeSubschemeLift_family C sX f hcd k W hW hDim hLocal g δ hδ
        x).trans (hg x).symm
  refine ⟨α - δ, by simpa using hδmem, ?_⟩
  rw [properPushforward_sub, hpushδ, sub_self]

/-! ### The exact sequence -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : Y ⟶ X) [IsProper f] (k : ℤ)

/-- Pushing forward along the second projection and then along `f` is pushing forward along the
first projection and then along `f`. -/
theorem properChowPushforward_snd_comp_eq_fst_comp :
    (properChowPushforward C (f ≫ sX) sX f rfl k
          (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k)).comp
        (properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
          (pullback_snd_comp_eq_pullback_fst_comp f sX) k
          (properPushforwardFactorsThroughRationalEquivalence C
            (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
            (pullback_snd_comp_eq_pullback_fst_comp f sX) k)) =
      (properChowPushforward C (f ≫ sX) sX f rfl k
          (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k)).comp
        (properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k
          (properPushforwardFactorsThroughRationalEquivalence C
            (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k)) := by
  rw [properChowPushforward_comp C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) sX (pullback.snd f f) f
      (pullback_snd_comp_eq_pullback_fst_comp f sX) rfl k _ _,
    properChowPushforward_comp C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) sX (pullback.fst f f) f
      rfl rfl k _ _]
  exact properChowPushforward_congr_of_eq C (pullback.fst f f ≫ f ≫ sX) sX
    (show pullback.snd f f ≫ f = pullback.fst f f ≫ f from pullback.condition.symm) _ _ k _ _

/-- Pushing a class on `Y ×_X Y` forward along the two projections, taking the difference and
pushing forward along `f` gives zero. -/
@[stacks 0GU8 "the composite of the two maps is zero"]
theorem envelope_chow_comp_eq_zero (γ : chowGroup C (pullback.fst f f ≫ f ≫ sX) k) :
    properChowPushforward C (f ≫ sX) sX f rfl k
        (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k)
        (properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k
            (properPushforwardFactorsThroughRationalEquivalence C
              (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k) γ -
          properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
            (pullback_snd_comp_eq_pullback_fst_comp f sX) k
            (properPushforwardFactorsThroughRationalEquivalence C
              (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
              (pullback_snd_comp_eq_pullback_fst_comp f sX) k) γ) = 0 := by
  rw [map_sub, sub_eq_zero]
  exact (congrFun (congrArg DFunLike.coe
    (properChowPushforward_snd_comp_eq_fst_comp C sX f k)) γ).symm

/-- For an envelope `f : Y ⟶ X` a class in
`A_k(Y)` pushes forward to zero in `A_k(X)` exactly when it is the difference of the pushforwards
of a single class in `A_k(Y ×_X Y)` along the two projections. -/
@[stacks 0GU8 "exactness at the middle term"]
theorem envelope_chow_exact (hcd : IsCompletelyDecomposed f) (β : chowGroup C (f ≫ sX) k) :
    properChowPushforward C (f ≫ sX) sX f rfl k
        (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k) β = 0 ↔
      ∃ γ : chowGroup C (pullback.fst f f ≫ f ≫ sX) k,
        β = properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k
              (properPushforwardFactorsThroughRationalEquivalence C
                (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k) γ -
            properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
              (pullback_snd_comp_eq_pullback_fst_comp f sX) k
              (properPushforwardFactorsThroughRationalEquivalence C
                (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
                (pullback_snd_comp_eq_pullback_fst_comp f sX) k) γ := by
  refine ⟨fun hβ ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨α, hα⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C (f ≫ sX) k) β
    have hzeroα : properChowPushforward C (f ≫ sX) sX f rfl k
        (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k)
        (QuotientAddGroup.mk' (rationalEquivalences C (f ≫ sX) k) α) = 0 := by
      rwa [hα]
    rw [properChowPushforward_mk] at hzeroα
    have hpush : properPushforward C (f ≫ sX) sX f rfl k α ∈ rationalEquivalences C sX k :=
      (QuotientAddGroup.eq_zero_iff _).mp hzeroα
    obtain ⟨α', hrel, hzero⟩ := exists_rationallyEquivalent_properPushforward_eq_zero C sX f
      hcd k α hpush
    obtain ⟨γ, hγ⟩ := exists_fibre_difference_of_properPushforward_eq_zero C sX f hcd k α' hzero
    have hclass : QuotientAddGroup.mk' (rationalEquivalences C (f ≫ sX) k) α =
        QuotientAddGroup.mk' (rationalEquivalences C (f ≫ sX) k) α' := by
      rw [← sub_eq_zero, ← map_sub]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hrel
    refine ⟨QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst f f ≫ f ≫ sX) k) γ, ?_⟩
    rw [← hα, hclass, hγ, map_sub, properChowPushforward_mk, properChowPushforward_mk]
  · rw [hγ]
    exact envelope_chow_comp_eq_zero C sX f k γ

/-- For an envelope `f : Y ⟶ X` with the two projections `p, q : Y ×_X Y ⟶ Y` of its fibre
square, the sequence

  `A_k(Y ×_X Y) --(p_* - q_*)--> A_k(Y) --f_*--> A_k(X) ⟶ 0`

is exact for every `k ∈ ℤ`: the composite of the two maps is zero, a class killed by `f_*` is a
difference `p_* γ - q_* γ`, and `f_*` is surjective. -/
@[stacks 0GU8 "the exact sequence of Chow groups of an envelope"]
theorem envelope_chow_exactSequence (hcd : IsCompletelyDecomposed f) :
    (∀ γ : chowGroup C (pullback.fst f f ≫ f ≫ sX) k,
        properChowPushforward C (f ≫ sX) sX f rfl k
          (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k)
          (properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k
              (properPushforwardFactorsThroughRationalEquivalence C
                (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k) γ -
            properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
              (pullback_snd_comp_eq_pullback_fst_comp f sX) k
              (properPushforwardFactorsThroughRationalEquivalence C
                (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
                (pullback_snd_comp_eq_pullback_fst_comp f sX) k) γ) = 0) ∧
      (∀ β : chowGroup C (f ≫ sX) k,
        properChowPushforward C (f ≫ sX) sX f rfl k
            (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k) β = 0 ↔
          ∃ γ : chowGroup C (pullback.fst f f ≫ f ≫ sX) k,
            β = properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX)
                  (pullback.fst f f) rfl k
                  (properPushforwardFactorsThroughRationalEquivalence C
                    (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k) γ -
                properChowPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX)
                  (pullback.snd f f) (pullback_snd_comp_eq_pullback_fst_comp f sX) k
                  (properPushforwardFactorsThroughRationalEquivalence C
                    (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
                    (pullback_snd_comp_eq_pullback_fst_comp f sX) k) γ) ∧
      Function.Surjective (properChowPushforward C (f ≫ sX) sX f rfl k
        (properPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k)) :=
  ⟨envelope_chow_comp_eq_zero C sX f k, envelope_chow_exact C sX f k hcd,
    envelope_chow_surjective C sX f ⟨‹IsProper f›, hcd⟩ k _⟩

/-! ### The sequence read against a structure morphism upstairs given by an equality -/

section OfCompEq

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) [IsProper f] (hs : f ≫ sX = sY) (k : ℤ)

include hs in
/-- Exactness at the middle term of the sequence of Chow groups of an envelope, with the
structure morphism of the source presented as a morphism `sY` *equal* to the composite `f ≫ sX`
rather than as that composite itself. -/
theorem envelope_chow_exact_of_comp_eq (hcd : IsCompletelyDecomposed f) (β : chowGroup C sY k) :
    properChowPushforward C sY sX f hs k
        (properPushforwardFactorsThroughRationalEquivalence C sY sX f hs k) β = 0 ↔
      ∃ γ : chowGroup C (pullback.fst f f ≫ sY) k,
        β = properChowPushforward C (pullback.fst f f ≫ sY) sY (pullback.fst f f) rfl k
              (properPushforwardFactorsThroughRationalEquivalence C
                (pullback.fst f f ≫ sY) sY (pullback.fst f f) rfl k) γ -
            properChowPushforward C (pullback.fst f f ≫ sY) sY (pullback.snd f f)
              (by rw [← hs, ← Category.assoc, ← pullback.condition, Category.assoc]) k
              (properPushforwardFactorsThroughRationalEquivalence C
                (pullback.fst f f ≫ sY) sY (pullback.snd f f)
                (by rw [← hs, ← Category.assoc, ← pullback.condition, Category.assoc]) k) γ := by
  subst hs
  exact envelope_chow_exact C sX f k hcd β

include hs in
/-- Surjectivity of proper pushforward along an envelope, with the structure morphism of the
source presented as a morphism `sY` equal to the composite `f ≫ sX` rather than as the composite
itself. -/
theorem envelope_chow_surjective_of_comp_eq (hf : IsEnvelope f) :
    Function.Surjective (properChowPushforward C sY sX f hs k
      (properPushforwardFactorsThroughRationalEquivalence C sY sX f hs k)) := by
  subst hs
  exact envelope_chow_surjective C sX f hf k _

end OfCompEq

end Stacks.Chow

end
