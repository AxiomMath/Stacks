module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundle
public import StacksCore.Tactic.StacksAttribute

/-!
# The splitting morphism is a tower of projective space bundles

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ_i` be a finite collection of finite locally free `𝒪_X`-modules of
ranks `r_i`. Stacks 02UL produces a morphism `π : P ⟶ X` of relative dimension `d` along which
flat pullback on Chow groups is injective and which splits every `ℰ_i`. This file proves that
`π` can be taken to be a finite composition of projective space bundles associated to finite
locally free modules of constant rank.

## Main definitions

* `Stacks.Chow.IsBundleTower`: the property of a `Stacks.Chow.SplittingMorphism` of being the
  identity or one layer `𝐏(ℰ) ⟶ X`, with `ℰ` finite locally free of constant rank `m + 1`,
  composed with a tower over `𝐏(ℰ)`.

## Main results

* `Stacks.Chow.exists_splittingMorphism_isBundleTower`: the morphism of Stacks 02UL can be taken
  to be a tower of projective space bundles of finite locally free modules of constant rank.

## Implementation notes

A layer is a `Stacks.Chow.BundleStep`, the datum of the projective bundle of a finite locally free
module, supplied as a parameter rather than constructed as a relative `Proj`. A
`Stacks.Chow.BundleStep` records the rank of the tautological kernel but not the rank of the
module the bundle is taken of, so `Stacks.Chow.IsBundleTower` carries that rank as a field of its
second constructor.

## References

* [Stacks Project, Tag 0FVE](https://stacks.math.columbia.edu/tag/0FVE)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Towers of projective space bundles -/

/-- `IsBundleTower C sX d T` says that the morphism of `T : SplittingMorphism C sX d` is either
the identity of `X` or the projection `𝐏(ℰ) ⟶ X` of a layer, with `ℰ` finite locally free of
constant rank `m + 1`, precomposed with a tower over `𝐏(ℰ)`. The relative dimension of a tower is
the sum of the relative dimensions of its layers. -/
inductive IsBundleTower (C : ChowSituation.{u}) : {X : Scheme.{u}} → (sX : X ⟶ C.S) →
    [LocallyOfFiniteType sX] → (d : ℕ) → SplittingMorphism C sX d → Prop
  /-- The identity of `X` is the empty tower, of relative dimension zero. -/
  | id {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] :
      IsBundleTower C sX 0 (SplittingMorphism.id C sX)
  /-- One layer `𝐏(ℰ) ⟶ X`, for `ℰ` finite locally free of constant rank `m + 1`, composed with a
  tower of relative dimension `n` over `𝐏(ℰ)`. -/
  | compStep {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1))
      (D : BundleStep C sX E m) (n : ℕ) (T : SplittingMorphism C D.sP n)
      (hT : IsBundleTower C D.sP n T) :
      IsBundleTower C sX (n + m) (SplittingMorphism.compStep D T)

/-! ### The splitting morphism as a tower -/

/-- For every `n`, finite locally free modules `E i` of ranks `r i` with `∑ binom(r_i, 2) = n` are
split by a splitting morphism of relative dimension `n` that is a tower of projective space
bundles. -/
private theorem exists_splittingMorphism_isBundleTower_aux (C : ChowSituation.{u})
    (step : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) →
        BundleStep C sY F m) :
    ∀ (n : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type)
      [Fintype I] (E : I → X.Modules) (r : I → ℕ),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) →
      ∑ i, (r i).choose 2 = n →
      ∃ T : SplittingMorphism C sX n, IsBundleTower C sX n T ∧
        ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X sX _ I _ E r hE hn
    by_cases hr : ∀ i, r i ≤ 1
    · have hn0 : n = 0 := by
        rw [← hn, Finset.sum_eq_zero]
        intro i _
        exact Nat.choose_eq_zero_of_lt (by have := hr i; omega)
      subst hn0
      refine ⟨SplittingMorphism.id C sX, IsBundleTower.id (C := C) sX, fun i ↦ ?_⟩
      exact Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one _ (r i)
        (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (𝟙 X) (E i) (r i) (hE i))
        (hr i)
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have hi : 1 < r i := by omega
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (r i - 1 + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ r i by omega)]
      exact hE i
    set D := step sX (E i) (r i - 1) hEi
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j)
        (Function.update r i (r i - 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E j) (r j) (hE j)
    have hchoose : (r i - 1).choose 2 + (r i - 1) = (r i).choose 2 := by
      obtain ⟨m, hm⟩ : ∃ m, r i = m + 1 := ⟨r i - 1, by omega⟩
      have key : (m + 1).choose 2 = m.choose 2 + m := by
        change Nat.choose (m + 1) (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        change m + Nat.choose m 2 = Nat.choose m 2 + m
        omega
      rw [hm, Nat.add_sub_cancel, key]
    have hsplit : ∀ f : I → ℕ, ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := fun f ↦
      (Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)).symm
    have hsum : (∑ j, (Function.update r i (r i - 1) j).choose 2) + (r i - 1) = n := by
      rw [hsplit, Function.update_self, ← hn, hsplit fun j ↦ (r j).choose 2,
        Finset.sum_congr rfl fun j hj ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
      omega
    have hlt : (∑ j, (Function.update r i (r i - 1) j).choose 2) < n := by omega
    obtain ⟨T, hTtower, hT⟩ := ih _ hlt D.sP I
      (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub)
      (Function.update r i (r i - 1)) hE' rfl
    subst hsum
    refine ⟨SplittingMorphism.compStep D T,
      IsBundleTower.compStep (C := C) sX (E i) (r i - 1) hEi D _ T hTtower, fun j ↦ ?_⟩
    simp only [SplittingMorphism.compStep_P, SplittingMorphism.compStep_π]
    have comp₁ : (Scheme.Modules.pullback T.π).obj
          ((Scheme.Modules.pullback D.π).obj (E j)) ≅
        (Scheme.Modules.pullback (T.π ≫ D.π)).obj (E j) :=
      (Scheme.Modules.pullbackComp T.π D.π).app (E j)
    by_cases hj : j = i
    · rw [hj] at comp₁ ⊢
      have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
          (Scheme.Modules.pullback T.π)).ShortExact :=
        Stacks.WeilCohomology.shortExact_map_pullback T.π _ D.shortExact
      have hleft : Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj D.sub) (r i - 1) := by
        simpa only [Function.update_self] using hT i
      have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback T.π).obj
            ((Scheme.Modules.pullback D.π).obj (E i))) (r i - 1 + 1) :=
        @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.π _ _
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E i) _ hEi)
      refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Nat.sub_add_cancel (show 1 ≤ r i by omega)] using
        Stacks.WeilCohomology.HasInvertibleFiltration.step _ _ _ hDx
          (Stacks.WeilCohomology.isInvertible_pullback_obj T.π D.twistModule
            D.twistModule_isInvertible)
          hrank.isFiniteLocallyFree hleft
    · refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Function.update_of_ne hj] using hT j

/-- The morphism `π : P ⟶ X` of Stacks 02UL is a finite composition of projective space bundles
associated to locally free modules of finite constant rank.

Let `(S, δ)` be the situation of Stacks 02QL, let `X` be locally of finite type over `S` and let
`ℰ_i`, `i ∈ I` finite, be finite locally free `𝒪_X`-modules of ranks `r_i`. Then there is a
splitting morphism `T`, flat and proper of relative dimension `d = ∑_i binom(r_i, 2)`, with
injective flat pullback on Chow groups in every degree, splitting every `ℰ_i`, and satisfying
`Stacks.Chow.IsBundleTower`: it is the identity of `X` or the projection of one layer `𝐏(ℰ)` with
`ℰ` finite locally free of constant rank, composed with such a tower over `𝐏(ℰ)`. -/
@[stacks 0FVE "clause (1) only: the 02UL morphism is a constant-rank projective bundle tower"]
theorem exists_splittingMorphism_isBundleTower (C : ChowSituation.{u})
    (step : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) →
        BundleStep C sY F m)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      IsBundleTower C sX (∑ i, (r i).choose 2) T ∧
        ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i) :=
  exists_splittingMorphism_isBundleTower_aux C step _ sX I E r hE rfl

end Stacks.Chow

end
