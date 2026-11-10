module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ProjectiveLayer
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.RestrictionInjective
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective

/-!
# The splitting principle

**Stacks 02UL.** Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S` and
`ℰ_i` (`i ∈ I`, finite) finite locally free `𝒪_X`-modules of ranks `r_i`. There is a projective
flat morphism `π : P ⟶ X` of relative dimension `d = ∑_i binom(r_i, 2)` such that

1. for every morphism `f : Y ⟶ X` the flat pullback `π_Y^* : CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` is
   injective, and
2. each `π^*ℰ_i` has a filtration whose successive quotients are invertible `𝒪_P`-modules;

and the restriction map `A^*(X) ⟶ A^*(P)` of Stacks 0B7F is injective.

The morphism is the tower of projective bundles of the source's proof: if some `r_i ≥ 2`, take
`ρ : 𝐏(ℰ_i) ⟶ X`, replace `ℰ_i` by the kernel of the tautological surjection `ρ^*ℰ_i ⟶ 𝒪(1)` and
the other modules by their pullbacks, and recurse on `∑_i binom(r_i, 2)`. Clause (1) and the last
assertion are `Stacks.Chow.IsProjectiveBundleTower.universallyChowInjective` and
`Stacks.Chow.IsProjectiveBundleTower.chowCohomologyTotalRestriction_injective`.

Projectivity in the sense of Stacks 01W8 is not obtained by composing the layers, which needs a
quasi-compact base (Stacks 0C4P). Instead the recursion carries, for the composite `g : Y ⟶ X`
built so far, that each module is up to a twist a quotient of a pullback along `g` of a
quasi-coherent `𝒪_X`-module of finite type (`Stacks.Chow.IsTwistedPullbackQuotient`). Then each
new layer is projective over `X` (`Stacks.Chow.isProjective_bundleProj_comp`), with no hypothesis
on `X`, and the property passes to the modules of the next layer.

## Main results

* `Stacks.Chow.exists_splittingMorphism_isProjective`: **Stacks 02UL.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance] SplittingMorphism.locallyOfFiniteType_π SplittingMorphism.flat_π

/-- The splitting tower with its projectivity, in the form the strong induction on
`∑ binom(r_i, 2)` proves: over a scheme `Y` with a projective morphism `g : Y ⟶ X` along which
every module is a twisted quotient of a pullback, the tower composed with `g` is projective. -/
private theorem exists_splittingMorphism_isProjective_aux (C : ChowSituation.{u}) :
    ∀ (n : ℕ) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (I : Type)
      [Fintype I] (E : I → Y.Modules) (r : I → ℕ),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) →
      ∑ i, (r i).choose 2 = n →
      ∀ {X : Scheme.{u}} (g : Y ⟶ X), IsProjective g →
        (∀ i, IsTwistedPullbackQuotient g (E i)) →
      ∃ T : SplittingMorphism C sY n, IsProjectiveBundleTower C sY n T ∧
        (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i)) ∧
        IsProjective (T.π ≫ g) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y sY _ I _ E r hE hn X g hg hTw
    by_cases hr : ∀ i, r i ≤ 1
    · -- every rank is at most one: the identity of `Y` is the empty tower
      have hn0 : n = 0 := by
        rw [← hn, Finset.sum_eq_zero]
        intro i _
        exact Nat.choose_eq_zero_of_lt (by have := hr i; omega)
      subst hn0
      refine ⟨SplittingMorphism.id C sY, IsProjectiveBundleTower.id (C := C) sY, fun i ↦ ?_, ?_⟩
      · exact Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one _ (r i)
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (𝟙 Y) (E i) (r i) (hE i))
          (hr i)
      · change IsProjective (𝟙 Y ≫ g)
        rw [Category.id_comp]
        exact hg
    -- some rank exceeds one: the bottom layer is the projective bundle of that module
    obtain ⟨i, hi⟩ := not_forall.mp hr
    obtain ⟨m, hm⟩ : ∃ m, r i = m + 1 + 1 := ⟨r i - 2, by omega⟩
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (m + 1 + 1) := hm ▸ hE i
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i) :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (E i)
        (m + 1 + 1)
    set D := projectiveBundleStep C sY (E i) m hEi with hDdef
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j)
        (Function.update r i (m + 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E j) (r j) (hE j)
    -- the bottom layer is projective over `X`, and the next modules are twisted quotients of
    -- pullbacks along it
    have hDproj : IsProjective (D.π ≫ g) := (hTw i).isProjective_bundleProj_comp hg
    have hTw' : ∀ j, IsTwistedPullbackQuotient (D.π ≫ g)
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j) := by
      intro j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        exact (hTw i).kernel_bundleTautological
      · rw [Function.update_of_ne hj]
        exact (hTw j).pullback D.π
    have hchoose : (m + 1).choose 2 + (m + 1) = (r i).choose 2 := by
      have key : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
        change Nat.choose (m + 1 + 1) (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        change m + 1 + Nat.choose (m + 1) 2 = Nat.choose (m + 1) 2 + (m + 1)
        omega
      rw [hm, key]
    have hA : (∑ j, (Function.update r i (m + 1) j).choose 2) =
        (m + 1).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ (Function.update r i (m + 1) j).choose 2) (Finset.mem_univ i),
        Function.update_self]
      exact congrArg _ (Finset.sum_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hB : (∑ j, (r j).choose 2) =
        (r i).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 :=
      (Finset.add_sum_erase Finset.univ (fun j ↦ (r j).choose 2) (Finset.mem_univ i)).symm
    have hsum : (∑ j, (Function.update r i (m + 1) j).choose 2) + (m + 1) = n := by
      rw [hA, ← hn, hB]; omega
    have hlt : (∑ j, (Function.update r i (m + 1) j).choose 2) < n := by omega
    obtain ⟨T, hTtower, hT, hTproj⟩ := ih _ hlt D.sP I
      (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub)
      (Function.update r i (m + 1)) hE' rfl (D.π ≫ g) hDproj hTw'
    subst hsum
    refine ⟨SplittingMorphism.compStep D T,
      IsProjectiveBundleTower.compStep (C := C) sY (E i) m hEi _ T hTtower, fun j ↦ ?_, ?_⟩
    · simp only [SplittingMorphism.compStep_P, SplittingMorphism.compStep_π]
      have comp₁ : (Scheme.Modules.pullback T.π).obj
            ((Scheme.Modules.pullback D.π).obj (E j)) ≅
          (Scheme.Modules.pullback (T.π ≫ D.π)).obj (E j) :=
        (Scheme.Modules.pullbackComp T.π D.π).app (E j)
      by_cases hj : j = i
      · rw [hj] at comp₁ ⊢
        rw [hm]
        have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
            (Scheme.Modules.pullback T.π)).ShortExact :=
          Stacks.WeilCohomology.shortExact_map_pullback T.π _ D.shortExact
        have hleft : Stacks.WeilCohomology.HasInvertibleFiltration T.P
            ((Scheme.Modules.pullback T.π).obj D.sub) (m + 1) := by
          simpa only [Function.update_self] using hT i
        have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Scheme.Modules.pullback T.π).obj
              ((Scheme.Modules.pullback D.π).obj (E i))) (m + 1 + 1) :=
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.π _ _
            (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E i) _ hEi)
        exact Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁
          (Stacks.WeilCohomology.HasInvertibleFiltration.step _ _ _ hDx
            (Stacks.WeilCohomology.isInvertible_pullback_obj T.π D.twistModule
              D.twistModule_isInvertible)
            hrank.isFiniteLocallyFree hleft)
      · refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
        simpa only [Function.update_of_ne hj] using hT j
    · rw [SplittingMorphism.compStep_π]
      exact (Category.assoc T.π D.π g).symm ▸ hTproj

/-- **Stacks 02UL (the splitting principle).** Let `(S, δ)` be as in Situation 02QL, `X` locally
of finite type over `S` and `ℰ_i` (`i ∈ I`, `I` finite) finite locally free `𝒪_X`-modules of
ranks `r_i`. There is a morphism `π : P ⟶ X` which is

* projective (Stacks 01W8), flat, and of relative dimension `d = ∑_i binom(r_i, 2)`,

such that

1. for every morphism `f : Y ⟶ X` with `Y` locally of finite type over `S`, the flat pullback
   `π_Y^* : CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` along the base change of `π` is injective for every
   `k` (`Stacks.Chow.UniversallyChowInjective`), and
2. each `π^*ℰ_i` has a filtration whose successive quotients `ℒ_{i,1}, …, ℒ_{i,r_i}` are
   invertible `𝒪_P`-modules;

moreover the restriction map `A^*(X) ⟶ A^*(P)` of Stacks 0B7F is injective. -/
@[stacks 02UL]
theorem exists_splittingMorphism_isProjective (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I] (E : I → X.Modules)
    (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      IsProjective T.π ∧ Flat T.π ∧
      AlgebraicGeometry.RelativeDimension T.π (∑ i, (r i).choose 2) ∧
      UniversallyChowInjective C T.π (∑ i, (r i).choose 2) T.relDim ∧
      (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i)) ∧
      ∀ (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso),
        Function.Injective (chowCohomologyTotalRestriction C G sX T.π hgys) := by
  have hTw : ∀ i, IsTwistedPullbackQuotient (𝟙 X) (E i) := fun i ↦ by
    have := (hE i).isFiniteLocallyFree
    have : (E i).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree (E i)
    exact isTwistedPullbackQuotient_id (E i)
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree (E i))
  obtain ⟨T, htower, hfilt, hproj⟩ :=
    exists_splittingMorphism_isProjective_aux C _ sX I E r hE rfl (𝟙 X) (isProjective_id X) hTw
  rw [Category.comp_id] at hproj
  exact ⟨T, hproj, inferInstance, T.relDim, htower.universallyChowInjective, hfilt,
    htower.chowCohomologyTotalRestriction_injective⟩

end Stacks.Chow

end
