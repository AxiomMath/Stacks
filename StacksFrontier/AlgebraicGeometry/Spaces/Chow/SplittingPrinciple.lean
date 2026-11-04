module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleHyperplaneCharts

/-!
# The splitting principle

In Situation 0EDT let `X/B` be good and let `ℰ_i` be a finite collection of finite locally free
`𝒪_X`-modules of ranks `r_i`. There is a projective flat morphism `π : P ⟶ X` of some relative
dimension `d` such that the flat pullback `π_Y^* : CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` is injective for
every morphism `Y ⟶ X` of good algebraic spaces over `B`, and such that every `π^*ℰ_i` has a
filtration whose successive quotients are invertible `𝒪_P`-modules.

The proof is the one of the source: induction on the ranks, replacing `X` by the projective
bundle `𝐏(ℰ_i)` of one of the modules, on which the tautological quotient `π^*ℰ_i ⟶ 𝒪(1)` splits
off an invertible quotient with a kernel of rank one less. Each step keeps the injectivity of the
flat pullback after every base change, by the injectivity half of Stacks 0ERV for projective
bundles, which is the top-degree case of Stacks 0ERU: for `α ∈ Z_k(Y)`,
`q_*(c₁(𝒪(1))^{s} ∩ q^*α) ∼_rat α` on `Y ×_X 𝐏(ℰ)`. That identity is proved on étale charts over
which the bundle is `ℙ^s` of an affine scheme, where the coordinate hyperplanes cut a chain of
effective Cartier divisors ending in a section.

## Main results

* `AlgebraicGeometry.Space.exists_projectiveBundleTower_hasInjectiveChowPullbacks_filtration`:
  Stacks 0ESC.

## Implementation notes

Projective morphisms of algebraic spaces are not defined in the source; the morphism `π` is a
finite composite of projective bundle projections,
`AlgebraicGeometry.Space.PrivateChern.IsProjectiveBundleTower`, which is the morphism the proof
of the source constructs. The Chow groups are those whose rational equivalences are indexed by
families in the universe `u + 1` of the integral closed subspaces of the spaces involved.

## References

* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space.PrivateChern

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})

attribute [local instance 10000] smallEtaleModulesAbelian abelian_modules hasZeroObject_modules
  hasInitial_modules initialMonoClass_modules hasCokernels_modules in
/-- **Stacks 0ESC, the splitting principle.** Let `X/B` be good and `ℰ_i`, `i ∈ ι` finite, finite
locally free `𝒪_X`-modules of ranks `r_i`. There are a good algebraic space `P/B` and a morphism
`π : P ⟶ X` over `B`, flat of some relative dimension `d` and a finite composite of projective
bundle projections, such that

* for every morphism `Y ⟶ X` of good algebraic spaces over `B` the flat pullback
  `CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` is injective (`HasInjectiveChowPullbacks`), and
* every `π^*ℰ_i` has a filtration `0 = F_0 ⊆ F_1 ⊆ ⋯ ⊆ F_{r_i} = π^*ℰ_i` by subobjects whose
  successive quotients `F_{j+1}/F_j` are invertible `𝒪_P`-modules.

The Chow groups are those whose rational equivalences are indexed by families in
the universe `u + 1` of the integral closed subspaces of the spaces involved, which is the universe
in which rational equivalence on algebraic spaces over the universe-`u` site is defined. -/
@[stacks 0ESC]
theorem exists_projectiveBundleTower_hasInjectiveChowPullbacks_filtration
    {ι : Type*} [Finite ι] (X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ι → ℕ)
    (hE : ∀ i, PrivateChern.IsFiniteLocallyFreeOfRank D sX hX (E i) (r i)) :
    ∃ (P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sP : P ⟶ D.space)
      (hP : D.IsGood sP) (π : P ⟶ X) (hπ : π ≫ sX = sP)
      (d : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
      (hd : HasRelativeDimension d D.site D.base D.base_mem π),
      IsProjectiveBundleTower π ∧ HasInjectiveChowPullbacks.{u + 1} D sX hX sP hP π hπ d hflat hd ∧
        ∀ i, ∃ (F : Fin (r i + 1) → Subobject ((spaceModulePullback D hX.1 hP.1 π).obj (E i)))
          (hF : Monotone F), F 0 = ⊥ ∧ F (Fin.last (r i)) = ⊤ ∧
            ∀ j : Fin (r i), IsInvertibleModule ⟨P, hP.1⟩
              (cokernel (Subobject.ofLE (F j.castSucc) (F j.succ) (hF j.castSucc_le_succ))) :=
  exists_projectiveBundleTower_filtration D
    (fun _ _ E s hE => hasInjectiveChowBaseChange_projectiveBundleDatum D E s hE) X sX hX E r hE

end AlgebraicGeometry.Space

end
