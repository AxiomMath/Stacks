module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Profinite
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Vanishing along a four-term exact sequence of discrete modules

Let `G` be a topological group and let

`0 → A → M → M' → B → 0`

be an exact sequence of discrete `G`-modules, split into the two short exact sequences
`0 → A → M → C → 0` and `0 → C → M' → B → 0`. If the continuous cohomology of `A` and of `B`
vanishes in degrees `≥ 2` and that of `M'` vanishes in degrees `≥ 1`, then the continuous
cohomology of `M` vanishes in degrees `≥ 3`.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_of_fourTerm`: the statement for the
  higher right derived functors of an additive functor between abelian categories.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_iff_isZero_rightDerived`: continuous
  group cohomology vanishes exactly when the `ℕ`-indexed right derived functor of
  `continuousGModuleInvariants` does.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_fourTerm`: the statement for
  continuous group cohomology.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_fourTerm_rat`: the same for a
  profinite `G` when `M'` is a rational vector space, with no hypothesis on `M'` otherwise.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedDelta

universe v₁ v₂ u₁ u₂

variable {B : Type u₁} [Category.{v₁} B] [Abelian B] [EnoughInjectives B]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **Vanishing in degrees `≥ 3` along a four-term exact sequence.** Let `Q` be an additive
functor out of an abelian category with enough injectives, and let

`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` and `0 ⟶ Y₁ ⟶ Y₂ ⟶ Y₃ ⟶ 0`

be short exact sequences with `X₃ ≅ Y₁`, so that together they form a four-term exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ Y₂ ⟶ Y₃ ⟶ 0`. If `RⁿQ X₁ = 0` and `RⁿQ Y₃ = 0` for `n ≥ 2` and `RⁿQ Y₂ = 0` for
`n ≥ 1`, then `RⁿQ X₂ = 0` for `n ≥ 3`. -/
theorem isZero_rightDerived_of_fourTerm (Q : B ⥤ D) [Q.Additive]
    {S₁ S₂ : ShortComplex B} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁.X₃ ≅ S₂.X₁)
    (h₁ : ∀ q : ℕ, 2 ≤ q → IsZero ((Q.rightDerived q).obj S₁.X₁))
    (h₂ : ∀ q : ℕ, 1 ≤ q → IsZero ((Q.rightDerived q).obj S₂.X₂))
    (h₃ : ∀ q : ℕ, 2 ≤ q → IsZero ((Q.rightDerived q).obj S₂.X₃))
    (q : ℕ) (hq : 3 ≤ q) :
    IsZero ((Q.rightDerived q).obj S₁.X₂) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by lia⟩
  exact isZero_rightDerived_X₂ hS₁ Q _ (h₁ _ (by lia)) <|
    (Iso.isZero_iff ((Q.rightDerived (n + 1)).mapIso e)).2 <|
      isZero_rightDerived_succ_X₁ hS₂ Q n (h₃ n (by lia)) (h₂ (n + 1) (by lia))

end Stacks.Cohomology.RightDerivedDelta

namespace Stacks.GroupCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- `ℤ`-modules are regarded as topological spaces with the discrete topology. -/
local instance hasForget₂ModuleCatTopCatFourTerm : HasForget₂ (ModuleCat.{v} ℤ) TopCat.{v} :=
  { forget₂ := forget (ModuleCat.{v} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Continuous group cohomology vanishes exactly when the `ℕ`-indexed right derived functor of
invariants does.** -/
theorem isZero_continuousGroupCohomology_iff_isZero_rightDerived (q : ℕ)
    (M : ContinuousGModule.{u, max u v} G) :
    IsZero (continuousGroupCohomology.{u, v} G q M) ↔
      IsZero (((continuousGModuleInvariants.{u, max u v} G).rightDerived q).obj M) :=
  (Iso.isZero_iff ((Stacks.DerivedIndexing.rightDerivedIso
    (continuousGModuleInvariants.{u, max u v} G) q).app M)).symm

variable {G}

/-- **Vanishing of continuous group cohomology in degrees `≥ 3` along a four-term exact sequence
of discrete `G`-modules.** Given short exact sequences `0 → A → M → C → 0` and
`0 → C → M' → B → 0` of discrete `G`-modules — presented as `S₁`, `S₂` and an isomorphism
`S₁.X₃ ≅ S₂.X₁` — with

`H ^ q(G, A) = 0` and `H ^ q(G, B) = 0` for `q ≥ 2` and `H ^ q(G, M') = 0` for `q ≥ 1`,

one has `H ^ q(G, M) = 0` for every `q ≥ 3`. -/
theorem isZero_continuousGroupCohomology_of_fourTerm
    {S₁ S₂ : ShortComplex (ContinuousGModule.{u, max u v} G)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁.X₃ ≅ S₂.X₁)
    (h₁ : ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q S₁.X₁))
    (h₂ : ∀ q : ℕ, 1 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q S₂.X₂))
    (h₃ : ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q S₂.X₃))
    (q : ℕ) (hq : 3 ≤ q) :
    IsZero (continuousGroupCohomology.{u, v} G q S₁.X₂) := by
  refine (isZero_continuousGroupCohomology_iff_isZero_rightDerived G q S₁.X₂).2 ?_
  refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_of_fourTerm _ hS₁ hS₂ e
    ?_ ?_ ?_ q hq <;> intro q' hq' <;>
    refine (isZero_continuousGroupCohomology_iff_isZero_rightDerived G q' _).1 ?_
  exacts [h₁ q' hq', h₂ q' hq', h₃ q' hq']

/-- **The same with the hypothesis on the rational term discharged.** For a profinite `G`, if the
middle term of the second short exact sequence is a rational vector space, then
`H ^ q(G, M) = 0` for every `q ≥ 3` as soon as `H ^ q(G, A) = 0` and `H ^ q(G, B) = 0` for
`q ≥ 2`. -/
theorem isZero_continuousGroupCohomology_of_fourTerm_rat
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G)
    {S₁ S₂ : ShortComplex (ContinuousGModule.{u, max u v} G)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁.X₃ ≅ S₂.X₁)
    [Module ℚ S₂.X₂.1.1.V]
    (h₁ : ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q S₁.X₁))
    (h₃ : ∀ q : ℕ, 2 ≤ q → IsZero (continuousGroupCohomology.{u, v} G q S₂.X₃))
    (q : ℕ) (hq : 3 ≤ q) :
    IsZero (continuousGroupCohomology.{u, v} G q S₁.X₂) :=
  isZero_continuousGroupCohomology_of_fourTerm hS₁ hS₂ e h₁
    (fun q' hq' ↦ isZero_continuousGroupCohomology_of_module_rat.{u, v} G hG q' (by lia) S₂.X₂)
    h₃ q hq

end Stacks.GroupCohomology

end
