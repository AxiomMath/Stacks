module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumOfLocallyGivenObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.KInjectiveRepresentativesOnAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedExhaustion

/-!
# Glueing locally given derived objects over a well ordered increasing cover

Let `(X, 𝒪_X)` be a ringed space, let `E` be a well ordered set and let `X = ⋃_{α ∈ E} W_α` be
an open covering with `W_α ⊆ W_{α+1}` and `W_α = ⋃_{β < α} W_β` when `α` is not a successor.
Let `K_α` be an object of `D(𝒪_{W_α})` with `Ext^i(K_α, K_α) = 0` for `i < 0`, and let
`ρ^α_β : K_α|_{W_β} → K_β` be isomorphisms for `β < α` satisfying `ρ^α_γ = ρ^β_γ ∘ ρ^α_β|_{W_γ}`
for `γ < β < α`. Then there is an object `K` of `D(𝒪_X)` and isomorphisms `K|_{W_α} → K_α`
compatible with the `ρ^α_β`.

This file reduces the statement to the glueing property
`Stacks.DerivedGlueing.GluesAlongWellOrderedCover`, in which the identifications of the
restrictions of the glued object are required to be compatible with the prescribed transitions
only at the stages of a cofinal family, and proves facts about chains of opens.

## Main definitions

* `Stacks.DerivedGlueing.GluesAlongWellOrderedCover`: the glueing property over a well ordered
  increasing cover, with the compatibility of the identifications required only cofinally.

## Main results

* `Stacks.DerivedGlueing.inf_eq_sSup_of_totallyOrdered`: in a collection of opens totally ordered
  by inclusion, the intersection of two members is the union of the members contained in it.
* `Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self_of_totallyOrdered` and
  `Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self_of_wellOrderedCover`: the global
  object of a solution of a system whose displayed opens are totally ordered by inclusion and
  cover `X` has no negative self-Ext.
* `Stacks.DerivedGlueing.le_of_succ_of_limit`: a cover increasing at the successors and
  continuous at the other stages is increasing along every pair of stages.
* `Stacks.DerivedGlueing.compatibility_of_lt`: identifications of the restrictions of a glued
  object compatible with the prescribed transitions at a stage `γ` are compatible with them at
  every pair of stages below `γ`.
* `Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover_of_gluesAlong`: the glued object of
  [Stacks, Tag 0D6B], with compatibility at every pair of stages, from
  `Stacks.DerivedGlueing.GluesAlongWellOrderedCover`.
* `Stacks.DerivedGlueing.totallyOrdered_range_of_wellOrderedCover`: the stages of an increasing
  cover are totally ordered by inclusion.
* `Stacks.DerivedGlueing.exists_wellOrderedCover_opens`: every covering collection of opens is
  exhausted by a well ordered increasing cover, with the stages a chain, each stage a union of
  members and each member inside a stage.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe v u

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Collections of opens totally ordered by inclusion -/

/-- If any two members of a collection of opens are comparable, then the intersection of two
members is the union of the members contained in it. -/
theorem inf_eq_sSup_of_totallyOrdered (ℬ : Set (Opens X.carrier))
    (hchain : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ≤ V ∨ V ≤ U) (U V : Opens X.carrier) (hU : U ∈ ℬ)
    (hV : V ∈ ℬ) :
    U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V} := by
  refine le_antisymm ?_ (sSup_le fun W hW => hW.2)
  rcases hchain U hU V hV with h | h
  · exact inf_le_left.trans (le_sSup ⟨hU, le_inf le_rfl h⟩)
  · exact inf_le_right.trans (le_sSup ⟨hV, le_inf h le_rfl⟩)

/-- Let `S` be a system of locally given derived objects whose displayed opens cover `X`, any two
of them comparable, and whose prescribed local objects have no negative self-Ext. Then the global
object of a solution of `S` has no negative self-Ext. -/
theorem Solution.subsingleton_shiftedHom_self_of_totallyOrdered {S : LocallyGiven X}
    (A : Solution S) (hcover : sSup S.opens = ⊤)
    (hchain : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ≤ V ∨ V ≤ U)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom A.obj A.obj i) :=
  A.subsingleton_shiftedHom_self hcover
    (fun U hU V hV => inf_eq_sSup_of_totallyOrdered S.opens hchain U V hU hV) hExt i hi

/-! ### Increasingness, from the source's hypothesis at the successors -/

/-- Let `W` be a family of opens indexed by a well ordered set, with `W_β ⊆ W_α` whenever `β` is
the immediate predecessor of `α` (`β < α`, and every `γ < α` satisfies `γ ≤ β`), and
`W_α = ⋃_{β < α} W_β` when `α` has no immediate predecessor. Then `W_β ⊆ W_α` for every pair
`β < α`. -/
theorem le_of_succ_of_limit {E : Type v} [LinearOrder E] [WellFoundedLT E]
    (W : E → Opens X.carrier)
    (hsucc : ∀ β α : E, β < α → (∀ γ : E, γ < α → γ ≤ β) → W β ≤ W α)
    (hlimit : ∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
      W α = ⨆ (β : E) (_ : β < α), W β) :
    ∀ β α : E, β < α → W β ≤ W α := by
  intro β α
  induction α using WellFoundedLT.induction generalizing β with
  | ind α ih =>
    intro hβα
    by_cases hα : ∃ δ : E, δ < α ∧ ∀ γ : E, γ < α → γ ≤ δ
    · obtain ⟨δ, hδα, hδ⟩ := hα
      rcases eq_or_lt_of_le (hδ β hβα) with rfl | hβδ
      · exact hsucc β α hβα hδ
      · exact (ih δ hδα β hβδ).trans (hsucc δ α hδα hδ)
    · rw [hlimit α hα]
      exact le_iSup₂_of_le β hβα le_rfl

/-! ### Compatibility of the glued identifications descends from a larger stage -/

/-- Let `σ_α : K|_{W_α} ≅ K_α` be identifications of the restrictions of an object `K` with the
prescribed objects. If `σ` is compatible with `ρ^γ_β` and with `ρ^γ_α` for some `γ` above `α`,
then it is compatible with `ρ^α_β`. -/
theorem compatibility_of_lt {S : LocallyGiven X}
    {E : Type v} [LinearOrder E] (W : E → Opens X.carrier)
    (hmono : ∀ β α : E, β < α → W β ≤ W α) (K : ∀ α : E, OpenDerivedCategory X (W α))
    (rho : ∀ (β α : E) (h : β < α), (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ) (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom)
    (G : OpenDerivedCategory X ⊤)
    (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α) {β α γ : E} (hβα : β < α)
    (hαγ : α < γ)
    (hβ : (S.restrictionComp (W β) (W γ) ⊤ (hmono β γ (hβα.trans hαγ)) le_top).hom.app G ≫
      (S.restriction (W β) (W γ) (hmono β γ (hβα.trans hαγ))).map (sigma γ).hom ≫
        (rho β γ (hβα.trans hαγ)).hom = (sigma β).hom)
    (hα : (S.restrictionComp (W α) (W γ) ⊤ (hmono α γ hαγ) le_top).hom.app G ≫
      (S.restriction (W α) (W γ) (hmono α γ hαγ)).map (sigma γ).hom ≫ (rho α γ hαγ).hom =
        (sigma α).hom) :
    (S.restrictionComp (W β) (W α) ⊤ (hmono β α hβα) le_top).hom.app G ≫
        (S.restriction (W β) (W α) (hmono β α hβα)).map (sigma α).hom ≫ (rho β α hβα).hom =
      (sigma β).hom := by
  rw [← hα, ← hβ, hcocycle β α γ hβα hαγ]
  simp only [Functor.map_comp, Category.assoc]
  rw [(S.restrictionComp (W β) (W α) (W γ) (hmono β α hβα)
    (hmono α γ hαγ)).hom.naturality_assoc (sigma γ).hom]
  simp only [Functor.comp_map]
  rw [← reassoc_of% S.restrictionComp_pentagon (W β) (W α) (W γ) ⊤ (hmono β α hβα)
    (hmono α γ hαγ) le_top G]

/-! ### The glueing property over a well ordered increasing cover -/

/-- The glueing property over a well ordered increasing cover, checked cofinally: a well ordered
increasing open covering of `X`, a prescribed object of the derived category on each member
without negative self-Ext, and compatible transition isomorphisms between them, admit a glued
object together with identifications of its restrictions with the prescribed objects whose
compatibility with the prescribed transitions holds at the stages of a cofinal family. -/
def GluesAlongWellOrderedCover (S : LocallyGiven X) : Prop :=
  ∀ (E : Type v) [LinearOrder E] [WellFoundedLT E] (W : E → Opens X.carrier)
    (hmono : ∀ β α : E, β < α → W β ≤ W α),
    (∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
        W α = ⨆ (β : E) (_ : β < α), W β) →
      (⨆ α : E, W α) = ⊤ →
      ∀ (K : ∀ α : E, OpenDerivedCategory X (W α)),
        (∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i)) →
        ∀ (rho : ∀ (β α : E) (h : β < α),
            (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β),
          (∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
              (rho γ α (hγβ.trans hβα)).hom =
                (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
                    (hmono β α hβα)).hom.app (K α) ≫
                  (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
                    (rho γ β hγβ).hom) →
            ∃ (G : OpenDerivedCategory X ⊤)
              (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α) (A : Set E),
              (∀ α : E, ∃ γ ∈ A, α ≤ γ) ∧
                ∀ (β γ : E) (h : β < γ), γ ∈ A →
                  (S.restrictionComp (W β) (W γ) ⊤ (hmono β γ h) le_top).hom.app G ≫
                      (S.restriction (W β) (W γ) (hmono β γ h)).map (sigma γ).hom ≫
                        (rho β γ h).hom =
                    (sigma β).hom

/-! ### Tag 0D6B -/

/-- Assume the glueing property `Stacks.DerivedGlueing.GluesAlongWellOrderedCover S`. Let `E` be
a well ordered set and let `X = ⋃_{α ∈ E} W_α` be an open covering with `W_β ⊆ W_α` when `β` is
the immediate predecessor of `α`, and `W_α = ⋃_{β < α} W_β` when `α` is not a successor. Let
`K_α` be an object of `D(𝒪_{W_α})` with `Ext^i(K_α, K_α) = 0` for `i < 0`, and let
`ρ^α_β : K_α|_{W_β} ≅ K_β` for `β < α` satisfy `ρ^α_γ = ρ^β_γ ∘ ρ^α_β|_{W_γ}` for `γ < β < α`.
Then there is an object `K` of `D(𝒪_X)` and isomorphisms `K|_{W_α} ≅ K_α` compatible with the
`ρ^α_β`. -/
theorem exists_glueing_of_wellOrderedCover_of_gluesAlong (S : LocallyGiven X)
    (hglue : GluesAlongWellOrderedCover.{v} S)
    (E : Type v) [LinearOrder E] [WellFoundedLT E]
    (W : E → Opens X.carrier)
    (hsucc : ∀ β α : E, β < α → (∀ γ : E, γ < α → γ ≤ β) → W β ≤ W α)
    (hlimit : ∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
      W α = ⨆ (β : E) (_ : β < α), W β)
    (hcover : (⨆ α : E, W α) = ⊤) (K : ∀ α : E, OpenDerivedCategory X (W α))
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (le_of_succ_of_limit W hsucc hlimit β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (le_of_succ_of_limit W hsucc hlimit γ β hγβ)
            (le_of_succ_of_limit W hsucc hlimit β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β)
            (le_of_succ_of_limit W hsucc hlimit γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom) :
    ∃ (G : OpenDerivedCategory X ⊤)
      (sigma : ∀ α : E, (S.restriction (W α) ⊤ le_top).obj G ≅ K α),
      ∀ (β α : E) (h : β < α),
        (S.restrictionComp (W β) (W α) ⊤
              (le_of_succ_of_limit W hsucc hlimit β α h) le_top).hom.app G ≫
            (S.restriction (W β) (W α)
              (le_of_succ_of_limit W hsucc hlimit β α h)).map (sigma α).hom ≫ (rho β α h).hom =
          (sigma β).hom := by
  obtain ⟨G, sigma, A, hA, hcompat⟩ :=
    hglue E W (le_of_succ_of_limit W hsucc hlimit) hlimit hcover K hExt rho hcocycle
  refine ⟨G, sigma, fun β α h => ?_⟩
  obtain ⟨γ, hγA, hαγ⟩ := hA α
  rcases eq_or_lt_of_le hαγ with rfl | hαγ
  · exact hcompat β α h hγA
  · exact compatibility_of_lt W (le_of_succ_of_limit W hsucc hlimit) K rho hcocycle G sigma h hαγ
      (hcompat β γ (h.trans hαγ) hγA) (hcompat α γ hαγ hγA)

/-- The members of a family of opens `W` indexed by a linear order, with `W β ≤ W α` for
`β < α`, are totally ordered by inclusion. -/
theorem totallyOrdered_range_of_wellOrderedCover {E : Type v} [LinearOrder E]
    (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α) :
    ∀ U ∈ Set.range W, ∀ V ∈ Set.range W, U ≤ V ∨ V ≤ U := by
  rintro U ⟨β, rfl⟩ V ⟨α, rfl⟩
  rcases lt_trichotomy β α with h | rfl | h
  · exact Or.inl (hmono β α h)
  · exact Or.inl le_rfl
  · exact Or.inr (hmono α β h)

/-- Let `𝒞` be a collection of opens covering `X`. Then there are a well ordered index set `E`
and a family `W : E → Opens X` with

* `W β ≤ W α` for every `β < α`;
* `W α = ⨆_{β < α} W β` at every stage with no immediate predecessor;
* `⨆_α W α = ⊤`;
* the stages totally ordered by inclusion;
* each stage the union of the members of `𝒞` it contains;
* each member of `𝒞` inside a single stage. -/
theorem exists_wellOrderedCover_opens (𝒞 : Set (Opens X.carrier)) (hcover : sSup 𝒞 = ⊤) :
    ∃ (E : Type u) (_ : LinearOrder E) (_ : WellFoundedLT E) (W : E → Opens X.carrier),
      (∀ β α : E, β < α → W β ≤ W α) ∧
        (∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
            W α = ⨆ (β : E) (_ : β < α), W β) ∧
          (⨆ α : E, W α) = ⊤ ∧
            (∀ U ∈ Set.range W, ∀ V ∈ Set.range W, U ≤ V ∨ V ≤ U) ∧
              (∀ α : E, W α = sSup {V | V ∈ 𝒞 ∧ V ≤ W α}) ∧
                ∀ V ∈ 𝒞, ∃ α : E, V ≤ W α := by
  obtain ⟨E, hlin, hwf, W, hmono, hlimit, htop, hstage, hmem⟩ :=
    exists_wellOrderedCover_of_sSup_eq_top 𝒞 hcover
  exact ⟨E, hlin, hwf, W, hmono, hlimit, htop,
    totallyOrdered_range_of_wellOrderedCover W hmono, hstage, hmem⟩

/-- Let `S` be a system of locally given derived objects whose displayed opens are those of a
family `W` with `W β ≤ W α` for `β < α` covering `X`, and whose prescribed local objects have no
negative self-Ext. Then the global object of a solution of `S` has no negative self-Ext. -/
theorem Solution.subsingleton_shiftedHom_self_of_wellOrderedCover {S : LocallyGiven X}
    {E : Type v} [LinearOrder E] (W : E → Opens X.carrier)
    (hmono : ∀ β α : E, β < α → W β ≤ W α) (hopens : S.opens = Set.range W)
    (hcover : (⨆ α : E, W α) = ⊤) (A : Solution S)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom A.obj A.obj i) := by
  refine A.subsingleton_shiftedHom_self_of_totallyOrdered ?_ ?_ hExt i hi
  · rwa [hopens, sSup_range]
  · rw [hopens]
    exact totallyOrdered_range_of_wellOrderedCover W hmono

end Stacks.DerivedGlueing

end
