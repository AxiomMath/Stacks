module

public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionOfComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedFlatPullback

/-!
# Homogeneous completed classes

A class of the completed bivariant group `A^*(X ⟶ Y)^∧` of Stacks 0FE0 which is concentrated in
one degree `n` on every connected component of `X` is a homogeneous class `x ∈ A^n(X ⟶ Y)` read as
a completed class (`Stacks.Chow.BivariantClass.toCompleted`). This file shows that three classes
appearing in the blow up formula of Stacks 0FVA are of this form when the relevant rank or
relative dimension is constant:

* the top Chern class `c_top(ℰ)` of a finite locally free module of constant rank `s` is the
  Chern class `c_s(ℰ)` of Stacks 0ESW (`Stacks.Chow.topChernClassOfInvertible_eq_toCompleted`);

Composition of completed classes extends composition of homogeneous ones by
`Stacks.Chow.completedBivariantCompositeOfInvertible_toCompleted`.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section TopChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsLocallyNoetherian X] (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The top Chern class of a module of constant rank `s` is its `s`-th Chern class**, as a
completed class: if `ℰ` has rank `s` on every connected component of `X`, then
`c_top(ℰ) = c_s(ℰ)` in `A^*(X)^∧`. -/
theorem topChernClassOfInvertible_eq_toCompleted (s : ℕ)
    (hs : ∀ i, Scheme.Modules.rankOnConnectedComponent E i = s) :
    topChernClassOfInvertible C sX E =
      (totalChernOfFiniteLocallyFree C sX E s).toCompleted C := by
  funext i
  rw [BivariantClass.toCompleted_apply, topChernClassOfInvertible]
  have h := (topChernClassOfInvertible_rankStratum C sX E i).2
  rw [hs i] at h ⊢
  rw [topChernClassOfInvertible, hs i, DirectSum.of_eq_same] at h
  rw [h]

end TopChern

/-- Restriction along the identity, with the structure morphisms equal but written differently,
changes nothing. -/
theorem chowGroupRestrict_id_heq (C : ChowSituation.{u}) {T : Scheme.{u}} (sA sB : T ⟶ C.S)
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (h : 𝟙 T ≫ sA = sB) (k : ℤ)
    (x : chowGroup C sA k) : chowGroupRestrict C sA sB (𝟙 T) h k x ≍ x := by
  obtain rfl : sA = sB := by simpa using h
  rw [chowGroupRestrict_id]

section FlatPullback

variable (C : ChowSituation.{u}) {P Y : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : P ⟶ Y) [LocallyOfFiniteType g] [Flat g]
  (hg : g ≫ sY = sP) [IsLocallyNoetherian P] [IsLocallyNoetherian Y] (m : ℕ)
  (hm : AlgebraicGeometry.RelativeDimension g m)

omit [Flat g] in
include hm in
/-- If `g` has relative dimension `m`, so has its restriction to a connected component. -/
theorem relativeDimension_resConnectedComponent (a : _root_.ConnectedComponents P) :
    AlgebraicGeometry.RelativeDimension (g.resConnectedComponent a) m := by
  have h : AlgebraicGeometry.RelativeDimension ((P.connectedComponentOpens a).ι ≫ g) m := by
    have := AlgebraicGeometry.RelativeDimension.comp_of_flat (P.connectedComponentOpens a).ι g
      (relativeDimension_of_isOpenImmersion _) hm
    rwa [Nat.zero_add] at this
  exact AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion _
    (Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι _
    (Scheme.Hom.resConnectedComponent_comp_ι g a) h

/-- **The restriction of a flat pullback to a connected component** (Stacks 0FDZ and Stacks 0B78)
is the flat pullback of the restriction `P_a ⟶ Y_{a(i)}`: both cap by flat pullback along the
base change, and restriction to the open subscheme `P_a ×_{Y_{a(i)}} T` of `P ×_Y T` commutes with
flat pullback. -/
theorem bivariantConnectedComponentRestriction_flatPullbackBivariantClassOfInvertible
    (a : _root_.ConnectedComponents P) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sP sY g hg (-(m : ℤ))
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (flatPullbackBivariantClassOfInvertible C sP sY g hg m hm) a =
      flatPullbackBivariantClassOfInvertible C ((P.connectedComponentOpens a).ι ≫ sP)
        ((Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι ≫ sY)
        (g.resConnectedComponent a) (g.resConnectedComponent_comp_ι_comp hg a) m
        (relativeDimension_resConnectedComponent g m hm a) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} s _ k β ↦ ?_
  rw [bivariantConnectedComponentRestriction_cap]
  set ιY := (Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι
  set ga := g.resConnectedComponent a
  set u := opensPullbackComparison g (P.connectedComponentOpens a)
    (Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)) ga
    (Scheme.Hom.resConnectedComponent_comp_ι g a) s
  have hu : u ≫ pullback.snd g (s ≫ ιY) = pullback.snd ga s ≫ 𝟙 T := by
    rw [Category.comp_id]; exact opensPullbackComparison_snd _ _ _ _ _ _
  have hga := relativeDimension_resConnectedComponent g m hm a
  have key := chowGroupRestrict_flatPullbackChow_of_comm C _ _ _ _ (pullback.snd g (s ≫ ιY))
    (pullbackSnd_comp_structureMorphism hg (s ≫ ιY)) (pullback.snd ga s)
    (pullbackSnd_comp_structureMorphism (g.resConnectedComponent_comp_ι_comp hg a) s) u
    (by rw [← Category.assoc, opensPullbackComparison_fst, Category.assoc]) (𝟙 T)
    (by rw [Category.id_comp, Category.assoc]) hu m (relativeDimension_pullbackSnd g hm _)
    (relativeDimension_pullbackSnd ga hga s) k
    (chowGroupCongr C (Category.assoc s ιY sY).symm k β)
  refine eq_of_heq (HEq.trans (chowGroupRestrict_heq_of_heq C _ _ _ _ (by ring) _ _
    (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _) _ k _)) ?_)
  refine HEq.trans (heq_of_eq key) ?_
  refine HEq.trans ?_ (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _) s k β).symm
  refine flatPullbackChow_heq_congr C _ _ _ _ _ _ rfl rfl _ _ rfl _ _ _ _ ?_
  exact (chowGroupRestrict_id_heq C _ _ _ _ _).trans (chowGroupCongr_heq C _ _ _)

/-- **The completed flat pullback of a flat morphism of constant relative dimension `m`** is its
flat pullback class `g^* ∈ A^{-m}(P ⟶ Y)` (Stacks 0B78), read as a completed class. -/
theorem completedFlatPullback_eq_toCompleted
    (hrel : ∀ a : _root_.ConnectedComponents P,
      ∃ r : ℕ, AlgebraicGeometry.RelativeDimension (g.resConnectedComponent a) r) :
    completedFlatPullback C sP sY g hg hrel =
      (flatPullbackBivariantClassOfInvertible C sP sY g hg m hm).toCompleted C := by
  funext a
  rw [completedFlatPullback_apply_of_relativeDimension C sP sY g hg hrel a m
      (relativeDimension_resConnectedComponent g m hm a), BivariantClass.toCompleted_apply,
    bivariantConnectedComponentRestriction_flatPullbackBivariantClassOfInvertible]

/-- **The completed flat pullback of a smooth morphism of constant relative dimension `m`** is its
flat pullback class `g^* ∈ A^{-m}(P ⟶ Y)`, read as a completed class. -/
theorem completedFlatPullbackOfSmooth_eq_toCompleted [Smooth g] :
    completedFlatPullbackOfSmooth C sP sY g hg =
      (flatPullbackBivariantClassOfInvertible C sP sY g hg m hm).toCompleted C := by
  rw [completedFlatPullbackOfSmooth_eq_completedFlatPullback C sP sY g hg
      (fun a ↦ ⟨m, relativeDimension_resConnectedComponent g m hm a⟩)]
  exact completedFlatPullback_eq_toCompleted C sP sY g hg m hm _

end FlatPullback

end Stacks.Chow

end
