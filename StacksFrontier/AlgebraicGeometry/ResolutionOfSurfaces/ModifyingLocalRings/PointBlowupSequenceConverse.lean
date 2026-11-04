module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.LocalSchemesFpqcCover.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupCorrespondence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalenceSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequenceSupplement

/-!
# Globalizing sequences of blowups at closed points

Let `S` be a scheme with finitely many pairwise distinct closed points `s i` whose open
complement `U` is quasi-compact, and let `F` be the base-change functor of [Stacks, Tag 0BFU]
from finitely presented morphisms to `S` that are isomorphisms over `U` to the product of the
corresponding categories over the local schemes `S_i = Spec 𝒪_{S, s i}`.

A morphism to `S` which factors as a finite sequence of blowups at closed points lying over the
`s i` localizes to such a sequence over each `S_i`; that is the necessity direction of
[Stacks, Tag 0BFY], proved in
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence`.
This file proves the converse: an object of the source category of `F` whose localizations all
factor as such sequences factors as such a sequence itself.

## Main results

* `AlgebraicGeometry.nonempty_pullbackBlowUpToBaseOverIso` identifies the base change of a
  blowup along a flat morphism of the base with the blowup in the inverse image of the centre,
  and `AlgebraicGeometry.nonempty_pullbackBlowUpOverIsoOfMiss` is its degenerate case: base
  changing a blowup at a closed point along a morphism whose image avoids that point changes
  nothing.
* `FinitePresentationAwayPointsSituation.exists_factorsAsPointBlowups_of_localChain`
  descends one local sequence, and
  `FinitePresentationAwayPointsSituation.exists_factorsAsPointBlowups_of_forall_local`
  concatenates all of them into a single global sequence with the prescribed localizations.
* `FinitePresentationAwayPointsSituation.isIso_pullback_hom_of_factorsAsPointBlowups`
  and
  `FinitePresentationAwayPointsSituation.finitePresentation_of_factorsAsPointBlowups`
  show that the global sequence is a finitely presented morphism which is an isomorphism over the
  open complement.
* `FinitePresentationAwayPointsSituation.factorsAsPointBlowups_of_forall_corresponds`
  is the sufficiency direction of [Stacks, Tag 0BFY], and
  `FinitePresentationAwayPointsSituation.factorsAsPointBlowups_iff_forall_corresponds`
  is the equivalence of [Stacks, Tag 0BFY].

## Implementation notes

Sufficiency uses the full faithfulness of `F`, which is part of [Stacks, Tag 0BFV],
`AlgebraicGeometry.finitePresentationAwayPointsBaseChange_isEquivalence_unconditional`.

## References

* [Stacks Project, Tag 0BFY](https://stacks.math.columbia.edu/tag/0BFY)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.ResolutionOfSurfaces

/-! ### Base change of a blowup along a flat morphism of the base -/

/-- Base change of a blowup along a flat morphism of the base: blowing up `A` in `I` and then
restricting to `T` is blowing up `A ×_S T` in the inverse image of `I`. -/
theorem nonempty_pullbackBlowUpToBaseOverIso {S T A : Scheme.{u}} (p : A ⟶ S) (g : T ⟶ S)
    [Flat g] (I : A.IdealSheafData) :
    Nonempty ((Over.pullback g).obj (Over.mk (blowUpToBase I ≫ p)) ≅
      Over.mk (blowUpToBase (I.comap (pullback.fst p g)) ≫ pullback.snd p g)) := by
  obtain ⟨b, hb⟩ := exists_isPullback_blowUpToBase_comap (pullback.fst p g) I
  refine ⟨Over.isoMk ((pullbackRightPullbackFstIso p g (blowUpToBase I)).symm ≪≫
    hb.flip.isoPullback.symm) ?_⟩
  have hinv : hb.flip.isoPullback.inv ≫ blowUpToBase (I.comap (pullback.fst p g)) =
      pullback.snd (blowUpToBase I) (pullback.fst p g) := by
    rw [Iso.inv_comp_eq]
    exact hb.flip.isoPullback_hom_snd.symm
  show ((pullbackRightPullbackFstIso p g (blowUpToBase I)).inv ≫ hb.flip.isoPullback.inv) ≫
      blowUpToBase (I.comap (pullback.fst p g)) ≫ pullback.snd p g =
    pullback.snd (blowUpToBase I ≫ p) g
  rw [Category.assoc, ← Category.assoc hb.flip.isoPullback.inv, hinv]
  exact pullbackRightPullbackFstIso_inv_snd_snd p g (blowUpToBase I)

/-- The inverse image of the ideal sheaf of a reduced closed point has empty support along a
morphism whose image avoids that point. -/
theorem support_comap_vanishingIdeal_singleton_eq_empty {A P : Scheme.{u}} (q : P ⟶ A) (x : A)
    (hx : IsClosed ({x} : Set A)) (hmiss : ∀ z : P, q z ≠ x) :
    (((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds A)).comap q).support :
      Set P) = ∅ := by
  rw [Scheme.IdealSheafData.support_comap]
  show q ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds A)).support :
    Set A) = ∅
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact Set.eq_empty_of_forall_notMem fun z hz => hmiss z hz

/-- Base change of a blowup at a closed point along a flat morphism of the base whose image
avoids that point: nothing happens. -/
theorem nonempty_pullbackBlowUpOverIsoOfMiss {S T A : Scheme.{u}} (p : A ⟶ S) (g : T ⟶ S)
    [Flat g] (x : A) (hx : IsClosed ({x} : Set A))
    (hmiss : ∀ z : ↥(pullback p g), pullback.fst p g z ≠ x) :
    Nonempty ((Over.pullback g).obj
        (Over.mk (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{x}, hx⟩ : Closeds A)) ≫ p)) ≅
      (Over.pullback g).obj (Over.mk p)) := by
  have hiso := isIso_blowUpToBase_of_support_eq_empty
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds A)).comap (pullback.fst p g))
    (support_comap_vanishingIdeal_singleton_eq_empty (pullback.fst p g) x hx hmiss)
  obtain ⟨e⟩ := nonempty_pullbackBlowUpToBaseOverIso p g
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds A))
  exact ⟨e ≪≫ Over.isoMk (asIso (blowUpToBase ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : Closeds A)).comap (pullback.fst p g)))) rfl⟩

/-- An equality of ideal sheaves identifies the blowups it defines, over a common base. -/
theorem nonempty_blowUpOverIso_congr {P T : Scheme.{u}} {I J : P.IdealSheafData} (h : I = J)
    (r : P ⟶ T) :
    Nonempty (Over.mk (blowUpToBase I ≫ r) ≅ Over.mk (blowUpToBase J ≫ r)) := by
  cases h
  exact ⟨Iso.refl _⟩

/-- Transporting a blowup at a closed point along an isomorphism of the blown-up scheme. -/
theorem nonempty_blowUpOverIso_of_isIso {X Y T : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (t : Y ⟶ T)
    (r : X ⟶ T) (hr : f ≫ t = r) (y : Y) (hy : IsClosed ({y} : Set Y)) (x : X) (hxy : f x = y) :
    ∃ hx : IsClosed ({x} : Set X),
      Nonempty (Over.mk (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{x}, hx⟩ : Closeds X)) ≫ r) ≅
        Over.mk (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{y}, hy⟩ : Closeds Y)) ≫ t)) := by
  obtain ⟨hx, hcomap⟩ := vanishingIdeal_singleton_comap_of_isIso f y hy x hxy
  refine ⟨hx, ?_⟩
  obtain ⟨d, hd⟩ := exists_blowUp_iso_comap_of_isIso f
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))
  obtain ⟨c⟩ := nonempty_blowUpOverIso_congr hcomap.symm r
  refine ⟨c ≪≫ Over.isoMk d ?_⟩
  show d.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hy⟩ : Closeds Y)) ≫ t =
    blowUpToBase ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f) ≫ r
  rw [← Category.assoc, hd, Category.assoc, hr]

/-! ### Descending a local sequence of blowups -/

/-- The underlying morphism of an isomorphism in an over category is an isomorphism. -/
private theorem isIso_left_of_overIso {T : Scheme.{u}} {X Y : Over T} (e : X ≅ Y) :
    IsIso e.hom.left := by
  show IsIso ((Over.forget T).map e.hom)
  infer_instance

/-- The two projections of a fibre product agree after composing to the base, pointwise. -/
private theorem apply_pullback_fst_eq_apply_snd {A T S : Scheme.{u}} (p : A ⟶ S) (g : T ⟶ S)
    (y : ↥(pullback p g)) : p (pullback.fst p g y) = g (pullback.snd p g y) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

namespace FinitePresentationAwayPointsSituation

/-- Blowing up a global object at a closed point lying over the `i`th distinguished point leaves
the localization at any other distinguished point unchanged. -/
theorem nonempty_pullbackBlowUpOverIso_of_ne (D : FinitePresentationAwayPointsSituation.{u})
    {i j : Fin D.n} (hij : i ≠ j) (A : Over D.S) (x : A.left)
    (hx : IsClosed ({x} : Set A.left)) (hxs : A.hom x = D.points i) :
    Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points j))).obj
        (Over.mk (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{x}, hx⟩ : Closeds A.left)) ≫ A.hom)) ≅
      (Over.pullback (D.S.fromSpecStalk (D.points j))).obj A) := by
  refine nonempty_pullbackBlowUpOverIsoOfMiss A.hom (D.S.fromSpecStalk (D.points j)) x hx ?_
  intro y hy
  refine D.fromSpecStalk_ne_points (Ne.symm hij)
    (pullback.snd A.hom (D.S.fromSpecStalk (D.points j)) y) ?_
  rw [← hxs, ← hy]
  exact (apply_pullback_fst_eq_apply_snd _ _ y).symm

/-- **Stacks Project, Tag 0BFY**, the descent of one local sequence. Let `A` be a morphism to `S`
factoring as a finite sequence of blowups at closed points lying over the distinguished points,
whose localization at the `i`th distinguished point is the identity. Every sequence of blowups at
closed points of `Spec 𝒪_{S, s i}` lying over its closed point is the localization at `s i` of a
longer such global sequence, which moreover leaves every other localization unchanged. -/
theorem exists_factorsAsPointBlowups_of_localChain
    (D : FinitePresentationAwayPointsSituation.{u}) (i : Fin D.n) {A₀ : Over D.S}
    (hA₀ : FactorsAsPointBlowups D.S (Set.range D.points) A₀.left A₀.hom)
    (e₀ : Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A₀ ≅
      Over.mk (𝟙 (D.localScheme i))))
    {LZ : Scheme.{u}} {lz : LZ ⟶ D.localScheme i}
    (h : Stacks.ResolutionOfSurfaces.PointBlowupChain (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} LZ lz) :
    ∃ A : Over D.S,
      FactorsAsPointBlowups D.S (Set.range D.points) A.left A.hom ∧
      Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A ≅ Over.mk lz) ∧
      ∀ j, j ≠ i → Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points j))).obj A ≅
        (Over.pullback (D.S.fromSpecStalk (D.points j))).obj A₀) := by
  induction h with
  | refl => exact ⟨A₀, hA₀, e₀, fun j _ => ⟨Iso.refl _⟩⟩
  | @step W wmap hchain z hz hzT ih =>
    obtain ⟨A, hA, ⟨eA⟩, hother⟩ := ih
    have hleft : IsIso eA.hom.left := isIso_left_of_overIso eA
    have hw : eA.hom.left ≫ wmap = pullback.snd A.hom (D.S.fromSpecStalk (D.points i)) :=
      Over.w eA.hom
    let eAiso := asIso eA.hom.left
    let z' : ↥(pullback A.hom (D.S.fromSpecStalk (D.points i))) := eAiso.inv z
    have heAz : eAiso.hom z' = z := by simp [z']
    have hz'closed : IsClosed ({z'} : Set ↥(pullback A.hom
        (D.S.fromSpecStalk (D.points i)))) := by
      have hset : ({z'} : Set ↥(pullback A.hom (D.S.fromSpecStalk (D.points i)))) =
          eAiso.hom ⁻¹' ({z} : Set W) := by
        ext y
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun hy => by rw [hy]; exact heAz,
          fun hy => eAiso.hom.isEmbedding.injective (hy.trans heAz.symm)⟩
      rw [hset]
      exact hz.preimage eAiso.hom.continuous
    have hsnd : pullback.snd A.hom (D.S.fromSpecStalk (D.points i)) z' =
        IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)) := by
      have := congrArg (fun k : (pullback A.hom (D.S.fromSpecStalk (D.points i)) ⟶
        D.localScheme i) => k.base z') hw
      rw [← this]
      show wmap (eAiso.hom z') = _
      rw [heAz]
      exact Set.mem_singleton_iff.mp hzT
    have hxclosed := isClosed_singleton_pullbackFst_fromSpecStalk A.hom (D.points i)
      (D.points_closed i) z' hz'closed hsnd
    have hxs : A.hom (pullback.fst A.hom (D.S.fromSpecStalk (D.points i)) z') = D.points i := by
      rw [apply_pullback_fst_eq_apply_snd, hsnd, Scheme.fromSpecStalk_closedPoint]
    refine ⟨Over.mk (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{pullback.fst A.hom (D.S.fromSpecStalk (D.points i)) z'}, hxclosed⟩ :
        Closeds A.left)) ≫ A.hom), hA.step _ hxclosed (by rw [hxs]; exact ⟨i, rfl⟩), ?_, ?_⟩
    · obtain ⟨_, hcomap⟩ := vanishingIdeal_singleton_comap_pullbackFst A.hom
        (D.S.fromSpecStalk (D.points i)) _ hxclosed
        (pointToSpecStalk A.hom _ hxs)
        (pointToSpecStalk_comp_fromSpecStalk A.hom _ hxs) z' rfl
      obtain ⟨e₁⟩ := nonempty_pullbackBlowUpToBaseOverIso A.hom
        (D.S.fromSpecStalk (D.points i)) (Scheme.IdealSheafData.vanishingIdeal
          (⟨{pullback.fst A.hom (D.S.fromSpecStalk (D.points i)) z'}, hxclosed⟩ :
            Closeds A.left))
      obtain ⟨e₂⟩ := nonempty_blowUpOverIso_congr hcomap
        (pullback.snd A.hom (D.S.fromSpecStalk (D.points i)))
      obtain ⟨_, ⟨e₃⟩⟩ := nonempty_blowUpOverIso_of_isIso eAiso.hom wmap
        (pullback.snd A.hom (D.S.fromSpecStalk (D.points i))) hw z hz z' heAz
      exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩
    · intro j hji
      obtain ⟨e₁⟩ := D.nonempty_pullbackBlowUpOverIso_of_ne (Ne.symm hji) A _ hxclosed hxs
      obtain ⟨e₂⟩ := hother j hji
      exact ⟨e₁ ≪≫ e₂⟩

/-- The identity of `S` localizes to the identity of `Spec 𝒪_{S, s i}`. -/
theorem nonempty_pullbackIdOverIso (D : FinitePresentationAwayPointsSituation.{u})
    (i : Fin D.n) :
    Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj (Over.mk (𝟙 D.S)) ≅
      Over.mk (𝟙 (D.localScheme i))) :=
  ⟨Over.isoMk (asIso (pullback.snd (𝟙 D.S) (D.S.fromSpecStalk (D.points i)))) (by simp)⟩

/-- **Stacks Project, Tag 0BFY**, the global sequence. If every local modification factors as a
finite sequence of blowups at closed points lying over the closed point, then there is a
morphism to `S` factoring as a finite sequence of blowups at closed points lying over the
distinguished points whose localizations are those local modifications. -/
theorem exists_factorsAsPointBlowups_of_forall_local
    (D : FinitePresentationAwayPointsSituation.{u}) (G : ∀ i : Fin D.n, Over (D.localScheme i))
    (h : ∀ i, FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (G i).left (G i).hom) :
    ∃ A : Over D.S,
      FactorsAsPointBlowups D.S (Set.range D.points) A.left A.hom ∧
      ∀ i, Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A ≅ G i) := by
  suffices H : ∀ k : ℕ, k ≤ D.n →
      ∃ A : Over D.S,
        FactorsAsPointBlowups D.S (Set.range D.points) A.left A.hom ∧
        (∀ i : Fin D.n, i.val < k →
          Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A ≅ G i)) ∧
        (∀ i : Fin D.n, k ≤ i.val →
          Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A ≅
            Over.mk (𝟙 (D.localScheme i)))) by
    obtain ⟨A, hA, hproc, -⟩ := H D.n le_rfl
    exact ⟨A, hA, fun i => hproc i i.isLt⟩
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Over.mk (𝟙 D.S), FactorsAsPointBlowups.refl (Set.range D.points),
      fun i hi => absurd hi (by omega), fun i _ => D.nonempty_pullbackIdOverIso i⟩
  | succ k ih =>
    intro hk
    obtain ⟨A, hA, hproc, hunproc⟩ := ih (by omega)
    have hkn : k < D.n := by omega
    obtain ⟨LZ, lz, hchain, e, he⟩ := h ⟨k, hkn⟩
    obtain ⟨B, hB, ⟨eB⟩, hother⟩ := D.exists_factorsAsPointBlowups_of_localChain ⟨k, hkn⟩ hA
      (hunproc ⟨k, hkn⟩ (by simp)) hchain
    refine ⟨B, hB, ?_, ?_⟩
    · intro i hi
      by_cases hik : i = ⟨k, hkn⟩
      · subst hik
        exact ⟨eB ≪≫ (Over.isoMk e he).symm⟩
      · have hik' : (i : ℕ) ≠ k := fun hh => hik (Fin.ext hh)
        obtain ⟨e₁⟩ := hother i hik
        obtain ⟨e₂⟩ := hproc i (by omega)
        exact ⟨e₁ ≪≫ e₂⟩
    · intro i hi
      have hik : i ≠ ⟨k, hkn⟩ := by
        rintro rfl
        simp at hi
      obtain ⟨e₁⟩ := hother i hik
      obtain ⟨e₂⟩ := hunproc i (by omega)
      exact ⟨e₁ ≪≫ e₂⟩

/-! ### The global sequence is a modification supported at the distinguished points -/

/-- Invertibility of the structure morphism of an object over a base depends only on its
isomorphism class. -/
private theorem isIso_hom_of_overIso {T : Scheme.{u}} {X Y : Over T} (e : X ≅ Y)
    (hY : IsIso Y.hom) : IsIso X.hom := by
  have := isIso_left_of_overIso e
  rw [← Over.w e.hom]
  infer_instance

/-- A sequence of blowups at closed points lying over the distinguished points becomes an
isomorphism after base change along any flat morphism whose image avoids those points. -/
theorem isIso_pullback_hom_of_factorsAsPointBlowups
    (D : FinitePresentationAwayPointsSituation.{u}) {A : Over D.S}
    (hA : FactorsAsPointBlowups D.S (Set.range D.points) A.left A.hom) {T : Scheme.{u}}
    (g : T ⟶ D.S) [Flat g] (hg : ∀ t : T, g t ∉ Set.range D.points) :
    IsIso ((Over.pullback g).obj A).hom := by
  have H : ∀ {Z : Scheme.{u}} {p : Z ⟶ D.S},
      Stacks.ResolutionOfSurfaces.PointBlowupChain D.S (Set.range D.points) Z p →
      IsIso ((Over.pullback g).obj (Over.mk p)).hom := by
    intro Z p hchain
    induction hchain with
    | refl => exact inferInstanceAs (IsIso (pullback.snd (𝟙 D.S) g))
    | @step W pW hh w hw hwT ih =>
      refine isIso_hom_of_overIso ?_ ih
      refine Classical.choice (nonempty_pullbackBlowUpOverIsoOfMiss pW g w hw ?_)
      intro y hy
      refine hg (pullback.snd pW g y) ?_
      rw [← apply_pullback_fst_eq_apply_snd, hy]
      exact hwT
  obtain ⟨Z, p, hchain, e, he⟩ := hA
  exact isIso_hom_of_overIso ((Over.pullback g).mapIso (Over.isoMk e he)) (H hchain)

/-- The distinguished points, reindexed by a type in the universe of the scheme. -/
private def indexedPoints (D : FinitePresentationAwayPointsSituation.{u}) :
    ULift.{u} (Fin D.n) → D.S := fun i ↦ D.points i.down

/-- The reindexed family of distinguished points consists of closed points. -/
private theorem indexedPoints_mem_closedPoints (D : FinitePresentationAwayPointsSituation.{u}) :
    ∀ i : ULift.{u} (Fin D.n), D.indexedPoints i ∈ closedPoints D.S :=
  fun i ↦ mem_closedPoints_iff.mpr (D.points_closed i.down)

/-- The open complement formed from the reindexed family is the open complement of the
situation. -/
private theorem complementOfClosedPoints_indexedPoints
    (D : FinitePresentationAwayPointsSituation.{u}) :
    complementOfClosedPoints D.indexedPoints D.indexedPoints_mem_closedPoints = D.complement := by
  apply Opens.ext
  apply Set.ext
  intro x
  show x ∈ (⋂ i : ULift.{u} (Fin D.n), ({D.points i.down} : Set D.S)ᶜ) ↔
    x ∈ (Set.range D.points)ᶜ
  simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · intro h ⟨i, hi⟩
    exact h (ULift.up i) hi.symm
  · intro h i hi
    exact h ⟨i.down, hi.symm⟩

/-- The open complement formed from the reindexed family has quasi-compact inclusion. -/
private theorem quasiCompact_complementOfClosedPoints_indexedPoints
    (D : FinitePresentationAwayPointsSituation.{u}) :
    QuasiCompact
      (complementOfClosedPoints D.indexedPoints D.indexedPoints_mem_closedPoints).ι := by
  rw [← Scheme.isoOfEq_hom_ι D.S D.complementOfClosedPoints_indexedPoints]
  have : QuasiCompact D.complement.ι := D.complement_quasiCompact
  infer_instance

/-- A sequence of blowups at closed points lying over the distinguished points is of finite
presentation as soon as its base changes to the spectra of the local rings at the distinguished
points are. -/
theorem finitePresentation_of_factorsAsPointBlowups
    (D : FinitePresentationAwayPointsSituation.{u}) {A : Over D.S}
    (hA : FactorsAsPointBlowups D.S (Set.range D.points) A.left A.hom)
    (hlocal : ∀ i : Fin D.n,
      FinitePresentation ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj A).hom) :
    FinitePresentation A.hom := by
  let 𝒰 : Precoverage.ZeroHypercover.{u} Scheme.fpqcPrecoverage D.S :=
    { I₀ := Option (ULift.{u} (Fin D.n))
      X := LocalSchemesCover.obj D.indexedPoints D.indexedPoints_mem_closedPoints
      f := LocalSchemesCover.map D.indexedPoints D.indexedPoints_mem_closedPoints
      mem₀ := LocalSchemesCover.presieve₀_mem_fpqcPrecoverage D.indexedPoints
        D.indexedPoints_mem_closedPoints
        D.quasiCompact_complementOfClosedPoints_indexedPoints }
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒰 ?_
  intro a
  match a with
  | none =>
    have hmiss : ∀ t : (complementOfClosedPoints D.indexedPoints
        D.indexedPoints_mem_closedPoints).toScheme,
        (complementOfClosedPoints D.indexedPoints D.indexedPoints_mem_closedPoints).ι t ∉
          Set.range D.points := by
      intro t ⟨j, hj⟩
      have hmem : (complementOfClosedPoints D.indexedPoints
          D.indexedPoints_mem_closedPoints).ι t ∈
            ((complementOfClosedPoints D.indexedPoints
              D.indexedPoints_mem_closedPoints) : Set D.S) := by
        rw [← Scheme.Opens.range_ι]
        exact ⟨t, rfl⟩
      exact (LocalSchemesCover.mem_complementOfClosedPoints_iff D.indexedPoints
        D.indexedPoints_mem_closedPoints).mp hmem (ULift.up j) hj.symm
    have : IsIso ((Over.pullback (complementOfClosedPoints D.indexedPoints
        D.indexedPoints_mem_closedPoints).ι).obj A).hom :=
      D.isIso_pullback_hom_of_factorsAsPointBlowups hA _ hmiss
    show FinitePresentation ((Over.pullback (complementOfClosedPoints D.indexedPoints
      D.indexedPoints_mem_closedPoints).ι).obj A).hom
    have : MorphismProperty.ContainsIdentities
        (@FinitePresentation : MorphismProperty Scheme.{u}) :=
      ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance⟩⟩
    have : MorphismProperty.RespectsIso (@FinitePresentation : MorphismProperty Scheme.{u}) :=
      finitePresentation_isLocalAtTarget.toRespects
    exact MorphismProperty.of_isIso (@FinitePresentation : MorphismProperty Scheme.{u}) _
  | some i => exact hlocal i.down

/-- Finite presentation of the structure morphism of an object over a base depends only on its
isomorphism class. -/
private theorem finitePresentation_hom_of_overIso {T : Scheme.{u}} {X Y : Over T} (e : X ≅ Y)
    (hY : FinitePresentation Y.hom) : FinitePresentation X.hom := by
  have : MorphismProperty.RespectsIso (@FinitePresentation : MorphismProperty Scheme.{u}) :=
    finitePresentation_isLocalAtTarget.toRespects
  have := isIso_left_of_overIso e
  rw [← Over.w e.hom]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@FinitePresentation : MorphismProperty Scheme.{u}) e.hom.left Y.hom).mpr hY

/-- The open complement of the distinguished points avoids them. -/
theorem complement_ι_notMem_range (D : FinitePresentationAwayPointsSituation.{u})
    (t : D.complement.toScheme) : D.complement.ι t ∉ Set.range D.points := by
  show D.complement.ι t ∈ (D.complement : Set D.S)
  rw [← Scheme.Opens.range_ι]
  exact ⟨t, rfl⟩

/-- **Stacks Project, Tag 0BFY**, sufficiency, for any functor carrying the canonical
identifications with base change to the spectra of the local rings. If every local modification
corresponding to `f : X ⟶ S` factors as a finite sequence of blowups at closed points lying over
the closed point of the corresponding local scheme, then `f` factors as a finite sequence of
blowups at closed points lying over the distinguished points.

The global sequence is built by concatenating the local ones; identifying its source with `f`
uses that the functor is an equivalence, which is [Stacks, Tag 0BFV]. -/
theorem factorsAsPointBlowups_of_forall_corresponds_of_baseChange
    (D : FinitePresentationAwayPointsSituation.{u}) (BC : BaseChangeFunctor D)
    (X : D.globalCategory) (Y : ∀ i, D.localCategory i)
    (hY : ∀ i, BC.functor.obj X i ≅ Y i)
    (h : ∀ i, FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
      (Y i).obj.hom) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom := by
  obtain ⟨A, hA, hlocal⟩ :=
    D.exists_factorsAsPointBlowups_of_forall_local (fun i => (Y i).obj) h
  have hfp : FinitePresentation A.hom :=
    D.finitePresentation_of_factorsAsPointBlowups hA fun i =>
      finitePresentation_hom_of_overIso (Classical.choice (hlocal i)) (Y i).property.1
  have hAway : IsIso ((Over.pullback D.complement.ι).obj A).hom :=
    D.isIso_pullback_hom_of_factorsAsPointBlowups hA D.complement.ι D.complement_ι_notMem_range
  let Aobj : D.globalCategory := ⟨A, ⟨hfp, hAway⟩⟩
  let cmp : ∀ i, (BC.functor.obj Aobj i).obj ≅ (BC.functor.obj X i).obj := fun i =>
    (BC.pullbackIso i).app Aobj ≪≫ Classical.choice (hlocal i) ≪≫
      ((ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).mapIso
        (hY i)).symm
  let m : BC.functor.obj Aobj ⟶ BC.functor.obj X := fun i =>
    (ObjectProperty.isoMk (IsFinitePresentationAway (D.puncturedLocalScheme i)) (cmp i)).hom
  have hm : ∀ i, IsIso (m i) := fun i =>
    (ObjectProperty.isoMk (IsFinitePresentationAway (D.puncturedLocalScheme i))
      (cmp i)).isIso_hom
  have : IsIso m := (isIso_pi_iff m).2 hm
  exact D.factorsAsPointBlowups_of_baseChange_iso_unconditional BC (asIso m) hA

/-- **Stacks Project, Tag 0BFY**, for any functor carrying the canonical identifications with
base change to the spectra of the local rings. A modification of `S` supported at the
distinguished points factors as a finite sequence of blowups at closed points lying over the
*set* of distinguished points exactly when, for every `i`, the corresponding local modification
factors as a finite sequence of blowups at closed points lying over the closed point of
`Spec 𝒪_{S, s i}`. -/
theorem factorsAsPointBlowups_iff_forall_corresponds_of_baseChange
    (D : FinitePresentationAwayPointsSituation.{u}) (BC : BaseChangeFunctor D)
    (X : D.globalCategory) (Y : ∀ i, D.localCategory i)
    (hY : ∀ i, BC.functor.obj X i ≅ Y i) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom ↔
      ∀ i, FactorsAsPointBlowups (D.localScheme i)
        {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
        (Y i).obj.hom :=
  ⟨fun hX i => D.factorsAsPointBlowups_of_corresponds BC X i (Y i) (hY i) hX,
    D.factorsAsPointBlowups_of_forall_corresponds_of_baseChange BC X Y hY⟩

/-- **Stacks Project, Tag 0BFY**, sufficiency, for the base-change functor `F` of
[Stacks, Tag 0BFU]. If every local modification `g i : Y i ⟶ Spec 𝒪_{S, s i}` corresponding to
`f : X ⟶ S` under `F` factors as a finite sequence of blowups at closed points lying over the
closed point, then `f` factors as a finite sequence of blowups at closed points lying over the
distinguished points. -/
theorem factorsAsPointBlowups_of_forall_corresponds
    (D : FinitePresentationAwayPointsSituation.{u}) (X : D.globalCategory)
    (Y : ∀ i, D.localCategory i)
    (hY : ∀ i, (finitePresentationAwayPointsBaseChange D).functor.obj X i ≅ Y i)
    (h : ∀ i, FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
      (Y i).obj.hom) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom :=
  D.factorsAsPointBlowups_of_forall_corresponds_of_baseChange
    (finitePresentationAwayPointsBaseChange D) X Y hY h

/-- **Stacks Project, Tag 0BFY.** Let `S` be a scheme, let `s 1, …, s n` be pairwise distinct
closed points whose open complement has quasi-compact inclusion, and let `f : X ⟶ S` correspond
to `g i : Y i ⟶ Spec 𝒪_{S, s i}` under the base-change functor `F` of [Stacks, Tag 0BFU]. Then
`f` admits a factorization `X = Z m ⟶ … ⟶ Z 0 = S` in which every step is the blowing up of its
target at a closed point lying over the *set* `{s 1, …, s n}` if and only if, for every `i`, the
morphism `g i` admits a factorization `Y i = Z i (m i) ⟶ … ⟶ Z i 0 = Spec 𝒪_{S, s i}` in which
every step is the blowing up of its target at a closed point lying over the closed point, which
is `s i` itself. -/
@[stacks 0BFY]
theorem factorsAsPointBlowups_iff_forall_corresponds
    (D : FinitePresentationAwayPointsSituation.{u}) (X : D.globalCategory)
    (Y : ∀ i, D.localCategory i)
    (hY : ∀ i, (finitePresentationAwayPointsBaseChange D).functor.obj X i ≅ Y i) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom ↔
      ∀ i, FactorsAsPointBlowups (D.localScheme i)
        {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} (Y i).obj.left
        (Y i).obj.hom :=
  D.factorsAsPointBlowups_iff_forall_corresponds_of_baseChange
    (finitePresentationAwayPointsBaseChange D) X Y hY

end FinitePresentationAwayPointsSituation

end AlgebraicGeometry

end
