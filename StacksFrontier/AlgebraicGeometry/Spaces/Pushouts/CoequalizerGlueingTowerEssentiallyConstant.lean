module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTower
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject

/-!
# The tower of glueing coequalizers is essentially constant with value `X`

Stacks 0AGL remarks that the meaning of Stacks 0AGK is that the system
`X_1 ⟶ X_2 ⟶ X_3 ⟶ …` of Stacks 0AGJ is essentially constant with value `X`, in the sense of
Stacks 05PU, with respect to the cocone formed by the morphisms `X_n ⟶ X`. This file proves
that implication in the category of algebraic spaces over `S`, taking the conclusion of
Stacks 0AGK as a hypothesis in exactly the form
`∃ n₀, ∀ n, n₀ ≤ n → ∃ m, N.FactorsThroughSection D n m` in which it is stated.

## Main definitions

* `ClosedSubspaceSystem.towerDiagram`: the tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ …` of Stacks 0AGJ as a
  diagram `ℕ ⥤ AlgebraicSpaces`.
* `ClosedSubspaceSystem.towerCocone`: the cocone over it with apex `X` formed by the morphisms
  `X_n ⟶ X`.

## Main results

* `CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_eventually_section`:
  a diagram over a directed set with a cocone `(X, {c_n})` is essentially constant with value
  `X` (Stacks 05PU(1)) as soon as for every `n` beyond some `n₀` some transition map
  `M_n ⟶ M_k` factors as `c_n` followed by a section of `c_k`.
* `ClosedSubspaceSystem.exists_isEssentiallyConstantWith_towerCocone`: the conclusion of
  Stacks 0AGK implies that the tower is essentially constant with value `X`.

## References

* [Stacks Project, Tag 0AGL](https://stacks.math.columbia.edu/tag/0AGL)
* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 0AGJ](https://stacks.math.columbia.edu/tag/0AGJ)
* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.EssentiallyConstantInd

variable {C : Type*} [Category C] {I : Type*} [Preorder I] [IsDirectedOrder I] {M : I ⥤ C}

/-- **A directed system with eventual sections of its cocone is essentially constant.** Let
`(X, {c_n : M_n ⟶ X})` be a cocone over a diagram `M` on a directed set. If for every `n` beyond
some `n₀` there are `k ≥ n` and a section `s : X ⟶ M_k` of `c_k` with `c_n ≫ s = M(n ≤ k)`, then
`M` is essentially constant with value `X` (Stacks 05PU(1)). -/
theorem exists_isEssentiallyConstantWith_of_eventually_section (t : Cocone M) (n₀ : I)
    (h : ∀ n, n₀ ≤ n → ∃ (k : I) (hnk : n ≤ k) (s : t.pt ⟶ M.obj k),
      s ≫ t.ι.app k = 𝟙 t.pt ∧ t.ι.app n ≫ s = M.map (homOfLE hnk)) :
    ∃ (i : I) (r : t.pt ⟶ M.obj i), IsEssentiallyConstantWith M t i r := by
  obtain ⟨i, hi, r, hr, -⟩ := h n₀ le_rfl
  refine ⟨i, r, ⟨hr, fun j => ?_⟩⟩
  obtain ⟨l, hjl, hil⟩ := directed_of (· ≤ ·) j i
  obtain ⟨k, hlk, s, -, hls⟩ := h l (hi.trans hil)
  have key : ∀ x (hx : x ≤ l), M.map (homOfLE (hx.trans hlk)) = t.ι.app x ≫ s := fun x hx => by
    rw [← homOfLE_comp hx hlk, M.map_comp, ← hls, t.w_assoc]
  exact ⟨k, homOfLE (hil.trans hlk), homOfLE (hjl.trans hlk), by
    rw [key j hjl, key i hil, reassoc_of% hr]⟩

end CategoryTheory.EssentiallyConstantInd

namespace AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem

open CategoryTheory.EssentiallyConstantInd

variable {T : CoequalizerGlueSituation.{u}} (N : T.ClosedSubspaceSystem)
  (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (N.glueMapAt n))

/-- **The tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ …` of Stacks 0AGJ, as a diagram indexed by `ℕ`.** Its
`n`th object is the coequalizer `X_n = (D n).space` and its transition maps are composites of
the morphisms `towerMap`. -/
def towerDiagram : ℕ ⥤ AlgebraicSpaces T.B T.S T.hS :=
  Functor.ofSequence (N.towerMap D)

/-- The `n`th object of the diagram is `X_n = (D n).space`. -/
@[simp]
theorem towerDiagram_obj (n : ℕ) : (N.towerDiagram D).obj n = (D n).space :=
  rfl

/-- The transition map `X_n ⟶ X_{n+1}` of the diagram is `towerMap`. -/
@[simp]
theorem towerDiagram_map_homOfLE_succ (n : ℕ) :
    (N.towerDiagram D).map (homOfLE (Nat.le_add_right n 1)) = N.towerMap D n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The transition map `X_n ⟶ X_{n+m}` of the diagram is the composite `towerTransition`. -/
theorem towerDiagram_map_homOfLE (n : ℕ) :
    ∀ m : ℕ, (N.towerDiagram D).map (homOfLE (Nat.le_add_right n m)) = N.towerTransition D n m
  | 0 => (N.towerDiagram D).map_id n
  | m + 1 => by
    rw [← homOfLE_comp (Nat.le_add_right n m) (Nat.le_add_right (n + m) 1), Functor.map_comp,
      towerDiagram_map_homOfLE n m, towerDiagram_map_homOfLE_succ]
    rfl

/-- **The cocone `(X, {X_n ⟶ X})` over the tower of Stacks 0AGJ**: its legs are the morphisms
`(D n).toTarget`, compatible with the tower by `towerMap_comp_toTarget`. -/
def towerCocone : Cocone (N.towerDiagram D) where
  pt := T.targetSpace
  ι := NatTrans.ofSequence (fun n => (D n).toTarget) fun n =>
    (congrArg (· ≫ (D (n + 1)).toTarget) (N.towerDiagram_map_homOfLE_succ D n)).trans
      ((N.towerMap_comp_toTarget D n).trans (Category.comp_id _).symm)

/-- The apex of the cocone is `X = T.targetSpace`. -/
@[simp]
theorem towerCocone_pt : (N.towerCocone D).pt = T.targetSpace :=
  rfl

/-- The `n`th leg of the cocone is `(D n).toTarget : X_n ⟶ X`. -/
@[simp]
theorem towerCocone_ι_app (n : ℕ) : (N.towerCocone D).ι.app n = (D n).toTarget :=
  rfl

/-- **The conclusion of Stacks 0AGK makes the tower essentially constant with value `X`.** If for
all `n` large enough there is an `m` such that `X_n ⟶ X_{n+m}` factors through a closed immersion
`X ⟶ X_{n+m}` which is a section of `X_{n+m} ⟶ X` (`FactorsThroughSection`), then the system
`X_1 ⟶ X_2 ⟶ X_3 ⟶ …` is essentially constant with value `X` (Stacks 05PU(1)) with respect to
the cocone of the morphisms `X_n ⟶ X`: there are an index `i` and a morphism `r : X ⟶ X_i` with
`X ⟶ X_i ⟶ X` the identity, such that every `X_j ⟶ X_k`, for `k` large, is
`X_j ⟶ X ⟶ X_i ⟶ X_k`. This is the content of Stacks 0AGL; the hypothesis is the conclusion of
Stacks 0AGK. -/
theorem exists_isEssentiallyConstantWith_towerCocone
    (h : ∃ n₀, ∀ n, n₀ ≤ n → ∃ m, N.FactorsThroughSection D n m) :
    ∃ (i : ℕ) (r : T.targetSpace ⟶ (D i).space),
      IsEssentiallyConstantWith (N.towerDiagram D) (N.towerCocone D) i r := by
  obtain ⟨n₀, hn₀⟩ := h
  refine exists_isEssentiallyConstantWith_of_eventually_section (N.towerCocone D) n₀
    fun n hn => ?_
  obtain ⟨m, c, -, hsec, hfac⟩ := hn₀ n hn
  exact ⟨n + m, Nat.le_add_right n m, c, hsec,
    hfac.trans (N.towerDiagram_map_homOfLE D n m).symm⟩

end AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem

end
