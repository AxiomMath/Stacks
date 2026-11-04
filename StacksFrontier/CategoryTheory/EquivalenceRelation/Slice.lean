module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EquivalenceRelation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Equivalence relations in a slice category

A pair of parallel morphisms of objects over a fixed object `S` is an internal equivalence
relation as soon as the underlying pair of morphisms of `C` is: the reflexivity, symmetry and
transitivity morphisms of the underlying relation automatically lie over `S`, and the pullback
of the two underlying morphisms, equipped with its composite to `S`, is a pullback in the
slice.

## Main results

* `CategoryTheory.jointlyMono₂_of_left`: a pair of parallel morphisms in `CategoryTheory.Over S`
  is jointly monic as soon as the underlying pair is.
* `CategoryTheory.isEquivalenceRelation_of_left`: a pair of parallel morphisms in
  `CategoryTheory.Over S` is an equivalence relation as soon as the underlying pair is.

## Implementation notes

No pullbacks are assumed to exist in the slice category: the limiting pullback cone carried by
the underlying equivalence relation is transported by hand, its vertex being the underlying
vertex with the composite of the first projection and the structure morphism.  That is also why
the conclusion is the propositional `CategoryTheory.IsEquivalenceRelation` rather than a chosen
`CategoryTheory.EquivalenceRelation` structure: the cone is the one the underlying structure
happens to carry.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

/-- A pair of parallel morphisms of objects over `S` is jointly monic as soon as the underlying
pair of morphisms is. -/
theorem jointlyMono₂_of_left {R U : Over S} (p₁ p₂ : R ⟶ U)
    [JointlyMono₂ p₁.left p₂.left] : JointlyMono₂ p₁ p₂ where
  right_cancellation T f g h₁ h₂ := by
    ext
    exact JointlyMono₂.right_cancellation f.left g.left
      (by simpa using congrArg Over.Hom.left h₁)
      (by simpa using congrArg Over.Hom.left h₂)

/-- A pair of parallel morphisms of objects over `S` is an internal equivalence relation as soon
as the underlying pair of morphisms is. -/
@[sga "3 IV 3.1.3" "special case"]
theorem isEquivalenceRelation_of_left {R U : Over S} (p₁ p₂ : R ⟶ U)
    [h : IsEquivalenceRelation p₁.left p₂.left] : IsEquivalenceRelation p₁ p₂ := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  have hjm : JointlyMono₂ p₁.left p₂.left := ⟨e.right_cancellation⟩
  have hcond : e.c.fst ≫ R.hom = e.c.snd ≫ R.hom := by simpa using e.c.condition =≫ U.hom
  let cpt : Over S := Over.mk (e.c.fst ≫ R.hom)
  let cfst : cpt ⟶ R := Over.homMk e.c.fst rfl
  let csnd : cpt ⟶ R := Over.homMk e.c.snd hcond.symm
  have hcc : cfst ≫ p₂ = csnd ≫ p₁ := by ext; exact e.c.condition
  have hlim : IsLimit (PullbackCone.mk cfst csnd hcc) := by
    refine PullbackCone.IsLimit.mk hcc
      (fun s => Over.homMk (PullbackCone.IsLimit.lift e.isLimit s.fst.left s.snd.left
        (by simpa using congrArg Over.Hom.left s.condition)) ?_) ?_ ?_ ?_
    · simp [cpt]
    · intro s; ext; exact PullbackCone.IsLimit.lift_fst _ _ _ _
    · intro s; ext; exact PullbackCone.IsLimit.lift_snd _ _ _ _
    · intro s m h₁ h₂
      ext
      refine PullbackCone.IsLimit.hom_ext e.isLimit ?_ ?_
      · simpa [cfst] using congrArg Over.Hom.left h₁
      · simpa [csnd] using congrArg Over.Hom.left h₂
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := jointlyMono₂_of_left p₁ p₂
      r := Over.homMk e.r (by rw [← Over.w p₁, ← Category.assoc, e.reflexivity₁, Category.id_comp])
      reflexivity₁ := by ext; simp
      reflexivity₂ := by ext; simp
      s := Over.homMk e.s (by simpa using e.symmetry₁ =≫ U.hom)
      symmetry₁ := by ext; exact e.symmetry₁
      symmetry₂ := by ext; exact e.symmetry₂
      c := PullbackCone.mk cfst csnd hcc
      isLimit := hlim
      t := Over.homMk e.t
        (by simpa using e.transitivity₁ =≫ U.hom : e.t ≫ R.hom = e.c.fst ≫ R.hom)
      transitivity₁ := by ext; exact e.transitivity₁
      transitivity₂ := by ext; exact e.transitivity₂ }

end CategoryTheory

end
