module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Inputs
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic

/-!
# The first Chern class operation: flat pullback, isomorphism invariance, rank one

`Stacks.Chow.GenuineChern.FlatCompat C` is the statement that the Segre pushforward of a
projective bundle commutes with flat pullback: for `f : Y ⟶ X` flat of relative dimension `d`
and `ℰ' ≅ f^*ℰ`,

  `c₁(ℰ') ∩ f^*α = f^*(c₁(ℰ) ∩ α)`.

This is the first Chern class part of [Stacks, Tag 02U8]. Assuming it, this file proves for the
operation `Stacks.Chow.GenuineChern.firstChern`: invariance under isomorphisms of modules (the
case `f = 𝟙`), flat pullback in every rank including zero, and the value in rank one.

## Main definitions

* `Stacks.Chow.GenuineChern.FlatCompat`: the Segre pushforward of a module of constant positive
  rank commutes with flat pullback.

## Main results

* `Stacks.Chow.GenuineChern.segre_congr`, `Stacks.Chow.GenuineChern.firstChern_congr` —
  invariance under isomorphisms of modules.
* `Stacks.Chow.GenuineChern.firstChern_flatPullback_heq` — flat pullback, in every rank.
* `Stacks.Chow.GenuineChern.firstChern_one` — the value in rank one.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- The Segre pushforward `segre` commutes with flat pullback: for every flat morphism
`f : Y ⟶ X` of relative dimension `d`, every module `ℰ` of constant positive rank on `X` and every
`ℰ' ≅ f^*ℰ`, `segre ℰ' (f^*α)` is `f^*(segre ℰ α)`. -/
def FlatCompat : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY)
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension f d) (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (E' : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    (_ : E' ≅ (Scheme.Modules.pullback f).obj E) (k : ℤ) (α : chowGroup C sX k),
    segre E' n C sY (k + (d : ℤ))
        (flatPullbackChow C sY sX f hf d hd k
          (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd k) α) ≍
      flatPullbackChow C sY sX f hf d hd (k - 1)
        (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd _)
        (segre E n C sX k α)

variable {C} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The Segre pushforward, at heterogeneously equal arguments in equal degrees. -/
theorem segre_heq (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] {k₁ k₂ : ℤ} (hk : k₁ = k₂)
    {x : chowGroup C sX k₁} {y : chowGroup C sX k₂} (hxy : x ≍ y) :
    segre E n C sX k₁ x ≍ segre E n C sX k₂ y :=
  heq_apply_of_degree C sX sX (fun k ↦ k) (fun k ↦ k - 1) (fun k ↦ segre E n C sX k) hk hxy

/-- **The Segre pushforward depends only on the isomorphism class of the module.** -/
theorem segre_congr (HF : FlatCompat C) {E E' : X.Modules} (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (e : E' ≅ E) (k : ℤ)
    (α : chowGroup C sX k) : segre E' n C sX k α = segre E n C sX k α := by
  have h := HF sX sX (𝟙 X) (Category.id_comp sX) 0 (relativeDimension_identity X) E n E'
    (e ≪≫ ((Scheme.Modules.pullbackId X).app E).symm) k α
  refine chowGroup_eq_of_heq C sX (HEq.trans ?_ ((h.trans (heq_of_eq
    (flatPullbackChow_id C sX (k - 1) (segre E n C sX k α)))).trans (chowGroupCast_heq C sX _ _)))
  exact segre_heq sX E' n (by simp)
    ((chowGroupCast_heq C sX _ α).symm.trans (heq_of_eq (flatPullbackChow_id C sX k α).symm))

/-- `firstChern` depends only on the value of the rank, not on its spelling. -/
theorem firstChern_rank_congr (E : X.Modules) {r r' : ℕ} (h : r = r')
    [i : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [i' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r'] (k : ℤ) :
    firstChern E C sX r k = firstChern E C sX r' k := by
  subst h; rfl

/-- **The first Chern class depends only on the isomorphism class of the module.** -/
theorem firstChern_congr (HF : FlatCompat C) {E E' : X.Modules} (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r] (e : E' ≅ E)
    (k : ℤ) (α : chowGroup C sX k) : firstChern E' C sX r k α = firstChern E C sX r k α := by
  rcases r with _ | n
  · rfl
  · have := isFiniteLocallyFree_of_rank E (n + 1)
    have := isFiniteLocallyFree_of_rank E' (n + 1)
    exact segre_congr sX HF n e k α

/-- Zero classes in equal degrees are heterogeneously equal. -/
theorem zero_heq_zero {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] {d e : ℤ}
    (h : d = e) : (0 : chowGroup C sP d) ≍ (0 : chowGroup C sP e) := by
  subst h; rfl

/-- **The first Chern class commutes with flat pullback**, in every rank. -/
theorem firstChern_flatPullback_heq (HF : FlatCompat C) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : Y ⟶ X) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY)
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension f d) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (E' : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (e : E' ≅ (Scheme.Modules.pullback f).obj E) (k : ℤ) (α : chowGroup C sX k) :
    firstChern E' C sY r (k + (d : ℤ))
        (flatPullbackChow C sY sX f hf d hd k
          (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd k) α) ≍
      flatPullbackChow C sY sX f hf d hd (k - 1)
        (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd _)
        (firstChern E C sX r k α) := by
  rcases r with _ | n
  · simp only [firstChern_zero, AddMonoidHom.zero_apply, map_zero]
    exact zero_heq_zero sY (by ring)
  · have := isFiniteLocallyFree_of_rank E (n + 1)
    have := isFiniteLocallyFree_of_rank E' (n + 1)
    exact HF sX sY f hf d hd E n E' e k α

/-- A module of rank one is invertible. -/
theorem isInvertible_of_rank_one (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  Stacks.InvertibleRankOneScheme.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one X L

/-- **The first Chern class in rank one** is the cap with the module. -/
theorem firstChern_one (H : TopHalf C) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] (k : ℤ)
    (α : chowGroup C sX k) :
    haveI := isInvertible_of_rank_one L
    firstChern L C sX 1 k α =
      firstChernClassCapChow C (k - 1) sX L (chowGroupCast C sX (by omega) α) := by
  have := isInvertible_of_rank_one L
  have := isFiniteLocallyFree_of_rank L 1
  exact segre_rank_one sX L H k α

end Stacks.Chow.GenuineChern

end
