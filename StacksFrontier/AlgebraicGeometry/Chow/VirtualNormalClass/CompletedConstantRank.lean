module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Components

/-!
# The completed class of a virtual normal bundle of constant rank

Let `𝒩` be a virtual normal bundle of constant rank `r` for a closed immersion `i : Z ⟶ X` of
schemes locally of finite type over the base of chapter 42 of the Stacks Project. The last
assertion of Stacks 0FBK is that `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`: the element
`Stacks.Chow.VirtualNormalBundle.completedClass` of `A^*(Z ⟶ X)^∧ ⊆ ∏_p A^p(Z ⟶ X)` has degree
`r` part the class `c(Z ⟶ X, 𝒩)` of the construction and all other parts zero.

On a connected component `Z_k` the rank of `𝒩` is `r`, and the restriction of `c(Z ⟶ X, 𝒩)` to
`Z_k ⟶ W_k` is `c(Z_k ⟶ W_k, 𝒩|_{Z_k})` by the base change clause of the tag for the cartesian
square of `Z_k ⟶ W_k` over `i`; so the two classes have the same restrictions to the pieces of
Stacks 0FDZ.

## Main results

* `Stacks.Chow.VirtualNormalBundle.bivariantPieceRestrictionOfInvertible_virtualNormalClass` —
  the restriction of `c(Z ⟶ X, 𝒩)` to `Z_k ⟶ W_k` is `c(Z_k ⟶ W_k, 𝒩|_{Z_k})`.
* `Stacks.Chow.VirtualNormalBundle.completedBivariantSequenceOfInvertible_completedClass_of_rank`
  — **Stacks 0FBK**, for `𝒩` of constant rank `r` the completed class is `c(Z ⟶ X, 𝒩)` in degree
  `r`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ) [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- The family in degree `p` at a component is the class of `𝒩|_{Z_k}` computed with any rank
instance `n = p`. -/
theorem componentFamily_eq (k : _root_.ConnectedComponents Z) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.restrictComponent k).bundle n]
    (p : ℤ) (hn : (n : ℤ) = p) :
    𝒩.componentFamily C sX sZ hZ p k =
      hn ▸ (𝒩.restrictComponent k).virtualNormalClass C ((componentAmbient i k).ι ≫ sX)
        ((Z.connectedComponentOpens k).ι ≫ sZ)
        (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ) n := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe k
  have hr : 𝒩.componentRank (ConnectedComponents.mk x) = n :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_unique (𝒩.restrictComponent _).bundle
      inferInstance ‹_› ⟨x, rfl⟩
  subst hr hn
  exact 𝒩.componentFamily_rank C sX sZ hZ _

section Rank

variable (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- `𝒩|_{Z_k}` has rank `r` when `𝒩` does. -/
instance isFiniteLocallyFreeOfRank_restrictComponent_of_rank (k : _root_.ConnectedComponents Z) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.restrictComponent k).bundle r :=
  isFiniteLocallyFreeOfRank_modulePullback (Z.connectedComponentOpens k).ι 𝒩.bundle r ‹_›

omit [IsLocallyNoetherian X] in
/-- When `𝒩` has rank `r` so does it on every connected component. -/
theorem componentRank_eq_of_rank (k : _root_.ConnectedComponents Z) : 𝒩.componentRank k = r := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe k
  exact (𝒩.fiberRank_eq_componentRank _ x rfl).symm.trans
    (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank 𝒩.bundle r x)

/-- **The restriction of `c(Z ⟶ X, 𝒩)` to a piece**: on the cartesian square of `Z_k ⟶ W_k` over
`i`, the restriction of `c(Z ⟶ X, 𝒩)` to `Z_k ⟶ W_k` (Stacks 0FDZ) is
`c(Z_k ⟶ W_k, 𝒩|_{Z_k})` (the base change clause of Stacks 0FBK). -/
theorem bivariantPieceRestrictionOfInvertible_virtualNormalClass
    (k : _root_.ConnectedComponents Z) :
    bivariantPieceRestrictionOfInvertible C sZ sX i hZ r Z.connectedComponentOpens
        (componentAmbient i) id (le_preimage_componentAmbient i) k
        (𝒩.virtualNormalClass C sX sZ hZ r) =
      (𝒩.restrictComponent k).virtualNormalClass C ((componentAmbient i k).ι ≫ sX)
        ((Z.connectedComponentOpens k).ι ≫ sZ)
        (baseChange_structure (isPullback_componentPiece i k) C sX sZ hZ) r := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun t _ n β => ?_
  refine Eq.trans ?_ ((Comparison.ofBaseChange (isPullback_componentPiece i k)
    𝒩).virtualNormalClass_cap_eq_chowGroupRestrict C sX sZ hZ r t (t ≫ (componentAmbient i k).ι)
    rfl (pieceComparison i Z.connectedComponentOpens (componentAmbient i) id
      (le_preimage_componentAmbient i) k t)
    (opensPullbackComparison_fst _ _ _ _ _ _) (opensPullbackComparison_snd _ _ _ _ _ _)
    (pieceComparison_comp_structureMorphism _ _ _ _ _ _ _ sZ) (Category.assoc _ _ _).symm n
    β).symm
  exact bivariantPieceRestrictionCap_apply C _ sZ sX i hZ r _ _ _ _ k _ t n β

/-- **Stacks 0FBK, constant rank.** If `𝒩` has constant rank `r` then the degree `p` part of
`c(Z ⟶ X, 𝒩)` is the class of the construction when `p = r`, and zero otherwise. -/
theorem degreeClass_of_rank (p : ℤ) :
    𝒩.degreeClass C sX sZ hZ p =
      if h : (r : ℤ) = p then h ▸ 𝒩.virtualNormalClass C sX sZ hZ r else 0 := by
  refine (bivariantPieceEquivOfInvertible C sZ sX i hZ p Z.connectedComponentOpens
    (componentAmbient i) id (le_preimage_componentAmbient i)
    Z.isClopenDecomposition_connectedComponentOpens).injective (funext fun k => ?_)
  refine (𝒩.bivariantPieceRestrictionOfInvertible_degreeClass C sX sZ hZ p k).trans ?_
  rw [bivariantPieceEquivOfInvertible_apply]
  split_ifs with h
  · subst h
    rw [𝒩.componentFamily_eq C sX sZ hZ k r _ rfl,
      𝒩.bivariantPieceRestrictionOfInvertible_virtualNormalClass C sX sZ hZ r k]
  · rw [𝒩.componentFamily_of_ne C sX sZ hZ (by rwa [𝒩.componentRank_eq_of_rank r k])]
    exact (bivariantPieceRestriction_zero C (gysinSystemOfInvertible C) sZ sX i hZ p
      Z.connectedComponentOpens (componentAmbient i) id (le_preimage_componentAmbient i) k
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)).symm

/-- **Stacks 0FBK, constant rank**: `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`. If `𝒩` has constant rank `r`,
the element `c(Z ⟶ X, 𝒩)` of `A^*(Z ⟶ X)^∧ ⊆ ∏_p A^p(Z ⟶ X)` is the class of the construction
in degree `r` and zero in every other degree. -/
theorem completedBivariantSequenceOfInvertible_completedClass_of_rank (p : ℤ) :
    completedBivariantSequenceOfInvertible C sZ sX i hZ (𝒩.completedClass C sX sZ hZ) p =
      if h : (r : ℤ) = p then h ▸ 𝒩.virtualNormalClass C sX sZ hZ r else 0 :=
  (𝒩.completedBivariantSequenceOfInvertible_completedClass C sX sZ hZ p).trans
    (𝒩.degreeClass_of_rank C sX sZ hZ r p)

end Rank

end Stacks.Chow.VirtualNormalBundle

end
