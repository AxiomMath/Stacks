module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.CompletedBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FBK: the bivariant class of a virtual normal bundle

Let `(S, δ)` be as in Situation 02QL, `i : Z ⟶ X` a closed immersion of schemes locally of finite
type over `S` and `𝒩` a virtual normal bundle for `i`. Stacks 0FBK states:

1. the construction preceding the tag defines a bivariant class
   `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`;
2. the construction is compatible with base change as in Stacks 0FBJ;
3. if `𝒩` has constant rank `r`, then `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`.

For `𝒩` of constant rank `r` the construction is
`Stacks.Chow.VirtualNormalBundle.virtualNormalClass`: the unique class with
`p^* ∘ c = ι_* ∘ j^* ∘ C` (`Stacks.Chow.VirtualNormalBundle.middleCap_virtualNormalClass_cap`,
`Stacks.Chow.VirtualNormalBundle.eq_virtualNormalClass_of_middleCap`). Its compatibility with base
change along any cartesian square is
`Stacks.Chow.VirtualNormalBundle.Comparison.virtualNormalClass_cap` and, for the restriction of
Stacks 0F9Z, `Stacks.Chow.VirtualNormalBundle.bivariantRestriction_virtualNormalClass`.

In general the rank of `𝒩` is constant on each connected component `Z_k` of `Z`, and
`Stacks.Chow.VirtualNormalBundle.completedClass` is the element of `A^*(Z ⟶ X)^∧` whose degree `p`
part restricts on `Z_k ⟶ W_k` (with `W_k ⊆ X` open, `i⁻¹(W_k) = Z_k`) to the class of the
construction for `𝒩|_{Z_k}` when `𝒩` has rank `p` on `Z_k`, and to zero otherwise. This file
states the three assertions of the tag for it with no hypothesis beyond those of the source: the
local Noetherianity of the schemes involved, which the completed groups need, follows from their
being locally of finite type over `S`.

## Main results

* `Stacks.Chow.VirtualNormalBundle.restriction_completedClass` and
  `Stacks.Chow.VirtualNormalBundle.eq_completedClass_of_restriction` — **(1)**, the class and its
  characterization.
* `Stacks.Chow.VirtualNormalBundle.baseChange_completedClass` — **(2)**,
  `c(Z' ⟶ X', g^*𝒩) = res(c(Z ⟶ X, 𝒩))`.
* `Stacks.Chow.VirtualNormalBundle.completedClass_of_constantRank` — **(3)**.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i)
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)

/-- **Stacks 0FBK (1), constant rank.** For `𝒩` of constant rank `r`, with `p : N ⟶ Z` the vector
bundle of `𝒩`, `C ∈ A^0(W_∞ ⟶ X)` the class of Stacks 0F9J, `j : C_ZX ⟶ W_∞` and
`ι : C_ZX ⟶ N`, a class `c ∈ A^r(Z ⟶ X)` satisfies `p^* ∘ c = ι_* ∘ j^* ∘ C` (read on
`T ×_X N` for every `T ⟶ X` locally of finite type) if and only if it is the class
`c(Z ⟶ X, 𝒩)` of the construction; such a class exists because `p^*` is bijective on Chow groups
(Stacks 02TY). -/
@[stacks 0FBK "(1), constant rank r: c(Z → X, 𝒩) ∈ A^r(Z → X) exists and is the unique class with \
p^* ∘ c = ι_* ∘ j^* ∘ C"]
theorem eq_virtualNormalClass_iff (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hZ r) :
    c = 𝒩.virtualNormalClass C sX sZ hZ r ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sX) k),
        haveI := 𝒩.locallyOfFiniteType_projection r
        haveI := 𝒩.flat_projection r
        middleCap C (gysinSystemOfInvertible C) (𝒩.proj ≫ sZ) sZ 𝒩.proj i
            rfl (-(r : ℤ)) (𝒩.pullbackClass C sZ r) t (k - r) (c.cap t k α) =
          chowGroupDegreeEquiv C (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ sZ))
            (by ring : k - (-(r : ℤ) + r) = k - r - -(r : ℤ))
            ((𝒩.pushforwardClass C sX sZ hZ r).cap t k α) := by
  refine ⟨fun hc => ?_, 𝒩.eq_virtualNormalClass_of_middleCap C sX sZ hZ r c⟩
  subst hc
  exact fun t _ k α => 𝒩.middleCap_virtualNormalClass_cap C sX sZ hZ r t k α

/-- **Stacks 0FBK (1).** The degree `p` part of `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧`, restricted to the
piece `Z_k ⟶ W_k` of a connected component `Z_k` of `Z` (Stacks 0FDZ), is the class
`c(Z_k ⟶ W_k, 𝒩|_{Z_k})` of the construction when `𝒩` has rank `p` on `Z_k`, and zero otherwise. -/
@[stacks 0FBK "(1): the degree p part of c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ restricts on each connected \
component Z_k to the class of the construction for 𝒩|Z_k if 𝒩 has rank p there, else to zero"]
theorem restriction_completedClass (p : ℤ) (k : _root_.ConnectedComponents Z) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    bivariantPieceRestrictionOfInvertible C sZ sX i hZ p Z.connectedComponentOpens
        (componentAmbient i) id (le_preimage_componentAmbient i) k
        (completedBivariantSequenceOfInvertible C sZ sX i hZ (𝒩.completedClass C sX sZ hZ) p) =
      𝒩.componentFamily C sX sZ hZ p k := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  rw [completedBivariantSequenceOfInvertible_completedClass]
  exact 𝒩.bivariantPieceRestrictionOfInvertible_degreeClass C sX sZ hZ p k

/-- **Stacks 0FBK (1), uniqueness.** `c(Z ⟶ X, 𝒩)` is the only element of `A^*(Z ⟶ X)^∧` whose
degree `p` parts restrict on the connected components of `Z` to the classes of the construction
in the degree of the rank of `𝒩`, and to zero in the other degrees. -/
@[stacks 0FBK "(1), uniqueness: c(Z → X, 𝒩) is the only element of A^*(Z → X)^∧ with these \
restrictions to the connected components"]
theorem eq_completedClass_of_restriction
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sX i hZ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    (∀ (p : ℤ) (k : _root_.ConnectedComponents Z),
      bivariantPieceRestrictionOfInvertible C sZ sX i hZ p Z.connectedComponentOpens
          (componentAmbient i) id (le_preimage_componentAmbient i) k
          (completedBivariantSequenceOfInvertible C sZ sX i hZ c p) =
        𝒩.componentFamily C sX sZ hZ p k) →
      c = 𝒩.completedClass C sX sZ hZ := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  intro hc
  refine completedBivariantSequence_injective C (gysinSystemOfInvertible C) sZ sX i hZ
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (funext fun p => ?_)
  refine (bivariantPieceEquivOfInvertible C sZ sX i hZ p Z.connectedComponentOpens
    (componentAmbient i) id (le_preimage_componentAmbient i)
    Z.isClopenDecomposition_connectedComponentOpens).injective (funext fun k => ?_)
  exact (hc p k).trans (𝒩.restriction_completedClass C sX sZ hZ p k).symm

/-- **Stacks 0FBK (2), compatibility with base change.** For `h : X' ⟶ X` locally of finite type,
`Z' = Z ×_X X'` and the virtual normal bundle `𝒩' = g^*𝒩` of Stacks 0FBJ for `Z' ⟶ X'`,
`c(Z' ⟶ X', 𝒩')` is the restriction `res(c(Z ⟶ X, 𝒩))` of Stacks 0F9Z, on the completed groups
of Stacks 0FE0. -/
@[stacks 0FBK "(2): c(Z' → X', g^*𝒩) = res(c(Z → X, 𝒩)) in A^*(Z' → X')^∧ for every X' → X \
locally of finite type"]
theorem baseChange_completedClass {X' : Scheme.{u}} (h : X' ⟶ X) [LocallyOfFiniteType h] :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sX)
    haveI := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i h ≫ sZ)
    (𝒩.baseChangePullback h).completedClass C (h ≫ sX) (pullback.fst i h ≫ sZ)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hZ h) =
      completedBivariantRestrictionOfInvertible C sZ sX i hZ h (𝒩.completedClass C sX sZ hZ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sX)
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i h ≫ sZ)
  exact 𝒩.completedClass_baseChange h C sX sZ hZ

/-- **Stacks 0FBK (3).** If `𝒩` has constant rank `r`, then `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)`: its degree
`r` part is the class `c(Z ⟶ X, 𝒩)` of the construction (the unique class with
`p^* ∘ c = ι_* ∘ j^* ∘ C`) and its other parts vanish. -/
@[stacks 0FBK "(3): for 𝒩 of constant rank r, c(Z → X, 𝒩) lies in A^r(Z → X): its degree r part \
is the class of the construction and its other parts vanish"]
theorem completedClass_of_constantRank (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] (p : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    completedBivariantSequenceOfInvertible C sZ sX i hZ (𝒩.completedClass C sX sZ hZ) p =
      if h : (r : ℤ) = p then h ▸ 𝒩.virtualNormalClass C sX sZ hZ r else 0 := by
  have := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  exact 𝒩.completedBivariantSequenceOfInvertible_completedClass_of_rank C sX sZ hZ r p

end Stacks.Chow.VirtualNormalBundle

end
