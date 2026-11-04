module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinCompletedCap
public import StacksCore.Tactic.StacksAttribute

/-!
# `f^![Y] = [X]` for the Gysin map of a local complete intersection morphism

Let `(S, δ)` be as in Situation 02QL and `f : X ⟶ Y` a local complete intersection morphism of
schemes locally of finite type over `S` for which the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of
Stacks 0FF3 exists, built from a factorization `f = g ∘ i` with `i : X ⟶ P` an immersion and
`g : P ⟶ Y` smooth. Stacks 0FF8 asserts, for `X` and `Y` satisfying the equivalent conditions of
Stacks 0FE3 (for example `Y` Cohen–Macaulay),

  `f^![Y] = [X]`   in `CH^0(X)`,

with `[X] = ∑_n [X_n]_n` the fundamental class of Stacks 0FE4.

## The argument

On a connected component `X_k` of `X`, lying over the connected component `U_a` of the open
`U ⊆ P` in which `i` is closed and over the connected component `Y_j` of `Y`, the class `f^!` has
the single entry `c_{r}(X_k ⟶ U_a, 𝒩) ∘ (g|_{U_a})^*` in degree `r - d`, `r` the rank of the normal
sheaf `𝒩` of `i` on `X_k` and `d` the relative dimension of `g` on `U_a`. If the generic points of
`Y_j` have δ-dimension `m`, then `g^*[Y_j]_m = [U_a]_{m + d}` (Stacks 02RE),
`c_r(X_k ⟶ U_a, 𝒩) ∩ [U_a]_{m + d} = [X_k]_{m + d - r}` (Stacks 0FBM for the normal sheaf of a
regular immersion), and the generic points of `X_k` have δ-dimension `m + d - r`
(`Stacks.Chow.relativeDimension_genericPoint_eq`); this is
`Stacks.Chow.completedCap_regularSmooth_componentFundamentalClass`. Neither the Cohen–Macaulay
hypothesis nor anything about `X` beyond `f` being a local complete intersection is used.

## Main results

* `Stacks.Chow.lciGysinClass_completedCap_componentFundamentalClass` — `f^![Y_j] = [X_k]` on every
  connected component, for `Y` satisfying the conditions of Stacks 0FE3.
* `Stacks.Chow.lciGysinClass_completedCapDegreeZero_fundamentalClass` — **Stacks 0FF8 (b)**,
  `f^![Y] = [X]` in `CH^0(X)`.

## References

* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Congr

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- The cap product of a completed class transported between the completed groups of two equal
morphisms (`Stacks.Chow.completedBivariantGroupCongr`) on the fundamental classes of the
components. -/
theorem completedCap_completedBivariantGroupCongr_componentFundamentalClass {f f' : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX)
    (hf' : f' ≫ sY = sX) (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (h : ∀ k n, completedCap C sX sY f hf c (componentFundamentalClass C sY) k n =
      componentFundamentalClass C sX k n) (k : _root_.ConnectedComponents X) (n : ℤ) :
    completedCap C sX sY f' hf'
        (completedBivariantGroupCongr C (gysinSystemOfInvertible C) sX sY hff hf hf' c)
        (componentFundamentalClass C sY) k n =
      componentFundamentalClass C sX k n := by
  subst hff
  exact h k n

end Congr

section Gysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hfs : f ≫ sY = sX)
  (hf : IsLocalCompleteIntersectionMorphism f) (F : SmoothFactorization f)

/-- **`f^![Y_j] = [X_k]` on the connected components.** For `f` a local complete intersection
morphism with Gysin map `f^!` (Stacks 0FF3) and `Y` satisfying the equivalent conditions of
Stacks 0FE3, the cap product of `f^!` with the fundamental classes `[Y_j]` of the connected
components of `Y` (in every degree) is the family of fundamental classes `[X_k]` of the connected
components of `X`. No hypothesis on `X` is needed. -/
theorem lciGysinClass_completedCap_componentFundamentalClass
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (k : _root_.ConnectedComponents X) (n : ℤ) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian sY
    completedCap C sX sY f hfs (lciGysinClass C sX sY f hfs hf F)
        (componentFundamentalClass C sY) k n =
      componentFundamentalClass C sX k n := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have := LocallyOfFiniteType.isLocallyNoetherian (F.closedAmbientStructure C sY)
  exact completedCap_completedBivariantGroupCongr_componentFundamentalClass C sX sY
    F.closedImm_closedProj _ hfs _
    (fun k n => completedCap_regularSmooth_componentFundamentalClass C sX sY F.closedImm
      (F.isRegularImmersion_closedImm hf) F.closedProj
      (F.closedImm_comp_closedAmbientStructure C sX sY hfs) hY k n) k n

/-- **Stacks 0FF8 (b), `f^![Y] = [X]`.** Let `f : X ⟶ Y` be a local complete intersection morphism
of schemes locally of finite type over `S` with Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3
(built from a factorization `F`), and let `X` and `Y` satisfy the equivalent conditions of
Stacks 0FE3. Then

  `f^![Y] = [X]`   in `CH^0(X) = ∏_n CH_n(X_n)`,

with `[X] = ∑_n [X_n]_n` and `[Y]` the fundamental classes of Stacks 0FE4 and `f^! ∩ -` the cap
product of the completed class on `CH^0` (`Stacks.Chow.completedCapDegreeZero`).

The source adds "for example if `Y` is Cohen–Macaulay"; that is only a sufficient condition for
the hypothesis of Stacks 0FE3 on `Y`, which is all that is assumed here. The hypothesis on `X`
enters only to write `[X]` as an element of `CH^0(X)`: the identity of the classes on the
connected components, `Stacks.Chow.lciGysinClass_completedCap_componentFundamentalClass`, needs
the hypothesis on `Y` alone. -/
@[stacks 0FF8 "second assertion: f^![Y] = [X] in CH^0(X) for X and Y satisfying the conditions of \
Tag 0FE3, with [X], [Y] the fundamental classes of Tag 0FE4 and f^! the Gysin map of Tag 0FF3; \
the source's example hypothesis that Y is Cohen-Macaulay is not needed"]
theorem lciGysinClass_completedCapDegreeZero_fundamentalClass
    (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY)) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := LocallyOfFiniteType.isLocallyNoetherian sY
    completedCapDegreeZero C sX hX sY f hfs hY (lciGysinClass C sX sY f hfs hf F)
        (fundamentalClass C sY hY) =
      fundamentalClass C sX hX := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  exact completedCapDegreeZero_fundamentalClass_of C sX hX sY f hfs hY _
    (lciGysinClass_completedCap_componentFundamentalClass C sX sY f hfs hf F hY)

end Gysin

end Stacks.Chow

end
