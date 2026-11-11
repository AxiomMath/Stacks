module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassInvertibleTwist

/-!
# Stacks 0ES4: the Chern classes of a twist by an invertible module

In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`
and let `ℒ` be an invertible `𝒪_X`-module. **Stacks 0ES4** asserts

  `c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} C(r - i + j, j) c_{i-j}(ℰ) c₁(ℒ)^j`   in `A^*(X)`.

The classes are those of Stacks 0ERZ: `c_j(ℰ) ∈ A^j(X)` is `AlgebraicGeometry.Space.chernClass`,
the bivariant class whose cap operation on a good test space `g : X' ⟶ X` is the map
`c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')` of Stacks 0ERY (`AlgebraicGeometry.Space.chernCap`, read on
`X ×_X X' ≅ X'` by `AlgebraicGeometry.Space.chernClass_cap`). The product of `A^*(X)` is
composition of bivariant classes (Stacks 0ERK), and a class is determined by its cap operations
(Stacks 0ERJ). So the identity in `A^*(X)` is the identity

  `c_i(ℰ ⊗ ℒ) ∩ - = ∑_{j=0}^{i} C(r - i + j, j) (c_{i-j}(ℰ) ∩ -) ∘ (c₁(ℒ) ∩ -)^j`

of operations on `⨁_k CH_k(X')`, for every good test space `g : X' ⟶ X`, which is what is stated
here (`AlgebraicGeometry.Space.chernCapGraded` is `c_j(ℰ) ∩ -` on `⨁_k CH_k(X')`).

## Main results

* `AlgebraicGeometry.Space.chernCapGraded_tensorObj_of_isInvertibleModule`: **Stacks 0ES4.**

## Implementation notes

The proof is the source's ("identical to the proof of Lemma 02UD"), carried out on every test
space `X'`: the cap operations of Stacks 0ERY on `X'` are the Chern classes of the inverse images
`g^*ℰ`, `g^*ℒ`, `g^*(ℰ ⊗ ℒ) ≅ g^*ℰ ⊗ g^*ℒ` on `CH_*(X')`
(`AlgebraicGeometry.Space.chowGroupCanonicalGradedToChowHomology_chernCapGraded`), for which the
formula is proved by the splitting principle
(`AlgebraicGeometry.Space.chernCap_tensorObj_of_isInvertibleModule`), and the identification of
`⨁_k CH_k(X')` with `CH_*(X')` is injective.

## References

* [Stacks Project, Tag 0ES4](https://stacks.math.columbia.edu/tag/0ES4)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

open PrivateChern

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Stacks 0ES4, the Chern classes of a twist by an invertible module.** In Situation 0EDT let
`X/B` be good, let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` and let `ℒ` be an
invertible `𝒪_X`-module; `ℰ ⊗ ℒ` is finite locally free of rank `r`. Then for every
`i = 0, …, r` (the range of the Chern classes of Definition 0ERZ)

  `c_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} C(r - i + j, j) c_{i-j}(ℰ) c₁(ℒ)^j`   in `A^*(X)`,

for the Chern classes `c_j ∈ A^j(X)` of Stacks 0ERZ (`AlgebraicGeometry.Space.chernClass`); for
`j ≤ i ≤ r` the source's `C(r - i + j, j)` is written `C(r + j - i, j)` in natural numbers.

The product of `A^*(X)` is composition (Stacks 0ERK) and a bivariant class is determined by its
cap operations on the good test spaces `g : X' ⟶ X` (Stacks 0ERJ), the cap operation of
`c_j(ℰ)` on `X'` being `c_j(ℰ) ∩ -` of Stacks 0ERY (`AlgebraicGeometry.Space.chernClass_cap`).
The identity is stated as that of the cap operations on `⨁_k CH_k(X')` for every good
`g : X' ⟶ X`: `c_j(ℰ) ∩ -` is `chernCapGraded`, and the product is composition. -/
@[stacks 0ES4 "c_i(E ⊗ L) = sum_{j=0}^{i} binom(r-i+j, j) c_{i-j}(E) c_1(L)^j in A^*(X) for the \
Chern classes of Definition 0ERZ (chernClass), as the identity of their cap operations of \
Lemma 0ERY on ⊕_k CH_k(X') (chernCapGraded, product = composition) for every good test space \
X' → X"]
theorem chernCapGraded_tensorObj_of_isInvertibleModule
    {E L : Modules.{u, u} D.site D.base D.base_mem X hX.1} {r : ℕ}
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E r)
    (hL : IsInvertibleModule (goodSpace hX) L) (i : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) :
    chernCapGraded D sX hX (E ⊗ L) r
        (isFiniteLocallyFreeOfRank_tensorObj_of_isInvertibleModule hE hL) g hY i =
      ∑ j : Fin ((i : ℕ) + 1), ((r + (j : ℕ) - (i : ℕ)).choose (j : ℕ) : ℤ) •
        (chernCapGraded D sX hX E r hE g hY ⟨(i : ℕ) - (j : ℕ), by have := i.isLt; omega⟩ *
          chernCapGraded D sX hX L 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL) g hY 1 ^
            (j : ℕ)) := by
  let a : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
    ObjectProperty.homMk g
  have hEL := isFiniteLocallyFreeOfRank_tensorObj_of_isInvertibleModule hE hL
  have hL1 := isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL
  have hF : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) r :=
    PrivateChern.isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem a hE
  have hG : IsInvertibleModule (goodSpace hY) ((spaceModulePullback D hX.1 hY.1 g).obj L) :=
    modulePullbackInvertible a L hL
  have hG1 : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj L) 1 :=
    PrivateChern.isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem a hL1
  have hFG : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj (E ⊗ L)) r :=
    PrivateChern.isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem a hEL
  -- the formula for the Chern classes of the inverse images on `CH_*(X')`
  have hY0 : PrivateChern.chernCap.{u, u + 1} (hX := hY)
      ((spaceModulePullback D hX.1 hY.1 g).obj (E ⊗ L)) r hFG i =
      ∑ j : Fin ((i : ℕ) + 1), ((r + (j : ℕ) - (i : ℕ)).choose (j : ℕ) : ℤ) •
        (PrivateChern.chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E)
            r hF ((i : ℕ) - (j : ℕ)) *
          PrivateChern.chernCap.{u, u + 1} (hX := hY)
            ((spaceModulePullback D hX.1 hY.1 g).obj L) 1 hG1 1 ^ (j : ℕ)) := by
    rw [PrivateChern.chernCap_eq_of_iso hY (@Functor.Monoidal.μIso _ _ _ _ _ _ _
        (modulePullbackMonoidal a) E L).symm r hFG
        (isFiniteLocallyFreeOfRank_tensorObj_of_isInvertibleModule hF hG) i,
      chernCap_tensorObj_of_isInvertibleModule hY hF hG i,
      ← Fin.sum_univ_eq_sum_range (fun j => ((r + j - (i : ℕ)).choose j : ℤ) •
        (PrivateChern.chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E)
            r hF ((i : ℕ) - j) *
          PrivateChern.chernCap.{u, u + 1} (hX := hY)
            ((spaceModulePullback D hX.1 hY.1 g).obj L) 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hY) hG) 1 ^ j))]
  -- transport along the injective identification of `⨁_k CH_k(X')` with `CH_*(X')`
  refine eq_of_intertwines (injective_chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY)
    (fun x => (chowGroupCanonicalGradedToChowHomology_chernCapGraded D sX hX (E ⊗ L) r hEL g hY
      hFG i x).symm)
    (fun x => intertwines_finset_sum _ Finset.univ (fun (j : Fin ((i : ℕ) + 1)) y =>
      intertwines_zsmul _
      (intertwines_mul _
        (fun z => (chowGroupCanonicalGradedToChowHomology_chernCapGraded D sX hX E r hE g hY hF
          ⟨(i : ℕ) - (j : ℕ), by have := i.isLt; omega⟩ z).symm)
        (intertwines_pow _ (fun z => (chowGroupCanonicalGradedToChowHomology_chernCapGraded D sX
          hX L 1 hL1 g hY hG1 1 z).symm) _)) _ y) x) hY0

end AlgebraicGeometry.Space

end
