module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SurjectionSiteEdgeMaps
public import StacksFrontier.Cotangent.SurjectionSiteFootnoteVanishing

/-!
# The second family of edge maps and the five term exact sequence of Remark 08RG

Let `A → B` be a **surjective** ring map with `I = ker(A → B)`, let `C_{B/A}` be the small model
`CommAlgCat.smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)` of the
polynomial site, write `H_i(C_{B/A}, ℱ) = (L_i colim)(ℱ)` for the homology of the site
([Stacks, Tag 08PF]), let `Ō = 𝒪 ⊗_A B̲` and let `𝒦ⁿ` be the `n`-th power of its augmentation
ideal.

`StacksFrontier.Cotangent.SurjectionSiteEdgeMaps` constructs the remark's second family of edge
maps and its five term exact sequence of low degree terms, but with the footnote vanishing

`H_j(C_{B/A}, 𝒦ⁿ) = 0` for `j < n`

as an explicit hypothesis `hvan`, and so registers no tag on any of them: that vanishing is the
footnote in the proof of [Stacks, Tag 08RF], a result the source itself proves, and a tag may
not sit on a declaration that assumes it.  `hvan` is now a theorem for a surjective `A → B` —
`isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional` in
`CommAlgCat`, whose two halves are the dévissage of
`StacksFrontier.Cotangent.SurjectionSiteFootnoteVanishing` and the pro-nilpotence
`CommAlgCat.smallPolynomialAugmentationProNilpotent` of
`StacksFrontier.Cotangent.SurjectionSiteProNilpotent`.

This file restates those six declarations with that binder discharged, under the remark's own
hypothesis and nothing more.  The hypothesis-carrying forms are kept where they are: a caller
with a vanishing of its own, at a cardinal or in a situation the surjective case does not cover,
still wants them.

## Main definitions

* `CommAlgCat.symmetricPowerToTorEdge_of_surjective`: **the second family of edge maps of
  [Stacks, Tag 08RG]**, `∧^i_B(I/I²) → Tor_i^A(B, B)` for `i > 0`.
* `CommAlgCat.fiveTermConnecting_of_surjective`: the middle map
  `H^{-3}(L_{B/A}) ⟶ ∧²_B(I/I²)` of the remark's five term sequence.

## Main results

* `CommAlgCat.exact_fiveTerm_cotangentNegThree_of_surjective`,
  `CommAlgCat.exact_fiveTerm_exteriorSquare_of_surjective`,
  `CommAlgCat.exact_fiveTerm_torTwo_of_surjective` and
  `CommAlgCat.epi_fiveTerm_torToCotangentEdge_two_of_surjective`: **the five term exact sequence
  of low degree terms of [Stacks, Tag 08RG]**, exact at each of its three interior terms and
  ending in zero.

## What carries the tag, and what does not

The source of the second family is written `∧^i_B(I/I²)` by the remark and
`H_i(C_{B/A}, Sym^i_{B̲}(Ω))` here.  Those are the same object by the remark's own second clause,
`CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective`, which this
library has for a surjective `A → B` and which already carries the `@[stacks 08RG]` of that
clause; the two of them are the covering set of the second family.  The clause produces its
linear equivalence inside a `Nonempty` — Remark 08SG is reached by décalage, which chooses an
isomorphism rather than constructing a canonical one — so there is no canonical map *out of*
`∧^i_B(I/I²)` to be had, and the edge map has to be stated at `H_i(C_{B/A}, Sym^i_{B̲}(Ω))`.

The five term exact sequence is registered on the four declarations that state its exactness and
its final zero: they are its covering set, and each of them names, in its own statement, every
map of the sequence it involves.  `CommAlgCat.fiveTermConnecting_of_surjective` constructs the
middle map alone and asserts nothing about the sequence, so it carries no tag, exactly as
`CommAlgCat.augmentationGradedOneδ` does not.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The second family of edge maps -/

/-- **The second family of edge maps of Stacks Remark 08RG**, for a surjective `A → B` and on no
other hypothesis: for every `i > 0` a map

`∧^i_B(I/I²) = H_i(C_{B/A}, Sym^i_{B̲}(Ω)) ⟶ Tor_i^A(B, B)`.

This is `CommAlgCat.symmetricPowerToTorEdge` with its hypothesis `hvan` discharged by
`isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional`,
the footnote vanishing of [Stacks, Tag 08RF]. The map itself is the remark's own, read off the
filtration `… ⊆ 𝒦² ⊆ 𝒦 ⊆ Ō` of the abutment. -/
@[stacks 08RG "the second family of edge maps, ∧^i_B(I/I²) → Tor_i^A(B, B) for every i > 0, for \
  a surjective A → B with I = ker(A → B). It is the remark's own map, read -- as the remark \
  reads it -- off the filtration … ⊆ 𝒦² ⊆ 𝒦 ⊆ Ō of the abutment, where Ō = 𝒪 ⊗_A B̲ and \
  𝒦 = ker(Ō → B̲) are presheaves on C_{B/A}: the composite \
  H_i(C_{B/A}, Sym^i(Ω)) ≅ H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹) ≅ H_i(C_{B/A}, 𝒦ⁱ) ⟶ H_i(C_{B/A}, 𝒦) ≅ \
  H_i(C_{B/A}, Ō) ≅ Tor_i^A(B, B), whose middle isomorphism is the diagonal identification \
  H_i(C_{B/A}, 𝒦ⁱ) ≅ H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹) and whose arrow is induced by the inclusion \
  𝒦ⁱ ⊆ 𝒦. Tor_i^A(B, B) is RingTheory.TorProducts.torBaseChange, the i-th left derived functor \
  of extension of scalars along A → B, in which this development identifies the abutment \
  H_i(C_{B/A}, Ō) of Theorem 08RF; and H_i(C_{B/A}, -) = L_i colim over the opposite of the \
  small model of the footnote-restricted site is Tag 08PF's definition of the homology of a \
  category. The source is written ∧^i_B(I/I²) by the remark and H_i(C_{B/A}, Sym^i_{B̲}(Ω)) \
  here; they are the same object by the remark's own second clause, which this library has \
  unconditionally as \
  CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective, and that \
  clause is the other declaration of this part's covering set. It is stated at the symmetric \
  power because the clause produces its linear equivalence inside a Nonempty -- Remark 08SG is \
  reached by décalage, which chooses an isomorphism rather than constructing a canonical one -- \
  so there is no canonical map out of ∧^i_B(I/I²) to be had. The construction needs the \
  footnote vanishing H_j(C_{B/A}, 𝒦ⁿ) = 0 for j < n of the proof of Theorem 08RF, which is a \
  theorem here for every surjective A → B, so no hypothesis beyond the remark's own \
  surjectivity is carried"]
def symmetricPowerToTorEdge_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) (i : ℕ) (hi : 0 < i) :
    (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B
            (standardResolutionVarCardinal A B)) i) ⟶
      (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) i).obj
        (ModuleCat.of A (B : Type u)) :=
  symmetricPowerToTorEdge A B i hi
    (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
      A B hsurj)

/-! ### The five term exact sequence of low degree terms -/

/-- **The middle map `H^{-3}(L_{B/A}) ⟶ ∧²_B(I/I²)` of the five term exact sequence of Stacks
Remark 08RG**, for a surjective `A → B` and on no other hypothesis: the connecting morphism
`H_3(C_{B/A}, 𝒦/𝒦²) ⟶ H_2(C_{B/A}, 𝒦²)` of the long exact sequence of
`0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0`, read through the identifications of the two ends.

This is `CommAlgCat.fiveTermConnecting` with its hypothesis `hvan` discharged.

It constructs one map of the sequence and asserts nothing about the sequence itself, so it
carries no `@[stacks 08RG]`; the four declarations below do. -/
def fiveTermConnecting_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    (cotangentComplex.{u, u} A B).homology (-((3 : ℕ) : ℤ)) ⟶
      (siteHomologyFunctor A B (standardResolutionVarCardinal A B) 2).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B
            (standardResolutionVarCardinal A B)) 2) :=
  fiveTermConnecting A B
    (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
      A B hsurj)

/-- **The five term exact sequence of Stacks Remark 08RG, exactness at `H^{-3}(L_{B/A})`**, for
a surjective `A → B` and on no other hypothesis: the image of the edge map
`Tor_3^A(B, B) → H^{-3}(L_{B/A})` is the kernel of the middle map `H^{-3}(L_{B/A}) → ∧²_B(I/I²)`.

This is `CommAlgCat.exact_fiveTerm_cotangentNegThree` with its hypothesis `hvan` discharged. -/
@[stacks 08RG "the five term exact sequence of low degree terms, \
  Tor_3^A(B, B) → H^{-3}(L_{B/A}) → ∧²_B(I/I²) → Tor_2^A(B, B) → H^{-2}(L_{B/A}) → 0, for a \
  surjective A → B with I = ker(A → B) -- exactness at H^{-3}(L_{B/A}). The sequence is the \
  five term segment of the long exact sequence of 0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0 on C_{B/A} read \
  through the remark's identifications H_i(C_{B/A}, 𝒦) = Tor_i^A(B, B) for i ≥ 1, \
  H_i(C_{B/A}, 𝒦/𝒦²) = H^{-i}(L_{B/A}) and H_2(C_{B/A}, 𝒦²) = H_2(C_{B/A}, Sym²(Ω)) = \
  ∧²_B(I/I²), the last of these being the remark's second clause \
  (CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective); its first \
  and fourth maps are the first family of edge maps, CommAlgCat.torToCotangentEdge, its third \
  is the second family, CommAlgCat.symmetricPowerToTorEdge_of_surjective, and its second is \
  CommAlgCat.fiveTermConnecting_of_surjective. The covering set of this part is this \
  declaration together with CommAlgCat.exact_fiveTerm_exteriorSquare_of_surjective, \
  CommAlgCat.exact_fiveTerm_torTwo_of_surjective and \
  CommAlgCat.epi_fiveTerm_torToCotangentEdge_two_of_surjective, which state exactness at the \
  other two interior terms and the final → 0. No spectral sequence is involved. The footnote \
  vanishing H_j(C_{B/A}, 𝒦ⁿ) = 0 for j < n of the proof of Theorem 08RF, which the sequence \
  needs, is a theorem here for every surjective A → B, so no hypothesis beyond the remark's own \
  surjectivity is carried"]
theorem exact_fiveTerm_cotangentNegThree_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    (ShortComplex.mk (torToCotangentEdge A B 3 (by norm_num))
      (fiveTermConnecting_of_surjective A B hsurj)
      (torToCotangentEdge_comp_fiveTermConnecting A B
        (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
          A B hsurj))).Exact :=
  exact_fiveTerm_cotangentNegThree A B _

/-- **The five term exact sequence of Stacks Remark 08RG, exactness at `∧²_B(I/I²)`**, for a
surjective `A → B` and on no other hypothesis: the image of the middle map
`H^{-3}(L_{B/A}) → ∧²_B(I/I²)` is the kernel of the second edge map `∧²_B(I/I²) → Tor_2^A(B, B)`.

This is `CommAlgCat.exact_fiveTerm_exteriorSquare` with its hypothesis `hvan` discharged. -/
@[stacks 08RG "the five term exact sequence of low degree terms, \
  Tor_3^A(B, B) → H^{-3}(L_{B/A}) → ∧²_B(I/I²) → Tor_2^A(B, B) → H^{-2}(L_{B/A}) → 0, for a \
  surjective A → B with I = ker(A → B) -- exactness at ∧²_B(I/I²), the term the remark writes \
  ∧²_B(I/I²) and this development spells H_2(C_{B/A}, Sym²_{B̲}(Ω)), the two being the same \
  object by the remark's second clause \
  (CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective). The \
  sequence is the five term segment of the long exact sequence of 0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0 on \
  C_{B/A} read through the remark's identifications H_i(C_{B/A}, 𝒦) = Tor_i^A(B, B) for i ≥ 1 \
  and H_i(C_{B/A}, 𝒦/𝒦²) = H^{-i}(L_{B/A}). The covering set of this part is this declaration \
  together with CommAlgCat.exact_fiveTerm_cotangentNegThree_of_surjective, \
  CommAlgCat.exact_fiveTerm_torTwo_of_surjective and \
  CommAlgCat.epi_fiveTerm_torToCotangentEdge_two_of_surjective. The footnote vanishing \
  H_j(C_{B/A}, 𝒦ⁿ) = 0 for j < n of the proof of Theorem 08RF, which the sequence needs, is a \
  theorem here for every surjective A → B, so no hypothesis beyond the remark's own \
  surjectivity is carried"]
theorem exact_fiveTerm_exteriorSquare_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    (ShortComplex.mk (fiveTermConnecting_of_surjective A B hsurj)
      (symmetricPowerToTorEdge_of_surjective A B hsurj 2 (by norm_num))
      (fiveTermConnecting_comp_symmetricPowerToTorEdge A B
        (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
          A B hsurj))).Exact :=
  exact_fiveTerm_exteriorSquare A B _

/-- **The five term exact sequence of Stacks Remark 08RG, exactness at `Tor_2^A(B, B)`**, for a
surjective `A → B` and on no other hypothesis: the image of the second edge map
`∧²_B(I/I²) → Tor_2^A(B, B)` is the kernel of the first edge map
`Tor_2^A(B, B) → H^{-2}(L_{B/A})`.

This is `CommAlgCat.exact_fiveTerm_torTwo` with its hypothesis `hvan` discharged. -/
@[stacks 08RG "the five term exact sequence of low degree terms, \
  Tor_3^A(B, B) → H^{-3}(L_{B/A}) → ∧²_B(I/I²) → Tor_2^A(B, B) → H^{-2}(L_{B/A}) → 0, for a \
  surjective A → B with I = ker(A → B) -- exactness at Tor_2^A(B, B), which is \
  RingTheory.TorProducts.torBaseChange in degree 2, the second left derived functor of \
  extension of scalars along A → B applied to B, in which this development identifies the \
  abutment H_2(C_{B/A}, Ō) of Theorem 08RF. The sequence is the five term segment of the long \
  exact sequence of 0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0 on C_{B/A} read through the remark's \
  identifications H_i(C_{B/A}, 𝒦) = Tor_i^A(B, B) for i ≥ 1, \
  H_i(C_{B/A}, 𝒦/𝒦²) = H^{-i}(L_{B/A}) and H_2(C_{B/A}, 𝒦²) = ∧²_B(I/I²). The covering set of \
  this part is this declaration together with \
  CommAlgCat.exact_fiveTerm_cotangentNegThree_of_surjective, \
  CommAlgCat.exact_fiveTerm_exteriorSquare_of_surjective and \
  CommAlgCat.epi_fiveTerm_torToCotangentEdge_two_of_surjective. The footnote vanishing \
  H_j(C_{B/A}, 𝒦ⁿ) = 0 for j < n of the proof of Theorem 08RF, which the sequence needs, is a \
  theorem here for every surjective A → B, so no hypothesis beyond the remark's own \
  surjectivity is carried"]
theorem exact_fiveTerm_torTwo_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    (ShortComplex.mk (symmetricPowerToTorEdge_of_surjective A B hsurj 2 (by norm_num))
      (torToCotangentEdge A B 2 (by norm_num))
      (symmetricPowerToTorEdge_comp_torToCotangentEdge A B
        (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
          A B hsurj))).Exact :=
  exact_fiveTerm_torTwo A B _

/-- **The five term exact sequence of Stacks Remark 08RG ends in zero**, for a surjective
`A → B` and on no other hypothesis: the first edge map `Tor_2^A(B, B) → H^{-2}(L_{B/A})` is
surjective.

This is `CommAlgCat.epi_fiveTerm_torToCotangentEdge_two` with its hypothesis `hvan`
discharged. -/
@[stacks 08RG "the five term exact sequence of low degree terms, \
  Tor_3^A(B, B) → H^{-3}(L_{B/A}) → ∧²_B(I/I²) → Tor_2^A(B, B) → H^{-2}(L_{B/A}) → 0, for a \
  surjective A → B with I = ker(A → B) -- the final → 0, i.e. surjectivity of the last map \
  Tor_2^A(B, B) → H^{-2}(L_{B/A}), which is the first family of edge maps \
  (CommAlgCat.torToCotangentEdge) in degree 2. It holds because H_1(C_{B/A}, 𝒦²) = 0, the \
  footnote vanishing of the proof of Theorem 08RF at j = 1 < 2 = n, which is a theorem here for \
  every surjective A → B; so no hypothesis beyond the remark's own surjectivity is carried. The \
  covering set of this part is this declaration together with \
  CommAlgCat.exact_fiveTerm_cotangentNegThree_of_surjective, \
  CommAlgCat.exact_fiveTerm_exteriorSquare_of_surjective and \
  CommAlgCat.exact_fiveTerm_torTwo_of_surjective, which state exactness at the sequence's three \
  interior terms"]
theorem epi_fiveTerm_torToCotangentEdge_two_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) :
    Epi (torToCotangentEdge A B 2 (by norm_num)) :=
  epi_fiveTerm_torToCotangentEdge_two A B
    (isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
      A B hsurj)

end CommAlgCat

end
