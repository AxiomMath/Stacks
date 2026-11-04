module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationSymmetricPower
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationTor
public import StacksFrontier.Cotangent.SurjectionSymmetricPowerVanishing

/-!
# The first family of edge maps of Remark 08RG, and the low degree segment

Let `A → B` be a ring map, let `κ` be a cardinal and let `C_{B/A}` be the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the polynomial site.  Write

`H_i(C_{B/A}, ℱ) = (L_i colim)(ℱ)`

for the homology of the site with coefficients in a presheaf `ℱ` of `B`-modules
([Stacks, Tag 08PF]), let `Ō = 𝒪 ⊗_A B̲`, let `𝒦ⁿ` be the `n`-th power of its augmentation
ideal and let `𝒦/𝒦²` be the first graded piece, all from
`StacksFrontier.Cotangent.SurjectionSiteAugmentationFiltration` and
`StacksFrontier.Cotangent.SurjectionSiteAugmentationGraded`.

This file extracts, from the long exact sequence of the short exact sequence of presheaves

`0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0`,

the five term segment

`H_3(C_{B/A}, 𝒦) → H_3(C_{B/A}, 𝒦/𝒦²) → H_2(C_{B/A}, 𝒦²) → H_2(C_{B/A}, 𝒦) →`
`H_2(C_{B/A}, 𝒦/𝒦²) → 0`,

exact at its three interior terms and surjective at its right end.  It is the engine of the five
term exact sequence of [Stacks, Tag 08RG]: under the identifications

* `H_i(C_{B/A}, 𝒦) = H_i(C_{B/A}, Ō) = Tor^A_i(B, B)` for `i ≥ 1`,
* `H_i(C_{B/A}, 𝒦/𝒦²) = H_i(C_{B/A}, Ω) = H^{-i}(L_{B/A})`,
* `H_2(C_{B/A}, 𝒦²) = H_2(C_{B/A}, Sym²(Ω)) = ∧²_B(I/I²)`,

the segment becomes the remark's

`Tor_3^A(B, B) → H^{-3}(L_{B/A}) → ∧²_B(I/I²) → Tor_2^A(B, B) → H^{-2}(L_{B/A}) → 0`.

Composed with the identification of `H_i(C_{B/A}, 𝒦/𝒦²)` with `H^{-i}(L_{B/A})`, the first of
those three identifications turns the map `Tor^A_i(B, B) ⟶ H_i(C_{B/A}, 𝒦/𝒦²)` of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationTor` into the remark's **first family of edge
maps**

`Tor_i^A(B, B) → H^{-i}(L_{B/A})`,  `i > 0`,

which is `CommAlgCat.torToCotangentEdge` below.  Neither that identification nor the map itself
asks anything of `A → B`.

## Main definitions

* `CommAlgCat.siteHomologyFunctor`: the functor `H_i(C_{B/A}, -)`.
* `CommAlgCat.siteHomologyGradedOneCotangentIso`:
  `H_i(C_{B/A}, 𝒦/𝒦²) ≅ H^{-i}(L_{B/A})`, the second and third of the identifications above.
* `CommAlgCat.torToCotangentEdge`: **the first family of edge maps of [Stacks, Tag 08RG]**,
  `Tor_i^A(B, B) ⟶ H^{-i}(L_{B/A})` for `i > 0`.
* `CommAlgCat.augmentationGradedOneδ`: the connecting morphism
  `H_{i+1}(C_{B/A}, 𝒦/𝒦²) ⟶ H_i(C_{B/A}, 𝒦²)` of the long exact sequence of
  `0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0`.
* `CommAlgCat.siteHomologyAugmentationIdealTorIso`:
  `H_i(C_{B/A}, 𝒦) ≅ Tor^A_i(B, B)` for `i > 0`.
* `CommAlgCat.siteHomologySymmetricPowerSelfIso`:
  `H_i(C_{B/A}, 𝒦ⁱ) ≅ H_i(C_{B/A}, Sym^i_{B̲}(Ω))`, on the footnote vanishing.
* `CommAlgCat.symmetricPowerToTorEdge`: the remark's **second** family of edge maps,
  `H_i(C_{B/A}, Sym^i_{B̲}(Ω)) ⟶ Tor_i^A(B, B)` for `i > 0`, on the footnote vanishing.
* `CommAlgCat.fiveTermConnecting`: the middle map `H^{-3}(L_{B/A}) ⟶ H_2(C_{B/A}, Sym²(Ω))` of
  the remark's five term sequence, on the footnote vanishing.

## Main results

* `CommAlgCat.exact_siteHomology_augmentationGradedOne_δ`,
  `CommAlgCat.exact_siteHomology_δ_augmentationIdealSq` and
  `CommAlgCat.exact_siteHomology_augmentationIdealSq_gradedOne`: exactness of the segment at its
  three interior terms, at every degree.
* `CommAlgCat.epi_siteHomology_map_gradedOneπ_of_isZero`: the right end of the segment is
  surjective as soon as `H_i(C_{B/A}, 𝒦²) = 0`, which for `i = 1` is the footnote vanishing of
  [Stacks, Tag 08RF].
* `CommAlgCat.exact_fiveTerm_cotangentNegThree`,
  `CommAlgCat.exact_fiveTerm_exteriorSquare`, `CommAlgCat.exact_fiveTerm_torTwo` and
  `CommAlgCat.epi_fiveTerm_torToCotangentEdge_two`: **the remark's five term exact sequence**,
  exact at each of its three interior terms and ending in zero, on the footnote vanishing.

## What carries the tag, and what does not

`CommAlgCat.torToCotangentEdge` is the one declaration here with a `@[stacks 08RG]` attribute.
It carries no hypothesis at all, so it states the remark's first family of edge maps under the
remark's own hypotheses and nothing more.

The second family and the five term sequence are **not** registered, and must not be: every
declaration below that mentions them takes the footnote vanishing
`H_j(C_{B/A}, 𝒦ⁿ) = 0` for `j < n` as an explicit hypothesis `hvan`, and that vanishing is a
result the source itself proves -- it is the footnote in the proof of [Stacks, Tag 08RF]. A tag
may not sit on a declaration that assumes a result its own source establishes. What those
declarations do instead is reduce both remaining clauses of the remark to that one statement:
the moment `hvan` is available for a surjective `A → B`, `CommAlgCat.symmetricPowerToTorEdge`
and the four five-term results become unconditional and can be registered as they stand.

`hvan` follows from `CommAlgCat.SmallPolynomialAugmentationProNilpotent` by
`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow`; the module docstring
of `StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing` records what is left of it.

The remark writes the source of the second family as `∧^i_B(I/I²)`.  That is
`H_i(C_{B/A}, Sym^i_{B̲}(Ω))` by the remark's own second clause,
`CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective`, which this
library has unconditionally; but that clause produces its linear equivalence inside a `Nonempty`
-- Remark 08SG is reached by décalage, which chooses an isomorphism rather than constructing a
canonical one -- so there is no canonical map *out of* `∧^i_B(I/I²)` to be had, and the maps
below are stated at `H_i(C_{B/A}, Sym^i_{B̲}(Ω))`, which is the same object.

## Implementation notes

Nothing here needs a spectral sequence.  The remark reads its edge maps and its five term
sequence off the filtration of the abutment, and the filtration is a filtration of *presheaves*;
so the long exact sequence of the left derived functors of `colim`
(`CategoryTheory.Functor.leftDerivedδ` and its three exactness lemmas, from
`StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe`) is the only machinery required.  The
three exactness statements below are that long exact sequence at the short exact sequence
`CommAlgCat.smallPolynomialAugmentationGradedShortComplex A B κ 1`, and no hypothesis is used
for them at all.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The homology of the site, as a functor -/

/-- **`H_i(C_{B/A}, -)`**, the homology of the small model of the polynomial site with
coefficients in a presheaf of `B`-modules: the `i`-th left derived functor of the colimit over
the opposite of the site, which is [Stacks, Tag 08PF]'s definition of the homology of a
category. -/
abbrev siteHomologyFunctor (i : ℕ) :
    ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
      ModuleCat.{u} (B : Type u) :=
  (colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) ⥤
    ModuleCat.{u} (B : Type u)).leftDerived i

/-! ### The first family of edge maps -/

/-- **`H_i(C_{B/A}, 𝒦/𝒦²) ≅ H^{-i}(L_{B/A})`.** The conormal map `Ω ≅ 𝒦/𝒦²`
(`CommAlgCat.smallPolynomialCotangentGradedIso`) read on `H_i(C_{B/A}, -)`, followed by Tag 08PU
at linear coefficients (`CommAlgCat.leftDerivedColimPolynomialCotangentIso`), which identifies
`H_i(C_{B/A}, Ω)` with the degree `-i` cohomology of the cotangent complex.

Proved for every ring map `A → B`. -/
def siteHomologyGradedOneCotangentIso (i : ℕ) :
    (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).obj
        (smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) 1) ≅
      (cotangentComplex.{u, u} A B).homology (-(i : ℤ)) :=
  (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).mapIso
      (smallPolynomialCotangentGradedIso A B (standardResolutionVarCardinal A B)).symm ≪≫
    leftDerivedColimPolynomialCotangentIso A B i

/-- **The first family of edge maps of Stacks Remark 08RG**: for every `i > 0` a map

`Tor_i^A(B, B) ⟶ H^{-i}(L_{B/A})`.

It is the remark's own map, read off the filtration `… ⊆ 𝒦² ⊆ 𝒦 ⊆ Ō` of the abutment: the
composite

`Tor^A_i(B, B) ≅ H_i(C_{B/A}, Ō) ≅ H_i(C_{B/A}, 𝒦) ⟶ H_i(C_{B/A}, 𝒦/𝒦²) ≅ H^{-i}(L_{B/A})`

of `CommAlgCat.torToCotangentHomologyEdge` with
`CommAlgCat.siteHomologyGradedOneCotangentIso`.  The first identification is
`CommAlgCat.leftDerivedColimQuotientTorIso`, the second
`CommAlgCat.leftDerivedColimAugmentationIdealIsoOfPos` — available because `H_j(C_{B/A}, B̲)`
vanishes for `j > 0` — the arrow is induced by the projection onto the first graded piece, and
the last identification is `Ω ≅ 𝒦/𝒦²` followed by Tag 08PU.

The remark states these maps for a surjective `A → B`; they exist for every ring map. -/
@[stacks 08RG "the first family of edge maps, Tor_i^A(B, B) → H^{-i}(L_{B/A}) for every i > 0, \
  for a surjective A → B with I = ker(A → B). These are the remark's own edge maps, read -- as \
  the remark reads them -- off the filtration … ⊆ 𝒦² ⊆ 𝒦 ⊆ Ō of the abutment, where \
  Ō = 𝒪 ⊗_A B̲ and 𝒦 = ker(Ō → B̲) are presheaves on C_{B/A}: the composite \
  Tor^A_i(B,B) ≅ H_i(C_{B/A}, Ō) ≅ H_i(C_{B/A}, 𝒦) ⟶ H_i(C_{B/A}, 𝒦/𝒦²) ≅ H^{-i}(L_{B/A}). \
  Tor^A_i(B, B) is RingTheory.TorProducts.torBaseChange, the i-th left derived functor of \
  extension of scalars along A → B, which is the spelling in which this development identifies \
  the abutment H_i(C_{B/A}, Ō) of Theorem 08RF; H^{-i}(L_{B/A}) is the degree -i cohomology of \
  the cotangent complex of Tag 08PN, reached by Tag 08PU at linear coefficients; and \
  H_i(C_{B/A}, -) = L_i colim over the opposite of the small model of the \
  footnote-restricted site is Tag 08PF's definition of the homology of a category. No spectral \
  sequence is involved, and no hypothesis is carried: the construction holds for every ring map \
  A → B, hence in particular for the surjective one of the remark. The remark's SECOND family, \
  ∧^i_B(I/I²) → Tor_i^A(B, B), is not this declaration; it needs the footnote vanishing of \
  Theorem 08RF and is recorded separately"]
def torToCotangentEdge (i : ℕ) (hi : 0 < i) :
    (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) i).obj
        (ModuleCat.of A (B : Type u)) ⟶
      (cotangentComplex.{u, u} A B).homology (-(i : ℤ)) :=
  torToCotangentHomologyEdge A B i hi ≫ (siteHomologyGradedOneCotangentIso A B i).hom

/-- The first edge map in degree `i + 1`, written out as the composite of
`CommAlgCat.torToCotangentHomologyEdgeSucc` with the identification
`H_{i+1}(C_{B/A}, 𝒦/𝒦²) ≅ H^{-i-1}(L_{B/A})`. -/
lemma torToCotangentEdge_succ (i : ℕ) :
    torToCotangentEdge A B (i + 1) i.succ_pos =
      torToCotangentHomologyEdgeSucc A B i ≫
        (siteHomologyGradedOneCotangentIso A B (i + 1)).hom :=
  rfl

/-! ### The connecting morphism of the first graded piece -/

/-- **The connecting morphism `H_{i+1}(C_{B/A}, 𝒦/𝒦²) ⟶ H_i(C_{B/A}, 𝒦²)`** of the long exact
sequence of `0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0`.  At `i = 2` this is the middle map
`H^{-3}(L_{B/A}) → ∧²_B(I/I²)` of the five term exact sequence of [Stacks, Tag 08RG]. -/
def augmentationGradedOneδ (i : ℕ) :
    (siteHomologyFunctor A B κ (i + 1)).obj (smallPolynomialAugmentationGraded A B κ 1) ⟶
      (siteHomologyFunctor A B κ i).obj (smallPolynomialAugmentationIdealPow A B κ 2) :=
  Functor.leftDerivedδ _ (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ 1) i

/-! ### Exactness of the segment -/

/-- **Exactness at `H_{i+1}(C_{B/A}, 𝒦/𝒦²)`**: the image of `H_{i+1}(C_{B/A}, 𝒦)` is the kernel
of the connecting morphism.  At `i = 2` this is exactness of the five term sequence of
[Stacks, Tag 08RG] at `H^{-3}(L_{B/A})`. -/
theorem exact_siteHomology_augmentationGradedOne_δ (i : ℕ) :
    (ShortComplex.mk ((siteHomologyFunctor A B κ (i + 1)).map
        (smallPolynomialAugmentationGradedπ A B κ 1))
      (augmentationGradedOneδ A B κ i)
      (Functor.leftDerived_map_g_comp_δ _
        (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ 1) i)).Exact :=
  Functor.leftDerived_exact_δ₁ _
    (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ 1) i

/-- **Exactness at `H_i(C_{B/A}, 𝒦²)`**: the image of the connecting morphism is the kernel of
the map induced by the inclusion `𝒦² ⊆ 𝒦`.  At `i = 2` this is exactness of the five term
sequence of [Stacks, Tag 08RG] at `∧²_B(I/I²)`. -/
theorem exact_siteHomology_δ_augmentationIdealSq (i : ℕ) :
    (ShortComplex.mk (augmentationGradedOneδ A B κ i)
      ((siteHomologyFunctor A B κ i).map (smallPolynomialAugmentationIdealPowIncl A B κ 1))
      (Functor.leftDerivedδ_comp_map_f _
        (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ 1) i)).Exact :=
  Functor.leftDerived_exact_δ₂ _
    (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ 1) i

/-- **Exactness at `H_i(C_{B/A}, 𝒦)`**: the image of `H_i(C_{B/A}, 𝒦²)` is the kernel of the map
to `H_i(C_{B/A}, 𝒦/𝒦²)`.  At `i = 2` this is exactness of the five term sequence of
[Stacks, Tag 08RG] at `Tor_2^A(B, B)`. -/
theorem exact_siteHomology_augmentationIdealSq_gradedOne (i : ℕ) :
    ((smallPolynomialAugmentationGradedShortComplex A B κ 1).map
      (siteHomologyFunctor A B κ i)).Exact :=
  Functor.leftDerived_exact _
    (shortExact_smallPolynomialAugmentationGradedShortComplex A B κ 1) i

/-- **The right end of the segment is surjective** as soon as `H_i(C_{B/A}, 𝒦²) = 0`: the
cokernel of `H_{i+1}(C_{B/A}, 𝒦) → H_{i+1}(C_{B/A}, 𝒦/𝒦²)` injects into `H_i(C_{B/A}, 𝒦²)` by
`CommAlgCat.exact_siteHomology_augmentationGradedOne_δ`.

At `i = 1` the hypothesis is the footnote vanishing of [Stacks, Tag 08RF],
`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow` at `i = 1 < 2 = n`, and
the conclusion is the final `→ 0` of the five term exact sequence of [Stacks, Tag 08RG]. -/
theorem epi_siteHomology_map_gradedOneπ_of_isZero (i : ℕ)
    (hz : IsZero ((siteHomologyFunctor A B κ i).obj
      (smallPolynomialAugmentationIdealPow A B κ 2))) :
    Epi ((siteHomologyFunctor A B κ (i + 1)).map
      (smallPolynomialAugmentationGradedπ A B κ 1)) :=
  (exact_siteHomology_augmentationGradedOne_δ A B κ i).epi_f (hz.eq_of_tgt _ _)

/-! ### The diagonal: `H_i(C_{B/A}, 𝒦ⁱ) = H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹)` -/

/-- **On the diagonal the projection `𝒦ⁱ → 𝒦ⁱ/𝒦ⁱ⁺¹` is invertible on `H_i(C_{B/A}, -)`**, given
the footnote vanishing of [Stacks, Tag 08RF].

In the long exact sequence of `0 → 𝒦ⁱ⁺¹ → 𝒦ⁱ → 𝒦ⁱ/𝒦ⁱ⁺¹ → 0` the term before
`H_i(C_{B/A}, 𝒦ⁱ)` is `H_i(C_{B/A}, 𝒦ⁱ⁺¹)`, which vanishes because `i < i + 1`, so the map is a
monomorphism; and the term after `H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹)` is `H_{i-1}(C_{B/A}, 𝒦ⁱ⁺¹)`, which
vanishes for the same reason, so the map is an epimorphism — for `i = 0` the long exact sequence
simply ends there and the epimorphism is `CategoryTheory.Functor.epi_leftDerivedZero_map_g`.

This is the identification that turns the remark's `H_i(C_{B/A}, Sym^i(Ω)) = ∧^i_B(I/I²)` into a
map to `H_i(C_{B/A}, Ō) = Tor_i^A(B, B)`, i.e. into the second family of edge maps of
[Stacks, Tag 08RG]. -/
theorem isIso_siteHomology_map_gradedπ_self (i : ℕ)
    (hvan : ∀ j n : ℕ, j < n → IsZero ((siteHomologyFunctor A B κ j).obj
      (smallPolynomialAugmentationIdealPow A B κ n))) :
    IsIso ((siteHomologyFunctor A B κ i).map
      (smallPolynomialAugmentationGradedπ A B κ i)) := by
  have hS := shortExact_smallPolynomialAugmentationGradedShortComplex A B κ i
  have hmono : Mono ((siteHomologyFunctor A B κ i).map
      (smallPolynomialAugmentationGradedπ A B κ i)) :=
    (Functor.leftDerived_exact _ hS i).mono_g
      ((hvan i (i + 1) (Nat.lt_succ_self i)).eq_of_src _ _)
  have hepi : Epi ((siteHomologyFunctor A B κ i).map
      (smallPolynomialAugmentationGradedπ A B κ i)) := by
    cases i with
    | zero => exact Functor.epi_leftDerivedZero_map_g _ hS
    | succ j =>
      exact (Functor.leftDerived_exact_δ₁ _ hS j).epi_f
        ((hvan j (j + 2) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **`H_i(C_{B/A}, 𝒦ⁱ) ≅ H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹)`**, read as an isomorphism. -/
def siteHomologyGradedSelfIso (i : ℕ)
    (hvan : ∀ j n : ℕ, j < n → IsZero ((siteHomologyFunctor A B κ j).obj
      (smallPolynomialAugmentationIdealPow A B κ n))) :
    (siteHomologyFunctor A B κ i).obj (smallPolynomialAugmentationIdealPow A B κ i) ≅
      (siteHomologyFunctor A B κ i).obj (smallPolynomialAugmentationGraded A B κ i) :=
  have := isIso_siteHomology_map_gradedπ_self A B κ i hvan
  asIso ((siteHomologyFunctor A B κ i).map (smallPolynomialAugmentationGradedπ A B κ i))

/-- **`H_i(C_{B/A}, 𝒦ⁱ) ≅ H_i(C_{B/A}, Sym^i_{B̲}(Ω))`**, given the footnote vanishing: the
isomorphism `CommAlgCat.siteHomologyGradedSelfIso` followed by
`CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso`, which identifies the graded
piece `𝒦ⁱ/𝒦ⁱ⁺¹` with the `i`-th symmetric power of `Ω`. -/
def siteHomologySymmetricPowerSelfIso (i : ℕ)
    (hvan : ∀ j n : ℕ, j < n → IsZero ((siteHomologyFunctor A B κ j).obj
      (smallPolynomialAugmentationIdealPow A B κ n))) :
    (siteHomologyFunctor A B κ i).obj (smallPolynomialAugmentationIdealPow A B κ i) ≅
      (siteHomologyFunctor A B κ i).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram (smallBoundedPolynomialSite A B κ)
          (B : Type u) (smallPolynomialCotangentModulePresheaf A B κ) i) :=
  siteHomologyGradedSelfIso A B κ i hvan ≪≫
    (siteHomologyFunctor A B κ i).mapIso
      (smallPolynomialAugmentationGradedSymmetricPowerIso A B κ i)

/-! ### The second family of edge maps -/

/-- **`H_i(C_{B/A}, 𝒦) ≅ Tor^A_i(B, B)` for `i > 0`.** The inclusion `𝒦 ⊆ Ō` is invertible on
`H_i(C_{B/A}, -)` in positive degrees
(`CommAlgCat.leftDerivedColimAugmentationIdealIsoOfPos`), and `H_i(C_{B/A}, Ō)` is the abutment
`Tor^A_i(B, B)` (`CommAlgCat.leftDerivedColimQuotientTorIso`).

Proved for every ring map `A → B`. -/
def siteHomologyAugmentationIdealTorIso (i : ℕ) (hi : 0 < i) :
    (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).obj
        (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) 1) ≅
      (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) i).obj
        (ModuleCat.of A (B : Type u)) :=
  leftDerivedColimAugmentationIdealIsoOfPos A B i hi ≪≫ leftDerivedColimQuotientTorIso A B i

/-- **The second family of edge maps of Stacks Remark 08RG**, in the form in which the homology
of the site carries it: for every `i > 0` a map

`H_i(C_{B/A}, Sym^i_{B̲}(Ω)) ⟶ Tor_i^A(B, B)`,

where the source is `∧^i_B(I/I²)` by the remark's second clause
(`CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective`).

It is the remark's own map, read off the filtration of the abutment: the composite

`H_i(C_{B/A}, Sym^i(Ω)) ≅ H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹) ≅ H_i(C_{B/A}, 𝒦ⁱ) ⟶ H_i(C_{B/A}, 𝒦)
  ≅ H_i(C_{B/A}, Ō) ≅ Tor_i^A(B, B)`,

the middle isomorphism being `CommAlgCat.siteHomologyGradedSelfIso` and the arrow the map
induced by the inclusion `𝒦ⁱ ⊆ 𝒦`.

**This declaration is not a formalization of Tag 08RG and carries no `@[stacks 08RG]`.** It
takes the footnote vanishing `H_j(C_{B/A}, 𝒦ⁿ) = 0` for `j < n` as the hypothesis `hvan`, and
that vanishing is a result the source proves — it is the footnote in the proof of
[Stacks, Tag 08RF]. A tag may not be registered on a declaration that assumes it. The remaining
obligation is `CommAlgCat.SmallPolynomialAugmentationProNilpotent` for a surjective `A → B`;
see the module docstring of
`StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing`. -/
def symmetricPowerToTorEdge (i : ℕ) (hi : 0 < i)
    (hvan : ∀ j n : ℕ, j < n →
      IsZero ((siteHomologyFunctor A B (standardResolutionVarCardinal A B) j).obj
        (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) n))) :
    (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B
            (standardResolutionVarCardinal A B)) i) ⟶
      (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) i).obj
        (ModuleCat.of A (B : Type u)) :=
  (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) i hvan).inv ≫
    (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).map
      (smallPolynomialAugmentationIdealPowMap A B (standardResolutionVarCardinal A B) hi) ≫
    (siteHomologyAugmentationIdealTorIso A B i hi).hom

/-! ### The five term exact sequence of low degree terms -/

/-- A composite of two maps is zero if it is isomorphic, termwise and compatibly, to one that is. -/
private lemma comp_eq_zero_of_iso_comm {C : Type*} [Category C] [Preadditive C]
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁} {f₂ : X₂ ⟶ Y₂} {g₂ : Y₂ ⟶ Z₂}
    (h : f₁ ≫ g₁ = 0) (e₁ : X₁ ≅ X₂) (e₂ : Y₁ ≅ Y₂) (e₃ : Z₁ ≅ Z₂)
    (hf : e₁.hom ≫ f₂ = f₁ ≫ e₂.hom) (hg : e₂.hom ≫ g₂ = g₁ ≫ e₃.hom) : f₂ ≫ g₂ = 0 := by
  rw [← cancel_epi e₁.hom, ← Category.assoc, hf, Category.assoc, hg, ← Category.assoc, h,
    zero_comp, comp_zero]

section FiveTerm

variable
  (hvan : ∀ j n : ℕ, j < n →
    IsZero ((siteHomologyFunctor A B (standardResolutionVarCardinal A B) j).obj
      (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) n)))

/-- **The middle map `H^{-3}(L_{B/A}) ⟶ H_2(C_{B/A}, Sym²_{B̲}(Ω))` of the five term exact
sequence of Stacks Remark 08RG.** It is the connecting morphism
`H_3(C_{B/A}, 𝒦/𝒦²) ⟶ H_2(C_{B/A}, 𝒦²)` of the long exact sequence of
`0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0`, read through `CommAlgCat.siteHomologyGradedOneCotangentIso` on the
left and `CommAlgCat.siteHomologySymmetricPowerSelfIso` on the right. -/
def fiveTermConnecting :
    (cotangentComplex.{u, u} A B).homology (-((3 : ℕ) : ℤ)) ⟶
      (siteHomologyFunctor A B (standardResolutionVarCardinal A B) 2).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B
            (standardResolutionVarCardinal A B)) 2) :=
  (siteHomologyGradedOneCotangentIso A B 3).inv ≫
    augmentationGradedOneδ A B (standardResolutionVarCardinal A B) 2 ≫
    (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan).hom

/-- The identification `H_{i+1}(C_{B/A}, 𝒦) ≅ Tor^A_{i+1}(B, B)` carries the first edge map to
the map induced by the projection `𝒦 ⟶ 𝒦/𝒦²`, followed by
`CommAlgCat.siteHomologyGradedOneCotangentIso`. -/
lemma siteHomologyAugmentationIdealTorIso_comp_torToCotangentEdge (i : ℕ) (hi : 0 < i) :
    (siteHomologyAugmentationIdealTorIso A B i hi).hom ≫ torToCotangentEdge A B i hi =
      (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).map
          (smallPolynomialAugmentationGradedπ A B (standardResolutionVarCardinal A B) 1) ≫
        (siteHomologyGradedOneCotangentIso A B i).hom := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
  have h := congrArg (fun φ => φ ≫ (siteHomologyGradedOneCotangentIso A B (j + 1)).hom)
    (leftDerivedColimSuccAugmentationIdealIso_comp_torToCotangentHomologyEdgeSucc A B j)
  simp only [Category.assoc] at h
  rw [show siteHomologyAugmentationIdealTorIso A B (j + 1) hi =
        leftDerivedColimSuccAugmentationIdealIso A B j ≪≫
          leftDerivedColimQuotientTorIso A B (j + 1) from rfl,
    Iso.trans_hom, torToCotangentEdge, torToCotangentHomologyEdge_succ]
  simp only [Category.assoc]
  exact h

/-- The identification `H_i(C_{B/A}, Sym^i(Ω)) ≅ H_i(C_{B/A}, 𝒦ⁱ)` carries the second edge map
to the map induced by the inclusion `𝒦ⁱ ⊆ 𝒦`. -/
lemma siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge (i : ℕ) (hi : 0 < i) :
    (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) i hvan).hom ≫
        symmetricPowerToTorEdge A B i hi hvan =
      (siteHomologyFunctor A B (standardResolutionVarCardinal A B) i).map
          (smallPolynomialAugmentationIdealPowMap A B
            (standardResolutionVarCardinal A B) hi) ≫
        (siteHomologyAugmentationIdealTorIso A B i hi).hom := by
  rw [symmetricPowerToTorEdge, Iso.hom_inv_id_assoc]

/-- The identification `H^{-3}(L_{B/A}) ≅ H_3(C_{B/A}, 𝒦/𝒦²)` carries the middle map of the
five term sequence to the connecting morphism. -/
lemma siteHomologyGradedOneCotangentIso_comp_fiveTermConnecting :
    (siteHomologyGradedOneCotangentIso A B 3).hom ≫ fiveTermConnecting A B hvan =
      augmentationGradedOneδ A B (standardResolutionVarCardinal A B) 2 ≫
        (siteHomologySymmetricPowerSelfIso A B
          (standardResolutionVarCardinal A B) 2 hvan).hom := by
  rw [fiveTermConnecting, Iso.hom_inv_id_assoc]

/-- The inclusion `𝒦² ⊆ 𝒦` is the `n = 1` step of the filtration. -/
lemma smallPolynomialAugmentationIdealPowMap_one_two :
    smallPolynomialAugmentationIdealPowMap A B (standardResolutionVarCardinal A B)
        (show 1 ≤ 2 by norm_num) =
      smallPolynomialAugmentationIdealPowIncl A B (standardResolutionVarCardinal A B) 1 :=
  rfl

/-- The square identifying the second edge map in degree two with the map induced by the
inclusion `𝒦² ⊆ 𝒦`, in the spelling the long exact sequence uses. -/
lemma siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge_two :
    (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan).hom ≫
        symmetricPowerToTorEdge A B 2 (by norm_num) hvan =
      (siteHomologyFunctor A B (standardResolutionVarCardinal A B) 2).map
          (smallPolynomialAugmentationIdealPowIncl A B
            (standardResolutionVarCardinal A B) 1) ≫
        (siteHomologyAugmentationIdealTorIso A B 2 (by norm_num)).hom := by
  rw [siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge A B hvan 2 (by norm_num),
    smallPolynomialAugmentationIdealPowMap_one_two]

/-- `Tor_3^A(B, B) → H^{-3}(L_{B/A}) → H_2(C_{B/A}, Sym²(Ω))` is a complex. -/
lemma torToCotangentEdge_comp_fiveTermConnecting :
    torToCotangentEdge A B 3 (by norm_num) ≫ fiveTermConnecting A B hvan = 0 :=
  comp_eq_zero_of_iso_comm
    (Functor.leftDerived_map_g_comp_δ _
      (shortExact_smallPolynomialAugmentationGradedShortComplex A B
        (standardResolutionVarCardinal A B) 1) 2)
    (siteHomologyAugmentationIdealTorIso A B 3 (by norm_num))
    (siteHomologyGradedOneCotangentIso A B 3)
    (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan)
    (siteHomologyAugmentationIdealTorIso_comp_torToCotangentEdge A B 3 (by norm_num))
    (siteHomologyGradedOneCotangentIso_comp_fiveTermConnecting A B hvan)

/-- `H^{-3}(L_{B/A}) → H_2(C_{B/A}, Sym²(Ω)) → Tor_2^A(B, B)` is a complex. -/
lemma fiveTermConnecting_comp_symmetricPowerToTorEdge :
    fiveTermConnecting A B hvan ≫ symmetricPowerToTorEdge A B 2 (by norm_num) hvan = 0 :=
  comp_eq_zero_of_iso_comm
    (Functor.leftDerivedδ_comp_map_f _
      (shortExact_smallPolynomialAugmentationGradedShortComplex A B
        (standardResolutionVarCardinal A B) 1) 2)
    (siteHomologyGradedOneCotangentIso A B 3)
    (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan)
    (siteHomologyAugmentationIdealTorIso A B 2 (by norm_num))
    (siteHomologyGradedOneCotangentIso_comp_fiveTermConnecting A B hvan)
    (siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge_two A B hvan)

/-- `H_2(C_{B/A}, Sym²(Ω)) → Tor_2^A(B, B) → H^{-2}(L_{B/A})` is a complex. -/
lemma symmetricPowerToTorEdge_comp_torToCotangentEdge :
    symmetricPowerToTorEdge A B 2 (by norm_num) hvan ≫
      torToCotangentEdge A B 2 (by norm_num) = 0 :=
  comp_eq_zero_of_iso_comm
    (by rw [← Functor.map_comp, smallPolynomialAugmentationIdealPowIncl_comp_gradedπ,
      Functor.map_zero])
    (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan)
    (siteHomologyAugmentationIdealTorIso A B 2 (by norm_num))
    (siteHomologyGradedOneCotangentIso A B 2)
    (siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge_two A B hvan)
    (siteHomologyAugmentationIdealTorIso_comp_torToCotangentEdge A B 2 (by norm_num))

/-- **The five term exact sequence of Stacks Remark 08RG, exactness at `H^{-3}(L_{B/A})`.** -/
theorem exact_fiveTerm_cotangentNegThree :
    (ShortComplex.mk (torToCotangentEdge A B 3 (by norm_num)) (fiveTermConnecting A B hvan)
      (torToCotangentEdge_comp_fiveTermConnecting A B hvan)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (siteHomologyAugmentationIdealTorIso A B 3 (by norm_num))
      (siteHomologyGradedOneCotangentIso A B 3)
      (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan)
      (siteHomologyAugmentationIdealTorIso_comp_torToCotangentEdge A B 3 (by norm_num))
      (siteHomologyGradedOneCotangentIso_comp_fiveTermConnecting A B hvan))
    (exact_siteHomology_augmentationGradedOne_δ A B (standardResolutionVarCardinal A B) 2)

/-- **The five term exact sequence of Stacks Remark 08RG, exactness at
`H_2(C_{B/A}, Sym²(Ω)) = ∧²_B(I/I²)`.** -/
theorem exact_fiveTerm_exteriorSquare :
    (ShortComplex.mk (fiveTermConnecting A B hvan)
      (symmetricPowerToTorEdge A B 2 (by norm_num) hvan)
      (fiveTermConnecting_comp_symmetricPowerToTorEdge A B hvan)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (siteHomologyGradedOneCotangentIso A B 3)
      (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan)
      (siteHomologyAugmentationIdealTorIso A B 2 (by norm_num))
      (siteHomologyGradedOneCotangentIso_comp_fiveTermConnecting A B hvan)
      (siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge_two A B hvan))
    (exact_siteHomology_δ_augmentationIdealSq A B (standardResolutionVarCardinal A B) 2)

/-- **The five term exact sequence of Stacks Remark 08RG, exactness at `Tor_2^A(B, B)`.** -/
theorem exact_fiveTerm_torTwo :
    (ShortComplex.mk (symmetricPowerToTorEdge A B 2 (by norm_num) hvan)
      (torToCotangentEdge A B 2 (by norm_num))
      (symmetricPowerToTorEdge_comp_torToCotangentEdge A B hvan)).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk
      (siteHomologySymmetricPowerSelfIso A B (standardResolutionVarCardinal A B) 2 hvan)
      (siteHomologyAugmentationIdealTorIso A B 2 (by norm_num))
      (siteHomologyGradedOneCotangentIso A B 2)
      (siteHomologySymmetricPowerSelfIso_comp_symmetricPowerToTorEdge_two A B hvan)
      (siteHomologyAugmentationIdealTorIso_comp_torToCotangentEdge A B 2 (by norm_num)))
    (exact_siteHomology_augmentationIdealSq_gradedOne A B
      (standardResolutionVarCardinal A B) 2)

include hvan in
/-- **The five term exact sequence of Stacks Remark 08RG ends in zero**: the first edge map
`Tor_2^A(B, B) → H^{-2}(L_{B/A})` is surjective, because `H_1(C_{B/A}, 𝒦²) = 0`. -/
theorem epi_fiveTerm_torToCotangentEdge_two :
    Epi (torToCotangentEdge A B 2 (by norm_num)) := by
  have hpi : Epi ((siteHomologyFunctor A B (standardResolutionVarCardinal A B) 2).map
      (smallPolynomialAugmentationGradedπ A B (standardResolutionVarCardinal A B) 1)) :=
    epi_siteHomology_map_gradedOneπ_of_isZero A B (standardResolutionVarCardinal A B) 1
      (hvan 1 2 (by norm_num))
  have : Epi ((siteHomologyFunctor A B (standardResolutionVarCardinal A B) 2).map
        (smallPolynomialAugmentationGradedπ A B (standardResolutionVarCardinal A B) 1) ≫
      (siteHomologyGradedOneCotangentIso A B 2).hom) := epi_comp _ _
  exact epi_of_epi_fac
    (siteHomologyAugmentationIdealTorIso_comp_torToCotangentEdge A B 2 (by norm_num))

end FiveTerm

end CommAlgCat

end
