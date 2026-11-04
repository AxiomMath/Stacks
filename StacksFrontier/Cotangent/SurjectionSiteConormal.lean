module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.Surjection

/-!
# The first homology of the polynomial site in the differentials, for a surjection

Let `A → B` be a surjective ring map and let `I = ker(A → B)`. Let `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` be the
sheaf of `B̲`-modules on the polynomial site `C_{B/A}`. Then

`H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω) = I/I²`,

which is the opening clause of Stacks Remark 08RG. The first equality is Tag 08PU in degree
`n = 1` and holds for every ring map; the second is Tag 08RA, transported along the
identification of the kernel of the presentation `A → B` with `I`.

## Main definitions

* `CommAlgCat.polynomialSiteHomologyOneCotangentNegOneIso`: the first equality.
* `CommAlgCat.polynomialSiteHomologyOneConormalIso`: the composite, i.e. the whole clause.

## Implementation notes

`H_1(C_{B/A}, Ω)` is read in the only form this library has it: the sections at the point of
`L₁π_!` at abelian coefficients, on the small model of the footnote-restricted site, exactly as
in Tag 08PU's `CommAlgCat.standardResolutionLeftDerivedCotangentComplexIso`. The isomorphisms
below are therefore isomorphisms of abelian groups, not of `B`-modules, and the tag attributes
are labelled with that caveat. The `B`-module statement `H^{-1}(L_{B/A}) = I/I²` itself is
unaffected: it is `CommAlgCat.cotangentComplex_homologyNegOneIso`, Tag 08RA.

Tag 08RA produces the conormal module of the presentation `A → B`,
`(CommAlgCat.surjectionExtension A B h).Cotangent`, whose underlying ideal lives in a
universe-lifted copy of `A`. `CommAlgCat.surjectionConormalAddEquiv` moves it to
`Ideal.Cotangent (RingHom.ker (algebraMap A B))`, which is `I/I²` for the remark's own `I` and
is the same module in which `RingHom.torOneSelfIsoCotangent` states the remark's
`Tor_1^A(B, B) = I/I²`.

### Where the rest of 08RG stands

Five of the remark's clauses are in the library:

* this one — also at linear coefficients, as
  `CommAlgCat.leftDerivedColimOneConormalLinearEquiv` in
  `StacksFrontier.Cotangent.SurjectionSiteExteriorConormal`;
* `H_k(C_{B/A}, Sym^k(Ω)) = ∧^k_B(I/I²)`,
  `CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective` in the same
  module, over an arbitrary commutative ring and with no hypothesis beyond surjectivity. That is
  Remark 08SG applied to `Ω`, and 08SG holds here as an identity over every commutative ring,
  `2` invertible or not:
  `Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram`, by Illusie's
  and Quillen's décalage. 08SG's own route to its identity, through the sign-twisted
  `S_k`-coinvariants of `H_1(C, ℱ)^{⊗ k}`, is a proof erratum: that step is refuted over `ℤ` by
  `Stacks.ChaoticSite.not_quillenSignedCoinvariants_int`, at the polynomial site of `ℤ[x] → ℤ`
  with `k = 2`, where both sides of the clause are `0` while the coinvariants are `ℤ/2`. The
  route taken avoids it;
* the `E₁`-page display, `CommAlgCat.pageOneDisplay_of_surjective` in
  `StacksFrontier.Cotangent.QuillenSpectralSequence`: every entry of the displayed array
  `E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))` is identified, which is what the display says.
  The zeros strictly above the diagonal are the final clause of Theorem 08RF
  (`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`); the
  column `p = 0` is `CommAlgCat.leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso`
  and `CommAlgCat.isZero_leftDerivedColimSucc_symmetricPower_polynomialCotangent_zero` in
  `StacksFrontier.Cotangent.SurjectionSiteZerothSymmetricPower` (08RF's vanishing is vacuous at
  `k = 0`, so that column needs its own argument); the column `p = 1` is Tag 08PU at linear
  coefficients (`CommAlgCat.leftDerivedColimPolynomialCotangentIso`) together with
  `Sym¹(Ω) = Ω`; and the diagonal `p = k` is the clause above;
* `Tor_1^A(B, B) = I/I²`, `RingHom.torOneSelfIsoCotangent` in
  `StacksFrontier.Cotangent.TorQuotientSelf`;
* the remark's **first** family of edge maps `Tor_i^A(B, B) → H^{-i}(L_{B/A})`, `i > 0`,
  `CommAlgCat.torToCotangentEdge` in `StacksFrontier.Cotangent.SurjectionSiteEdgeMaps`, which
  carries no hypothesis at all.

Both of the remark's remaining assertions are now in the library too: its **second** family of
edge maps `∧^i_B(I/I²) → Tor_i^A(B, B)` and the five term exact sequence
`Tor_3^A(B, B) → H^{-3}(L_{B/A}) → ∧²_B(I/I²) → Tor_2^A(B, B) → H^{-2}(L_{B/A}) → 0`. Both are
*built*, in `StacksFrontier.Cotangent.SurjectionSiteEdgeMaps`, on the footnote vanishing
`H_j(C_{B/A}, 𝒦ⁿ) = 0` for `j < n` as an explicit hypothesis, so the declarations there carry
no `@[stacks 08RG]`: a tag may not sit on a declaration that assumes a result the source proves,
and that vanishing is the footnote to the source's proof of Theorem 08RF. It is now a theorem
for every surjective `A → B`, and `StacksFrontier.Cotangent.SurjectionSiteEdgeMapsUnconditional`
restates both assertions without that hypothesis and registers them, so every assertion of the
remark is formalized.

Neither assertion needs Quillen's spectral sequence, a term of
`CommAlgCat.QuillenFiltrationData A B`, or a low-degree analysis of an abutting spectral
sequence. The remark reads its edge maps off the filtration of the abutment, and that filtration
is induced by a filtration of **presheaves**: writing `Ō = 𝒪 ⊗_A B̲` and `𝒦 = ker(Ō → B̲)` it is
`… ⊂ 𝒦² ⊂ 𝒦 ⊂ Ō`, and `H_i(C_{B/A}, Ō)` is the abutment `Tor_i^A(B, B)`. So the maps and the
exactness are the long exact sequence of the left derived functors of `colim`, and that is all
they are:

* `H_i(C_{B/A}, 𝒦) ≅ H_i(C_{B/A}, Ō) ≅ Tor_i^A(B, B)` for `i ≥ 1`
  (`CommAlgCat.leftDerivedColimAugmentationIdealIsoOfPos` and
  `CommAlgCat.leftDerivedColimQuotientTorIso`, both for every ring map), composed with
  `H_i(C_{B/A}, 𝒦) ⟶ H_i(C_{B/A}, 𝒦/𝒦²)` and then with `𝒦/𝒦² ≅ Ω` followed by Tag 08PU, is the
  first family;
* `H_i(C_{B/A}, 𝒦ⁱ) ≅ H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹)` (`CommAlgCat.siteHomologyGradedSelfIso`),
  composed with `H_i(C_{B/A}, 𝒦ⁱ) ⟶ H_i(C_{B/A}, Ō)`, is the second. This is the one step that
  needs the footnote vanishing, and it needs it unavoidably: the second family is a map *out of*
  the graded piece, so it uses the inverse of `H_i(C_{B/A}, 𝒦ⁱ) ⟶ H_i(C_{B/A}, 𝒦ⁱ/𝒦ⁱ⁺¹)`, and
  the long exact sequence makes that map a monomorphism only once `H_i(C_{B/A}, 𝒦ⁱ⁺¹)` vanishes
  and an epimorphism only once `H_{i-1}(C_{B/A}, 𝒦ⁱ⁺¹)` does;
* the five term sequence is one segment of the long exact sequence of
  `0 → 𝒦² → 𝒦 → 𝒦/𝒦² → 0`, exact at each of its three interior terms with no hypothesis at
  all (`CommAlgCat.exact_siteHomology_augmentationGradedOne_δ`,
  `CommAlgCat.exact_siteHomology_δ_augmentationIdealSq` and
  `CommAlgCat.exact_siteHomology_augmentationIdealSq_gradedOne` in
  `StacksFrontier.Cotangent.SurjectionSiteEdgeMaps`), and surjective at its right end once
  `H_1(C_{B/A}, 𝒦²)` vanishes. Its two outer maps are the `i = 3` and `i = 2` members of the
  first family, so the sequence is the remark's, maps included; what needs the footnote vanishing
  is its term `∧²_B(I/I²)`, its middle map, and its final `→ 0`.

`H^{-2}(L_{B/A})` and `H^{-3}(L_{B/A})` are no obstacle: the remark does not compute them, and
`CommAlgCat.leftDerivedColimPolynomialCotangentIso` identifies `H_i(C_{B/A}, Ω)` with
`(cotangentComplex A B).homology (-i)` for every `i` and every ring map.

Of the two identifications of presheaves these assertions use, the first is proved:
`𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)` is
`CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso` in
`StacksFrontier.Cotangent.SurjectionSiteAugmentationSymmetricPower`, for every ring map. What is
left is the footnote vanishing alone. Its dévissage half is
`CommAlgCat.epi_leftDerivedColim_map_smallPolynomialAugmentationIdealPowMap`; what remains is the
source's own first claim in that proof, named
`CommAlgCat.SmallPolynomialAugmentationProNilpotent` in
`StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing`. The footnote vanishing cannot be
reached by any finite argument from the vanishing of the graded pieces: the long exact sequences
give `H_j(C_{B/A}, 𝒦ᵐ) ≅ H_j(C_{B/A}, 𝒦ʲ⁺²)` for every `m ≥ j + 2`, so its whole content is that
this stable value is zero, which is what the pro-nilpotence supplies.

For the second family of edge maps there is also a route through the multiplication on Tor,
which produces different maps: `Tor^A_*(B, B)` carries its full
associative graded multiplication (`GradedTor.canonicalAlgebra` and
`RingTheory.TorProducts.torProduct`, Tags 068K and 068J, in
`StacksFrontier.Homology.Tor.GradedAlgebra` and `StacksFrontier.Homology.Tor.CrossProduct`), so
`(I/I²)^{⊗ i} → Tor_i^A(B, B)` is available by iterating it along
`RingHom.torOneSelfIsoCotangent`. Factoring that through `∧^i_B(I/I²)` needs `x · x = 0` for
`x` of degree `1`, which neither `GradedTor.Algebra` nor `TorCrossProduct.System` records, and
which over `ℤ` does not follow formally from graded commutativity. Such maps would in any case
be a different construction from the remark's edge maps, which are read off the filtration of
the abutment; the route through the presheaf filtration above produces the remark's own maps
instead.

## References

* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08RA](https://stacks.math.columbia.edu/tag/08RA)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **Stacks 08RG**, the first equality of the remark's opening clause, which is Tag 08PU in
degree `n = 1`: the sections at the point of `L₁π_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the degree `-1`
cohomology of the cotangent complex `L_{B/A}`. The remark states it for a surjective `A → B`; it
holds for every ring map. -/
@[stacks 08RG "the first equality of the opening clause, H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω), as \
  the degree n = 1 case of Tag 08PU: the sections at the point of L₁π_!(Ω_{𝒪/A} ⊗_𝒪 B̲) are the \
  degree -1 cohomology of the cotangent complex of Tag 08PN. As in Tag 08PU, Lπ_! is read \
  degreewise at abelian coefficients, as the left derived functors of the π_! of Tag 08PF, on \
  the small model of the footnote-restricted site, so this is an isomorphism of abelian groups; \
  the B-module statement H^{-1}(L_{B/A}) = I/I² is Tag 08RA, \
  CommAlgCat.cotangentComplex_homologyNegOneIso. Proved for every ring map A → B, hence in \
  particular for the surjective one of the remark"]
def polynomialSiteHomologyOneCotangentNegOneIso :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
        (((Stacks.ChaoticSite.abelianPointLowerShriek
              (smallBoundedPolynomialSite A B
                (standardResolutionVarCardinal A B))).leftDerived 1).obj
          (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B))) ≅
      (forget₂ (ModuleCat.{u} ↥B) AddCommGrpCat.{u}).obj
        ((cotangentComplex.{u, u} A B).homology (-1)) :=
  standardResolutionLeftDerivedCotangentComplexIso A B 1

variable (h : Function.Surjective (algebraMap A ↥B))

/-- The conormal module of the presentation of `B` by `A` itself is `I/I²` for
`I = ker(A → B)`, as an additive group: the type synonym `Algebra.Extension.Cotangent` is
discarded and the universe lift of `A` undone. -/
def surjectionConormalAddEquiv :
    (surjectionExtension.{u, u} A B h).Cotangent ≃+
      (RingHom.ker (algebraMap A ↥B)).Cotangent :=
  (surjectionExtension.{u, u} A B h).cotangentEquivCotangentKer.toAddEquiv.trans
    (surjectionKerCotangentEquiv.{u, u} A B h).toAddEquiv

/-- **Stacks 08RG**, the opening clause `H^{-1}(L_{B/A}) = H_1(C_{B/A}, Ω) = I/I²` for a
surjective ring map `A → B` with kernel `I`: the sections at the point of
`L₁π_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` are the conormal module `I/I²`. The isomorphism is the composite of
`CommAlgCat.polynomialSiteHomologyOneCotangentNegOneIso` with Tag 08RA's
`CommAlgCat.cotangentComplex_homologyNegOneIso`, so it factors through `H^{-1}(L_{B/A})` exactly
as the remark says. -/
@[stacks 08RG "the second equality of the opening clause, H_1(C_{B/A}, Ω) = I/I² for \
  I = ker(A → B), as the composite of the first equality with Tag 08RA: for a surjective A → B \
  the sections at the point of L₁π_!(Ω_{𝒪/A} ⊗_𝒪 B̲) are \
  Ideal.Cotangent (RingHom.ker (algebraMap A B)), by way of H^{-1}(L_{B/A}), so the whole \
  opening clause is covered by this declaration together with \
  CommAlgCat.polynomialSiteHomologyOneCotangentNegOneIso. As in Tag 08PU, Lπ_! is read \
  degreewise at abelian coefficients, so this is an isomorphism of abelian groups; the \
  B-module statement H^{-1}(L_{B/A}) = I/I² is Tag 08RA itself. This declaration carries no \
  hypothesis beyond the remark's own surjectivity of A → B. It states the opening clause and \
  that clause alone; the section `Where the rest of 08RG stands` of this module's docstring says \
  where each of the remark's other clauses stands"]
def polynomialSiteHomologyOneConormalIso :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
        (((Stacks.ChaoticSite.abelianPointLowerShriek
              (smallBoundedPolynomialSite A B
                (standardResolutionVarCardinal A B))).leftDerived 1).obj
          (smallPolynomialCotangentSheaf A B (standardResolutionVarCardinal A B))) ≅
      AddCommGrpCat.of (RingHom.ker (algebraMap A ↥B)).Cotangent :=
  polynomialSiteHomologyOneCotangentNegOneIso A B ≪≫
    (forget₂ (ModuleCat.{u} ↥B) AddCommGrpCat.{u}).mapIso
      (cotangentComplex_homologyNegOneIso.{u, u} A B h) ≪≫
    (surjectionConormalAddEquiv A B h).toAddCommGrpIso

end CommAlgCat

end
