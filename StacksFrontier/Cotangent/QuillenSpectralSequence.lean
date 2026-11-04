module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.PageVanishing
public import StacksFrontier.Cotangent.SurjectionSiteExteriorConormal
public import StacksFrontier.Cotangent.SurjectionSiteZerothSymmetricPower
public import StacksFrontier.Homology.Tor.CrossProduct

/-!
# Quillen's spectral sequence: the datum, and the filtered complex it reduces to

Let `A → B` be a surjective ring map, let `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` be the sheaf of `B̲`-modules on the
polynomial site `C_{B/A}`, and let `Sym^p_{B̲}(Ω)` be its `p`-th sectionwise symmetric power.
Stacks Theorem 08RF produces a cohomological spectral sequence of `B`-modules, starting at the
first page and with `d_r` of bidegree `(r, -r + 1)`, with

`E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`,  abutting to  `Tor^A_{-p-q}(B, B)`,

whose edge maps `Tor_i^A(B, B) → H^{-i}(L_{B/A})` and `∧^i_B(I/I²) → Tor_i^A(B, B)` and five
term exact sequence are the remaining clauses of Stacks Remark 08RG.  The `E₁`-page display of
that remark is settled here without the spectral sequence, as
`CommAlgCat.pageOneDisplay_of_surjective`: it is the identification of every entry of the
displayed array, and the array is Theorem 08RF's own description of the first page.
`CommAlgCat.QuillenSpectralSequenceData` is the datum of Theorem 08RF, and
`CommAlgCat.QuillenFiltrationData` is a single filtered complex out of which it is assembled here.

## Main definitions

* `CommAlgCat.symmetricPowerSiteHomology`: the entries `H_i(C_{B/A}, Sym^k_{B̲}(Ω))` of the
  `E₁`-page, for `i : ℤ`.
* `CommAlgCat.pageOneDisplayEntry`: the same entries indexed by the position `(p, q)` of the
  array displayed in Remark 08RG, `E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`.
* `CommAlgCat.torAbutment`: `Tor^A_{-n}(B, B)` with its `B`-module structure, in cohomological
  degree `n`.
* `CommAlgCat.QuillenSpectralSequenceData`: the datum of Theorem 08RF -- the spectral sequence,
  the identification of its first page, the vanishing of that page in negative first degree, and
  its abutment by `Tor^A_*(B, B)`.
* `CommAlgCat.QuillenFiltrationData`: a degreewise finite filtration of a complex of `B`-modules
  which is the whole complex in nonpositive filtration degrees, together with the identification
  of its cohomology with `Tor^A_*(B, B)` and of the first page of its spectral sequence with the
  homology of the symmetric powers.

## Main results

* `CommAlgCat.pageOneDisplay_of_surjective`: **the `E₁`-page display of Remark 08RG**, as the
  identification of every entry of the displayed array, for a surjective `A → B` and with no
  further hypothesis.
* `CommAlgCat.QuillenFiltrationData.toQuillenSpectralSequenceData` and
  `CommAlgCat.nonempty_quillenSpectralSequenceData_of_nonempty_quillenFiltrationData`:
  **a `QuillenFiltrationData` yields a `QuillenSpectralSequenceData`.**
* `CommAlgCat.QuillenSpectralSequenceData.isZero_pageOne_of_pos` and
  `CommAlgCat.QuillenSpectralSequenceData.isZero_pageOne_of_lt`: the zeros of the `E₁`-page
  display of Remark 08RG -- below the antidiagonal `p + q = 0`, and strictly above the diagonal
  `-p - q = p`, the latter by Tag 08RF's own vanishing clause.
* `CommAlgCat.QuillenSpectralSequenceData.pageOneZeroZeroIso` and
  `CommAlgCat.QuillenSpectralSequenceData.isZero_pageOne_zero_of_neg`: the whole `p = 0` column
  of that display, `B` on top and zeros below it.
* `CommAlgCat.QuillenSpectralSequenceData.isZero_pageOne_of_not_display`: the three vanishings
  together -- the `E₁`-page is concentrated in the triangle `0 ≤ p`, `p + q ≤ 0`, `p ≤ -p - q`.

## Implementation notes

`H_i(C_{B/A}, -)` is `L_i` of the colimit over the opposite of the small model of the
footnote-restricted site at linear coefficients -- Tag 08PF's definition of the homology of a
category, and the reading in which the rest of this library's 08RF/08RG material is stated
(`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`,
`CommAlgCat.leftDerivedColimPolynomialCotangentIso`,
`CommAlgCat.leftDerivedColimOneConormalLinearEquiv`).  `Sym^k_{B̲}` is
`Stacks.ChaoticSite.symmetricPowerDiagram`, the sectionwise symmetric power, which is the sheaf
symmetric power because the topology of `C_{B/A}` is chaotic.  `symmetricPowerSiteHomology`
extends that `ℕ`-indexed homology to `ℤ` by zero, which is what the bidegree `(p, q)` of a
cohomological spectral sequence needs.

### What is built here, and what is left

The spectral sequence of a filtered complex is already in the library
(`CochainComplex.Filtered.spectralSequenceFunctor`), as is its convergence
(`CochainComplex.Filtered.abutsTo_shiftStart_of_isDegreewiseFinite`, Tag 012W), and
`CochainComplex.Filtered.isZero_page_of_lt_of_eq_top` shows that a filtration which is already
everything in nonpositive filtration degrees gives a spectral sequence concentrated in `p ≥ 0`.
Those three, with `CategoryTheory.SpectralSequence.AbutsTo.of_iso` to move the abutment across
the identification of the cohomology, are what
`QuillenFiltrationData.toQuillenSpectralSequenceData` is: every clause of the datum except the
two identifications is *proved* here, and the vanishing in negative first degree is proved rather
than assumed.

The `E₁`-page display of Remark 08RG is `pageOneDisplay_of_surjective`, which identifies every
entry of the displayed array: the zeros strictly below the antidiagonal by the indexing of the
symmetric powers, the zeros strictly above the diagonal by Tag 08RF's vanishing
(`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`), the
column `p = 0` by `CommAlgCat.leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso` and
`CommAlgCat.isZero_leftDerivedColimSucc_symmetricPower_polynomialCotangent_zero`, the column
`p = 1` by Tag 08PU at linear coefficients
(`CommAlgCat.leftDerivedColimPolynomialCotangentIso`) composed with `Sym¹(Ω) = Ω`
(`Stacks.ChaoticSite.symPowOneDiagramIso`), and the diagonal `p = k` by
`CommAlgCat.exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective`.  That
statement is about the array `pageOneDisplayEntry`, which is what Theorem 08RF identifies the
page with; the `QuillenSpectralSequenceData.isZero_pageOne_*` and
`QuillenSpectralSequenceData.pageOneZeroZeroIso` results below transport the same facts onto the
page of a datum, along its `pageOneIso` field.

What is **not** built here is a `QuillenFiltrationData` for a surjective `A → B`.  That is the
mathematical content of Theorem 08RF, and nothing in this library yet filters a resolution of `B`
over `A` so that the graded pieces compute the homology of the symmetric powers of `Ω`: the only
filtration in the Quillen material is `MvPolynomial.tor_map_variableIdeal_pow_succ_eq_zero`'s
multidegree filtration of a single Koszul complex (Tag 08RE), which is private to its file and is
an input to the degeneration rather than the filtration producing the page.  So
`Nonempty (QuillenFiltrationData A B)` for a surjective `A → B` is the one obligation left, and
`nonempty_quillenSpectralSequenceData_of_nonempty_quillenFiltrationData` is the statement that it
is the only one.

### What `Nonempty (QuillenFiltrationData A B)` needs

The source's construction runs through the sheaves `Ō = 𝒪/I𝒪` and `𝒦 = 𝒥/I𝒪` on `C_{B/A}`, where
`I = ker(A → B)` and `𝒥 = ker(𝒪 → B̲)`, and the filtration `… ⊂ 𝒦² ⊂ 𝒦 ⊂ Ō`.  The two ends of
that argument are in the library and the whole middle is absent:

* **absent**: `Ō` and `𝒦` as presheaves of modules on
  `smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)`, and the powers `𝒦ⁿ`.  The
  nearest thing is `CommAlgCat.polynomialAugmentationIdeal`
  (`StacksFrontier.Cotangent.PolynomialAlgebraSiteAugmentationIdeal`, Tag 08R7), which is `𝒥` on the
  unrestricted site as a `SheafOfModules.{u + 1}` -- a different universe shape from the
  `Cᵒᵖ ⥤ ModuleCat.{u} B` world the 08RD/08RF machinery lives in -- and is used by no other file;
* **absent**: `𝒦ᵏ/𝒦ᵏ⁺¹ ≅ Sym^k_{B̲}(Ω)`, sectionwise or as presheaves, and with it `Ω = 𝒦/𝒦²`.
  This library's 08RF/08RG material works with `Sym^k_{B̲}(Ω)` directly and never meets the
  graded pieces;
* **absent**: `Lπ_!` of `𝒦ⁿ` or of `Ō`, and with it both the convergence vanishing
  `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < k`, `n > k²` and the a posteriori `i < n` form.  Its four
  ingredients are each proved: Tag 08RE
  (`MvPolynomial.tor_map_variableIdeal_pow_succ_eq_zero`), Tag 068F
  (`exists_tor_change_of_rings_spectral_sequence`), Tag 08Q2
  (`main_covariant`/`main_contravariant`) and Tag 08QJ
  (`CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentation`, for a module in
  degree zero on the small model);
* **absent**: `B ⊗_A^{\mathbf L} B = Lπ_!(Ō)`, which is the `cohomologyIso` field.  Half of Tag
  08QK is available unlabelled as
  `CommAlgCat.isIso_totalDerivedColimit_smallPolynomialAugmentation`, and `Lπ_!(B̲) ≅ B` is proved
  only in the informal proof of Stacks 08QK (structure sheaf values);
* **absent**: the filtered complex itself, which the source omits ("construction of `C` and `F`
  omitted").  Everything downstream of it -- `spectralSequenceFunctor`,
  `abutsTo_shiftStart_of_isDegreewiseFinite` (Tag 012W), `isZero_page_of_lt_of_eq_top` -- is
  proved.

A design note on the `isDegreewiseFinite` field, which is not a restatement of the source.  The
filtration the source describes, with `F^pC` representing `Lπ_!(𝒦^p)`, is **not** degreewise
finite: degreewise it is the `𝒦ⁿ`-adic filtration of a polynomial ring, where no power vanishes.
What does satisfy the field is the canonical truncation `τ^{≤ -p}(F^pC)` for `p ≥ 1` (and `C`
itself for `p ≤ 0`), which is degreewise zero above `p = -n`, is still a decreasing filtration by
subcomplexes, and has the same graded pieces up to quasi-isomorphism -- by the footnote vanishing
`H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, which makes each inclusion `τ^{≤ -p}(F^pC) → F^pC` a
quasi-isomorphism.  So the field is satisfiable, but not by the filtration as the source writes
it, and the footnote vanishing is needed twice over: once for convergence and once to get the
filtration into this shape.

### The remaining clauses of Remark 08RG, and which of them this obligation closes

`Nonempty (QuillenFiltrationData A B)` closes neither of the remark's two clauses that are
settled here.  It is also **not** what the edge maps `Tor_i^A(B, B) → H^{-i}(L_{B/A})` and
`∧^i_B(I/I²) → Tor_i^A(B, B)` and the five term exact sequence need, which is what an earlier
reading of this section asserted.  The remark reads those maps off the filtration of the
abutment, and that filtration is induced by the filtration of *presheaves*
`… ⊂ 𝒦² ⊂ 𝒦 ⊂ Ō` on the site, so the maps and the exactness are the long exact sequence of the
left derived functors of `colim` and nothing more; see the section `Where the rest of 08RG
stands` of `StacksFrontier.Cotangent.SurjectionSiteConormal`, and
`StacksFrontier.Cotangent.SurjectionSiteEdgeMaps` for the five term segment itself.  The filtration
datum and those two assertions do, however, share their two remaining inputs:
`𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)` and the footnote vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`.

The `E₁`-page display does not need it.  The display is the array of entries
`E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))` -- Theorem 08RF's own identification of the first
page -- and identifying every one of those entries is `pageOneDisplay_of_surjective` above,
proved for a surjective `A → B` and nothing more.  What the page adds over the array is the
differentials and the abutment, and the remark's claim about the differentials, "with horizontal
differential", is Theorem 08RF's own clause that `d_r` has bidegree `(r, -r + 1)`, at `r = 1`:
it holds by definition of `CohomologicalSpectralSequence _ 1`, the type carried by
`QuillenSpectralSequenceData.sequence`.

Nor does the clause `H_k(C_{B/A}, Sym^k(Ω)) = ∧^k_B(I/I²)`: it is a consequence of Remark 08SG
rather than of the spectral sequence, and 08SG holds over every commutative ring by Illusie's
and Quillen's décalage, `LSym^k(M[1]) = (∧^k M)[k]`
(`Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram`).  08SG's own
route to it, through the sign-twisted `S_k`-coinvariants of `H_1(C, ℱ)^{⊗ k}`, is a proof
erratum, refuted over `ℤ` by `Stacks.ChaoticSite.not_quillenSignedCoinvariants_int`; see
`StacksFrontier.Cotangent.SurjectionSiteExteriorConormal`.  Since the source spells both the
display's diagonal and the five term sequence's middle term as `∧^i_B(I/I²)`, that clause feeds
the display here and would feed the five term sequence.

What the edge maps and the five term sequence do need is recorded in the section
`Where the rest of 08RG stands` of `StacksFrontier.Cotangent.SurjectionSiteConormal`.  Two earlier
entries on that list have since been struck off: `H^{-2}(L_{B/A})` and `H^{-3}(L_{B/A})` are
available for every `i` and every ring map from
`CommAlgCat.leftDerivedColimPolynomialCotangentIso`, the remark computing neither of them; and no
low-degree analysis of an abutting spectral sequence is required, since the long exact sequence
of `colim`'s left derived functors supplies the maps and the exactness directly.

`pageOneDisplay_of_surjective` is the one declaration here carrying a `@[stacks 08RG]`
attribute, and it states the display clause whole under the remark's own hypotheses.  No
declaration here carries a `@[stacks 08RF]` attribute: the datum and the filtration are objects,
and the results about a datum take it as an argument.  The remark's other clauses that are
proved outright live in `StacksFrontier.Cotangent.SurjectionSiteConormal`,
`StacksFrontier.Cotangent.SurjectionSiteExteriorConormal` and
`StacksFrontier.Cotangent.TorQuotientSelf`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RG](https://stacks.math.columbia.edu/tag/08RG)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The entries of the first page -/

/-- `H_i(C_{B/A}, Sym^k_{B̲}(Ω))`, the entry of the `E₁`-page of Quillen's spectral sequence in
the column `p = k` and total degree `-i`: the `i`-th left derived functor of the colimit over the
opposite of the small model of the footnote-restricted polynomial site, applied to the `k`-th
sectionwise symmetric power of `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`, and the zero module for `i < 0`. -/
def symmetricPowerSiteHomology (k : ℕ) : ℤ → ModuleCat.{u} B
  | .ofNat i =>
    ((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived i).obj
      (Stacks.ChaoticSite.symmetricPowerDiagram
        (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) k)
  | .negSucc _ => ModuleCat.of (B : Type u) PUnit.{u + 1}

/-- In nonnegative degree, `symmetricPowerSiteHomology` is `L_i colim` of the symmetric power
on the nose. -/
lemma symmetricPowerSiteHomology_natCast (k i : ℕ) :
    symmetricPowerSiteHomology A B k (i : ℤ) =
      ((colim :
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
              ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived i).obj
        (Stacks.ChaoticSite.symmetricPowerDiagram
          (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
          (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) k) :=
  rfl

/-- There is no homology in negative degree. -/
lemma isZero_symmetricPowerSiteHomology_of_neg (k : ℕ) {i : ℤ} (hi : i < 0) :
    IsZero (symmetricPowerSiteHomology A B k i) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
  change IsZero (ModuleCat.of (B : Type u) PUnit.{u + 1})
  exact ModuleCat.isZero_of_subsingleton _

/-! ### The displayed `E₁`-page array -/

/-- For a surjective `A → B`, `H_i(C_{B/A}, Sym^k_{B̲}(Ω))` vanishes for `i < k`. -/
private theorem isZero_symmetricPowerSiteHomology_of_lt
    (h : Function.Surjective (algebraMap A (B : Type u))) (k : ℕ) {i : ℤ} (hi : i < k) :
    IsZero (symmetricPowerSiteHomology A B k i) := by
  rcases lt_or_ge i 0 with hneg | hnn
  · exact isZero_symmetricPowerSiteHomology_of_neg A B k hneg
  obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  exact isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective A B h k l
    (by omega)

/-- `H_i(C_{B/A}, Sym^0_{B̲}(Ω))` vanishes for `0 < i`. -/
private theorem isZero_symmetricPowerSiteHomology_zero_of_pos {i : ℤ} (hi : 0 < i) :
    IsZero (symmetricPowerSiteHomology A B 0 i) := by
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, i = ((l + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by push_cast; omega⟩
  exact isZero_leftDerivedColimSucc_symmetricPower_polynomialCotangent_zero A B l

/-- **The entry of the `E₁`-page display of Remark 08RG at the position `(p, q)`.**  Theorem 08RF
identifies the first page of Quillen's spectral sequence as
`E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`, and this is that module: the display of Remark
08RG is the array of these entries, with `p` running along the columns and `q` down the rows, so
that the array's first row is `q = 0`, its first column is `p = 0`, its antidiagonal is
`p + q = 0` and its diagonal is `-p - q = p`.

On a `CommAlgCat.QuillenSpectralSequenceData` the identification of the page with this array is
the field `pageOneIso`. -/
def pageOneDisplayEntry (p : ℕ) (q : ℤ) : ModuleCat.{u} B :=
  symmetricPowerSiteHomology A B p (-(p : ℤ) - q)

/-- The entry of the `E₁`-page display at `(p, q)` is
`symmetricPowerSiteHomology A B p (-p - q)`. -/
@[simp]
lemma pageOneDisplayEntry_def (p : ℕ) (q : ℤ) :
    pageOneDisplayEntry A B p q = symmetricPowerSiteHomology A B p (-(p : ℤ) - q) :=
  rfl

/-- **Stacks 08RG**, the `E₁`-page display, for a surjective ring map `A → B` with kernel `I`:
every entry of the displayed array

```
B
0
0   I/I²
0   H^{-2}(L_{B/A})
0   H^{-3}(L_{B/A})   ∧²(I/I²)
0   H^{-4}(L_{B/A})   H_3(C_{B/A}, Sym²(Ω))
0   H^{-5}(L_{B/A})   H_4(C_{B/A}, Sym²(Ω))   ∧³(I/I²)
```

is the module the remark displays there.  The array is `E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p(Ω))`
of Theorem 08RF, `p` along the columns and `q` down the rows from `q = 0`, so the six conjuncts
below are, in order:

* the entries strictly below the antidiagonal `p + q = 0` vanish — those are the positions the
  display leaves blank beyond the triangle, where the homological degree `-p - q` is negative;
* the entries strictly above the diagonal `-p - q = p` vanish — the blanks inside the triangle,
  by the final clause of Theorem 08RF;
* the top entry of the column `p = 0` is `B`;
* the rest of the column `p = 0` vanishes — together with the previous two conjuncts this is the
  column `B, 0, 0, …` the display opens with;
* the column `p = 1` is `H^{-i}(L_{B/A})` in homological degree `i`, which at `i = 1`, the
  position `(1, -2)`, is the `I/I²` of the third row by the remark's opening clause;
* the diagonal entry at `(p, -2p)` is `∧^p_B(I/I²)`, by the remark's second clause.

The entries strictly inside the triangle with `p ≥ 2` — `H_3(C_{B/A}, Sym²(Ω))` and
`H_4(C_{B/A}, Sym²(Ω))` in the display — are left as they stand, exactly as the remark leaves
them.

"With horizontal differential" is Theorem 08RF's own clause that `d_r` has bidegree
`(r, -r + 1)`, at `r = 1`; it holds by definition of `CohomologicalSpectralSequence _ 1`, which
is the type of `CommAlgCat.QuillenSpectralSequenceData.sequence`. -/
@[stacks 08RG "the E₁-page display, for a surjective A → B with I = ker(A → B): every entry of \
  the displayed array is identified. The array is E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω)), \
  which is Theorem 08RF's own identification of the first page, read here as the ℕ × ℤ-indexed \
  family CommAlgCat.pageOneDisplayEntry with p along the columns and q down the rows from q = 0; \
  H_i(C_{B/A}, -) = L_i colim over the opposite of the small model of the footnote-restricted \
  site at linear coefficients is Tag 08PF's definition of the homology of a category, and \
  Sym^p_{B̲} is the sectionwise symmetric power, which is the sheaf symmetric power because the \
  topology of C_{B/A} is chaotic. The six conjuncts are the array's six regions: zero strictly \
  below the antidiagonal p + q = 0 (negative homological degree); zero strictly above the \
  diagonal -p - q = p, by the final clause of Theorem 08RF; B at the top of the column p = 0; \
  zero down the rest of that column, which Theorem 08RF's vanishing does not give since it is \
  vacuous at p = 0; H^{-i}(L_{B/A}) down the column p = 1, by Tag 08PU together with Sym¹(Ω) = \
  Ω, which at the position (1, -2) is the I/I² of the display's third row by the remark's \
  opening clause; and ∧^p_B(I/I²) at the diagonal position (p, -2p), by the remark's second \
  clause. The entries strictly inside the triangle with p ≥ 2, which the display writes as \
  H_3(C_{B/A}, Sym²(Ω)) and H_4(C_{B/A}, Sym²(Ω)), the remark leaves unidentified and so does \
  this statement. The display's parenthetical `with horizontal differential` is Theorem 08RF's \
  clause that d_r has bidegree (r, -r + 1), at r = 1, which holds by definition of the type \
  CohomologicalSpectralSequence _ 1 carried by \
  CommAlgCat.QuillenSpectralSequenceData.sequence. I/I² is \
  (CommAlgCat.surjectionExtension A B h).Cotangent, the conormal module of the presentation of B \
  by A itself, which CommAlgCat.surjectionConormalAddEquiv identifies with \
  Ideal.Cotangent (RingHom.ker (algebraMap A B)). No hypothesis beyond the remark's own \
  surjectivity of A → B"]
theorem pageOneDisplay_of_surjective (h : Function.Surjective (algebraMap A (B : Type u))) :
    (∀ (p : ℕ) (q : ℤ), 0 < (p : ℤ) + q → IsZero (pageOneDisplayEntry A B p q)) ∧
      (∀ (p : ℕ) (q : ℤ), -(p : ℤ) - q < p → IsZero (pageOneDisplayEntry A B p q)) ∧
      Nonempty (pageOneDisplayEntry A B 0 0 ≅ ModuleCat.of (B : Type u) (B : Type u)) ∧
      (∀ q : ℤ, q < 0 → IsZero (pageOneDisplayEntry A B 0 q)) ∧
      (∀ i : ℕ, Nonempty (pageOneDisplayEntry A B 1 (-1 - (i : ℤ)) ≅
          (cotangentComplex.{u, u} A B).homology (-(i : ℤ)))) ∧
      (∀ p : ℕ, Nonempty (pageOneDisplayEntry A B p (-2 * (p : ℤ)) ≅
          ModuleCat.of (B : Type u)
            (⋀[(B : Type u)]^p (surjectionExtension.{u, u} A B h).Cotangent))) := by
  refine ⟨fun p q hpq => isZero_symmetricPowerSiteHomology_of_neg A B p (by omega), ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun p q hpq => isZero_symmetricPowerSiteHomology_of_lt A B h p hpq
  · refine ⟨(eqToIso ?_).trans
      (leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso A B)⟩
    change symmetricPowerSiteHomology A B 0 (-((0 : ℕ) : ℤ) - 0) = _
    rw [show -(((0 : ℕ) : ℤ)) - 0 = ((0 : ℕ) : ℤ) from by norm_num,
      symmetricPowerSiteHomology_natCast]
  · exact fun q hq => isZero_symmetricPowerSiteHomology_zero_of_pos A B (by push_cast; omega)
  · intro i
    refine ⟨(eqToIso ?_).trans
      ((((colim :
            ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
              ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived i).mapIso
          (Stacks.ChaoticSite.symPowOneDiagramIso
            (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (B : Type u)
            (smallPolynomialCotangentModulePresheaf A B
              (standardResolutionVarCardinal A B))).symm).trans
        (leftDerivedColimPolynomialCotangentIso A B i))⟩
    change symmetricPowerSiteHomology A B 1 (-(((1 : ℕ) : ℤ)) - (-1 - (i : ℤ))) = _
    rw [show -(((1 : ℕ) : ℤ)) - (-1 - (i : ℤ)) = ((i : ℕ) : ℤ) from by push_cast; ring,
      symmetricPowerSiteHomology_natCast]
  · intro p
    obtain ⟨e⟩ :=
      exteriorPower_conormal_leftDerivedColim_symmetricPower_of_surjective A B h p
    refine ⟨(eqToIso ?_).trans e.toModuleIso⟩
    change symmetricPowerSiteHomology A B p (-((p : ℕ) : ℤ) - (-2 * (p : ℤ))) = _
    rw [show -((p : ℕ) : ℤ) - (-2 * (p : ℤ)) = ((p : ℕ) : ℤ) from by ring,
      symmetricPowerSiteHomology_natCast]

/-! ### The abutment -/

/-- `Tor^A_{-n}(B, B)` with its canonical `B`-module structure, placed in cohomological degree
`n`: the Tor module in homological degree `-n` for `n ≤ 0`, and the zero module in the positive
degrees, where no Tor module occurs.  `Tor^A_i(B, B)` is read as the `i`-th left derived functor
of extension of scalars along `A → B`, applied to `B` as an `A`-module. -/
def torAbutment : ℤ → ModuleCat.{u} B
  | .ofNat 0 =>
    (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) 0).obj
      (ModuleCat.of A (B : Type u))
  | .ofNat (_ + 1) => ModuleCat.of (B : Type u) PUnit.{u + 1}
  | .negSucc k =>
    (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) (k + 1)).obj
      (ModuleCat.of A (B : Type u))

/-- The abutment is `Tor^A_k(B, B)` in cohomological degree `-k`. -/
lemma torAbutment_neg_natCast (k : ℕ) :
    torAbutment A B (-(k : ℤ)) =
      (RingTheory.TorProducts.torBaseChange.{u, u, u} A (B : Type u) k).obj
        (ModuleCat.of A (B : Type u)) := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The abutment vanishes in positive cohomological degree. -/
lemma isZero_torAbutment_of_pos {n : ℤ} (hn : 0 < n) : IsZero (torAbutment A B n) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = ((k + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by push_cast; omega⟩
  change IsZero (ModuleCat.of (B : Type u) PUnit.{u + 1})
  exact ModuleCat.isZero_of_subsingleton _

/-! ### The datum -/

/-- **The data of Quillen's spectral sequence** ([Stacks, Tag 08RF]) for a ring map `A → B`: a
cohomological spectral sequence of `B`-modules starting at the first page, its first page
identified with the homology of the polynomial site in the symmetric powers of `Ω`, vanishing in
negative first degree, and abutting to `Tor^A_*(B, B)`.

The source asserts existence rather than uniqueness, and `CategoryTheory.SpectralSequence.AbutsTo`
is the existential form of convergence -- the filtration of the abutment and the identifications
of its graded pieces with the terms of the infinity page are quantified away.  That is exactly
what the remaining clauses of [Stacks, Tag 08RG] need, since they assert only that the edge maps
and the five term exact sequence exist. -/
structure QuillenSpectralSequenceData where
  /-- The spectral sequence, with `d_r` of bidegree `(r, -r + 1)` on the `r`-th page. -/
  sequence : CohomologicalSpectralSequence (ModuleCat.{u} B) 1
  /-- The first page is `E₁^{p,q} = H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`. -/
  pageOneIso (p : ℕ) (q : ℤ) :
    (sequence.page 1).X ((p : ℤ), q) ≅ symmetricPowerSiteHomology A B p (-(p : ℤ) - q)
  /-- The symmetric powers are indexed by the natural numbers, so the first page vanishes in
  negative first degree. -/
  pageOne_isZero (p q : ℤ) (hp : p < 0) : IsZero ((sequence.page 1).X (p, q))
  /-- The spectral sequence abuts to `Tor^A_{-p-q}(B, B)`. -/
  abutment : SpectralSequence.AbutsTo sequence (torAbutment A B)

/-- **The `E₁`-page display of [Stacks, Tag 08RG] is zero below its antidiagonal.**  For
`0 < p + q` the homological degree `-p - q` is negative, where there is no homology. -/
theorem QuillenSpectralSequenceData.isZero_pageOne_of_pos (D : QuillenSpectralSequenceData A B)
    (p q : ℤ) (hpq : 0 < p + q) : IsZero ((D.sequence.page 1).X (p, q)) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact D.pageOne_isZero p q hp
  · lift p to ℕ using hp with n
    exact (isZero_symmetricPowerSiteHomology_of_neg A B n (by omega)).of_iso (D.pageOneIso n q)

/-- **The `E₁`-page display of [Stacks, Tag 08RG] is zero strictly above its diagonal**, for a
surjective `A → B`.  The entry at `(p, q)` is `H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`, which vanishes
for `-p - q < p` by the final clause of [Stacks, Tag 08RF],
`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`. -/
theorem QuillenSpectralSequenceData.isZero_pageOne_of_lt (D : QuillenSpectralSequenceData A B)
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) (p q : ℤ) (hpq : -p - q < p) :
    IsZero ((D.sequence.page 1).X (p, q)) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact D.pageOne_isZero p q hp
  lift p to ℕ using hp with n
  exact (isZero_symmetricPowerSiteHomology_of_lt A B hsurj n hpq).of_iso (D.pageOneIso n q)

/-- **The top entry of the `p = 0` column of the `E₁`-page display of [Stacks, Tag 08RG] is
`B`.**  `E₁^{0,0} = H_0(C_{B/A}, Sym^0_{B̲}(Ω)) = B`, by
`CommAlgCat.leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso`. -/
def QuillenSpectralSequenceData.pageOneZeroZeroIso (D : QuillenSpectralSequenceData A B) :
    (D.sequence.page 1).X (0, 0) ≅ ModuleCat.of (B : Type u) (B : Type u) := by
  refine (D.pageOneIso 0 0).trans ((eqToIso ?_).trans
    (leftDerivedColimZeroSymmetricPowerPolynomialCotangentZeroIso A B))
  rw [show -(((0 : ℕ) : ℤ)) - 0 = ((0 : ℕ) : ℤ) from by norm_num,
    symmetricPowerSiteHomology_natCast]

/-- **The rest of the `p = 0` column of the `E₁`-page display of [Stacks, Tag 08RG] is zero.**
`E₁^{0,q} = H_{-q}(C_{B/A}, Sym^0_{B̲}(Ω)) = 0` for `q < 0`, by
`CommAlgCat.isZero_leftDerivedColimSucc_symmetricPower_polynomialCotangent_zero`.  Together with
`QuillenSpectralSequenceData.pageOneZeroZeroIso` and
`QuillenSpectralSequenceData.isZero_pageOne_of_pos` this is the whole first column
`B, 0, 0, …` of the display.

Tag 08RF's vanishing is vacuous at `k = 0`, which is why this needs its own argument. -/
theorem QuillenSpectralSequenceData.isZero_pageOne_zero_of_neg
    (D : QuillenSpectralSequenceData A B) (q : ℤ) (hq : q < 0) :
    IsZero ((D.sequence.page 1).X (0, q)) := by
  exact (isZero_symmetricPowerSiteHomology_zero_of_pos A B (i := -((0 : ℕ) : ℤ) - q)
    (by push_cast; omega)).of_iso (D.pageOneIso 0 q)

/-- **The `E₁`-page of Quillen's spectral sequence is concentrated in the triangle displayed by
[Stacks, Tag 08RG]**, for a surjective `A → B`: `E₁^{p,q} = 0` unless `0 ≤ p`, `p + q ≤ 0` and
`p ≤ -p - q`, that is, unless the entry `H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))` lies weakly below the
diagonal of the array.  This collects the three vanishing statements above. -/
theorem QuillenSpectralSequenceData.isZero_pageOne_of_not_display
    (D : QuillenSpectralSequenceData A B)
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) (p q : ℤ)
    (h : ¬ (0 ≤ p ∧ p + q ≤ 0 ∧ p ≤ -p - q)) :
    IsZero ((D.sequence.page 1).X (p, q)) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact D.pageOne_isZero p q hp
  rcases lt_or_ge (0 : ℤ) (p + q) with hpq | hpq
  · exact D.isZero_pageOne_of_pos A B p q hpq
  exact D.isZero_pageOne_of_lt A B hsurj p q (by omega)

/-! ### The filtered complex the datum reduces to -/

/-- **A filtered complex presenting Quillen's spectral sequence.**  A complex of `B`-modules
filtered by subcomplexes, the filtration degreewise finite ([Stacks, Tag 012W]) and already the
whole complex in nonpositive filtration degrees, together with the two identifications
[Stacks, Tag 08RF] asserts: of the cohomology of the complex with `Tor^A_*(B, B)`, and of the
first page of its spectral sequence with the homology of the polynomial site in the symmetric
powers of `Ω`.

This is the whole remaining content of Theorem 08RF:
`QuillenFiltrationData.toQuillenSpectralSequenceData` turns such a datum into a
`QuillenSpectralSequenceData`. -/
structure QuillenFiltrationData where
  /-- The filtered complex of `B`-modules. -/
  complex : CochainComplex.Filtered (ModuleCat.{u} B)
  /-- The filtration is finite in every degree, which is what makes the spectral sequence
  converge ([Stacks, Tag 012W]). -/
  isDegreewiseFinite : complex.filtration.IsDegreewiseFinite
  /-- The filtration is the whole complex in nonpositive filtration degrees, which is what makes
  the spectral sequence concentrated in `p ≥ 0`. -/
  filtrationSubobject_eq_top (p n : ℤ) (hp : p ≤ 0) :
    CochainComplex.filtrationSubobject complex p n = ⊤
  /-- The cohomology of the complex is `Tor^A_{-n}(B, B)`. -/
  cohomologyIso (n : ℤ) : complex.X.homology n ≅ torAbutment A B n
  /-- The first page of the spectral sequence is `H_{-p-q}(C_{B/A}, Sym^p_{B̲}(Ω))`. -/
  pageOneIso (p : ℕ) (q : ℤ) :
    ((CochainComplex.Filtered.spectralSequenceFunctor.obj complex).page 1).X ((p : ℤ), q) ≅
      symmetricPowerSiteHomology A B p (-(p : ℤ) - q)

/-- **Quillen's spectral sequence, from a filtered complex presenting it.**  The sequence is the
one [Stacks, Tag 012M] attaches to the filtered complex, read from its first page; its abutment is
[Stacks, Tag 012W] transported along the identification of the cohomology; and the vanishing in
negative first degree is proved, not assumed, from the filtration being the whole complex in
nonpositive filtration degrees. -/
def QuillenFiltrationData.toQuillenSpectralSequenceData (D : QuillenFiltrationData A B) :
    QuillenSpectralSequenceData A B where
  sequence :=
    (CochainComplex.Filtered.spectralSequenceFunctor.obj D.complex).shiftStart (by omega)
  pageOneIso p q := D.pageOneIso p q
  pageOne_isZero p q hp :=
    CochainComplex.Filtered.isZero_page_of_lt_of_eq_top D.complex
      (fun p n hp => D.filtrationSubobject_eq_top p n hp) 1 p q (by omega) hp
  abutment :=
    (CochainComplex.Filtered.abutsTo_shiftStart_of_isDegreewiseFinite D.complex (by omega)
      D.isDegreewiseFinite).of_iso D.cohomologyIso

/-- **The datum of Quillen's spectral sequence exists as soon as a filtered complex presenting it
does.**  This is the reduction of [Stacks, Tag 08RF] to a single existence statement about a
filtered complex of `B`-modules; nothing in this library yet constructs such a complex. -/
theorem nonempty_quillenSpectralSequenceData_of_nonempty_quillenFiltrationData
    (h : Nonempty (QuillenFiltrationData A B)) : Nonempty (QuillenSpectralSequenceData A B) :=
  ⟨h.some.toQuillenSpectralSequenceData A B⟩

end CommAlgCat

end
