module

public import StacksFrontier.Algebra.Homology.TotalRowComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexDegeneration
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexGeneral
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRow
public import StacksFrontier.AlgebraicTopology.ConstantCofaceMapComplex

/-!
# The second spectral sequence of [Stacks, Tag 07LG] from a rowwise comparison

`Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplexDegeneration.lean` runs the
two degenerations of the double complex `K^{a,b}` from the acyclicity of its columns off `0` *and
of its rows off `0`*.  The second of those hypotheses is **not** what the completed clause of
[Stacks, Lemma 60.21.2, Tag 07LD] supplies, and
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRowObstruction.lean`
proves it unsatisfiable for the crystalline `K`: `H⁰` of a completed de Rham complex contains the
horizontal sections, and killing them forces `p` to be invertible in `D̂(b)`.

What the source actually uses is a *comparison*.  Each row `K^{*,b}` is quasi-isomorphic to the
row `K^{*,0} = M ⊗^∧_D Ω^*_D`, so on the `E₁` page `E₁^{a,b} = H^a(M ⊗^∧_D Ω^*_D)` for every `b`
and the differentials of that page are `0, 1, 0, 1, …`, the codiagonal `ε_b : D(b) → D` being a
common retraction of the `b + 1` coprojections.  A complex with those differentials has the
cohomology of its degree `0` — that is
`AlgebraicTopology.constantAlternatingCofaceMapComplex_exactAt` — so the degeneration is run here
by *comparing `K` with the constant cosimplicial object* on `M ⊗^∧_D Ω^*_D`, not by making the
rows off `0` vanish.

## The four steps

* **The comparison object.**  `AlgebraicTopology.constantCosimplicialCochainComplex` applies the
  constant cosimplicial object functor in each exterior degree, so `Const(R)^{a,b} = R^a` for
  every `b`.  `Crystalline.cosimplicialRowComplex_constantCosimplicialCochainComplex` says its
  rows are `R` again, in every `b`.
* **The comparison morphism.**  `Crystalline.CosimplicialDoubleComplex.constHom` builds a morphism
  `K ⟶ Const(R)` out of a family of maps `K^a(⦋b⦌) ⟶ R^a` compatible with the cosimplicial
  transition maps and with the differential of `K`; the cosimplicial compatibility is exactly
  naturality against a constant object, and for the crystalline double complex it is
  `Crystalline.completedEnvelopeCodiagonal_map`, the identity `ε_n ∘ D(φ) = ε_m`.  Applying
  `Crystalline.cosimplicialDoubleComplexFunctor` turns it into a morphism of double complexes.
* **The columns of `Const(R)` resolve their degree-`0` terms.**
  `Crystalline.exactAt_constCosimplicialDoubleComplex_X` and
  `Crystalline.constCosimplicialDoubleComplex_X_d_zero_one` are the two halves of that, both from
  the computation of the differentials of a constant Moore complex.
* **The degeneration.**
  `StacksDraft.TotalRowComparison.rowZeroHomologyIsoColumnZero_of_rowComparison` assembles the
  three: the row `0` of `Const(R)` is its total complex up to quasi-isomorphism, the
  rowwise comparison identifies the two total complexes, and the column degeneration — already
  available, because the columns off `0` *are* acyclic by [Stacks, Lemma 60.19.1, Tag 07LA] —
  brings it back to the column `0`.

## Main results

* `Crystalline.exactAt_constCosimplicialDoubleComplex_X`,
  `Crystalline.constCosimplicialDoubleComplex_X_d_zero_one`,
  `Crystalline.diagonalFinite_constCosimplicialDoubleComplex` — the inputs the degeneration needs
  about the comparison object.
* `Crystalline.cosimplicialDoubleComplexRowComparisonHomologyIso` — **the replacement for
  `Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso`**: the same conclusion, with the
  acyclicity of the rows off `0` replaced by the hypothesis that each row map
  `K^{*,b} ⟶ R` is a quasi-isomorphism.

That last hypothesis is the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD], proved as
clause 2 of `Crystalline.DividedPowerPolynomial.stacks07LD`; it is the only genuinely new
mathematics the chain needs.  No tag attribute is placed anywhere here: this is the
homological-algebra step inside the proof of [Stacks, Tag 07LG], which is
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial

universe u

namespace Crystalline

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)
  (R : CochainComplex AddCommGrpCat.{u} ℕ)

/-! ### The comparison object and the comparison morphism -/

/-- **The rows of a cochain complex of constant cosimplicial groups are the complex itself**, in
every cosimplicial degree: the row `b` of `Crystalline.cosimplicialRowComplex` evaluates each
cosimplicial group at `⦋b⦌`, and a constant one takes the same value in every degree. -/
public theorem cosimplicialRowComplex_constantCosimplicialCochainComplex (b : ℕ) :
    cosimplicialRowComplex (constantCosimplicialCochainComplex.obj R) b = R := rfl

/-! ### The columns of the comparison object resolve their degree-zero terms -/

/-- The column of a double complex of a cosimplicial cochain complex is zero outside `ℕ`. -/
private theorem isZero_cosimplicialDoubleComplex_X_of_not_exists_nat
    (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) {a : ℤ}
    (ha : ¬∃ n : ℕ, (n : ℤ) = a) : IsZero ((cosimplicialDoubleComplexFunctor.obj L).X a) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat a (fun i hi => ha ⟨i, hi⟩)

/-- **Each column of the double complex of `Const(R)` is exact off degree `0`.**

The column `a` is the `ℕ`-to-`ℤ` extension of the Moore complex of the constant cosimplicial
group on `R^a`, which is exact in every positive degree by
`AlgebraicTopology.constantAlternatingCofaceMapComplex_exactAt`; the extension adds no cohomology
in a degree of the image of the embedding, and in a negative degree the term itself vanishes. -/
public theorem exactAt_constCosimplicialDoubleComplex_X (a : ℤ) {q : ℤ} (hq : q ≠ 0) :
    ((cosimplicialDoubleComplexFunctor.obj
      (constantCosimplicialCochainComplex.obj R)).X a).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine IsZero.of_iso ?_
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q).mapIso
        (cosimplicialDoubleComplexColumnIso (constantCosimplicialCochainComplex.obj R) n))
    by_cases hq0 : 0 ≤ q
    · lift q to ℕ using hq0
      refine IsZero.of_iso ?_
        ((constantAlternatingCofaceMapComplex (R.X n)).extendHomologyIso
          ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl)
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact constantAlternatingCofaceMapComplex_exactAt_of_ne_zero (R.X n) q
        (by exact_mod_cast hq)
    · exact ShortComplex.isZero_homology_of_isZero_X₂ (_ : ShortComplex AddCommGrpCat.{u})
        (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
          (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega))
  · refine Functor.map_isZero
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) q)
      (isZero_cosimplicialDoubleComplex_X_of_not_exists_nat _ ha)

/-- **The differential out of degree `0` of each column of the double complex of `Const(R)`
vanishes**, so the degree-`0` cocycles of the column are the whole of the row `0`.

In the Moore complex of a constant cosimplicial object `d⁰ = δ⁰ - δ¹ = 0`
(`AlgebraicTopology.constantAlternatingCofaceMapComplex_d_zero_one`); the extension from `ℕ` to
`ℤ` conjugates it by the identifications of the terms. -/
public theorem constCosimplicialDoubleComplex_X_d_zero_one (a : ℤ) :
    ((cosimplicialDoubleComplexFunctor.obj
      (constantCosimplicialCochainComplex.obj R)).X a).d 0 1 = 0 := by
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine StacksDraft.TotalRowComparison.d_eq_zero_of_iso
      (cosimplicialDoubleComplexColumnIso (constantCosimplicialCochainComplex.obj R) n) 0 1 ?_
    have h0 : ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
        ((constantCosimplicialCochainComplex.obj R).X n)).d 0 1 = 0 :=
      constantAlternatingCofaceMapComplex_d_zero_one (R.X n)
    rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
      (i := 0) (j := 1) (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)
      (show ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) from rfl), h0, zero_comp, comp_zero]
  · exact (Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) 0)
      (isZero_cosimplicialDoubleComplex_X_of_not_exists_nat _ ha)).eq_of_src _ _

/-- **The double complex of `Const(R)` has finite diagonals**, being concentrated in the first
quadrant. -/
public theorem diagonalFinite_constCosimplicialDoubleComplex :
    DiagonalFinite (cosimplicialDoubleComplexFunctor.obj
      (constantCosimplicialCochainComplex.obj R)) :=
  StacksDraft.TotalRowComparison.diagonalFinite_of_bounded _ 0
    (fun a _ hb => isZero_cosimplicialDoubleComplex_X_X_of_neg _ a hb)
    (fun _ ha => isZero_cosimplicialDoubleComplex_X_of_neg _ ha)

/-- **A row map in negative cosimplicial degree is automatically a quasi-isomorphism**: both rows
vanish there, by `Crystalline.isZero_cosimplicialDoubleComplex_flip_X_X_of_neg`.  So the rowwise
hypothesis of `Crystalline.cosimplicialDoubleComplexRowComparisonHomologyIso`, although stated
over all of `ℤ`, only ever has content for a `b` in the image of `ℕ`. -/
public theorem quasiIso_flipMap_cosimplicialDoubleComplexFunctor_map_of_neg
    (rho : K ⟶ constantCosimplicialCochainComplex.obj R) {b : ℤ} (hb : b < 0) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) := by
  have h (L : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ) :
      IsZero ((cosimplicialDoubleComplexFunctor.obj L).flip.X b) :=
    StacksDraft.TotalDegeneration.isZero_of_isZero_X
      (fun a => isZero_cosimplicialDoubleComplex_flip_X_X_of_neg L hb a)
  have := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero
    ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b) (h K) (h _)
  infer_instance

/-! ### The replacement for the second spectral sequence -/

/-- **The two spectral sequences of [Stacks, Proposition 60.21.3, Tag 07LG], composed — with the
second one run from a comparison instead of from a vanishing.**

This is the replacement for `Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso`.  Its
conclusion is the same: the cohomology of the row `0` of the double complex of `K` is the
cohomology of the Moore complex of the `0`-th cosimplicial group of `K`, which for the crystalline
`K` is the comparison of `M ⊗^∧_D Ω^*_D` with `M(•)` that the proof of that proposition performs.
Its hypotheses differ in the row direction:

* `hcol` is unchanged — the acyclicity of the columns off `0`, which is
  [Stacks, Lemma 60.19.1, Tag 07LA];
* where `Crystalline.cosimplicialDoubleComplexRowZeroHomologyIso` asks that the rows off `0` be
  acyclic — which `CosimplicialDeRhamRowObstruction.lean` shows cannot hold — this asks for a
  cochain complex `R` of abelian groups, a morphism `rho : K ⟶ Const(R)`, and that each of the
  induced row maps be a **quasi-isomorphism**.  That is the completed clause of
  [Stacks, Lemma 60.21.2, Tag 07LD], the statement that
  `M ⊗^∧_D Ω^*_D ⟶ M ⊗^∧_D Ω^*_{D(b)}` is a quasi-isomorphism, proved as clause 2 of
  `Crystalline.DividedPowerPolynomial.stacks07LD` and taken here as a hypothesis on `rho`.

The rows indexed by a negative integer need no hypothesis of their own: both sides vanish there
(`Crystalline.isZero_cosimplicialDoubleComplex_flip_X_X_of_neg`), so the row map is automatically
a quasi-isomorphism; `hrows` is stated over all of `ℤ` only because that is the index the flip of
the double complex uses. -/
public def cosimplicialDoubleComplexRowComparisonHomologyIso
    (rho : K ⟶ constantCosimplicialCochainComplex.obj R)
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).homology j))
    (hrows : ∀ b : ℤ, QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map rho)).f b))
    (j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj K).flip.X 0).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X 0)).homology j :=
  (StacksDraft.TotalRowComparison.rowZeroHomologyIsoColumnZero_of_rowComparison
        (cosimplicialDoubleComplexFunctor.map rho)
        (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg K p hq)
        (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg K hp)
        (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg _ p hq)
        (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg _ hp)
        (diagonalFinite_constCosimplicialDoubleComplex R)
        (fun a _q hq => exactAt_constCosimplicialDoubleComplex_X R a hq)
        (constCosimplicialDoubleComplex_X_d_zero_one R) hrows
        (acyclic_cosimplicialDoubleComplex_X_of_ne_zero K hcol) (j : ℤ)).trans
    (cosimplicialDoubleComplexColumnZeroHomologyIso K j)

end Crystalline

end
