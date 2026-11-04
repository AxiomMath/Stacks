module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowRetraction
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialPair
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemCohomology

/-!
# The row zero of the double complex of a crystal computes crystalline cohomology

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` over an affine situation,
`M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)` the cosimplicial module of
[Stacks, Proposition 60.20.1, Tag 07JN], and suppose each `M(b)` carries a completed connection
`∇_b` compatible with the cosimplicial direction and with square-zero de Rham differential, so that
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` is a double complex
(`...SmallSite.wholeSpaceDoubleComplex`).

This module composes the two halves of the proof of [Stacks, Proposition 60.21.3, Tag 07LG] that
do not depend on how the connections were obtained:

* the column half — the columns `a > 0` are acyclic by [Stacks, Lemma 60.19.3, Tag 07LF]
  (`...SmallSite.isZero_homology_wholeSpaceDoubleComplex_X`), and the column `a = 0` is the
  complex `M(0) → M(1) → ⋯` (`...SmallSite.wholeSpaceDoubleComplexColumnZeroHomologyIso`), which
  computes `RΓ(Cris(X/S), ℱ)` by [Stacks, Tag 07JN]
  (`...SmallSite.computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison`);
* the row half, from a retraction of every coprojection `K^{*,0} ⟶ K^{*,b}` with the homotopy
  of [Stacks, Lemma 60.21.2, Tag 07LD]
  (`Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroHomologyIso`).

Every map in the composite is named, so the comparison is a `def` and not a mere existence.

## Main definitions

* `...SmallSite.wholeSpaceRowZeroCohomologyIso` — **`H^j(M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}) ≅
  H^j(Cris(X/S), ℱ)`**, given the row retractions.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme] (Fc : QuasiCoherentCrystal S)
  (nabla : ∀ b : ℕ, CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
    ((wholeSpaceDPAlgebra hp).forms S.p 1 b) ((wholeSpaceDPAlgebra hp).differential S.p b)
    ((wholeSpaceCosimplicialModule hp Fc).carrier b))
  (hnabla : ∀ {m n : SimplexCategory} (φ : m ⟶ n)
    (x : (wholeSpaceCosimplicialModule hp Fc).carrier m.len),
    nabla n.len ((wholeSpaceCosimplicialModule hp Fc).map φ x) =
      (wholeSpaceCosimplicialModule hp Fc).tensorMap φ 1 (nabla m.len x))
  (hsq : ∀ b : ℕ, CompletedDeRham.IsSquareZero S.p
    ((wholeSpaceDPAlgebra hp).completedRing S.p b)
    (fun a => (wholeSpaceDPAlgebra hp).forms S.p a b) ((wholeSpaceDPAlgebra hp).wedge S.p b)
    ((wholeSpaceDPAlgebra hp).deRham S.p b)
    ((wholeSpaceCosimplicialModule hp Fc).carrier b) (nabla b)
    ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p b))

/-- **The comparison of [Stacks, Proposition 60.20.1, Tag 07JN] for a crystal in quasi-coherent
modules, as an isomorphism**: `H^j(M(0) → M(1) → ⋯) ≅ H^j(Cris(X/S), ℱ)`.  The two hypotheses of
that proposition are discharged from the crystal: local quasi-coherence by
`...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` and the surjectivity of the
comparison maps along closed immersions by `...SmallSite.isSurjectiveComparison_of_isSheafCrystal`.
-/
def wholeSpaceSectionsComplexCohomologyIso (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).homology j ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  haveI := isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp Fc.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1)
    (isSurjectiveComparison_of_isSheafCrystal Fc.property.2) j
  asIso (computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp Fc.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1)
    (isSurjectiveComparison_of_isSheafCrystal Fc.property.2) j)

/-- **The row zero `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` of the double complex of a crystal in
quasi-coherent modules computes `RΓ(Cris(X/S), ℱ)`**, degree by degree, given for every
cosimplicial degree `b` a retraction `π_b` of the coprojection `K^{*,0} ⟶ K^{*,b}` commuting with
the de Rham differentials, with `ι_b ∘ π_b` homotopic to the identity through `h_b`.

The composite is: the two degenerations of the double complex
(`Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroHomologyIso`, whose column input is
[Stacks, Lemma 60.19.3, Tag 07LF]), the identification of the column zero with
`M(0) → M(1) → ⋯`, and [Stacks, Tag 07JN]. -/
def wholeSpaceRowZeroCohomologyIso
    (piDeg : ∀ b i : ℕ,
      (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj i b →+
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj i 0)
    (hDeg : ∀ b i : ℕ,
      (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj
          (i + 1) b →+
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj i b)
    (hpi : ∀ (b i : ℕ) (y :
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj i b),
      (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDifferential 0 i (piDeg b i y) =
        piDeg b (i + 1)
          ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDifferential b i y))
    (hretract : ∀ (b i : ℕ) (x :
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj i 0),
      piDeg b i ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).rowFromZeroDeg b i x) = x)
    (h0 : ∀ (b : ℕ) (x :
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj 0 b),
      hDeg b 0 ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDifferential b 0 x) +
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).rowFromZeroDeg b 0 (piDeg b 0 x) = x)
    (hsucc : ∀ (b i : ℕ) (x :
        (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule.obj
          (i + 1) b),
      (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDifferential b i (hDeg b i x) +
          hDeg b (i + 1)
            ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDifferential b (i + 1) x) +
          (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).rowFromZeroDeg b (i + 1)
            (piDeg b (i + 1) x) = x)
    (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDeRhamComplex 0).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
      ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).rowZeroColumnZeroHomologyIso
        (fun n hn j => isZero_homology_wholeSpaceDoubleComplex_X hp Fc nabla hnabla hsq n hn j)
        piDeg hDeg hpi hretract h0 hsucc j) ≪≫
    wholeSpaceDoubleComplexColumnZeroHomologyIso hp Fc nabla hnabla hsq j ≪≫
    wholeSpaceSectionsComplexCohomologyIso hp Fc j

/-- **The row zero `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` of the double complex of a crystal in
quasi-coherent modules computes `RΓ(Cris(X/S), ℱ)`**, degree by degree, as soon as every
coprojection `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is a quasi-isomorphism —
the conclusion of [Stacks, Lemma 60.21.2, Tag 07LD] for the presentation of `D(b)` as a completed
divided power polynomial algebra over `D` of [Stacks, Lemma 60.17.5, Tag 07L2]. -/
def wholeSpaceRowZeroCohomologyIsoOfQuasiIso
    (hq : ∀ b : ℕ, QuasiIso ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).rowFromZeroHom b))
    (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).degreeDeRhamComplex 0).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
      ((wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).rowZeroColumnZeroHomologyIsoOfQuasiIso
        (fun n hn j => isZero_homology_wholeSpaceDoubleComplex_X hp Fc nabla hnabla hsq n hn j)
        hq j) ≪≫
    wholeSpaceDoubleComplexColumnZeroHomologyIso hp Fc nabla hnabla hsq j ≪≫
    wholeSpaceSectionsComplexCohomologyIso hp Fc j

end Crystalline.GlobalCrystallineSituation.SmallSite

end
