module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionDeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemCohomology

/-!
# [Stacks, Tag 07LG] from [Stacks, Tag 07JN] and the comparison of the two complexes

[Stacks, Proposition 60.21.3, Tag 07LG] says that for a crystal `ℱ` in quasi-coherent
`𝒪_{X/S}`-modules on the small crystalline site of an affine situation, the complex
`M ⊗^∧_D Ω^*_D` of the corresponding pair computes `RΓ(Cris(X/S), ℱ)`.  The library states it as
`Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG`.

[Stacks, Tag 07JN] is formalized as
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison`: it says that the
*other* complex of the source's proof, `M(0) → M(1) → M(2) → ⋯`, computes `RΓ(Cris(X/S), ℱ)`.
The whole remaining content of [Stacks, Tag 07LG] is therefore the comparison of the two
complexes — the two spectral sequences of the double complex `K^{a,b} = M ⊗̂_D Ω^a_{D(b)}`, whose
first column is `M(•)` and whose first row is `M ⊗^∧_D Ω^*_D`.

This module performs that composition, so that [Stacks, Tag 07JN] is plugged in once and for all
and what remains of [Stacks, Tag 07LG] is exactly one statement about the two complexes.

## Main result

* `...SmallSite.computes07LG_of_sectionsComplexHomologyIso` — [Stacks, Tag 07LG] holds as soon as
  the de Rham complex of the pair and the complex `M(0) → M(1) → M(2) → ⋯` have the same
  cohomology in every degree, for every coefficient sheaf satisfying the tag's hypothesis.

## What is carried, and why

One hypothesis is named, and **no tag attribute is placed** here: this is a reduction, and
[Stacks, Tag 07LG] is `...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`.

* `hcomp`, the comparison of the two complexes.  This is the mathematical content of
  [Stacks, Tag 07LG] that is not [Stacks, Tag 07JN], namely the two spectral sequences of the
  double complex.  Of their two degenerations the acyclicity half is available, as
  `HomologicalComplex₂.acyclic_total_of_acyclic_column` of
  `StacksFrontier/Algebra/Homology/SpectralSequence/TotalAcyclic.lean`, with the acyclicity of the
  columns supplied by [Stacks, Tag 07LA]
  (`Crystalline.id_completedTensorCompletedForms_homotopic_zero`).

  The double complex itself now exists, for the coefficient sheaf `𝒪_{X/S}`: the bigraded family
  `Ω^a_{D(b)}` with its de Rham differential in the `a` direction is
  `Crystalline.envelopeStructureDoubleComplex` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialStructurePair.lean`, whose
  row `b` is the completed de Rham complex of the cosimplicial degree `b` by
  `Crystalline.CosimplicialCompletedPair.rowDeRhamIso` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRow.lean` and whose
  column `a = 0` is the cosimplicial module `M(•)` by
  `Crystalline.envelopeStructureColumnZeroIso`.  The double complex of a *general* crystal is
  that of `...SmallSite.crystalCosimplicialPair` of `SmallSite/CrystalCosimplicialPair.lean`, and
  the proof of [Stacks, Tag 07LG] from it is
  `...SmallSite.crystalPairDeRhamDerivedPlusIso`; this file does not supply `hcomp`
  from it.

Both hypotheses of [Stacks, Tag 07JN] on the coefficient sheaf — the source's own hypotheses at
[Stacks, Tag 07LG], which opens "assumptions as in Proposition 07JN" — are now discharged, and
neither is named any more.

* Local quasi-coherence is the half of [Stacks, Tag 07IT] the library proves, on the small site:
  `...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/QuasicoherentImpliesLocal.lean`.
* Hypothesis (2), `...SmallSite.CohomologyRestriction.IsSurjectiveComparison`, follows from the
  crystal property alone, by `...SmallSite.isSurjectiveComparison_of_isSheafCrystal` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalComparisonSurjectivity.lean`; and
  the crystal property of a quasi-coherent coefficient sheaf is the standing hypothesis `h07IT`,
  which is [Stacks, Tag 07IT].  This is exactly how the source gets it: the proof of
  [Stacks, Tag 07JH] writes `M_e = M_{e+1}/p^e M_{e+1}` "since `ℱ` is a crystal".

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

universe u uI

open CategoryTheory AlgebraicGeometry Opposite

namespace Crystalline

open DividedPowers

namespace GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1)) (p : ℕ)
  {ι : Type uI} (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))
  [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)
  (hsq : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    CompletedDeRham.IsSquareZero p Dr Om wedge deRham
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla hleib)

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from [Stacks, Proposition 60.20.1, Tag 07JN].**

[Stacks, Tag 07JN] says that `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), ℱ)`.  So as soon as
the complex `M ⊗^∧_D Ω^*_D` of the pair corresponding to `ℱ` has the same cohomology as that
complex in every degree, it computes `RΓ(Cris(X/S), ℱ)` too, which is [Stacks, Tag 07LG].

The only hypothesis is `hcomp`, the comparison the source carries out with the two spectral
sequences of the double complex `K^{a,b} = M ⊗̂_D Ω^a_{D(b)}`.  Neither of the two hypotheses of
[Stacks, Tag 07JN] on the coefficient sheaf is carried any more.  Local quasi-coherence is
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
applied to the coefficient sheaf, and hypothesis (2) — local surjectivity of the comparison
morphisms — is
`Crystalline.GlobalCrystallineSituation.SmallSite.isSurjectiveComparison_of_isSheafCrystal`
applied to the crystal property `h07IT F hF`, which is how the source gets it too.  See the module
documentation. -/
public theorem computes07LG_of_sectionsComplexHomologyIso
    (hcomp : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (j : ℕ), Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
            (hsq F hF)).homology j) ≅
        (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j)) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq := by
  intro F hF j
  obtain ⟨e⟩ := hcomp F hF j
  exact ⟨e.trans (computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison hp F
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF)
    (isSurjectiveComparison_of_isSheafCrystal (h07IT F hF)) j).some⟩

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
