module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowDerived
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceColumnZeroSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamComputesCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemDerived

/-!
# The de Rham complex of a crystal computes `RΓ(Cris(X/S), ℱ)` in the derived category

In the situation of [Stacks, Proposition 60.21.3, Tag 07LG] — `X = Spec(C)` over `S = Spec(A)`,
both affine, `p` nilpotent on `X`, `ℱ` a crystal in quasi-coherent `𝒪_{X/S}`-modules and `(M, ∇)`
its module with connection over `D` ([Stacks, Lemma 60.17.3, Tag 07JG]) — the complex
`M ⊗^∧_D Ω^*_D` (`...SmallSite.crystalPairDeRhamComplex`) computes `RΓ(Cris(X/S), ℱ)`.  This module
gives that comparison as an isomorphism in the derived category:

`M ⊗^∧_D Ω^*_D ≅ RΓ(Cris(X/S), ℱ)`

in `D(Ab)` (`...SmallSite.crystalPairDeRhamDerivedIso`) and in `D⁺(Ab)`
(`...SmallSite.crystalPairDeRhamDerivedPlusIso`, which carries the tag), `RΓ` being
`...SmallSite.derivedGlobalSections`, the right derived functor of global sections, and the complex
being lifted to the universe of the abelian sheaves on `Cris(X/S)` and extended by zero from `ℕ`
to `ℤ`.

## The comparison

It is the composite of the source's two steps, each read in `D(Ab)`:

* the double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` identifies its row zero
  `M ⊗^∧_D Ω^*_D` with its column zero `M(•)`
  (`Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroDerivedIso`, with the acyclic columns of
  [Stacks, Lemma 60.19.3, Tag 07LF] and the quasi-isomorphic rows of
  [Stacks, Lemma 60.21.2, Tag 07LD]);
* the column zero, lifted, is the complex `M(0) → M(1) → ⋯` of the system of thickenings
  (`...SmallSite.wholeSpaceMooreComplexSectionsIso`), which is `RΓ(Cris(X/S), ℱ)` by
  [Stacks, Proposition 60.20.1, Tag 07JN] (`...SmallSite.wholeSpaceSystemDerivedIsoOfAbelian`),
  whose two hypotheses hold for a crystal in quasi-coherent modules.

## Main definitions

* `...SmallSite.crystalPairDeRhamDerivedIso` — `M ⊗^∧_D Ω^*_D ≅ RΓ(Cris(X/S), ℱ)` in `D(Ab)`.
* `...SmallSite.crystalPairDeRhamDerivedPlusIso` — **[Stacks, Tag 07LG]**, the same comparison in
  `D⁺(Ab)`, with `...SmallSite.ι_map_crystalPairDeRhamDerivedPlusIso_hom` reading it in `D(Ab)`.
* `...SmallSite.crystalPairDeRhamDerivedHomologyIso` — its cohomology in degree `j`,
  `H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(Cris(X/S), ℱ)`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicTopology Simplicial

universe w w' u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The complex `M ⊗^∧_D Ω^*_D` of a crystal computes `RΓ(Cris(X/S), ℱ)`, in `D(Ab)`**: an
isomorphism `M ⊗^∧_D Ω^*_D ≅ RΓ(Cris(X/S), ℱ)` in the derived category of abelian groups, the
complex lifted to the universe of the abelian sheaves on `Cris(X/S)` and extended by zero to `ℤ`.

It is the comparison of the proof of [Stacks, Proposition 60.21.3, Tag 07LG]: the identification
of the row zero of the double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` with its column zero
through the total complex (`Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroDerivedIso`),
the identification of the column zero with `M(0) → M(1) → ⋯`, and the Čech comparison of
[Stacks, Proposition 60.20.1, Tag 07JN] (`...SmallSite.wholeSpaceSystemDerivedIsoOfAbelian`). -/
def crystalPairDeRhamDerivedIso :
    DerivedCategory.Q.obj
        (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (crystalPairDeRhamComplex hp Fc)).extend ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Plus.ι.obj ((derivedGlobalSections S).obj (abelianSheaf Fc.obj)) :=
  DerivedCategory.Q.mapIso
      (HomologicalComplex.mapHomologicalComplexExtendIso AddCommGrpCat.uliftFunctor.{u + 1, u}
          (crystalPairDeRhamComplex hp Fc) ComplexShape.embeddingUpNat ≪≫
        (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapIso
            (eqToIso (crystalCosimplicialPair_degreeDeRhamComplex_zero hp Fc).symm))) ≪≫
    (crystalCosimplicialPair hp Fc).rowZeroColumnZeroDerivedIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}
      (fun n hn j => isZero_homology_wholeSpaceDoubleComplex_X hp Fc
        (crystalCosimplicialPair hp Fc).nabla (crystalCosimplicialPair hp Fc).nabla_tensorMap
        (crystalCosimplicialPair hp Fc).isSquareZero n hn j)
      (quasiIso_crystalCosimplicialPair_rowFromZeroHom hp Fc) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.mapHomologicalComplexExtendIso AddCommGrpCat.uliftFunctor.{u + 1, u}
          ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
            ((wholeSpaceCosimplicialModule hp Fc).column 0))
          ComplexShape.embeddingUpNat).symm ≪≫
        (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).mapIso
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
              (ComplexShape.up ℕ)).mapIso
            ((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
              (wholeSpaceCosimplicialModule hp Fc).columnZeroIso) ≪≫
            wholeSpaceMooreComplexSectionsIso hp Fc)) ≪≫
    wholeSpaceSystemDerivedIsoOfAbelian hp (abelianSheaf Fc.obj)
      (vanishing07JJ_abelianSheaf Fc.obj
        (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1))
      (fun n e => surjective_wholeSpaceSystem_level_map hp Fc.obj
        (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1)
        (isSurjectiveComparison_of_isSheafCrystal Fc.property.2) n e)

/-- **[Stacks, Proposition 60.21.3, Tag 07LG]: the complex `M ⊗^∧_D Ω^*_D` computes
`RΓ(Cris(X/S), ℱ)`**, as an isomorphism in the bounded below derived category `D⁺(Ab)`:

`M ⊗^∧_D Ω^*_D ≅ RΓ(Cris(X/S), ℱ)`.

The situation is that of [Stacks, Proposition 60.20.1, Tag 07JN]: `X` and `S` affine, `p`
nilpotent on `X`, and `D` the completed envelope of a surjective polynomial presentation
`A[x_i : i ∈ ι] → C`, supplied as the instance `...SmallSite.WholeSpacePresentation S hp`, by
default the tautological one.  `ℱ` is a crystal in quasi-coherent `𝒪_{X/S}`-modules and `(M, ∇)`
the module with connection over `D` corresponding to it under [Stacks, Lemma 60.17.3, Tag 07JG]
(`...SmallSite.crystalPairFunctor`); the complex `M ⊗^∧_D Ω^*_D` is
`...SmallSite.crystalPairDeRhamComplex`, lifted to the universe of the abelian sheaves on
`Cris(X/S)` and extended by zero to `ℤ`, and `RΓ(Cris(X/S), -)` is
`...SmallSite.derivedGlobalSections`, the right derived functor of global sections.  Read in
`D(Ab)` it is `...SmallSite.crystalPairDeRhamDerivedIso`, the comparison of the proof. -/
@[stacks 07LG "for any surjective polynomial presentation A[x_i : i ∈ ι] → C, supplied as the \
WholeSpacePresentation instance (by default the tautological one): an isomorphism \
M ⊗^∧_D Ω*_D ≅ RΓ(Cris(X/S), F) in D⁺(Ab), through the double complex \
M(b) ⊗^∧_{D(b)} Ω^a_{D(b)} and the comparison of 07JN, for F a crystal in quasi-coherent \
modules and (M, ∇) its module with connection"]
def crystalPairDeRhamDerivedPlusIso :
    DerivedCategory.Plus.Q.obj
        (Stacks.Cohomology.extendPlusObj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (crystalPairDeRhamComplex hp Fc))) ≅
      (derivedGlobalSections S).obj (abelianSheaf Fc.obj) :=
  DerivedCategory.Plus.ι.preimageIso (crystalPairDeRhamDerivedIso hp Fc)

/-- **The derived comparison of [Stacks, Tag 07LG] read in `D(Ab)`** is
`...SmallSite.crystalPairDeRhamDerivedIso`. -/
theorem ι_map_crystalPairDeRhamDerivedPlusIso_hom :
    DerivedCategory.Plus.ι.map (crystalPairDeRhamDerivedPlusIso hp Fc).hom =
      (crystalPairDeRhamDerivedIso hp Fc).hom :=
  DerivedCategory.Plus.ι.map_preimage _

/-- **The cohomology of the derived comparison of [Stacks, Tag 07LG]**:
`H^j(M ⊗^∧_D Ω^*_D) ≅ H^j(Cris(X/S), ℱ)` for every `j`, the degree-`j` cohomology of
`...SmallSite.crystalPairDeRhamDerivedIso`, read through the identification of the cohomology of
`RΓ` with the graded crystalline cohomology (`...SmallSite.homologyDerivedGlobalSectionsIsoObj`). -/
def crystalPairDeRhamDerivedHomologyIso (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj ((crystalPairDeRhamComplex hp Fc).homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso
      AddCommGrpCat.uliftFunctor.{u + 1, u} (crystalPairDeRhamComplex hp Fc) j).symm ≪≫
    (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (crystalPairDeRhamComplex hp Fc)).extendHomologyIso
        ComplexShape.embeddingUpNat (j' := (j : ℤ)) rfl).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} (j : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (j : ℤ)).mapIso
      (crystalPairDeRhamDerivedIso hp Fc) ≪≫
    homologyDerivedGlobalSectionsIsoObj S (abelianSheaf Fc.obj) j

end Crystalline.GlobalCrystallineSituation.SmallSite

end
