module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Computes07LGSquareZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceKernelClause

/-!
# The double complex reduction of [Stacks, Tag 07LG] with both `hsq` and `hker` discharged

Two reductions of [Stacks, Proposition 60.21.3, Tag 07LG] in this library each discharge one of
the two hypotheses that are **not** among the tag's own.

* `...SmallSite.computes07LG_of_doubleComplexSmall_of_isGradedExterior` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGSquareZero.lean` builds the square-zero
  family `hsq` out of `[Fintype ι]`, `hext` and `hdx`, which are properties of the carried graded
  family of forms rather than assumptions about the coefficient sheaf.  It still carries `hker`.
* `...SmallSite.computes07LG_of_doubleComplexSmall_of_edges` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Computes07LGWithoutHker.lean` discharges
  `hker` from the carried `h07IT`.  It still carries `hsq`.

**Nothing composed the two**, so no single reduction in the library had both discharged.  This
module composes them: the statement below carries neither, and what is left of it is exactly the
six hypotheses of the source's own proof — the double complex `K`, the acyclicity `hcolumns` of
its columns off zero, the row target and comparison `rowTarget` and `rowComparison`, their
quasi-isomorphy `hrows`, and the two edge identifications `hrow0` and `hcolumn0` — together with
`hext`, `hdx` and `[Fintype ι]`.

## Main result

* `...SmallSite.computes07LG_of_edges_of_isGradedExterior` — the reduction of
  [Stacks, Tag 07LG] to `K`, `hcolumns`, `rowTarget`, `rowComparison`, `hrows`, `hrow0` and
  `hcolumn0`, at the **constructed** square-zero family
  `...SmallSite.squareZero07JG`.

## What is and is not proved

**No tag attribute is placed in this module.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.  The statement here is a reduction with named
hypotheses; what this module does is remove the last hypothesis that was not one of the source's
own from a single statement.  No double complex `K` for a general crystal is supplied here.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.14.2, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

universe u uI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

namespace Crystalline

open DividedPowers

namespace GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1)) (p : ℕ)
  {ι : Type uI} [Fintype ι] (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))
  [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (R : Reduction07JG S A Dr g (Om 1) der p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from a double complex of cosimplicial abelian
groups, with both the square-zero family and the kernel clause discharged.**

This is the composition of
`...SmallSite.computes07LG_of_doubleComplexSmall_of_isGradedExterior`, which builds `hsq`, with
`...SmallSite.hker_of_h07IT`, which proves `hker`.  Neither of those two hypotheses is one of the
tag's own; after this no statement of the reduction carries either.

What remains is the double complex and the five facts about it the source's proof establishes:
the acyclicity of the columns off zero ([Stacks, Lemma 60.19.3, Tag 07LF]), the rowwise
comparison with the completed de Rham complex of `(M, ∇)` and its quasi-isomorphy
([Stacks, Lemma 60.20.2, Tag 07LD]), and the two edge identifications.  The three further inputs
`[Fintype ι]`, `hext` and `hdx` constrain the carried family of forms `Om`, `wedge`, `deRham`,
`dx` to be the divided power forms the tag is about; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGSquareZero.lean`.

Nothing is weakened: the conclusion is `...SmallSite.Computes07LG` itself. -/
public theorem computes07LG_of_edges_of_isGradedExterior
    (hext : CompletedDeRham.IsGradedExterior (Dr : Type u) Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0)
    (K : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)
    (hcolumns : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (n : ℕ), 0 < n → ∀ j : ℕ, IsZero (((alternatingCofaceMapComplex
        AddCommGrpCat.{u}).obj ((K F hF).X n)).homology j))
    (rowTarget : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CochainComplex AddCommGrpCat.{u} ℕ)
    (rowComparison : ∀ (F : SheafOfModules.{u} (structureSheaf S))
      (hF : F.IsQuasicoherentOnSite),
      K F hF ⟶ AlgebraicTopology.constantCosimplicialCochainComplex.obj (rowTarget F hF))
    (hrows : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (b : ℤ), QuasiIso ((StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map (rowComparison F hF))).f b))
    (hrow0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (j : ℕ), Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
            (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx
              F hF)).homology j) ≅
        AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          (((cosimplicialDoubleComplexFunctor.obj (K F hF)).flip.X 0).homology (j : ℤ))))
    (hcolumn0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      IsCrystalLevelQuotient (wholeSpaceSystem S hp) (abelianSheaf F).val
          (wholeSpaceLevelExponent hp) →
        ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
            (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
              ((K F hF).X 0)).homology j) ≅
          (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j)) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT
      (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx) :=
  computes07LG_of_doubleComplexSmall_of_isGradedExterior S A Dr g Om der p dx wedge deRham hleib
    hp R h07IT hext hdx K hcolumns rowTarget rowComparison hrows hrow0 hcolumn0
    (hker_of_h07IT hp h07IT)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
