module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Computes07LGDoubleComplexSmall
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceKernelClause

/-!
# The double complex reduction of [Stacks, Tag 07LG] without the kernel clause

This file reduces [Stacks, Proposition 60.21.3, Tag 07LG] to seven hypotheses: a double complex
`K` of cosimplicial abelian groups, the acyclicity `hcolumns` of its columns, a row target and
comparison `rowTarget`, `rowComparison`, the row quasi-isomorphisms `hrows`, and the two edge
comparisons `hrow0` and `hcolumn0`. The kernel clause of the crystal property is not a
hypothesis: it holds for every quasi-coherent coefficient sheaf by
`...SmallSite.hker_of_h07IT`, from the hypothesis `h07IT` ([Stacks, Lemma 60.14.2, Tag 07IT]).

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.computes07LG_of_doubleComplexSmall_of_edges`:
  the reduction of [Stacks, Tag 07LG] to `K`, `hcolumns`, `rowTarget`, `rowComparison`, `hrows`,
  `hrow0` and `hcolumn0`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
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

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from a double complex of cosimplicial abelian
groups.**  The double complex `K`, the acyclicity of its columns, a row comparison whose rows are
quasi-isomorphisms, and the two edge comparisons `hrow0` and `hcolumn0` give
`...SmallSite.Computes07LG`. -/
public theorem computes07LG_of_doubleComplexSmall_of_edges
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
            (hsq F hF)).homology j) ≅
        AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          (((cosimplicialDoubleComplexFunctor.obj (K F hF)).flip.X 0).homology (j : ℤ))))
    (hcolumn0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      IsCrystalLevelQuotient (wholeSpaceSystem S hp) (abelianSheaf F).obj
          (wholeSpaceLevelExponent hp) →
        ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
            (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
              ((K F hF).X 0)).homology j) ≅
          (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j)) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  computes07LG_of_doubleComplexSmall S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq
    K hcolumns rowTarget rowComparison hrows hrow0 hcolumn0 (hker_of_h07IT hp h07IT)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
