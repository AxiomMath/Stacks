module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.Computes07LGDoubleComplexSmall

/-!
# The hypothesis `hsq` of [Stacks, Tag 07LG] is a theorem over finitely many coordinates

`...SmallSite.Computes07LG` — the statement of [Stacks, Proposition 60.21.3, Tag 07LG] in this
library — is parametrised by

`hsq : ∀ ℱ quasi-coherent, CompletedDeRham.IsSquareZero … (functor07JG R).obj ℱ …`,

the condition that the complex `M ⊗^∧_D Ω^*_D` whose cohomology the tag computes is a complex.  In
the source `d² = 0` follows from the integrability of the connection, [Stacks, Tag 07JD], which is
clause (07JD) of [Stacks, Lemma 60.17.3, Tag 07JG] and so a property of the pair the functor
produces, not an assumption on `ℱ`.

Every `Crystalline.Pair` carries integrability in its field `Crystalline.Pair.isIntegrable` and a
coordinate expansion in its field `Crystalline.Pair.hasCoordinateOperators`, and
`Crystalline.Pair.isSquareZero` turns the two into `IsSquareZero` whenever the coordinates are
**finite** in number.  This module constructs the family `hsq` in this way, from three inputs, none
of them a statement about a crystal:

* `[Fintype ι]` on the index type of the coordinates.  In [Stacks, Tag 07JG] the coordinates are
  the variables of the polynomial presentation `A[x_i] → C`.
* `hext`, that the carried graded family of forms is exterior:
  `Crystalline.CompletedDeRham.IsGradedExterior`, that is `d ∘ d = 0`, the wedge alternating, and
  the Leibniz rule for the wedge against closed one-forms.
* `hdx`, that the coordinate differentials are closed, `d (d x_j) = 0`.

`hext` and `hdx` are properties of the parameters `Om`, `wedge`, `deRham` and `dx` of the
statement.  They hold for the completed divided power forms `Ω^*_D` of [Stacks, Tag 07J9]
(`Crystalline.isGradedExterior_completedDividedPower`) and in each cosimplicial degree of the
envelope (`Crystalline.CosimplicialDPAlgebra.isGradedExterior`).

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `squareZero07JG` — **the family `hsq`, constructed**: the de Rham differentials of the pair
  attached to any crystal in quasi-coherent modules compose to zero.
* `computes07LG_of_doubleComplexSmall_of_isGradedExterior` —
  `...SmallSite.computes07LG_of_doubleComplexSmall` with `hsq` replaced by `hext`, `hdx` and
  `[Fintype ι]`, so that its conclusion is `...SmallSite.Computes07LG` at the **constructed**
  square-zero family.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
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

/-- **The hypothesis `hsq` of [Stacks, Proposition 60.21.3, Tag 07LG] holds.**

For every crystal in quasi-coherent `𝒪_{X/S}`-modules the completed de Rham differentials of the
pair `(M, ∇)` that the functor of [Stacks, Lemma 60.17.3, Tag 07JG] attaches to it compose to
zero, provided the carried graded family of forms is exterior (`hext`), the coordinate
differentials are closed (`hdx`) and the coordinates are finite in number. -/
public theorem squareZero07JG
    (hext : CompletedDeRham.IsGradedExterior (Dr : Type u) Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0) (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite) :
    CompletedDeRham.IsSquareZero p Dr Om wedge deRham
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla hleib :=
  Pair.isSquareZero p (Dr : Type u) Om wedge deRham hleib dx
    ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)) hext hdx

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from a double complex of cosimplicial abelian
groups, at the square-zero family `...SmallSite.squareZero07JG`.**

Given the double complex `K`, the acyclicity of its columns, the row comparison and its
quasi-isomorphy, the identification of the row `b = 0`, the identification of the column `a = 0`
and the kernel clause, together with the properties `hext` and `hdx` of the carried family of
forms and `[Fintype ι]`, `...SmallSite.Computes07LG` holds at the square-zero family
`...SmallSite.squareZero07JG`. -/
public theorem computes07LG_of_doubleComplexSmall_of_isGradedExterior
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
          (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j))
    (hker : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (_hF : F.IsQuasicoherentOnSite)
      (n e : ℕ) (x : (abelianSheaf F).val.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))),
      levelMap (wholeSpaceSystem S hp) (abelianSheaf F).val n e x = 0 →
        ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT
      (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx) :=
  computes07LG_of_doubleComplexSmall S A Dr g Om der p dx wedge deRham hleib hp R h07IT
    (squareZero07JG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hext hdx)
    K hcolumns rowTarget rowComparison hrows hrow0 hcolumn0 hker

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
