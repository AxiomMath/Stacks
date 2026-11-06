module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Computes07LGFromDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowQuasiIso

/-!
# [Stacks, Tag 07LG] from the double complex, with the rowwise hypothesis stated about the rows

`...SmallSite.computes07LG_of_doubleComplex` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFromDoubleComplex.lean` states its rowwise
hypothesis `hrows` about the *flip of the double complex*: each

`(StacksDraft.TotalRowComparison.flipMap (cosimplicialDoubleComplexFunctor.map rho)).f b`,
`b : ℤ`,

is to be a quasi-isomorphism.  That is the index the degeneration runs over, but it is not the
shape anything is proved in: the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] is about
the complexes `M ⊗^∧_D Ω^*_D` and `M ⊗^∧_D Ω^*_{D'}` themselves, which are the *rows* of `K`,
indexed by a natural number and with no `ℕ`-to-`ℤ` extension in sight.

This module restates the reduction with `hrows` moved to the rows, by
`Crystalline.quasiIso_flipMap_of_quasiIso_row`.  Nothing else changes: the other hypotheses are
kept verbatim, and the two statements are interderivable.

## Why this is the useful shape

Three things come for free with it.

* The hypothesis is about `Crystalline.cosimplicialRowComplex`, the complex `a ↦ K^a(⦋b⦌)`, so for
  a `K` built from a `Crystalline.CosimplicialCompletedPair` it is a hypothesis about the completed
  de Rham complex `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`, by
  `Crystalline.CosimplicialCompletedPair.rowDeRhamIso`.
* It is indexed by `ℕ`, so the vacuous rows in negative degree are gone — they are discharged
  inside `Crystalline.quasiIso_flipMap_of_quasiIso_row` rather than being an obligation the caller
  has to notice is vacuous.
* The direction is the one the perturbation lemma produces, by
  `Crystalline.CompletedDeRham.quasiIso_of_section`: the row map goes `K^{*,b} ⟶ R` whereas
  [Stacks, Tag 07LD] produces the comparison `R ⟶ K^{*,b}`, and a map with a section which is a
  quasi-isomorphism is one itself.  For the crystalline `K` the section is a coprojection and the
  row map is induced by the codiagonal, which retracts it
  (`Crystalline.completedEnvelopeCodiagonal_coprojection`).

## The named hypotheses

Exactly those of `...SmallSite.computes07LG_of_doubleComplex`, with `hrows` replaced.  **No tag
attribute is placed**: this is a reduction with named hypotheses, and [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.  See the module documentation of
`Computes07LGFromDoubleComplex.lean` for what each hypothesis is and why.

## Main result

* `...SmallSite.computes07LG_of_doubleComplex_rowwise` — [Stacks, Tag 07LG] from the double
  complex, with the rowwise hypothesis stated about the rows of `K`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
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

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from the double complex, with the rowwise hypothesis
stated about the rows of `K`.**

This is `...SmallSite.computes07LG_of_doubleComplex` with its hypothesis `hrows` replaced by the
equivalent statement about the rows: for every cosimplicial degree `b : ℕ`, the row `b` of the
comparison morphism `rowComparison` — the map `K^{*,b} ⟶ rowTarget` of
`Crystalline.cosimplicialRowMap` — is a quasi-isomorphism.  The passage between the two is
`Crystalline.quasiIso_flipMap_of_quasiIso_row`, which also discharges the rows indexed by a
negative integer, both sides vanishing there.

Every other hypothesis is kept verbatim; see the module documentation of
`Computes07LGFromDoubleComplex.lean` for what each one is.  **No tag attribute is placed** on this
reduction; [Stacks, Tag 07LG] is `...SmallSite.crystalPairDeRhamComplex_computesCohomology`. -/
public theorem computes07LG_of_doubleComplex_rowwise
    (K : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CochainComplex (CosimplicialObject AddCommGrpCat.{u + 1}) ℕ)
    (hcolumns : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (n : ℕ), 0 < n → ∀ j : ℕ, IsZero (((alternatingCofaceMapComplex
        AddCommGrpCat.{u + 1}).obj ((K F hF).X n)).homology j))
    (rowTarget : ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CochainComplex AddCommGrpCat.{u + 1} ℕ)
    (rowComparison : ∀ (F : SheafOfModules.{u} (structureSheaf S))
      (hF : F.IsQuasicoherentOnSite),
      K F hF ⟶ AlgebraicTopology.constantCosimplicialCochainComplex.obj (rowTarget F hF))
    (hrows : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (b : ℕ), QuasiIso (cosimplicialRowMap (rowComparison F hF) b))
    (hrow0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (j : ℕ), Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
          ((crystalDeRhamComplex S A Dr g Om der p dx wedge deRham hleib R h07IT F hF
            (hsq F hF)).homology j) ≅
        ((cosimplicialDoubleComplexFunctor.obj (K F hF)).flip.X 0).homology (j : ℤ)))
    (hcolumn0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      IsCrystalLevelQuotient (wholeSpaceSystem S hp) (abelianSheaf F).obj
          (wholeSpaceLevelExponent hp) →
        ∀ j : ℕ, Nonempty (((alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
            ((K F hF).X 0)).homology j ≅
          (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j))
    (hker : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (_hF : F.IsQuasicoherentOnSite)
      (n e : ℕ) (x : (abelianSheaf F).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))),
      levelMap (wholeSpaceSystem S hp) (abelianSheaf F).obj n e x = 0 →
        ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq :=
  computes07LG_of_doubleComplex S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq K hcolumns
    rowTarget rowComparison
    (fun F hF => quasiIso_flipMap_of_quasiIso_row (rowComparison F hF) (hrows F hF)) hrow0
    hcolumn0 hker

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
