module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Computes07LGFromDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair

/-!
# The double complex reduction of [Stacks, Tag 07LG] at the universe the double complex lives in

`...SmallSite.computes07LG_of_doubleComplex` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFromDoubleComplex.lean` asks for the
double complex `K^{a,b}` as a

`CochainComplex (CosimplicialObject AddCommGrpCat.{u + 1}) ℕ`,

and **no double complex of this library lives there.**
`Crystalline.CosimplicialCompletedPair.doubleComplex` lands in
`CochainComplex (CosimplicialObject AddCommGrpCat.{max v w}) ℕ`, where `v` is the universe of
the divided power algebras `D(b)` and `w` that of the carriers `M(b)`; for the cosimplicial
envelope of an affine crystalline situation that is `max u w` with `w` the universe of the index
type of the polynomial presentation, and the presentation the small site actually uses —
`...SmallSite.canonicalPresentation`, the tautological one on `C = Γ(X, 𝒪_X)` — has `w = u`.  So
`Crystalline.envelopeStructureDoubleComplex` is a
`CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ`: one universe level below what the
reduction asks for, with no functor in the library carrying a cochain complex of cosimplicial
groups up a level.

That mismatch is **not** essential, and this module removes it.  The `u + 1` is forced by
exactly two of the reduction's hypotheses, `hrow0` and `hcolumn0`, and only through their
*other* side: the crystalline cohomology `H^j(Cris(X/S), ℱ)` exists in `Type (u + 1)` and
nowhere lower, because `...SmallSite.cohomologyFunctor` is `Ext` on the small site and the
injectives and `Ext`-groups are available at `u + 1`.  Nothing on the side of `K` needs `u + 1`:
`Crystalline.cosimplicialDoubleComplexFunctor`,
`Crystalline.cosimplicialDoubleComplexRowComparisonHomologyIso`,
`AlgebraicTopology.alternatingCofaceMapComplex` and
`AlgebraicTopology.constantCosimplicialCochainComplex` are all universe-polymorphic, and the
reduction's own `hrow0` *already* carries an `AddCommGrpCat.uliftFunctor.{u + 1, u}` on the
`crystalDeRhamComplex` side for precisely this reason.

So the reduction is restated here with `K` at `AddCommGrpCat.{u}` and the lift moved onto the
`K` side of those two hypotheses, where it belongs.  The proof is the same chain of three
isomorphisms; the middle one, which lives at `u`, is pushed up by
`CategoryTheory.Functor.mapIso`.  Nothing is weakened: the two carried comparisons are the same
comparisons, read through the same `uliftFunctor` the original already used, and the conclusion
is the same `...SmallSite.Computes07LG`.

This does **not** supply `K`, nor `hcolumn0` and `hker`.  What is removed is one *checkable*
obstruction: after this, the carrier universe of `Crystalline.envelopeStructureDoubleComplex` is
the universe the reduction asks for.  A `Crystalline.CosimplicialCompletedPair` for a general
crystal now exists, as `...SmallSite.crystalCosimplicialPair` of
`SmallSite/CrystalCosimplicialPair.lean`, and [Stacks, Tag 07LG] itself is proved from it, as
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`, without going through this reduction.

## Main result

* `...SmallSite.computes07LG_of_doubleComplexSmall` — the reduction with `K` a
  `CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ`.
* `...SmallSite.structureSheafDoubleComplexK` — the witness that the universe now fits: the
  double complex of the coefficient sheaf, `Crystalline.envelopeStructureDoubleComplex` of the
  affine situation and the tautological presentation the small site uses, typed as the `K` of
  the reduction above.  It typechecks, which is the whole point; it is of course the wrong `K`
  for a general crystal, being constant in `ℱ`.

No tag attribute is placed: this is a reduction with named hypotheses, exactly as the original
is; the tag is on `...SmallSite.crystalPairDeRhamDerivedPlusIso`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
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

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from a double complex of cosimplicial abelian
groups in the universe `u`**, which is the universe
`Crystalline.CosimplicialCompletedPair.doubleComplex` of the cosimplicial envelope actually
lands in.

This is `...SmallSite.computes07LG_of_doubleComplex` with `K` one universe level lower.  The
hypotheses are the same five, with the `AddCommGrpCat.uliftFunctor.{u + 1, u}` that the original
carries on the `crystalDeRhamComplex` side of `hrow0` now carried on the `K` side of `hrow0` and
`hcolumn0` as well — the two places where the crystalline cohomology, which exists only at
`u + 1`, is compared with a homology group of `K`.

The hypotheses `hcolumns`, `rowTarget`, `rowComparison` and `hrows` move down without a lift,
because the homological algebra they feed —
`Crystalline.cosimplicialDoubleComplexRowComparisonHomologyIso` — is universe-polymorphic. -/
public theorem computes07LG_of_doubleComplexSmall
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
          (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j))
    (hker : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (_hF : F.IsQuasicoherentOnSite)
      (n e : ℕ) (x : (abelianSheaf F).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))),
      levelMap (wholeSpaceSystem S hp) (abelianSheaf F).obj n e x = 0 →
        ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y) :
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq := by
  refine computes07LG_of_sectionsComplexHomologyIso S A Dr g Om der p dx wedge deRham hleib hp R
    h07IT hsq ?_
  intro F hF j
  have hcrys := isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le hp F
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF)
    (isSurjectiveComparison_of_isSheafCrystal (h07IT F hF)) (hker F hF)
  exact ⟨(hrow0 F hF j).some.trans
    ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
        (cosimplicialDoubleComplexRowComparisonHomologyIso (K F hF) (rowTarget F hF)
          (rowComparison F hF) (hcolumns F hF) (hrows F hF) j)).trans
      (hcolumn0 F hF hcrys j).some)⟩

/-- **The witness that the carrier universe now fits.**

`Crystalline.envelopeStructureDoubleComplex` of the affine situation
`...SmallSite.affineSituation` and the tautological presentation
`...SmallSite.canonicalPresentation` — the situation and the presentation the small site's own
cosimplicial system `...SmallSite.wholeSpaceSystem` is built from — has exactly the type the `K`
of `...SmallSite.computes07LG_of_doubleComplexSmall` asks for.  That this definition elaborates
is the content: against `...SmallSite.computes07LG_of_doubleComplex` it does not, the
presentation's index type being `Γ(X, 𝒪_X) : Type u` so that the complex lives at `u` and not at
`u + 1`.

It is **not** a `K` for a general crystal: it is constant in `ℱ`, being the double complex of
the coefficient sheaf `𝒪_{X/S}`, the one crystal whose cosimplicial module with connection the
library has.  Supplying a genuine `K` needs a `Crystalline.CosimplicialCompletedPair` for a
general crystal, which does not exist; see the documentation of
`Computes07LGFromDoubleComplex.lean`. -/
public noncomputable def structureSheafDoubleComplexK :
    ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ :=
  fun _ _ ↦ envelopeStructureDoubleComplex (affineSituation S hp)
    (canonicalPresentation (affineSituation S hp))

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
