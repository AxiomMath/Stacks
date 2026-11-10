module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Computes07LGFrom07JN
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelExponentAnnihilation

/-!
# [Stacks, Tag 07LG] from the double complex, with its two spectral sequences discharged

`...SmallSite.computes07LG_of_sectionsComplexHomologyIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFrom07JN.lean` reduces
[Stacks, Proposition 60.21.3, Tag 07LG] to one hypothesis `hcomp`, the comparison of the complex
`M ⊗^∧_D Ω^*_D` with the complex `M(0) → M(1) → M(2) → ⋯` of
[Stacks, Proposition 60.20.1, Tag 07JN].  That hypothesis is the whole of the source's proof
after [Stacks, Tag 07JN]: the two spectral sequences of the double complex
`K^{a,b} = M ⊗̂_D Ω^a_{D(b)}`.

This module **discharges the two spectral sequences** and leaves their inputs.  The homological
algebra is `Crystalline.cosimplicialDoubleComplexRowComparisonHomologyIso`, which runs the first
degeneration of `StacksFrontier/Algebra/Homology/TotalDegeneration.lean` and the second one from a
*rowwise comparison* rather than a rowwise vanishing; what remains are its four inputs, kept as
named hypotheses.  [Stacks, Tag 07LG] itself is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`, which supplies those inputs for the cosimplicial
pair `...SmallSite.crystalCosimplicialPair` of a crystal.

## The named hypotheses, and what each is

Neither hypothesis of [Stacks, Tag 07JN] on the coefficient sheaf is named: both are discharged
in `Computes07LGFrom07JN.lean` — local quasi-coherence by the half of [Stacks, Tag 07IT] the
library proves on the small site, and hypothesis (2) by
`...SmallSite.isSurjectiveComparison_of_isSheafCrystal` from the standing crystal hypothesis
`h07IT`.  What is named is:

* `K`, the bigraded family itself, as a cochain complex of cosimplicial abelian groups — the
  `a` direction already a complex, the `b` direction still cosimplicial, which is the shape
  `Crystalline.cosimplicialDoubleComplexFunctor` consumes.  The ingredients exist:
  `Crystalline.envelopeDPAlgebra` is the cosimplicial family of divided power algebras `D(*)`,
  `Crystalline.envelopeForms` the bigraded `Ω^a_{D(b)}` with
  `Crystalline.envelopeFormsMap_deRham` saying the two differentials commute, and
  `Crystalline.completedEnvelopeCodiagonal` the codiagonal `ε_b : D(b) → D`.

  **A warning, because the obvious reading of the codiagonal is wrong and was recorded here as
  settled.**  It is tempting to use `ε_b` to make `M` a `D(b)`-module uniformly in `b` and set
  `K^{a,b} = M ⊗̂_{D(b)} Ω^a_{D(b)}`.  That construction makes `hcolumn0` **false**, not merely
  hard.  In exterior degree `0` it gives `K^{0,b} = M ⊗̂_{D(b)} D(b) = M`, and the cosimplicial
  map for `φ : ⦋m⦌ ⟶ ⦋n⦌` is `m ⊗ ω ↦ m ⊗ D(φ) ω`, which in degree `0` is `m ↦ m · 1 = m`.  So
  the `a = 0` column is the *constant* cosimplicial group `M`, its Moore differential is
  `d⁰ - d¹ = 0`, and its homology is `M` in degree `0` and zero above — whereas `hcolumn0` asks
  for `H^j(Cris(X/S), F)`, which is nonzero in positive degrees in general and is
  `ker(M(0) → M(1))` rather than `M` in degree `0`.

  The source's `K^{a,b} = M ⊗^∧_D Ω^a_{D(b)}` tensors over `D`, with `Ω^a_{D(b)}` a `D`-module
  along a *coprojection*, so that `K^{0,b} = M ⊗̂_D D(b) = M(b)` — and that identity is exactly
  where the crystal property enters, which is why `hcolumn0` is stated as a consequence of
  `Crystalline.GlobalCrystallineSituation.SmallSite.IsCrystalLevelQuotient`.  A single
  coprojection does not give a cosimplicial object either, since
  `D(φ) ∘ coproj_j^{(m)} = coproj_{φ(j)}^{(n)}` and `φ(0) = 0` fails for `d⁰`.  The correct `K`
  therefore needs the geometric cosimplicial module `M(•)` carrying a connection over `D(•)` in
  each degree: `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`.  That is
  `Crystalline.CosimplicialCompletedPair.doubleComplex`, and for the coefficient sheaf
  `𝒪_{X/S}` a term of it exists — `Crystalline.envelopeStructureDoubleComplex`, built in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialStructurePair.lean` from
  the universal connection `∇ x = 1 ⊗ d x`.  For a general crystal it is the double complex of
  `...SmallSite.crystalCosimplicialPair` of `SmallSite/CrystalCosimplicialPair.lean`; this file
  keeps `K` as a variable.

  What the codiagonal *is* for is the row argument: [Stacks, Tag 07LG]'s proof uses it to see
  that the `b + 1` coprojections induce the same map on cohomology
  (`Crystalline.completedEnvelopeCodiagonal_coprojection` says `ε_b` is a retraction of each),
  with `Crystalline.completedEnvelopeCodiagonal_map` the cosimplicial compatibility
  `ε_n ∘ D(φ) = ε_m`.

* `hcolumns`, the acyclicity of the columns in positive degree.  This is
  [Stacks, Lemma 60.19.1, Tag 07LA], which is proved as
  `Crystalline.id_completedTensorCompletedForms_homotopic_zero`, **in a different shape**: its
  `Ω^i_{D(n)}` is the completion of the exterior power of the *completed* differentials
  `Crystalline.CosimplicialEnvelope.differentials`, while the forms of
  `Crystalline.envelopeForms` — and of the target complex of this tag, as
  `Crystalline.completedDividedPowerDeRhamComplex` builds it — are the completion of the exterior
  power of the *uncompleted* ones.

  The two are now identified **in each cosimplicial degree separately**, by
  `Crystalline.completedFormsShapeEquiv` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShape.lean`, and in
  exactly the exterior degrees [Stacks, Tag 07LA] speaks about, namely the positive ones:
  `AdicCompletion_B(⋀^i_B Ω) ≃+ AdicCompletion_{B̂}(⋀^i_{B̂} Ω̂)` for `i > 0`, pinned down on
  wedges by `Crystalline.completedFormsShapeEquiv_of_ιMulti`, and it is `B̂`-linear by
  `Crystalline.completedFormsShapeEquiv_smul` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShapeLinear.lean`, and
  natural in `B` by `Crystalline.completedFormsShapeEquiv_natural` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShapeNatural.lean`:
  it commutes with the maps a ring map of bases induces on the two shapes, in the semilinear
  shape of `Crystalline.adicCompletionMapₛₗ` that the transition maps `D(m) → D(n)` act in.

  **What still stops the hypothesis from being discharged is `K`, not the comparison.**
  `hcolumns` is a statement about the `K` this theorem also carries as a variable, so no
  instance of it is provable while `K` is free; and the `K` it would have to be about is
  `Crystalline.CosimplicialCompletedPair.doubleComplex`, which needs the per-degree connection
  on `M(•)` discussed under `K` above.  What is left on the comparison's own side is small and
  named, and it is now **proved**, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/ColumnAcyclicityInputs.lean`:
  `Crystalline.CosimplicialDPAlgebra.formsShapeMap` forms the `ExteriorAlgebra.powMapₛₗ` of the
  completed differentials that was outstanding on the completed side,
  `Crystalline.CosimplicialDPAlgebra.formsShapeEquiv_formsMap` is the comparison of the two
  shapes commuting with the cosimplicial transition maps, and
  `Crystalline.exteriorPowerFunctor_restrictₛₗ` identifies the transition map of a degreewise
  exterior power with `ExteriorAlgebra.powMapₛₗ` of the transition map, for every cosimplicial
  ring.  [Stacks, Tag 07LA] is instantiated at the cosimplicial module `M(•)` of an arbitrary
  `Crystalline.CosimplicialCompletedModule` as
  `Crystalline.homotopic_id_columnTargetModule_zero`.

  What remains between that and `hcolumns` is **not** mathematics: it is the degreewise
  identification of `Crystalline.CosimplicialCompletedModule.column` with
  `Crystalline.columnTargetModule`, and it is blocked on a spelling.  The two sides name the same
  ring by `Crystalline.CosimplicialDPAlgebra.completedRing` on one side and by
  `(Crystalline.cosimplicialEnvelopeRing s f hf).obj ⦋b⦌` on the other; the terms are
  definitionally equal, and Lean checks that cheaply for the rings and for the differentials, but
  **not inside an exterior power** — unifying `⋀[R]^a N` across the two spellings exhausts the
  heartbeat limit, because reconciling the two `Module` instances drives the unifier through the
  sealed `TensorAlgebra`/`CliffordAlgebra` quotients under `ExteriorAlgebra`.  So the transport
  has to be routed through `Crystalline.ExteriorPowerFunctor.componentIso`, with the change of
  spelling performed once, on the rings and the differentials only.  See the module documentation
  of `Cosimplicial/ColumnAcyclicityInputs.lean`.  The hypothesis is kept whole rather than
  split, because splitting it would need the double complex that `K` carries.

* `rowTarget`, `rowComparison` and `hrows`, the **rowwise comparison**.  This used to be the
  acyclicity of the rows in positive degree, which is **not** the completed clause of
  [Stacks, Lemma 60.21.2, Tag 07LD] and which for the crystalline `K` forces `p` to be invertible
  in `D̂(b)`, so that it could never be discharged.  The clause of [Stacks, Tag 07LD] says that
  `M ⊗^∧_D Ω^*_D → M ⊗^∧_D Ω^*_{D'}` is a quasi-isomorphism, so the source's rows `K^{*,b}` are
  each quasi-isomorphic to the row `K^{*,0} = M ⊗^∧_D Ω^*_D` and are *not* acyclic; its second
  spectral sequence degenerates because the `E_1` page is `H^a(M ⊗^∧_D Ω^*_D)` in every `b` with
  differentials `0, 1, 0, 1, …`, the codiagonal `ε_b : D(b) → D` retracting every coprojection.
  For a `K` built as `Crystalline.CosimplicialCompletedPair.doubleComplex`,
  `Crystalline.CosimplicialCompletedPair.acyclic_flip_X_of_ne_zero` reduced the old hypothesis to
  the acyclicity of `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` for `b > 0`, and
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamRowObstruction.lean`
  proves *that* unsatisfiable: `H⁰` of a completed de Rham complex contains the horizontal
  sections, and for the coefficient sheaf `𝒪_{X/S}` it would make `p` invertible in `D̂(b)`.

  So what is named now is the comparison the source actually uses: a cochain complex
  `rowTarget` of abelian groups — for the crystalline `K` it is `M ⊗^∧_D Ω^*_D` — a morphism
  `rowComparison : K ⟶ Const(rowTarget)` of cochain complexes of cosimplicial groups, which is
  what the codiagonal `Crystalline.completedEnvelopeCodiagonal` supplies by way of
  `Crystalline.CosimplicialDoubleComplex.constHom` (its cosimplicial compatibility being
  `Crystalline.completedEnvelopeCodiagonal_map`, `ε_n ∘ D(φ) = ε_m`), and `hrows`, the statement
  that each of the induced row maps is a **quasi-isomorphism**.  That is the completed clause of
  [Stacks, Tag 07LD], proved as clause 2 of `Crystalline.DividedPowerPolynomial.stacks07LD`
  (`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`); this file keeps it
  as the argument `hrows`, for an abstract cochain complex of cosimplicial groups.  `hrows` is
  stated for every `b : ℤ` because that is the index the flip of the double complex uses, but it
  has content only for `b ≥ 0`:
  `Crystalline.quasiIso_flipMap_cosimplicialDoubleComplexFunctor_map_of_neg` discharges the rest.

  The degeneration itself is no longer
  `StacksDraft.TotalDegeneration.totalHomologyIsoRowZero`, whose hypothesis *is* the rowwise
  vanishing, but
  `StacksDraft.TotalRowComparison.rowZeroHomologyIsoColumnZero_of_rowComparison` of
  `StacksFrontier/Algebra/Homology/TotalRowComparison.lean`, which runs it from
  `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map` ([Stacks, Tag 0133]).

* `hrow0` and `hcolumn0`, the identification of the two edges of the double complex with the two
  complexes being compared.  `hrow0` is the row `b = 0`, which is `M ⊗^∧_D Ω^*_D` because
  `Crystalline.zeroEnvelopeRingEquiv` is `D(0) ≅ D`.  For a `K` built from a pair the row `b = 0`
  is identified with `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` by
  `Crystalline.CosimplicialCompletedPair.rowZeroHomologyIso`, so what is left of `hrow0` is
  exactly that ring isomorphism carried through the completion, the forms and the completed
  tensor product.  `hcolumn0` is the column `a = 0`, which is
  `M(•)`: that is entry 6 in the list of missing inputs of `SmallSite/AffineCohomology.lean`, and
  it is the one place the crystal property enters, so `hcolumn0` is stated as a *consequence* of
  `...SmallSite.IsCrystalLevelQuotient` rather than unconditionally.

  For a `K` built as `Crystalline.CosimplicialCompletedPair.doubleComplex` the first half of
  `hcolumn0` is **proved**: the column `a = 0` of that `K` is the cosimplicial module `M(•)`, by
  `Crystalline.CosimplicialCompletedModule.columnZeroIso` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CosimplicialDeRhamColumnZero.lean`,
  whose one hypothesis is the `p`-adic completeness of each `M(b)`; what is left of `hcolumn0` is
  then the comparison of the Moore complex of `M(•)` with `...SmallSite.sectionsComplex`, where
  the crystal property is the whole content.

* `hker`, the kernel clause of the crystal property, named as the **inclusion**
  `ker(M(n)_{e+1} ⟶ M(n)_e) ⊆ p^{N+e} M(n)_{e+1}` and not as the equality.  The reverse inclusion
  is proved, for every sheaf of modules and with no hypothesis, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelExponentAnnihilation.lean`:
  `...SmallSite.levelMap_nsmul_pow_p_eq_zero`, because `p^{N+e}` annihilates the sections over the
  level `e` outright, that level being `D(n)/(p)^{N+e}`.  So what this theorem consumes is
  `...SmallSite.isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le` of that file.

  The companion surjectivity clause is **not** named either:
  `...SmallSite.isCrystalLevelQuotient_wholeSpaceSystem_of_ker` discharges it
  from local quasi-coherence and from hypothesis (2) of [Stacks, Tag 07JN], both of which are now
  proved — the latter from the crystal property, by
  `...SmallSite.isSurjectiveComparison_of_isSheafCrystal`.  So what is assumed of the crystal
  property here is exactly the half that separates [Stacks, Tag 07LG] from [Stacks, Lemma 60.19.3,
  Tag 07LF] — the source's own footnote at [Stacks, Tag 07LF] says that under the hypotheses of
  [Stacks, Tag 07JN] alone "we don't know that `M(n)_e = M(n)_{e+1}/p^e M(n)_{e+1}`.  If `ℱ` is a
  crystal then this does hold".  The exponent is `Crystalline.uniformLevel + e` and not `e`,
  because the levels of `...SmallSite.wholeSpaceSystem` are `D(n)/(p)^{N+e}`.

## What is proved

The two spectral sequences, and nothing else: `Crystalline.cosimplicialDoubleComplexFunctor`
builds the double complex from `K`, the column degeneration identifies the cohomology of its total
complex with the cohomology of its column `0`, the rowwise comparison with the constant
cosimplicial object on `rowTarget` identifies it with the cohomology of its row `0`, and composing
them is the comparison `hcomp` asked for.

**No tag attribute is placed**: the statement below is a reduction with named hypotheses.
[Stacks, Tag 07LG] is `...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`, proved through the cosimplicial pair
`...SmallSite.crystalCosimplicialPair` of a general crystal.

## Main result

* `...SmallSite.computes07LG_of_doubleComplex` — [Stacks, Tag 07LG] from the double complex and
  the hypotheses above.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
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

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from the double complex `K^{a,b}`, with its two
spectral sequences discharged.**

The comparison `hcomp` of `...SmallSite.computes07LG_of_sectionsComplexHomologyIso` is the
source's two spectral sequences; they are run here, by
`Crystalline.cosimplicialDoubleComplexRowComparisonHomologyIso`, and what is left are their
inputs: the double complex `K` itself, the acyclicity of its columns off `0`
([Stacks, Tag 07LA] in the shape of the uncompleted forms), the **rowwise comparison** of `K`
with the constant cosimplicial object on `rowTarget` together with the hypothesis that each of its
row maps is a quasi-isomorphism — the completed clause of [Stacks, Lemma 60.21.2, Tag 07LD] — the
identification of its two edges with the two complexes being compared, and — the only part of the
crystal property not already available — the kernel inclusion
`ker(M(n)_{e+1} → M(n)_e) ⊆ p^{N+e} M(n)_{e+1}`.  Only the inclusion is assumed: the reverse one
is `...SmallSite.levelMap_nsmul_pow_p_eq_zero`, proved for every sheaf of modules.

The rowwise hypothesis is *not* the acyclicity of the rows off `0`: that is what this theorem used
to carry, and `Cosimplicial/CosimplicialDeRhamRowObstruction.lean` proves it unsatisfiable.  See
the module documentation. -/
public theorem computes07LG_of_doubleComplex
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
      (b : ℤ), QuasiIso ((StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map (rowComparison F hF))).f b))
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
    Computes07LG S A Dr g Om der p dx wedge deRham hleib hp R h07IT hsq := by
  refine computes07LG_of_sectionsComplexHomologyIso S A Dr g Om der p dx wedge deRham hleib hp R
    h07IT hsq ?_
  intro F hF j
  have hcrys := isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le hp F
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF)
    (isSurjectiveComparison_of_isSheafCrystal (h07IT F hF)) (hker F hF)
  exact ⟨(hrow0 F hF j).some.trans
    ((cosimplicialDoubleComplexRowComparisonHomologyIso (K F hF) (rowTarget F hF)
        (rowComparison F hF) (hcolumns F hF) (hrows F hF) j).trans
      (hcolumn0 F hF hcrys j).some)⟩

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
