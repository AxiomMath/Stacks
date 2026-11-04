module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPsiCompat
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGradedMulPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiMultiplicativeScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistGradedAlgebra

/-!
# The graded algebra of twists of a relative Proj, `ψ`, and their base change (Stacks 084D)

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084B.
Stacks 084D equips `P` with a quasi-coherent sheaf of `ℤ`-graded `𝒪_P`-algebras
`⨁_{n ∈ ℤ} 𝒪_P(n)` and a homomorphism of graded algebras `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` whose
base change to any scheme `T` over `X` is the graded algebra of twists and the homomorphism `ψ` of
Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`.

This file collects the whole statement on `P` itself, for any presentation `X = U/R` used to
construct the twists:

* the graded algebra is `AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra`, with
  quasi-coherent homogeneous pieces `𝒪_P(n)`, multiplication
  `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul` and unit
  `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraUnit`;
* `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` is `AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`, and it
  carries the multiplication and the unit of `π^*𝒜`
  (`AlgebraicGeometry.Space.RelativeProjSituation.psiSourceMul`, `…psiSourceUnit`) to those of the
  twists;
* for every scheme point `f : T ⟶ X` the identifications
  `(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` of
  `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso` carry the inverse
  images of the multiplication, of the unit and of `ψ` to the multiplication, the unit and `ψ` of
  Stacks 01NR on `T ×_X P`, and are natural in the scheme point.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_eq_twistModule` and
  `…pullbackTransitionCompatibleIso_spec_twistModule`: the base change identification and its
  description on the étale cover, with the twist spelled as
  `AlgebraicGeometry.Space.RelativeProjSituation.twistModule`.
* `…RelativeProjSituation.modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso`: the base
  change identification carries `ψ` to `ψ` of Stacks 01NR.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra_psi_baseChange_of_compat`:
  the full statement of Stacks 084D on `P`, given that `ψ` of Stacks 01NR on the scheme of
  `U ×_X P` is multiplicative and unital.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra_psi_baseChange`:
  **Stacks 084D** on `P`, unconditionally.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

section Point

variable (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **The base change identification, with the twist `𝒪_P(n)` spelled as
`…RelativeProjSituation.twistModule`**: `…RelativeProjSituation.fibreToSpaceTwistModuleIso` is the
identification of Stacks 03M3 along `T ×_X P ⟶ P` of the twist `…RelativeProjSituation.twistModule`
with its chart identification `…RelativeProjSituation.twistModuleChartIso` (the spelling of
`…RelativeProjSituation.exists_fibreToSpace_twistModule_iso`). -/
theorem fibreToSpaceTwistModuleIso_eq_twistModule (n : ℤ) :
    s.fibreToSpaceTwistModuleIso Px T f n =
      RelativeProjPoints.pullbackTransitionCompatibleIso
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.twistModule Px n) (s.twistTransition Px n) (s.twistModuleChartIso Px n)
      (s.twistModuleChartIso_comm_spaceBaseDescent Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (Px.alongPointRelationMap f) (Px.alongPointRelationMap_comp_target f)
        (Px.alongPointRelationMap_comp_source f) n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n) :=
  rfl

/-- **The description of the base change identification on the étale cover, with the twist
`𝒪_P(n)` spelled as `…RelativeProjSituation.twistModule`**: the inverse image along the atlas of
`T ×_X P` of the identification, followed by the identification of the twist of Stacks 01NR there,
is the composite of the comparisons of twists of Tag 01O3 (the right side of
`…RelativeProjSituation.fibreToSpaceTwistModuleIso_eq_twistModule`). -/
theorem pullbackTransitionCompatibleIso_spec_twistModule (n : ℤ) :
    type_of% (RelativeProjPoints.pullbackTransitionCompatibleIso_spec
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.twistModule Px n) (s.twistTransition Px n) (s.twistModuleChartIso Px n)
      (s.twistModuleChartIso_comm_spaceBaseDescent Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (Px.alongPointRelationMap f) (Px.alongPointRelationMap_comp_target f)
        (Px.alongPointRelationMap_comp_source f) n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)) :=
  RelativeProjPoints.pullbackTransitionCompatibleIso_spec
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.twistModule Px n) (s.twistTransition Px n) (s.twistModuleChartIso Px n)
      (s.twistModuleChartIso_comm_spaceBaseDescent Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (Px.alongPointRelationMap f) (Px.alongPointRelationMap_comp_target f)
        (Px.alongPointRelationMap_comp_source f) n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)

/-- **The base change identification carries `ψ` to `ψ` of Stacks 01NR**: for a scheme point
`f : T ⟶ X` and `n ≥ 0`, the inverse image along `T ×_X P ⟶ P` of `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)`,
followed by the identification `(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` of
`…RelativeProjSituation.fibreToSpaceTwistModuleIso`, is `ψ` of Tag 01NR on
`T ×_X P = Proj_T(f^*𝒜)`, read through the identification of the sources
(`…RelativeProjSituation.fibrePsiHom`). -/
theorem modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso (n : ℕ) :
    (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
        (s.psiTwistHom Px n) ≫ (s.fibreToSpaceTwistModuleIso Px T f (n : ℤ)).hom =
      s.fibrePsiHom T f n :=
  by
  rw [s.fibreToSpaceTwistModuleIso_eq_twistModule Px T f (n : ℤ)]
  exact s.modulePullback_map_psiTwistHom_comp_eq_fibrePsiHom Px T f n _
    (s.pullbackTransitionCompatibleIso_spec_twistModule Px T f (n : ℤ))

end Point

/-- **Stacks 084D on the relative Proj `P = Proj_X(𝒜)`, given that `ψ` of Tag 01NR on the chart is
multiplicative and unital.**  For any presentation `X = U/R`:

1. `⨁_{n ∈ ℤ} 𝒪_P(n)` (`…RelativeProjSituation.twistGradedAlgebra`) is a sheaf of `ℤ`-graded
   `𝒪_P`-algebras with quasi-coherent homogeneous pieces `𝒪_P(n)`, whose multiplication and unit
   are `…RelativeProjSituation.twistAlgebraMul` and `…RelativeProjSituation.twistAlgebraUnit`;
2. `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)`, `n ≥ 0` (`…RelativeProjSituation.psiTwistHom`), is a homomorphism of
   graded algebras: it carries the multiplication and the unit of `π^*𝒜`
   (`…RelativeProjSituation.psiSourceMul`, `…RelativeProjSituation.psiSourceUnit`) to those of the
   twists;
3. there are isomorphisms `e_{T,f,n} : (T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a`, for every scheme point
   `f : T ⟶ X`, with the twists of Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`, carrying the inverse
   images of the multiplication, of the unit and of `ψ` to the multiplication, the unit and `ψ` of
   Stacks 01NR, and compatible with further base change along any `τ : T' ⟶ T` (through the
   comparison of twists of Tag 01O3).

The inputs are that `ψ` of Stacks 01NR on the scheme of `U ×_X P` is multiplicative and unital
(`…RelativeProjSituation.PsiChartSchemeMulCompat`,
`…RelativeProjSituation.PsiChartSchemeUnitCompat`). -/
theorem twistGradedAlgebra_psi_baseChange_of_compat
    (hBmul : ∀ i j : ℕ, s.PsiChartSchemeMulCompat Px i j)
    (hBunit : s.PsiChartSchemeUnitCompat Px) :
    -- (1) the quasi-coherent sheaf of `ℤ`-graded algebras `⨁_{n ∈ ℤ} 𝒪_P(n)`
    (∀ n : ℤ, (s.twistGradedAlgebra Px).piece n = (s.twistModule Px n).obj) ∧
    (∀ n : ℤ, ((s.twistGradedAlgebra Px).piece n).IsQuasicoherentOnSite) ∧
    (∀ i j : ℤ,
      haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
        AddCommGrpCat.{u}
      haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
        s.relativeProjFunctor AddCommGrpCat.{u}
      SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u}
          (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
          (s.twistGradedAlgebra Px) i j =
        (modulesTensorObjIso s.site s.base s.containsBase s.relativeProjFunctor
            s.isAlgebraicSpace_relativeProjFunctor (s.twistModule Px i).obj
            (s.twistModule Px j).obj).inv ≫ s.twistAlgebraMul Px i j) ∧
    (haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
        AddCommGrpCat.{u}
     haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
        s.relativeProjFunctor AddCommGrpCat.{u}
     SheafOfModules.GradedAlgebra.oneHom.{u, u + 1, u}
          (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
          (s.twistGradedAlgebra Px) = s.twistAlgebraUnit Px) ∧
    -- (2) `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` is a homomorphism of graded algebras
    (∀ i j : ℕ, s.psiSourceMul (i : ℤ) (j : ℤ) ≫ s.psiTwistHom Px (i + j) =
      (s.psiTwistHom Px i ⊗ₘ s.psiTwistHom Px j) ≫ s.twistAlgebraMul Px (i : ℤ) (j : ℤ)) ∧
    s.psiSourceUnit ≫ s.psiTwistHom Px 0 = s.twistAlgebraUnit Px ∧
    -- (3) the base change to every scheme point is the graded algebra and `ψ` of Stacks 01NR
    ∃ e : ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) (n : ℤ),
        (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
          (s.twistModule Px n).obj ≅
          ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
            (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f n)).obj,
      (∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)
        (i j : ℤ),
        (modulePullbackTensorIso s.site s.base s.containsBase (s.fibreToSpaceHom T f)
            (s.twistModule Px i).obj (s.twistModule Px j).obj).inv ≫
          (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
            (s.twistAlgebraMul Px i j) ≫ (e T f (i + j)).hom =
        ((e T f i).hom ⊗ₘ (e T f j).hom) ≫
          representedTensorChartMul s.site s.base s.containsBase (s.twistPieceMul T f i j)) ∧
      (∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1),
        (modulePullbackUnitIso s.site s.base s.containsBase (s.fibreToSpaceHom T f)).inv ≫
            (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
              (s.twistAlgebraUnit Px) ≫ (e T f 0).hom =
          representedUnitChartHom s.site s.base s.containsBase (s.twistPieceUnit T f)) ∧
      (∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) (n : ℕ),
        (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
            (s.psiTwistHom Px n) ≫ (e T f (n : ℤ)).hom = s.fibrePsiHom T f n) ∧
      ∀ {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
        (f : yoneda.obj T ⟶ s.space.1)
        {y : s.relativeProjPoints.fibre T' (yoneda.map τ ≫ f) ⟶ s.relativeProjPoints.fibre T f}
        (hy : s.relativeProjPoints.LiesOver y τ) (n : ℤ),
        e T' (yoneda.map τ ≫ f) n =
          eqToIso (congrArg (fun k :
              (⟨yoneda.obj (s.relativeProjPoints.fibre T' (yoneda.map τ ≫ f)),
                isAlgebraicSpace_yoneda s.site s.base s.containsBase _⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶
                  ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
              (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px n).obj)
              (s.representedSpaceMap_comp_fibreToSpaceHom τ f hy).symm) ≪≫
            attachedModuleIsoPullback
              (X := ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩)
              (s.twistModule Px n).obj (s.fibreToSpaceHom T f) y
              (e T f n) (s.twistPieceComparison τ rfl y hy n) :=
  ⟨s.twistGradedAlgebra_piece Px, s.isQuasicoherentOnSite_twistGradedAlgebra_piece Px,
    s.mulSheaf_twistGradedAlgebra Px, s.oneHom_twistGradedAlgebra Px,
    fun i j => s.psiSourceMul_comp_psiTwistHom_of_psiChartSchemeMulCompat Px i j (hBmul i j),
    s.psiSourceUnit_comp_psiTwistHom_of_psiChartSchemeUnitCompat Px hBunit,
    ⟨fun T f => s.fibreToSpaceTwistModuleIso Px T f,
      fun T f => s.fibreToSpaceTwistModuleIso_twistAlgebraMul Px T f,
      fun T f => s.fibreToSpaceTwistModuleIso_twistAlgebraUnit Px T f,
      fun T f => s.modulePullback_map_psiTwistHom_comp_fibreToSpaceTwistModuleIso Px T f,
      fun τ f _ hy n => s.fibreToSpaceTwistModuleIso_comp Px τ f hy n⟩⟩

/-- **Stacks 084D on the relative Proj `P = Proj_X(𝒜)` of Situation 0849.**  For any presentation
`X = U/R` used to construct the twists:

1. `⨁_{n ∈ ℤ} 𝒪_P(n)` (`…RelativeProjSituation.twistGradedAlgebra`) is a quasi-coherent sheaf of
   `ℤ`-graded `𝒪_P`-algebras: its homogeneous pieces are the twists `𝒪_P(n)`, quasi-coherent, and
   its multiplication and unit are `…RelativeProjSituation.twistAlgebraMul` and
   `…RelativeProjSituation.twistAlgebraUnit`;
2. the canonical `ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)`, `n ≥ 0` (`…RelativeProjSituation.psiTwistHom`), is a
   homomorphism of graded algebras `π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)`: it carries the multiplication and
   the unit of `π^*𝒜` (`…RelativeProjSituation.psiSourceMul`,
   `…RelativeProjSituation.psiSourceUnit`) to those of the twists;
3. its base change to any scheme `f : T ⟶ X` over `X` agrees with Stacks 01NR: there are
   isomorphisms `e_{T,f,n} : (T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` with the twists of Stacks 01NR on
   `T ×_X P = Proj_T(f^*𝒜)`, carrying the inverse images of the multiplication, of the unit and of
   `ψ` to the multiplication, the unit and `ψ` of Stacks 01NR, and compatible with further base
   change along any `τ : T' ⟶ T` (through the comparison of twists of Tag 01O3). -/
@[stacks 084D "on the constructed relative Proj P = Proj_X(A) itself: the quasi-coherent sheaf of \
Z-graded O_P-algebras (+)_n O_P(n) (twistGradedAlgebra: pieces, quasi-coherence, multiplication, \
unit), the canonical psi : pi^*A -> (+)_{n >= 0} O_P(n) as a homomorphism of graded algebras \
(multiplicative and unital), and for every scheme T -> X identifications of the base change with \
the graded algebra of Tag 01NR on Proj_T(f^*A) carrying multiplication, unit and psi to those of \
Tag 01NR, natural in the scheme"]
theorem twistGradedAlgebra_psi_baseChange :
    -- (1) the quasi-coherent sheaf of `ℤ`-graded algebras `⨁_{n ∈ ℤ} 𝒪_P(n)`
    (∀ n : ℤ, (s.twistGradedAlgebra Px).piece n = (s.twistModule Px n).obj) ∧
    (∀ n : ℤ, ((s.twistGradedAlgebra Px).piece n).IsQuasicoherentOnSite) ∧
    (∀ i j : ℤ,
      haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
        AddCommGrpCat.{u}
      haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
        s.relativeProjFunctor AddCommGrpCat.{u}
      SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u}
          (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
          (s.twistGradedAlgebra Px) i j =
        (modulesTensorObjIso s.site s.base s.containsBase s.relativeProjFunctor
            s.isAlgebraicSpace_relativeProjFunctor (s.twistModule Px i).obj
            (s.twistModule Px j).obj).inv ≫ s.twistAlgebraMul Px i j) ∧
    (haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
        AddCommGrpCat.{u}
     haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
        s.relativeProjFunctor AddCommGrpCat.{u}
     SheafOfModules.GradedAlgebra.oneHom.{u, u + 1, u}
          (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
          (s.twistGradedAlgebra Px) = s.twistAlgebraUnit Px) ∧
    -- (2) `ψ : π^*𝒜 ⟶ ⨁_{n ≥ 0} 𝒪_P(n)` is a homomorphism of graded algebras
    (∀ i j : ℕ, s.psiSourceMul (i : ℤ) (j : ℤ) ≫ s.psiTwistHom Px (i + j) =
      (s.psiTwistHom Px i ⊗ₘ s.psiTwistHom Px j) ≫ s.twistAlgebraMul Px (i : ℤ) (j : ℤ)) ∧
    s.psiSourceUnit ≫ s.psiTwistHom Px 0 = s.twistAlgebraUnit Px ∧
    -- (3) the base change to every scheme point is the graded algebra and `ψ` of Stacks 01NR
    ∃ e : ∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) (n : ℤ),
        (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
          (s.twistModule Px n).obj ≅
          ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
            (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f n)).obj,
      (∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)
        (i j : ℤ),
        (modulePullbackTensorIso s.site s.base s.containsBase (s.fibreToSpaceHom T f)
            (s.twistModule Px i).obj (s.twistModule Px j).obj).inv ≫
          (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
            (s.twistAlgebraMul Px i j) ≫ (e T f (i + j)).hom =
        ((e T f i).hom ⊗ₘ (e T f j).hom) ≫
          representedTensorChartMul s.site s.base s.containsBase (s.twistPieceMul T f i j)) ∧
      (∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1),
        (modulePullbackUnitIso s.site s.base s.containsBase (s.fibreToSpaceHom T f)).inv ≫
            (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
              (s.twistAlgebraUnit Px) ≫ (e T f 0).hom =
          representedUnitChartHom s.site s.base s.containsBase (s.twistPieceUnit T f)) ∧
      (∀ (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) (n : ℕ),
        (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).map
            (s.psiTwistHom Px n) ≫ (e T f (n : ℤ)).hom = s.fibrePsiHom T f n) ∧
      ∀ {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
        (f : yoneda.obj T ⟶ s.space.1)
        {y : s.relativeProjPoints.fibre T' (yoneda.map τ ≫ f) ⟶ s.relativeProjPoints.fibre T f}
        (hy : s.relativeProjPoints.LiesOver y τ) (n : ℤ),
        e T' (yoneda.map τ ≫ f) n =
          eqToIso (congrArg (fun k :
              (⟨yoneda.obj (s.relativeProjPoints.fibre T' (yoneda.map τ ≫ f)),
                isAlgebraicSpace_yoneda s.site s.base s.containsBase _⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶
                  ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
              (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px n).obj)
              (s.representedSpaceMap_comp_fibreToSpaceHom τ f hy).symm) ≪≫
            attachedModuleIsoPullback
              (X := ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩)
              (s.twistModule Px n).obj (s.fibreToSpaceHom T f) y
              (e T f n) (s.twistPieceComparison τ rfl y hy n) :=
  s.twistGradedAlgebra_psi_baseChange_of_compat Px (s.psiChartSchemeMulCompat Px)
    (s.psiChartSchemeUnitCompat Px)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
