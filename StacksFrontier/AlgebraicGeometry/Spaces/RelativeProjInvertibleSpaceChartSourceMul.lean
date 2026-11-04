module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceRepresentedSpaceBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaMul

/-!
# The source factor of the chart maps of `θ` of Stacks 0D2Z is multiplicative and unital

Let `w : W ⟶ U(ψ)` be a scheme point of the open subspace `U(ψ)` of Stacks 0D2Z.  The chart map
`χ_w = σ_w ≫ m_w ≫ τ_w` of `θ` at `w` (`…InvertibleTwistingRestriction.chartMap`) has as source
factor `σ_w` the identification `w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a`
(`…InvertibleTwistingRestriction.chartSourceIso`): the comparison of Stacks 03LU for the two
factorisations `w ≫ r = c_w ≫ (W ×_Y P ⟶ P)`, the inverse image along `c_w` of the base change
identification of Stacks 084D (`…RelativeProjSituation.fibreToSpaceTwistModuleIso`) and
Stacks 03DX (2).  This file shows that `σ_w` carries the inverse image along `w` of the
multiplication and of the unit of the source `r^*𝒪(d)` of `θ`
(`…InvertibleTwistingRestriction.thetaSourceMul`, `…thetaSourceUnit`) to the morphisms attached
to the pullback along `c_w` of the multiplication and of the unit of the twists of Stacks 01NR on
`W ×_Y P`.  These are the hypotheses `hσ` of `AlgebraicGeometry.Space.mul_of_factor_squares` and
`AlgebraicGeometry.Space.one_of_factor_squares`.

## Main results

* `…InvertibleTwistingRestriction.compTransportFibreToSpace_hom_mul`,
  `…InvertibleTwistingRestriction.compTransportFibreToSpace_hom_one`: the statement at
  variables (any scheme point of the base, any section of the base change, any factorisation),
  with the identifications and the source multiplication given by their values.
* `…InvertibleTwistingRestriction.chartSourceIso_hom_mul`,
  `…InvertibleTwistingRestriction.chartSourceIso_hom_one`: **the source identification of the
  chart maps is multiplicative and unital**, the instance at `…chartSourceIso`.

## Implementation notes

Each factor is a variable and each value an equation, and the instance supplies the values by
`…InvertibleTwistingRestriction.chartSourceIso_eq_value`,
`…InvertibleTwistingRestriction.thetaSourceMul.eq_1` and `…thetaSourceUnit.eq_1`, each given as
`(e : _)` so that it is elaborated alone and then matched; the statements of the instances are the
types of their proofs.  At variables, the steps are
`AlgebraicGeometry.Space.compTransportTrans_hom_mul` and `…_hom_one` together with the
multiplicativity of Stacks 084D (`…fibreToSpaceTwistModuleIso_twistAlgebraMul`) and of
Stacks 03DX (2) (`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_mul`).
The represented algebraic space of the fibre is written in one spelling throughout (that of
`AlgebraicGeometry.Space.representedSpaceMap`); the base change identification is stated at the
spelling `AlgebraicGeometry.Space.representedAlgebraicSpace`, which is that one after unfolding a
reducible constant, and `CategoryTheory.yoneda` is locally irreducible so that the unifier unfolds
that constant rather than `yoneda` when it compares the two (about 80,000 heartbeats instead of
more than 500,000).

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

namespace RelativeProjSituation.InvertibleTwistingRestriction

section FibreToSpace

variable {s : RelativeProjSituation.{u, m}}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T : BigFppfOver s.site s.base s.containsBase} {v : yoneda.obj T ⟶ s.space.1}
  {Y : AlgebraicSpaces s.site s.base s.containsBase}
  {a : (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
    AlgebraicSpaces s.site s.base s.containsBase) ⟶ Y}
  {b : Y ⟶ ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩}
  {c : T ⟶ s.relativeProjPoints.fibre T v}
  {h : @CategoryStruct.comp (AlgebraicSpaces s.site s.base s.containsBase) _ _ _ _ a b =
    @CategoryStruct.comp (AlgebraicSpaces s.site s.base s.containsBase) _ _ _ _
      (representedSpaceMap s.site s.base s.containsBase c)
      (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
        isAlgebraicSpace_yoneda s.site s.base s.containsBase (s.relativeProjPoints.fibre T v)⟩ :
          AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)}

attribute [local irreducible] CategoryTheory.yoneda

/-- **The source identification `a^*b^*𝒪(n) ≅ (c^*𝒪(n))^a` through the base change
identification of Stacks 084D is multiplicative**, at variables: for a scheme point
`v : T ⟶ Y` of the base, a section `c : T ⟶ T ×_Y P` of the base change, morphisms
`a : T ⟶ Y'`, `b : Y' ⟶ P = Proj_Y(𝒜)` of algebraic spaces with `a ≫ b = c ≫ (T ×_Y P ⟶ P)`,
identifications `σ_n` given by their value (the comparison of Stacks 03LU, written out as its
three factors, the inverse image along `c` of
`…RelativeProjSituation.fibreToSpaceTwistModuleIso` and Stacks 03DX (2)), and a morphism `x`
given by its value `b^*𝒪(i) ⊗ b^*𝒪(j) ≅ b^*(𝒪(i) ⊗ 𝒪(j)) ⟶ b^*𝒪(i + j)` (Stacks 03EL and the
multiplication of the twists), the inverse image of `x` along `a`, read through Stacks 03EL, is
carried by `σ` to the morphism attached to the pullback along `c` of the multiplication of the
twists of Stacks 01NR on `T ×_Y P`.

Every represented algebraic space is written `⟨yoneda.obj _, isAlgebraicSpace_yoneda _ _ _ _⟩`
(the spelling of `…InvertibleTwistingRestriction.chartSourceIso_eq_value`), and the factorisation
`h` is stated in the category `AlgebraicGeometry.AlgebraicSpaces` itself. -/
theorem compTransportFibreToSpace_hom_mul (i j : ℤ)
    {σ : ∀ n : ℤ, (modulePullback s.site s.base s.containsBase a).obj
      ((modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px n).obj) ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase T).functor.obj
        (quasicoherentPullbackObj s.site s.base s.containsBase c (s.twistPieceQcoh T v n))).obj}
    (hσ : ∀ n : ℤ, σ n =
      ((((modulePullbackCompIso s.site s.base s.containsBase a b).app (s.twistModule Px n).obj ≪≫
          (eqToIso (congrArg (fun k : (⟨yoneda.obj T,
                isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
                  AlgebraicSpaces s.site s.base s.containsBase) ⟶
                ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
              (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px n).obj)
                h) : _) ≪≫
          ((modulePullbackCompIso s.site s.base s.containsBase
            (representedSpaceMap s.site s.base s.containsBase c)
            (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
                isAlgebraicSpace_yoneda s.site s.base s.containsBase
                  (s.relativeProjPoints.fibre T v)⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).app
              (s.twistModule Px n).obj).symm) :
          (modulePullback s.site s.base s.containsBase a).obj
              ((modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px n).obj) ≅
            (modulePullback s.site s.base s.containsBase
              (representedSpaceMap s.site s.base s.containsBase c)).obj
              ((modulePullback s.site s.base s.containsBase
                (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
                    isAlgebraicSpace_yoneda s.site s.base s.containsBase
                      (s.relativeProjPoints.fibre T v)⟩ :
                    AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).obj
                (s.twistModule Px n).obj)) ≪≫
        (modulePullback s.site s.base s.containsBase
          (representedSpaceMap s.site s.base s.containsBase c)).mapIso
          (s.fibreToSpaceTwistModuleIso Px T v n) ≪≫
        modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase c
          (s.twistPieceQcoh T v n)))
    {x : (modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px i).obj ⊗
        (modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px j).obj ⟶
      (modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px (i + j)).obj}
    (hx : x = (modulePullbackTensorIso s.site s.base s.containsBase b (s.twistModule Px i).obj
        (s.twistModule Px j).obj).inv ≫
      (modulePullback s.site s.base s.containsBase b).map (s.twistAlgebraMul Px i j)) :
    ((modulePullbackTensorIso s.site s.base s.containsBase a
        ((modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px i).obj)
        ((modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px j).obj)).inv ≫
      (modulePullback s.site s.base s.containsBase a).map x) ≫ (σ (i + j)).hom =
    ((σ i).hom ⊗ₘ (σ j).hom) ≫ representedTensorChartMul s.site s.base s.containsBase
      ((quasicoherentPullbackTensorIso s.site s.base s.containsBase c (s.twistPieceQcoh T v i)
          (s.twistPieceQcoh T v j)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase c (s.twistPieceMul T v i j)) := by
  subst hx
  exact compTransportTrans_hom_mul a b (representedSpaceMap s.site s.base s.containsBase c)
    (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase (s.relativeProjPoints.fibre T v)⟩ :
        AlgebraicSpaces s.site s.base s.containsBase) ⟶ _) h
    (hσ i : _) (hσ j : _) (hσ (i + j) : _)
    (s.fibreToSpaceTwistModuleIso_twistAlgebraMul Px T v i j : _)
    (modulePullbackRepresentedQuasicoherentIso_hom_mul_assoc c (s.twistPieceMul T v i j) : _)

/-- The unit companion of `…InvertibleTwistingRestriction.compTransportFibreToSpace_hom_mul`:
the inverse image along `a` of `x = (𝒪 ≅ b^*𝒪 ⟶ b^*𝒪(0))` (Stacks 03LU and the unit of the
twists), read through Stacks 03LU, is carried by `σ` to the morphism attached to the pullback
along `c` of the unit of the twists of Stacks 01NR on `T ×_Y P`; at variables. -/
theorem compTransportFibreToSpace_hom_one
    {σ : (modulePullback s.site s.base s.containsBase a).obj
      ((modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px 0).obj) ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase T).functor.obj
        (quasicoherentPullbackObj s.site s.base s.containsBase c (s.twistPieceQcoh T v 0))).obj}
    (hσ : σ =
      ((((modulePullbackCompIso s.site s.base s.containsBase a b).app (s.twistModule Px 0).obj ≪≫
          (eqToIso (congrArg (fun k : (⟨yoneda.obj T,
                isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
                  AlgebraicSpaces s.site s.base s.containsBase) ⟶
                ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
              (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px 0).obj)
                h) : _) ≪≫
          ((modulePullbackCompIso s.site s.base s.containsBase
            (representedSpaceMap s.site s.base s.containsBase c)
            (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
                isAlgebraicSpace_yoneda s.site s.base s.containsBase
                  (s.relativeProjPoints.fibre T v)⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).app
              (s.twistModule Px 0).obj).symm) :
          (modulePullback s.site s.base s.containsBase a).obj
              ((modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px 0).obj) ≅
            (modulePullback s.site s.base s.containsBase
              (representedSpaceMap s.site s.base s.containsBase c)).obj
              ((modulePullback s.site s.base s.containsBase
                (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
                    isAlgebraicSpace_yoneda s.site s.base s.containsBase
                      (s.relativeProjPoints.fibre T v)⟩ :
                    AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).obj
                (s.twistModule Px 0).obj)) ≪≫
        (modulePullback s.site s.base s.containsBase
          (representedSpaceMap s.site s.base s.containsBase c)).mapIso
          (s.fibreToSpaceTwistModuleIso Px T v 0) ≪≫
        modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase c
          (s.twistPieceQcoh T v 0)))
    {x : SheafOfModules.unit (structureRingSheaf s.site s.base s.containsBase Y) ⟶
      (modulePullback s.site s.base s.containsBase b).obj (s.twistModule Px 0).obj}
    (hx : x = (modulePullbackUnitIso s.site s.base s.containsBase b).inv ≫
      (modulePullback s.site s.base s.containsBase b).map (s.twistAlgebraUnit Px)) :
    ((modulePullbackUnitIso s.site s.base s.containsBase a).inv ≫
      (modulePullback s.site s.base s.containsBase a).map x) ≫ σ.hom =
    representedUnitChartHom s.site s.base s.containsBase
      ((quasicoherentPullbackUnitIso s.site s.base s.containsBase c).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase c (s.twistPieceUnit T v)) := by
  subst hx
  exact compTransportTrans_hom_one a b (representedSpaceMap s.site s.base s.containsBase c)
    (s.fibreToSpaceHom T v : (⟨yoneda.obj (s.relativeProjPoints.fibre T v),
      isAlgebraicSpace_yoneda s.site s.base s.containsBase (s.relativeProjPoints.fibre T v)⟩ :
        AlgebraicSpaces s.site s.base s.containsBase) ⟶ _) h (hσ : _)
    (s.fibreToSpaceTwistModuleIso_twistAlgebraUnit Px T v : _)
    (modulePullbackRepresentedQuasicoherentIso_hom_one_assoc c (s.twistPieceUnit T v) : _)

end FibreToSpace

section ChartSource

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)

/-- **The identification of the source of the chart map is multiplicative** (Stacks 084D and
0D2Z): at a scheme point `w : W ⟶ U(ψ)`, the identification `w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a`
(`…InvertibleTwistingRestriction.chartSourceIso`) carries the inverse image along `w` of the
multiplication of the source of `θ` (`…InvertibleTwistingRestriction.thetaSourceMul`), read
through Stacks 03EL, to the morphism attached (Stacks 03DX (2)) to the pullback along the section
`c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of the multiplication of the twists of Stacks 01NR on
`W ×_Y Proj_Y(𝒜)`.  This is the hypothesis `hσ` of `AlgebraicGeometry.Space.mul_of_factor_squares`
for the source factor of a chart map, in the site `s.site` on which `…chartSourceIso` is defined.

The statement is the instance of
`…InvertibleTwistingRestriction.compTransportFibreToSpace_hom_mul` at `σ = chartSourceIso`, its
value supplied by `…InvertibleTwistingRestriction.chartSourceIso_eq_value` and the multiplication
by `…InvertibleTwistingRestriction.thetaSourceMul.eq_1`. -/
theorem chartSourceIso_hom_mul (i j : ℤ) :
    type_of% (compTransportFibreToSpace_hom_mul Px i j
      (h := (pointHom_comp_invertibleSpaceMorphism w : _))
      (σ := fun n => chartSourceIso Px w (locusOpen_locusPoint w) n)
      (fun n => (chartSourceIso_eq_value Px w n : _))
      (thetaSourceMul.eq_1 (ofUnitalHom s f L ψ) X.property Px i j : _)) :=
  compTransportFibreToSpace_hom_mul Px i j
    (h := (pointHom_comp_invertibleSpaceMorphism w : _))
    (σ := fun n => chartSourceIso Px w (locusOpen_locusPoint w) n)
    (fun n => (chartSourceIso_eq_value Px w n : _))
    (thetaSourceMul.eq_1 (ofUnitalHom s f L ψ) X.property Px i j : _)

/-- `…InvertibleTwistingRestriction.chartSourceIso_hom_one` over the site `s.site` of the
source identification (the unit companion of `…chartSourceIso_hom_mul`). -/
theorem chartSourceIso_hom_one :
    type_of% (compTransportFibreToSpace_hom_one Px
      (h := (pointHom_comp_invertibleSpaceMorphism w : _)) (chartSourceIso_eq_value Px w 0 : _)
      (thetaSourceUnit.eq_1 (ofUnitalHom s f L ψ) X.property Px : _)) :=
  compTransportFibreToSpace_hom_one Px
      (h := (pointHom_comp_invertibleSpaceMorphism w : _)) (chartSourceIso_eq_value Px w 0 : _)
    (thetaSourceUnit.eq_1 (ofUnitalHom s f L ψ) X.property Px : _)

end ChartSource

end RelativeProjSituation.InvertibleTwistingRestriction

end AlgebraicGeometry.Space

end
