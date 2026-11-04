module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeThetaGraded

/-!
# The isomorphism `θ` of Stacks 085C of graded algebras

In Situation 0849 let `g : X' ⟶ X` be a morphism of algebraic spaces, `P = Proj_X(𝒜)` and
`P' = Proj_{X'}(g^*𝒜)` the two relative Projs of Stacks 084B, and `h : P' ⟶ P` the morphism of
Stacks 085C, so that `h = pr_2 ∘ r` for the isomorphism `r : P' ≅ X' ×_X P`
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeIso_hom_snd`).  This file
constructs the second isomorphism of Stacks 085C,

`θ : r^* pr_2^* (⨁_{d ∈ ℤ} 𝒪_P(d)) ≅ ⨁_{d ∈ ℤ} 𝒪_{P'}(d)`,

as an isomorphism of sheaves of `ℤ`-graded `𝒪_{P'}`-algebras
(`AlgebraicGeometry.Space.ModulePullbackGradedAlgebraIso`), for the sheaves of graded algebras of
twists of Stacks 084D (`AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra`).  In
every degree `θ` is `θ_d` of
`AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistModuleIso`,
descended from the comparisons of twists of Tag 01O3 on the presenting schemes, as in the
source's hint; these comparisons are multiplicative and unital, so `θ` is one of graded algebras.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongGradedAlgebraIso`: the inverse image
  of a descended sheaf of graded algebras along a morphism of relative Projs is the descended
  sheaf of graded algebras of the pulled-back chart data.
* `AlgebraicGeometry.Space.Presentation.ofAtlas`: the presentation of an algebraic space by a
  surjective étale atlas and its kernel pair.
* `AlgebraicGeometry.Space.Presentation.comap`: the presentation `X' = U'/R'` with
  `U' = U'₀ ×_X U`, compatible with a presentation `X = U/R` along `g`.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistGradedAlgebraIso`: `θ` for
  presentations of `X` and `X'` compatible with `g`.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistGradedAlgebraIsoOfPresentation`:
  **Stacks 085C, `θ` as an isomorphism of `ℤ`-graded algebras, for any presentations of `X` and
  of `X'`.**

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

namespace RelativeProjPoints

section GradedPullbackAlong

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {XA XA' : AlgebraicSpaces B S hS} {PA PA' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {πA : PA ⟶ XA.obj} {πA' : PA' ⟶ XA'.obj} {dA : RelativeProjPoints B S hS πA}
  {dA' : RelativeProjPoints B S hS πA'} {hA : PA' ⟶ PA}
  (Px : Presentation B S hS XA.obj XA.property)
  (Px' : Presentation B S hS XA'.obj XA'.property) (hP : IsAlgebraicSpace B S hS PA)
  (hP' : IsAlgebraicSpace B S hS PA') {ℓ : Px'.U ⟶ Px.U} {ℓR : Px'.R ⟶ Px.R}
  (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ) (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ)
  (yU : dA'.fibre Px'.U Px'.toSpace ⟶ dA.fibre Px.U Px.toSpace)
  (hyU : dA'.LiesOverAlong dA hA yU ℓ)
  (yR : dA'.fibre Px'.R (relationPoint Px') ⟶ dA.fibre Px.R (relationPoint Px))
  (hyR : dA'.LiesOverAlong dA hA yR ℓR)
  {Mn : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : ∀ n, quasicoherentPullbackObj B S hS (dA.spaceTarget Px hP) (Mn n) ⟶
    quasicoherentPullbackObj B S hS (dA.spaceSource Px hP) (Mn n))
  (hc : ∀ n, PresentationSchemeCocycle (dA.spacePresentation Px hP) (Mn n) (τ n))
  (hu : ∀ n, PresentationSchemeUnit (dA.spacePresentation Px hP) (Mn n) (τ n))
  (m : ∀ i j, quasicoherentTensorObj B S hS (dA.fibre Px.U Px.toSpace) (Mn i) (Mn j) ⟶
    Mn (i + j))
  (ν : quasicoherentUnitObj B S hS (dA.fibre Px.U Px.toSpace) ⟶ Mn 0)
  {Mn'' : ℤ → (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA'.fibre Px'.U Px'.toSpace)).ringCatSheaf).FullSubcategory}
  (τ'' : ∀ n, quasicoherentPullbackObj B S hS (dA'.spaceTarget Px' hP') (Mn'' n) ⟶
    quasicoherentPullbackObj B S hS (dA'.spaceSource Px' hP') (Mn'' n))
  (hc'' : ∀ n, PresentationSchemeCocycle (dA'.spacePresentation Px' hP') (Mn'' n) (τ'' n))
  (hu'' : ∀ n, PresentationSchemeUnit (dA'.spacePresentation Px' hP') (Mn'' n) (τ'' n))
  (m'' : ∀ i j, quasicoherentTensorObj B S hS (dA'.fibre Px'.U Px'.toSpace) (Mn'' i) (Mn'' j) ⟶
    Mn'' (i + j))
  (ν'' : quasicoherentUnitObj B S hS (dA'.fibre Px'.U Px'.toSpace) ⟶ Mn'' 0)
  (Θ : ∀ n, quasicoherentPullbackObj B S hS yU (Mn n) ≅ Mn'' n)
  (hΘ : ∀ n, PullbackTransitionCompatible Px Px' hP hP' hℓt hℓs yU hyU yR hyR (τ n) (τ'' n)
    (Θ n))
  (hΘm : ∀ i j, QuasicoherentPullbackMulCompat yU (m i j) (Θ i) (Θ j) (Θ (i + j)) (m'' i j))
  (hΘu : QuasicoherentPullbackUnitCompat yU ν (Θ 0) ν'')
  (hbt : ∀ i j, RepresentedC3TensorCompat B S hS (dA.spaceTarget Px hP) (Mn i) (Mn j))
  (hbs : ∀ i j, RepresentedC3TensorCompat B S hS (dA.spaceSource Px hP) (Mn i) (Mn j))
  (hm : ∀ i j, dA.TransitionMulCompat Px hP (τ i) (τ j) (τ (i + j)) (m i j))
  (hbtu : RepresentedC3UnitCompat B S hS (dA.spaceTarget Px hP))
  (hbsu : RepresentedC3UnitCompat B S hS (dA.spaceSource Px hP))
  (hmu : dA.TransitionUnitCompat Px hP (τ 0) ν)
  (hassoc : QuasicoherentMulAssoc (dA.fibre Px.U Px.toSpace) m)
  (hone : QuasicoherentOneMul (dA.fibre Px.U Px.toSpace) m ν)
  (hcomm : QuasicoherentMulComm (dA.fibre Px.U Px.toSpace) m)
  (hbt'' : ∀ i j, RepresentedC3TensorCompat B S hS (dA'.spaceTarget Px' hP') (Mn'' i) (Mn'' j))
  (hbs'' : ∀ i j, RepresentedC3TensorCompat B S hS (dA'.spaceSource Px' hP') (Mn'' i) (Mn'' j))
  (hm'' : ∀ i j, dA'.TransitionMulCompat Px' hP' (τ'' i) (τ'' j) (τ'' (i + j)) (m'' i j))
  (hbtu'' : RepresentedC3UnitCompat B S hS (dA'.spaceTarget Px' hP'))
  (hbsu'' : RepresentedC3UnitCompat B S hS (dA'.spaceSource Px' hP'))
  (hmu'' : dA'.TransitionUnitCompat Px' hP' (τ'' 0) ν'')
  (hassoc'' : QuasicoherentMulAssoc (dA'.fibre Px'.U Px'.toSpace) m'')
  (hone'' : QuasicoherentOneMul (dA'.fibre Px'.U Px'.toSpace) m'' ν'')
  (hcomm'' : QuasicoherentMulComm (dA'.fibre Px'.U Px'.toSpace) m'')

include hℓt hℓs hyU hyR hΘ hΘm hΘu in
/-- **The inverse image of a descended sheaf of graded algebras along a morphism of relative
Projs is the descended sheaf of graded algebras of the pulled-back chart data** (Stacks 03M3):
for a morphism `y : U' ×_{X'} P' ⟶ U ×_X P` of the presenting schemes lying over `ℓ : U' ⟶ U`
and `h : P' ⟶ P`, and identifications `Θ_n : y^*M_n ≅ M''_n` compatible with the transitions,
the multiplications and the units, the isomorphisms `h^*D(M_n) ≅ D(M''_n)`
(`AlgebraicGeometry.Space.RelativeProjPoints.pullbackAlongDescendedIso`) form an isomorphism of
sheaves of graded algebras. -/
def pullbackAlongGradedAlgebraIso :
    ModulePullbackGradedAlgebraIso (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS)
        ⟶ ⟨PA, hP⟩) (dA.spacePresentationGradedAlgebra Px hP τ hc hu m hbt hbs hm ν hbtu hbsu hmu
            hassoc hone
        hcomm) (dA'.spacePresentationGradedAlgebra Px' hP' τ'' hc'' hu'' m'' hbt'' hbs'' hm'' ν''
            hbtu''
        hbsu'' hmu'' hassoc'' hone'' hcomm'') where
  iso := pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ hc hu m ν τ'' hc''
    hu'' m'' ν'' Θ hΘ hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt'' hbs'' hm'' hbtu'' hbsu''
    hmu'' hassoc'' hone'' hcomm''
  mul_comp := pullbackMulCompat_pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR
    τ hc hu m ν τ'' hc'' hu'' m'' ν'' Θ hΘ hΘm hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt''
    hbs'' hm'' hbtu'' hbsu'' hmu'' hassoc'' hone'' hcomm''
  unit_comp := pullbackUnitCompat_pullbackAlongDescendedModuleIso Px Px' hP hP' hℓt hℓs yU hyU yR
    hyR τ hc hu m ν τ'' hc'' hu'' m'' ν'' Θ hΘ hΘu hbt hbs hm hbtu hbsu hmu hassoc hone hcomm hbt''
    hbs'' hm'' hbtu'' hbsu'' hmu'' hassoc'' hone'' hcomm''

end GradedPullbackAlong

end RelativeProjPoints

/-! ### Presentations of `X'` compatible with a presentation of `X` -/

namespace Presentation

open Stacks.Groupoids

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  {hX' : IsAlgebraicSpace B S hS X'}

/-- **A presentation of an algebraic space from a surjective étale atlas** (Stacks 0263): the
relation is the fibre product `U ×_{X'} U`, which exists because the atlas is relatively
representable, and is an étale equivalence relation by Stacks 0262. -/
noncomputable def ofAtlas {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X')
    (hasurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (haetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a) :
    Presentation B S hS X' hX' := by
  classical
  have hrel : MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a := by
    simpa [MorphismProperty.presheaf] using haetale
  let hf : yoneda.relativelyRepresentable a := hrel.1
  let R := hf.pullback a
  let src : R ⟶ U := hf.snd a
  let tgt : R ⟶ U := yoneda.preimage (hf.fst a)
  have hkernel : IsPullback (yoneda.map tgt) (yoneda.map src) a a := by
    simpa [tgt, src] using hf.isPullback a
  exact
    { U := U
      R := R
      target := tgt
      source := src
      isEtaleEquivalenceRelation :=
        { isEquivalenceRelation := by
            simpa only [prod.lift_fst, prod.lift_snd] using
              isEquivalenceRelation_of_isPullback B S hS a tgt src hkernel
          etale_source := by
            simp only [prod.lift_snd]
            exact hrel.2 a (hf.fst a) (hf.snd a) (hf.isPullback a)
          etale_target := by
            simp only [prod.lift_fst]
            exact hrel.2 a (yoneda.map src) tgt (by simpa [tgt, src] using (hf.isPullback a).flip) }
      toSpace := a
      surjective := hasurj
      etale := haetale
      isPullback := hkernel }

/-- The chart of `Presentation.ofAtlas` is the source of the atlas. -/
@[simp]
theorem ofAtlas_U {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X') hasurj haetale :
    (ofAtlas (hX' := hX') a hasurj haetale).U = U :=
  rfl

/-- The atlas of `Presentation.ofAtlas` is the given one. -/
@[simp]
theorem ofAtlas_toSpace {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X') hasurj haetale :
    (ofAtlas (hX' := hX') a hasurj haetale).toSpace = a :=
  rfl

variable (Px : Presentation B S hS X hX) (g : X' ⟶ X) (Px₀ : Presentation B S hS X' hX')

/-- **A presentation `X' = U'/R'` compatible with a presentation `X = U/R` along `g : X' ⟶ X`**:
its chart is `U' = U'₀ ×_X U` for a presentation `X' = U'₀/R'₀`, with the atlas
`U' ⟶ U'₀ ⟶ X'`, so that `U' ⟶ X' ⟶ X` factors through `U ⟶ X`. -/
noncomputable def comap : Presentation B S hS X' hX' :=
  ofAtlas (yoneda.map (Px.alongPointToPoint (Px₀.toSpace ≫ g)) ≫ Px₀.toSpace)
    (MorphismProperty.comp_mem _ _ _ (Px.surjective_alongPointToPoint _) Px₀.surjective)
    (MorphismProperty.comp_mem _ _ _ (Px.etale_alongPointToPoint _) Px₀.etale)

/-- The morphism `U' ⟶ U` of the charts of `Presentation.comap`. -/
noncomputable abbrev comapToAtlas : (Px.comap g Px₀).U ⟶ Px.U :=
  Px.alongPointToAtlas (Px₀.toSpace ≫ g)

/-- The chart of `Presentation.comap` maps to the chart of the presentation of `X` over `g`. -/
theorem map_comapToAtlas_comp_toSpace :
    yoneda.map (Px.comapToAtlas g Px₀) ≫ Px.toSpace = (Px.comap g Px₀).toSpace ≫ g :=
  (Px.map_alongPointToAtlas_comp_toSpace _).trans (Category.assoc _ _ _).symm

/-- The morphism `R' ⟶ R` of the relations of `Presentation.comap`, through `R = U ×_X U`. -/
noncomputable def comapRelationMap : (Px.comap g Px₀).R ⟶ Px.R :=
  yoneda.preimage (Px.isPullback.lift
    (yoneda.map ((Px.comap g Px₀).target ≫ Px.comapToAtlas g Px₀))
    (yoneda.map ((Px.comap g Px₀).source ≫ Px.comapToAtlas g Px₀)) (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        map_comapToAtlas_comp_toSpace, ← Category.assoc, ← Category.assoc,
        (Px.comap g Px₀).isPullback.w]))

/-- The morphism of the relations commutes with the target projections. -/
theorem comapRelationMap_target :
    Px.comapRelationMap g Px₀ ≫ Px.target = (Px.comap g Px₀).target ≫ Px.comapToAtlas g Px₀ :=
  yoneda.map_injective (by
    rw [Functor.map_comp, comapRelationMap, Functor.map_preimage]
    exact Px.isPullback.lift_fst _ _ _)

/-- The morphism of the relations commutes with the source projections. -/
theorem comapRelationMap_source :
    Px.comapRelationMap g Px₀ ≫ Px.source = (Px.comap g Px₀).source ≫ Px.comapToAtlas g Px₀ :=
  yoneda.map_injective (by
    rw [Functor.map_comp, comapRelationMap, Functor.map_preimage]
    exact Px.isPullback.lift_snd _ _ _)

end Presentation

/-! ### The isomorphism `θ` of Stacks 085C -/

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m}) {X' : AlgebraicSpaces s.site s.base s.containsBase}
  (g : X' ⟶ s.space)
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (Px' : Presentation s.site s.base s.containsBase X'.obj X'.property)
  (ℓ : Px'.U ⟶ Px.U) (hℓ : yoneda.map ℓ ≫ Px.toSpace = Px'.toSpace ≫ g.hom)
  (ℓR : Px'.R ⟶ Px.R) (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ)

/-- The comparisons of twists of Tag 01O3 along `U' ×_{X'} P' ⟶ U ×_X P` carry the
multiplication of the twists of `U ×_X P` to that of `U' ×_{X'} P'`, as the named proposition
`AlgebraicGeometry.Space.QuasicoherentPullbackMulCompat`. -/
theorem quasicoherentPullbackMulCompat_chartTwistComparison (i j : ℤ) :
    QuasicoherentPullbackMulCompat (B := s.site) (S := s.base) (hS := s.containsBase)
      (V := (s.pullback g).relativeProjPoints.fibre Px'.U Px'.toSpace)
      (U := s.relativeProjPoints.fibre Px.U Px.toSpace) (s.chartBaseChangeMap g Px Px' ℓ hℓ)
      (s.twistPieceMul Px.U Px.toSpace i j)
      (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) i)
      (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) j)
      (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) (i + j))
      ((s.pullback g).twistPieceMul Px'.U Px'.toSpace i j) :=
  ⟨s.baseChangeTwistPieceComparison_mul g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
    (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) i j⟩

/-- The comparison of twists of Tag 01O3 along `U' ×_{X'} P' ⟶ U ×_X P` carries the unit of the
twists of `U ×_X P` to that of `U' ×_{X'} P'`, as the named proposition
`AlgebraicGeometry.Space.QuasicoherentPullbackUnitCompat`. -/
theorem quasicoherentPullbackUnitCompat_chartTwistComparison :
    QuasicoherentPullbackUnitCompat (B := s.site) (S := s.base) (hS := s.containsBase)
      (V := (s.pullback g).relativeProjPoints.fibre Px'.U Px'.toSpace)
      (U := s.relativeProjPoints.fibre Px.U Px.toSpace) (s.chartBaseChangeMap g Px Px' ℓ hℓ)
      (s.twistPieceUnit Px.U Px.toSpace) (s.chartTwistComparison g Px Px' ℓ hℓ 0)
      ((s.pullback g).twistPieceUnit Px'.U Px'.toSpace) :=
  ⟨s.baseChangeTwistPieceComparison_unit g ℓ hℓ _
    (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ)⟩

include hℓt in
/-- **The isomorphism `θ` of Stacks 085C, for compatible presentations.**  For a morphism
`g : X' ⟶ X` of algebraic spaces and the quasi-coherent graded `𝒪_X`-algebra `𝒜` of Situation
0849, let `P = Proj_X(𝒜)`, `P' = Proj_{X'}(g^*𝒜)` and `h : P' ⟶ P` the morphism of Stacks 085C
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeHom`), which is `pr_2 ∘ r`
for the isomorphism `r : P' ≅ X' ×_X P`
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeIso_hom_snd`).  Then the
inverse image `h^* = r^* pr_2^*` of the sheaf of `ℤ`-graded `𝒪_P`-algebras
`⨁_{d ∈ ℤ} 𝒪_P(d)` of Stacks 084D
(`AlgebraicGeometry.Space.RelativeProjSituation.twistGradedAlgebra`)
is isomorphic, as a sheaf of `ℤ`-graded `𝒪_{P'}`-algebras, to `⨁_{d ∈ ℤ} 𝒪_{P'}(d)`: the
isomorphisms `θ_d : h^*𝒪_P(d) ≅ 𝒪_{P'}(d)`
(`AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistModuleIso`) carry the
multiplication of `⨁ 𝒪_P(d)`, pulled back along `h` and read through Stacks 03EL, to the
multiplication of `⨁ 𝒪_{P'}(d)`, and the pulled-back unit, read through Stacks 03LU, to the
unit.  The twists are those descended from presentations `X = U/R` and `X' = U'/R'` compatible
with `g`, along `ℓ : U' ⟶ U` and `ℓR : R' ⟶ R`; on the presenting schemes `θ` is the
comparison of twists of Tag 01O3, as in the source's hint. -/
def baseChangeTwistGradedAlgebraIso (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ) :
    ModulePullbackGradedAlgebraIso (s.relativeProjBaseChangeSpaceHom g) (s.twistGradedAlgebra Px)
      ((s.pullback g).twistGradedAlgebra Px') :=
  RelativeProjPoints.pullbackAlongGradedAlgebraIso (XA' := X') (dA := s.relativeProjPoints)
    (dA' := (s.pullback g).relativeProjPoints) (hA := s.relativeProjBaseChangeHom g) Px Px'
    s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor
    hℓt hℓs (s.chartBaseChangeMap g Px Px' ℓ hℓ) (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ)
    (s.relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
    (s.liesOverAlong_relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
    (Mn := s.twistPieceQcoh Px.U Px.toSpace) (s.twistTransition Px)
    (s.presentationSchemeCocycle_twistTransition Px) (s.presentationSchemeUnit_twistTransition Px)
    (s.twistPieceMul Px.U Px.toSpace) (s.twistPieceUnit Px.U Px.toSpace)
    (Mn'' := (s.pullback g).twistPieceQcoh Px'.U Px'.toSpace) ((s.pullback g).twistTransition Px')
    ((s.pullback g).presentationSchemeCocycle_twistTransition Px')
    ((s.pullback g).presentationSchemeUnit_twistTransition Px')
    ((s.pullback g).twistPieceMul Px'.U Px'.toSpace)
    ((s.pullback g).twistPieceUnit Px'.U Px'.toSpace)
    (s.chartTwistComparison g Px Px' ℓ hℓ)
    (s.pullbackTransitionCompatible_chartBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt hℓs)
    (s.quasicoherentPullbackMulCompat_chartTwistComparison g Px Px' ℓ hℓ)
    (s.quasicoherentPullbackUnitCompat_chartTwistComparison g Px Px' ℓ hℓ)
    (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    (s.transitionMulCompat_twistTransition Px)
    (representedC3UnitCompat s.site s.base s.containsBase _)
    (representedC3UnitCompat s.site s.base s.containsBase _)
    (s.transitionUnitCompat_twistTransition Px)
    (s.quasicoherentMulAssoc_twistPieceMul Px.U Px.toSpace)
    (s.quasicoherentOneMul_twistPieceUnit Px.U Px.toSpace)
    (s.quasicoherentMulComm_twistPieceMul Px.U Px.toSpace)
    (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    (fun _ _ => representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    ((s.pullback g).transitionMulCompat_twistTransition Px')
    (representedC3UnitCompat s.site s.base s.containsBase _)
    (representedC3UnitCompat s.site s.base s.containsBase _)
    ((s.pullback g).transitionUnitCompat_twistTransition Px')
    ((s.pullback g).quasicoherentMulAssoc_twistPieceMul Px'.U Px'.toSpace)
    ((s.pullback g).quasicoherentOneMul_twistPieceUnit Px'.U Px'.toSpace)
    ((s.pullback g).quasicoherentMulComm_twistPieceMul Px'.U Px'.toSpace)

/-- **Stacks 085C, the isomorphism `θ` of graded algebras, for any presentations of `X` and
`X'`.**  For a presentation `X = U/R` the twists `𝒪_P(d)` of `P = Proj_X(𝒜)` are descended along
it, and those of `P' = Proj_{X'}(g^*𝒜)` along the presentation `X' = U'/R'` with
`U' = U'₀ ×_X U` obtained from any presentation `X' = U'₀/R'₀`
(`AlgebraicGeometry.Space.Presentation.comap`); then
`θ : r^* pr_2^* (⨁_d 𝒪_P(d)) ≅ ⨁_d 𝒪_{P'}(d)` is an isomorphism of `ℤ`-graded `𝒪_{P'}`-algebras
(`AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistGradedAlgebraIso`),
with `h = pr_2 ∘ r` the morphism `Proj_{X'}(g^*𝒜) ⟶ Proj_X(𝒜)`. -/
@[stacks 085C "theta for every presentation X = U/R of X (and X' = U'_0/R'_0 of X'), the \
twists of Proj_{X'}(g^*A) descended along the presentation of X' over U'_0 x_X U: the \
isomorphism r^* pr_2^* (+)_{d in Z} O_{Proj_X(A)}(d) -> (+)_{d in Z} O_{Proj_{X'}(g^*A)}(d) \
of Z-graded O_{Proj_{X'}(g^*A)}-algebras"]
def baseChangeTwistGradedAlgebraIsoOfPresentation
    (Px₀ : Presentation s.site s.base s.containsBase X'.obj X'.property) :
    ModulePullbackGradedAlgebraIso (s.relativeProjBaseChangeSpaceHom g) (s.twistGradedAlgebra Px)
      ((s.pullback g).twistGradedAlgebra (Px.comap g.hom Px₀)) :=
  s.baseChangeTwistGradedAlgebraIso g Px (Px.comap g.hom Px₀) (Px.comapToAtlas g.hom Px₀)
    (Px.map_comapToAtlas_comp_toSpace g.hom Px₀) (Px.comapRelationMap g.hom Px₀)
    (Px.comapRelationMap_target g.hom Px₀) (Px.comapRelationMap_source g.hom Px₀)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
