module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnital
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Morphism.BaseChange

/-!
# A homomorphism of graded algebras on an algebraic space, restricted to the scheme points

In Situation 0849 let `ψ : 𝒜 ⟶ ℬ` be a map of quasi-coherent graded `𝒪_X`-algebras. For every
scheme point `f : T ⟶ X` it restricts to a homomorphism `f^*ψ : f^*𝒜 ⟶ f^*ℬ` of the restrictions
of Situation 01NN on the scheme of `T`, and these restrictions commute with the identifications
`(f ∘ τ)^*𝒜 ≅ τ^*(f^*𝒜)` of the restriction datum of Stacks 084A.

The restriction is the pullback of sheaves of graded algebras of Stacks 0FQX along the morphism of
small étale ringed topoi of `f`, read on the Zariski opens of `T`, exactly as the restricted
algebras themselves are built (`AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`). For
the shrunk situation it is first transported to the re-presentations of the algebras with
sections in the universe of the schemes.

## Main definitions

* `AlgebraicGeometry.Space.pointAlgebraHom`: the restriction of a unital homomorphism to a
  scheme point.
* `SheafOfModules.GradedAlgebra.smallPresentationMap`: a unital homomorphism transported to the
  small presentations.
* `AlgebraicGeometry.Space.RelativeProjSituation.shrinkMap`: a map `𝒜₁ ⟶ 𝒜₂` of graded algebras
  on `X`, carried to the algebras of the two shrunk situations.
* `AlgebraicGeometry.Space.RelativeProjSituation.restrictHom`: the restrictions of `ψ` to the
  scheme points, as homomorphisms of the restricted algebras of the two situations.

## Main results

* `AlgebraicGeometry.Space.pointComparison_comp_pointAlgebraHom_app`: the restrictions commute
  with the comparisons of the restricted algebras.
* `AlgebraicGeometry.Space.RelativeProjSituation.epi_restrictHom_app_iff`: `restrictHom` is an
  epimorphism in a degree exactly when the restriction `pointAlgebraHom` of the shrunk map is.
* `AlgebraicGeometry.Space.pointAlgebraHom_comp_app` and
  `SheafOfModules.GradedAlgebra.smallPresentationMap_comp`: both constructions carry a composite
  to the composite.

The compatibility of `restrictHom` with the restriction data of the two situations, and the map of
graded algebras over the scheme points of the base it defines, are in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.HomPoints`.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj
  unitalGradedPull)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom baseAlgebra baseAlgebraMapHom)

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The restriction maps are natural in the algebra -/

section Naturality

variable {X P P' : AlgebraicSpaces B S hS}

/-- The pullback of a homomorphism of sheaves of graded algebras along the morphism of small étale
ringed topoi of a morphism of algebraic spaces. -/
abbrev etalePullHom (f : P ⟶ X)
    {A A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)} (g : A ⟶ A') :=
  (gradedPull (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS f)).map g

/-- The pullback of a unital homomorphism of sheaves of graded algebras along the morphism of small
étale ringed topoi of a morphism of algebraic spaces, as a unital homomorphism. -/
def etaleUnitalPull (f : P ⟶ X)
    {A A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)}
    (g : SheafOfModules.GradedAlgebra.UnitalHom A A') :
    SheafOfModules.GradedAlgebra.UnitalHom
      ((gradedPull (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).obj A)
      ((gradedPull (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).obj A') where
  app n := (etalePullHom f g.toHom).app n
  map_mul := (etalePullHom f g.toHom).map_mul
  map_one := Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPull_map_one
    (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS f) g.toHom g.map_one

/-- **The restriction maps of pulled-back graded algebras are natural in the algebra.** -/
theorem gradedPullRestriction_naturality (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') {A A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)}
    (g : A ⟶ A') :
    etalePullHom f g ≫ gradedPullRestriction φ f f' h A' =
      gradedPullRestriction φ f f' h A ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS P)
          (smallEtaleRingedToposHom B S hS φ)).map (etalePullHom f' g) := by
  subst h
  exact Adjunction.unitTranspose_naturality _ _ _ _ g

/-- `gradedPullRestriction_naturality` in one degree. -/
theorem gradedPullRestriction_naturality_app (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X)
    (h : φ ≫ f = f') {A A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)}
    (g : A ⟶ A') (n : ℤ) :
    (etalePullHom f g).app n ≫ (gradedPullRestriction φ f f' h A').app n =
      (gradedPullRestriction φ f f' h A).app n ≫
        (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map ((etalePullHom f' g).app n) :=
  congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n)
    (gradedPullRestriction_naturality φ f f' h g)

end Naturality

/-! ### The restriction of a unital homomorphism to a scheme point -/

section Point

variable {X : AlgebraicSpaces B S hS}
  {A₁ A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom A₁ A₂)

/-- The Zariski reading of a unital homomorphism of sheaves of graded algebras on a represented
algebraic space. -/
def zariskiReadingHom (T : BigFppfOver B S hS)
    {E₁ E₂ : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf B S hS (yonedaSpace B S hS T))}
    (g : SheafOfModules.GradedAlgebra.UnitalHom E₁ E₂) :
    SheafOfModules.GradedAlgebra.UnitalHom (zariskiReading T E₁) (zariskiReading T E₂) :=
  haveI := isContinuous_selfOpensFunctor B S hS T
  { app := (g.toHom.pushforward (selfOpensStructureMap B S hS T)).app
    map_mul := (g.toHom.pushforward (selfOpensStructureMap B S hS T)).map_mul
    map_one := fun _ => g.map_one _ }

/-- **The restriction `f^*Φ : f^*A₁ ⟶ f^*A₂` of a unital homomorphism to a scheme point**: the
pullback of `Φ` along the morphism of small étale ringed topoi of `f`, read on the Zariski opens
of the scheme of `T`. -/
def pointAlgebraHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    SheafOfModules.GradedAlgebra.UnitalHom (zariskiReading T (etalePointAlgebra A₁ T f))
      (zariskiReading T (etalePointAlgebra A₂ T f)) :=
  zariskiReadingHom T (etaleUnitalPull (pointHom f) Φ)

/-- In degree `n`, `pointAlgebraHom Φ T f` is the pushforward along the Zariski-opens structure
map of the degree-`n` component of the pullback of `Φ` along `pointHom f`. -/
theorem pointAlgebraHom_app (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (pointAlgebraHom Φ T f).app n =
      (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
        ((etalePullHom (pointHom f) Φ.toHom).app n) := rfl

/-- `gradedPullRestriction_naturality` at a scheme point, on sections. -/
theorem pointGradedPullRestriction_naturality_val_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ)
    (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (x : ((zariskiReading T (etalePointAlgebra A₁ T f)).piece n).val.obj O) :
    ((etalePullHom (pointHom f) Φ.toHom ≫
        gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
          (pointHom_comp τ hf) A₂).app n).val.app (op ((selfOpensFunctor B S hS T).obj O.unop)) x =
      ((gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
          (pointHom_comp τ hf) A₁ ≫
        (gradedPush (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
          (Y := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ))).map
          (etalePullHom (pointHom f') Φ.toHom)).app n).val.app
        (op ((selfOpensFunctor B S hS T).obj O.unop)) x :=
  congrArg (fun k => (SheafOfModules.GradedAlgebra.Hom.app k n).val.app
      (op ((selfOpensFunctor B S hS T).obj O.unop)) x)
    (gradedPullRestriction_naturality (representedSpaceMap B S hS τ) (pointHom f)
      (pointHom f') (pointHom_comp τ hf) Φ.toHom)

/-- The restriction maps of the pulled-back algebras commute with the pullbacks of `Φ`, on
sections. -/
theorem pointGradedPullRestriction_app_val_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ)
    (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (x : ((zariskiReading T (etalePointAlgebra A₁ T f)).piece n).val.obj O) :
    ((gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
        (pointHom_comp τ hf) A₂).app n).val.app (op ((selfOpensFunctor B S hS T).obj O.unop))
        (((etalePullHom (pointHom f) Φ.toHom).app n).val.app
          (op ((selfOpensFunctor B S hS T).obj O.unop)) x) =
      ((testToposHom τ).pushforwardModules.map ((etalePullHom (pointHom f') Φ.toHom).app n)).val.app
        (op ((selfOpensFunctor B S hS T).obj O.unop))
        (((gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
          (pointHom_comp τ hf) A₁).app n).val.app
            (op ((selfOpensFunctor B S hS T).obj O.unop)) x) :=
  pointGradedPullRestriction_naturality_val_app Φ τ f f' hf n O x

/-- The restriction maps of the restricted algebras commute with the restrictions of `Φ`, on
sections over a Zariski open, written through the sections of direct images. -/
theorem pointRestriction_naturality_section {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ)
    (O : (chartScheme (idEtaleChart B S hS T)).Opensᵒᵖ)
    (x : ((zariskiReading T (etalePointAlgebra A₁ T f)).piece n).val.obj O) :
    ((Sheaf.moduleSheafFunctor (testRing T')).map
        ((etalePullHom (pointHom f') Φ.toHom).app n)).hom.app
        (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O.unop)))
        (directImageSelfOpensSection τ O.unop _
          (((gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A₁).app n).val.app
              (op ((selfOpensFunctor B S hS T).obj O.unop)) x)) =
      directImageSelfOpensSection τ O.unop _
        (((gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A₂).app n).val.app (op ((selfOpensFunctor B S hS T).obj O.unop))
          (((etalePullHom (pointHom f) Φ.toHom).app n).val.app
            (op ((selfOpensFunctor B S hS T).obj O.unop)) x)) := by
  rw [pointGradedPullRestriction_app_val_app Φ τ f f' hf n O x]
  exact (directImageSelfOpensSection_map τ O.unop
    ((Sheaf.moduleSheafFunctor (testRing T')).map
      ((etalePullHom (pointHom f') Φ.toHom).app n)) _).symm

/-- **The restriction maps of the restricted algebras commute with the restrictions of `Φ`.** -/
theorem pointRestriction_comp_pointAlgebraHom_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (pointRestriction A₁ τ f f' hf).app n ≫
      (Stacks.RingedSpace.pushforwardFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((pointAlgebraHom Φ T' f').app n) =
      (pointAlgebraHom Φ T f).app n ≫ (pointRestriction A₂ τ f f' hf).app n := by
  ext O x
  exact pointRestriction_naturality_section Φ τ f f' hf n O x

/-- **The restrictions commute with the comparisons of the restricted algebras.** For
`τ : T' ⟶ T`, the comparison `τ^*(f^*A) ⟶ (f ∘ τ)^*A` intertwines `τ^*(f^*Φ)` and
`(f ∘ τ)^*Φ`. -/
theorem pointComparison_comp_pointAlgebraHom_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    (pointComparison A₁ τ f f' hf).app n ≫ (pointAlgebraHom Φ T' f').app n =
      (baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map τ) (pointAlgebraHom Φ T f)).app n ≫
        (pointComparison A₂ τ f f' hf).app n := by
  set adj := Stacks.RingedSpace.pullbackAdjunction
    (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))
  change (adj.homEquiv _ _).symm ((pointRestriction A₁ τ f f' hf).app n) ≫ _ =
    _ ≫ (adj.homEquiv _ _).symm ((pointRestriction A₂ τ f f' hf).app n)
  exact (adj.homEquiv_naturality_right_symm _ _).symm.trans
    ((congrArg (adj.homEquiv _ _).symm
      (pointRestriction_comp_pointAlgebraHom_app Φ τ f f' hf n)).trans
      (adj.homEquiv_naturality_left_symm _ _))

/-- **The restriction to a scheme point of a composite is the composite of the restrictions.** -/
theorem pointAlgebraHom_comp_app
    {A₃ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)}
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom A₂ A₃) (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (pointAlgebraHom (Φ.comp Ψ) T f).app n =
      (pointAlgebraHom Φ T f).app n ≫ (pointAlgebraHom Ψ T f).app n := by
  rw [pointAlgebraHom_app, pointAlgebraHom_app, pointAlgebraHom_app]
  refine (congrArg (fun k => (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
    (SheafOfModules.GradedAlgebra.Hom.app k n))
    ((gradedPull (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
      (Y := smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedToposHom B S hS (pointHom f))).map_comp Φ.toHom Ψ.toHom)).trans ?_
  exact Functor.map_comp _ _ _

end Point

end AlgebraicGeometry.Space

namespace SheafOfModules.GradedAlgebra

universe t a w v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}
  [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((A.piece n).val.obj U)]
  [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((B.piece n).val.obj U)]

/-- **A unital homomorphism carried to the small presentations**: on sections it is the given
homomorphism conjugated by the identifications of the small presentations with the algebras. -/
noncomputable def smallPresentationMap (g : UnitalHom A B) :
    UnitalHom (smallPresentation.{t, a, w} A) (smallPresentation.{t, a, w} B) where
  app n := ⟨{
    app := fun U => ModuleCat.ofHom
      ((smallPieceEquiv B n U).symm.toLinearMap ∘ₗ ((g.app n).val.app U).hom ∘ₗ
        (smallPieceEquiv A n U).toLinearMap)
    naturality := fun {U V} f => by
      ext x
      change (smallPieceEquiv B n V).symm ((g.app n).val.app V (smallPieceEquiv A n V
          ((smallPiece A n).val.map f x))) =
        (smallPiece B n).val.map f ((smallPieceEquiv B n U).symm
          ((g.app n).val.app U (smallPieceEquiv A n U x)))
      refine ((congrArg (fun z => (smallPieceEquiv B n V).symm ((g.app n).val.app V z))
        (smallPieceEquiv_naturality A n f x)).trans ?_).trans
          ((smallPresentationEquiv B).map_symm n f _).symm
      exact congrArg (smallPieceEquiv B n V).symm
        (PresheafOfModules.naturality_apply (g.app n).val f _) }⟩
  map_mul i j U x y := by
    apply (smallPieceEquiv B (i + j) U).injective
    refine (LinearEquiv.apply_symm_apply _ _).trans ?_
    refine (congrArg (fun z => (g.app (i + j)).val.app U z)
      (smallPresentation_equiv_mul_app A i j U x y)).trans ?_
    refine (g.map_mul i j U _ _).trans ?_
    refine Eq.trans ?_ (smallPresentation_equiv_mul_app B i j U _ _).symm
    exact congrArg₂ (fun a b => (B.mul i j).app U a b)
      (LinearEquiv.apply_symm_apply _ _).symm (LinearEquiv.apply_symm_apply _ _).symm
  map_one U := by
    change (smallPieceEquiv B 0 U).symm ((g.app 0).val.app U
        (smallPieceEquiv A 0 U ((smallPresentation A).one.eval U))) =
      (smallPresentation B).one.eval U
    rw [smallPresentation_equiv_one_eval A U, g.map_one]
    apply (smallPieceEquiv B 0 U).injective
    rw [LinearEquiv.apply_symm_apply, smallPresentation_equiv_one_eval B U]

/-- `smallPresentationMap` carries a composite to the composite. -/
theorem smallPresentationMap_comp {D : GradedAlgebra.{t, a} R}
    [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((D.piece n).val.obj U)]
    (g : UnitalHom A B) (h : UnitalHom B D) :
    smallPresentationMap.{t, a, w} (g.comp h) =
      (smallPresentationMap.{t, a, w} g).comp (smallPresentationMap.{t, a, w} h) := by
  refine UnitalHom.ext fun n => ?_
  ext U x
  change (smallPieceEquiv D n U).symm ((h.app n).val.app U ((g.app n).val.app U
      (smallPieceEquiv A n U x))) =
    (smallPieceEquiv D n U).symm ((h.app n).val.app U (smallPieceEquiv B n U
      ((smallPieceEquiv B n U).symm ((g.app n).val.app U (smallPieceEquiv A n U x)))))
  rw [LinearEquiv.apply_symm_apply]

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Space.RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProjMapDomain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- A unital homomorphism of commutative sheaves of graded algebras on a scheme, read as a
homomorphism of the graded algebra data of Situation 01NN they define. -/
noncomputable def toSheafGradedAlgebraHom {Z : Scheme.{u}}
    {E₁ E₂ : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf}
    {h₁ : Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.IsCommutative E₁}
    {h₂ : Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.VanishesInNegativeDegrees E₁}
    {h₃ : ∀ n : ℤ, ((E₁.piece n : Z.Modules)).IsQuasicoherent}
    {h₁' : Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.IsCommutative E₂}
    {h₂' : Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.VanishesInNegativeDegrees E₂}
    {h₃' : ∀ n : ℤ, ((E₂.piece n : Z.Modules)).IsQuasicoherent}
    (g : SheafOfModules.GradedAlgebra.UnitalHom E₁ E₂) :
    SheafGradedAlgebraHom
      (Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra E₁ h₁ h₂ h₃)
      (Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra E₂ h₁' h₂' h₃') where
  app := g.app
  app_mul i j U a b := g.map_mul i j (op U) a b
  app_one U := g.map_one (op U)

section Map

variable {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k

/-- **A map of graded algebras, carried to the re-presentations of the algebras with sections in
the universe of the schemes**: for `ψ : 𝒜₁ ⟶ 𝒜₂` the map of the algebras of the two shrunk
situations of Situation 0849. -/
noncomputable def shrinkMap (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂) :
    @SheafOfModules.GradedAlgebra.UnitalHom _ _ _ (structureRingSheaf B S hS X)
      (𝔰₁).shrink.algebra (𝔰₂).shrink.algebra :=
  @SheafOfModules.GradedAlgebra.smallPresentationMap _ _ _ _ (𝔰₁).algebra (𝔰₂).algebra
    (𝔰₁).small_sections (𝔰₂).small_sections ψ

/-- **The restriction of a map of graded algebras to a scheme point of the base**, as a
homomorphism of the restricted algebras of the two situations in the sense of Situation 01NN: for
`ψ : 𝒜₁ ⟶ 𝒜₂` and a scheme point `f : T ⟶ X`, the homomorphism `f^*ψ : f^*𝒜₁ ⟶ f^*𝒜₂`,
transported to the re-presentations of the algebras with sections in the universe of the
schemes. -/
noncomputable def restrictHom (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    SheafGradedAlgebraHom ((𝔰₁).shrink.pointAlgebra T f) ((𝔰₂).shrink.pointAlgebra T f) :=
  toSheafGradedAlgebraHom
    (@pointAlgebraHom B S hS X _ _ (shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) T f)

/-- The degree-`n` component of `restrictHom` is that of the restriction `pointAlgebraHom`. -/
theorem restrictHom_toSituationHom_app (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T f).toSituationHom.app n =
      (@pointAlgebraHom B S hS X _ _ (shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) T f).app n :=
  rfl

/-- `restrictHom` is an epimorphism in degree `n` exactly when the restriction `pointAlgebraHom`
of the shrunk map is. -/
theorem epi_restrictHom_app_iff (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    Epi ((restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T f).app n) ↔
      Epi ((@pointAlgebraHom B S hS X _ _ (shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) T
        f).app n) :=
  Iff.rfl

end Map

end AlgebraicGeometry.Space.RelativeProjSituation

end
