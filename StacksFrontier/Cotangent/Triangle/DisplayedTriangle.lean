module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Triangle.BaseChangeComparison
public import StacksFrontier.Cotangent.Triangle.BaseChangeLegTensor
public import StacksFrontier.Cotangent.Triangle.DisplayMorphisms

/-!
# The displayed triangle of Tag 08QS on the display's own vertices and morphisms

For ring maps `A → B → C`, Equation 92.7.0.1 of the Stacks Project displays the triangle

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`. `StacksFrontier/Cotangent/Triangle/FundamentalDisplay.lean` names its three vertices and
`StacksFrontier/Cotangent/Triangle/DisplayMorphisms.lean` constructs the first two displayed
morphisms.

This file constructs the display's **own** third morphism `L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)⟦1⟧` as
data, for `B → C` injective, by transporting the connecting morphism of the triangle of Tag 08SD
along the two canonical identifications of the vertices — the first vertex by
`CommAlgCat.cotangentTriangle_obj₁DerivedBaseChangeIso`, the third by the identification of
Remark 08SE, `CommAlgCat.baseChangedCotangentComplexIsoOfInjective`. It also identifies **both**
of the first two morphisms of the triangle of Tag 08SD with the display's own
`CommAlgCat.fundamentalMor₁` and `CommAlgCat.fundamentalMor₂`, so the assembled distinguished
triangle is the display on its own three vertices with its own first two morphisms.

## Main definitions

* `CommAlgCat.fundamentalDisplayVertex₃Iso`: the third vertex of the triangle of Tag 08SD is the
  display's third vertex `L_{C/B}`, for `B → C` injective.
* `CommAlgCat.fundamentalMor₃`: **the third displayed morphism** `L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)⟦1⟧`,
  on the display's own vertices.
* `CommAlgCat.fundamentalDisplayMor₂`: the second morphism of the triangle of Tag 08SD read
  between the display's second and third vertices.
* `CommAlgCat.differentialSequenceSecondComparison` and
  `CommAlgCat.baseRingCotangentComparison`: the two maps of simplicial `C`-modules
  `Ω[Q_•⁄A] ⊗ C ⟶ Ω[R̄_•⁄B] ⊗ C` through the common resolution `R̄_• = R_• ⊗_{S_•} B` of
  Remark 08SE, one through `Q̄_•` and one through `R_•`.
* `CommAlgCat.baseRingCotangentSimplicialMap`: the functoriality map of Tag 08PN for the change of
  base ring, read between the two cotangent simplicial modules.

## Main results

* `CommAlgCat.cotangentTriangle_mor₁_eq_fundamentalMor₁`: the first morphism of the triangle of
  Tag 08SD, read out of the display's first vertex, **is** the display's
  `CommAlgCat.fundamentalMor₁`. This is a chain-level statement: the first map of the differential
  sequence of Tag 08SD is the functoriality map of Tag 08PN after extension of scalars.
* `CommAlgCat.fundamentalDisplayMor₂_eq_fundamentalMor₂`: the second morphism of the triangle of
  Tag 08SD, read between the display's second and third vertices, **is** the display's
  `CommAlgCat.fundamentalMor₂`.
* `CommAlgCat.fundamentalTriangle_distinguished`: `Triangle.mk fundamentalMor₁ fundamentalMor₂
  fundamentalMor₃` is a distinguished triangle in `D(C)`, on the display's own three vertices and
  with the display's own first two morphisms.
* `CommAlgCat.differentialSequenceSecondComponent_comp_baseChangedComparison`,
  `CommAlgCat.differentialSequenceSecondComparison_eq`,
  `CommAlgCat.secondMap_comp_baseChangedCotangentComparison` and
  `CommAlgCat.cotangentTriangle_mor₂_comp_baseChangedCotangentComplexIso`: the same identity
  degreewise, on simplicial modules, on complexes and in `D(C)`.

## How the second morphism is identified

`CommAlgCat.baseChangedCotangentComplexIso_hom_comp` pins the identification of Remark 08SE down
by its composite with the comparison `L_{C/B} ⟶ Ω[R̄_•⁄B] ⊗ C`, and that comparison is an
isomorphism in `D(C)`, so what the identification needs is

`(the quotient Ω[Q_•⁄A] ⊗ C ⟶ Ω[Q̄_•⁄B] ⊗ C) ≫ (induced by Q̄_• ⟶ R̄_•)`
  `= (functoriality of A → B at the standard resolutions) ≫ (induced by R_• ⟶ R̄_•)`

and nothing else. In each simplicial degree that is
`CommAlgCat.differentialSequenceSecondComponent_comp_baseChangedComparison`: both sides carry
`1 ⊗ d q` to `1 ⊗ d (δ (v q))`, because the two composite algebra maps `Q_n ⟶ R̄_n` are both
`q ↦ v(q) ⊗ 1` (`CommAlgCat.baseChangedComparison_apply` and
`CommAlgCat.relativeBaseChangeLeg_apply`).

The passage from there to complexes is plumbing, and the plumbing is constrained.
`CommAlgCat.baseChangedCotangentComparison` typechecks only because
`(CommAlgCat.relativeBaseChange f).right` and
`(CommAlgCat.baseChangedStandardResolution A f).right` are definitionally — but not *reducibly* —
equal: both unfold to `CommAlgCat.of ↥B ↥C` with the algebra structure `f.hom.toRingHom.toAlgebra`,
one of them through the semireducible `CommAlgCat.overBase`. A goal mentioning that map is reported
as "not type-correct under the `implicit` transparency level", so `rw` refuses to act on it, and a
*composite* written out afresh across that wall times out at `whnf`. The assembly here therefore
crosses the wall exactly once, in the statement of
`CommAlgCat.differentialSequenceSecondComparison`, where the composite is elaborated once as data;
everything after it is `Eq.trans`, `congrArg`, `Functor.map_comp` and `eq_of_heq` on terms that are
already elaborated, with no `rw` and no `simp only` anywhere in the chain. The two maps of
simplicial modules are compared degreewise on pure differentials, at an arbitrary object of `Δᵒᵖ` —
never at a concrete simplex, which is where the unifier would have to evaluate the standard
resolution.

### The carried hypothesis

`B → C` is assumed injective, as Tag 08SD assumes it, and that is the only gap left between
`CommAlgCat.fundamentalTriangle_distinguished` and Tag 08QX. It is **not** removable on this
route: the injectivity is what makes `Q_n` a polynomial algebra over `P_n`
(`CommAlgCat.standardResolution_isPolynomialAlgebra`,
`StacksFrontier/Cotangent/Triangle/BaseChange.lean:216`, through
`MvPolynomial.rename_injective`), and all three inputs of the route consume that:

* the degreewise short exact sequence of Tag 08SD needs `P_n ⟶ Q_n` formally smooth
  (`CommAlgCat.standardResolution_towerDifferential_shortExact_extendScalars`,
  `StacksFrontier/Cotangent/Triangle/DifferentialSequence.lean:249`, used at `:1113`);
* the flatness hypothesis of Tag 08RX needs `Q_n` flat over `P_n`
  (`CommAlgCat.flat_standardResolution`, `StacksFrontier/Cotangent/Triangle/KeyFact.lean:251`);
* the polynomiality of `Q̄_•` and of `R̄_•` of Remark 08SE
  (`CommAlgCat.baseChangedStandardResolution_isPolynomialAlgebra`,
  `StacksFrontier/Cotangent/Triangle/BaseChangeComparison.lean:588`).

Each of those fails without injectivity, already in degree `0`: for `f b₁ = f b₂` with `b₁ ≠ b₂`
the map `A[B] ⟶ A[C]`, `X_b ↦ X_{f b}`, kills `X_{b₁} - X_{b₂}`, so it is not injective, `A[C]`
is not flat over `A[B]`, and `Q̄_0 = A[C] ⊗_{A[B]} B` is a polynomial algebra over
`B/(b₁ - b₂, …)` rather than over `B`. Dropping the hypothesis is the passage to
`A → B → B × C` that Remark 08SD itself prescribes, where the map is the split injection
`b ↦ (b, f b)`, followed by base change along the flat projection `B × C → C`. That passage is
carried out in `StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, on top of the product
decomposition of Tag 08SC (`CommAlgCat.isIso_Q_map_cotangentComplexProductMap` of
`StacksFrontier/Cotangent/ProductDecompositionBase.lean`).

**So no `@[stacks 08QS]` and no `@[stacks 08QX]` attribute is added here**: both tags are stated
for arbitrary `A → B → C`, whereas the statements of this file assume `B → C` injective. They are
registered on the declarations of `StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, which
assume nothing: `CommAlgCat.productFundamentalMor₃` carries `@[stacks 08QS]` for the third
displayed morphism, and `CommAlgCat.productFundamentalTriangle_distinguished` carries
`@[stacks 08QX]` together with `@[stacks 08QS]` for the display's distinguishedness clause. The
other registrations of Tag 08QS — the three vertices in
`StacksFrontier/Cotangent/Triangle/FundamentalDisplay.lean` and the first two displayed morphisms in
`StacksFrontier/Cotangent/Triangle/DisplayMorphisms.lean` — are unchanged and continue to claim
exactly what they claimed.

## References

* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the displayed triangle.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is
  distinguished.
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial

universe u

namespace CommAlgCat

section Chain

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

/-- **The first map of the differential sequence of Tag 08SD is the functoriality map of
Tag 08PN after extension of scalars.** On Moore complexes: the comparison of the alternating face
map complex with degreewise extension of scalars, followed by
`CommAlgCat.cotangentExtendScalarsMooreMap`, is the first map of the differential sequence. Both
send the pure differential `1 ⊗ 1 ⊗ d p` to `1 ⊗ d (u p)`, for `u : P_• ⟶ Q_•` the canonical map
of the standard resolutions of `B` and of `C` over `A`. -/
theorem cotangentExtendScalarsMooreMap_eq_differentialSequenceFirstMap (f : B ⟶ C) :
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso
          (ModuleCat.extendScalars f.hom.toRingHom)).app
        (cotangentSimplicialModule.{u, u} A B).object).inv ≫
        cotangentExtendScalarsMooreMap (A := A) (A' := A) (B := B) (B' := C) f.hom =
      (alternatingFaceMapComplex (ModuleCat.{u} ↥C)).map (differentialSequenceFirstMap A f) := by
  apply HomologicalComplex.hom_ext
  intro n
  refine Eq.trans (HomologicalComplex.comp_f _ _ _) ?_
  refine Eq.trans ?_
    (alternatingFaceMapComplex_map_f (differentialSequenceFirstMap A f) n).symm
  refine Eq.trans (Category.id_comp _) ?_
  refine (differentialSequenceFirstHom_ext' A f (op ⦋n⦌) _ _ fun p => ?_).symm
  refine ((differentialSequenceFirstComponent_differential' A f (op ⦋n⦌) p).trans ?_).trans
    (cotangentExtendScalarsMooreMap_f_mk f.hom n p).symm
  exact congrArg (cotangentTermDifferential.{u, u} A C (op ⦋n⦌))
    (congrArg (fun φ : (standardResolution.{u, u} A B).left.obj (op ⦋n⦌) →+*
        (standardResolution.{u, u} A C).left.obj (op ⦋n⦌) => φ p)
      (standardResolutionSquareMap_idSquare f (op ⦋n⦌)).symm)

/-- **The first displayed morphism at chain level.** The identification
`CommAlgCat.cotangentDifferentialComplexesX₁Iso` of the first term of the differential short
complex of Tag 08SD with the degreewise extension of scalars of `L_{B/A}`, followed by the
functoriality map of Tag 08PN after extension of scalars, is the first map of the differential
sequence of Tag 08SD. -/
theorem cotangentDifferentialComplexesX₁Iso_hom_comp (f : B ⟶ C) :
    (cotangentDifferentialComplexesX₁Iso A f).hom ≫
        cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := B) (B' := C) f.hom =
      (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
        (differentialSequenceFirstMap A f) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} ↥C)).map
          (((alternatingFaceMapComplexCompMapHomologicalComplexIso
              (ModuleCat.extendScalars f.hom.toRingHom)).app
            (cotangentSimplicialModule.{u, u} A B).object).inv) ≫ z)
      (Iso.hom_inv_id_assoc _ _)) ?_
  refine Eq.trans (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
      (ModuleCat.{u} ↥C)).map_comp _ _).symm ?_
  exact congrArg
    (fun z => ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} ↥C)).map z)
    (cotangentExtendScalarsMooreMap_eq_differentialSequenceFirstMap f)

end Chain

section Second

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

/-- **The degreewise identity behind the second identification.** In simplicial degree `n`, the
quotient `Ω[Q_n⁄A] ⊗ C ⟶ Ω[Q̄_n⁄B] ⊗ C` of the differential sequence of Tag 08SD followed by the
comparison induced by `Q̄_• ⟶ R̄_•` agrees with the functoriality map of the change of base ring
followed by the comparison induced by `R_• ⟶ R̄_•`: both carry the pure differential `1 ⊗ d q` to
`1 ⊗ d (δ (v q))`, for `v : Q_n → R_n` the variables-to-variables map of the change of base ring
and `δ : R_n → R̄_n` the pushout leg. -/
theorem differentialSequenceSecondComponent_comp_baseChangedComparison (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) (q : (standardResolution A C).left.obj n) :
    overDifferentialsFunctor.map
        ((resolutionOverMap (baseChangedStandardResolution A f).hom (relativeBaseChange f).hom
          (baseChangedComparison f) (baseChangedComparison_comp_hom f)).app n)
        (differentialSequenceSecondComponent A f n (cotangentTermDifferential A C n q)) =
      overDifferentialsFunctor.map
        ((resolutionOverMap (standardResolution ↥B (algebraOver f)).hom (relativeBaseChange f).hom
          (relativeBaseChangeLeg f) (relativeBaseChangeLeg_comp_hom f)).app n)
        (squareCotangentTermMap.{u, u, u} (baseRingSquareTop f) n
          (cotangentTermDifferential A C n q)) := by
  refine Eq.trans (congrArg (fun z => overDifferentialsFunctor.map
      ((resolutionOverMap (baseChangedStandardResolution A f).hom (relativeBaseChange f).hom
        (baseChangedComparison f) (baseChangedComparison_comp_hom f)).app n) z)
      (differentialSequenceSecondComponent_differential' A f n q)) ?_
  refine Eq.trans (overDifferentialsFunctor_map_mk
      ((resolutionOverMap (baseChangedStandardResolution A f).hom (relativeBaseChange f).hom
        (baseChangedComparison f) (baseChangedComparison_comp_hom f)).app n)
      (canonicalBaseChangeMap A f n q)) ?_
  refine Eq.trans ?_ (congrArg (fun z => overDifferentialsFunctor.map
      ((resolutionOverMap (standardResolution ↥B (algebraOver f)).hom (relativeBaseChange f).hom
        (relativeBaseChangeLeg f) (relativeBaseChangeLeg_comp_hom f)).app n) z)
      (squareCotangentTermMap_D (baseRingSquareTop f) n q)).symm
  refine Eq.trans ?_ (overDifferentialsFunctor_map_mk
      ((resolutionOverMap (standardResolution ↥B (algebraOver f)).hom (relativeBaseChange f).hom
        (relativeBaseChangeLeg f) (relativeBaseChangeLeg_comp_hom f)).app n)
      (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n q)).symm
  exact congrArg (overDifferentialsMk ((resolutionOver (relativeBaseChange f).hom).obj n))
    ((baseChangedComparison_apply f n q).trans
      (relativeBaseChangeLeg_apply f n
        (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n q)).symm)

/-- The second map of the differential sequence of Tag 08SD, followed by the comparison
`Ω[Q̄_•⁄B] ⊗ C ⟶ Ω[R̄_•⁄B] ⊗ C` induced by the canonical map `Q̄_• ⟶ R̄_•` of Remark 08SE: a map of
simplicial `C`-modules out of `Ω[Q_•⁄A] ⊗ C`. -/
def differentialSequenceSecondComparison (f : B ⟶ C) :
    (cotangentSimplicialModule.{u, u} A C).object ⟶
      resolutionOver (relativeBaseChange f).hom ⋙ overDifferentialsFunctor :=
  differentialSequenceSecondMap A f ≫
    Functor.whiskerRight (resolutionOverMap (baseChangedStandardResolution A f).hom
      (relativeBaseChange f).hom (baseChangedComparison f)
      (baseChangedComparison_comp_hom f)) overDifferentialsFunctor

/-- **The functoriality map of Tag 08PN for the change of base ring from `A` to `B`**, read
between the two cotangent simplicial modules: restriction of scalars along the identity of `C` is
the identity functor, so `CommAlgCat.squareCotangentSimplicialMap` at the square
`CommAlgCat.baseRingSquareTop` needs no comparison isomorphism to be read this way. -/
def baseRingCotangentSimplicialMap (f : B ⟶ C) :
    (cotangentSimplicialModule.{u, u} A C).object ⟶
      (cotangentSimplicialModule.{u, u} ↥B (algebraOver f)).object :=
  squareCotangentSimplicialMap.{u, u, u} (baseRingSquareTop f)

/-- The functoriality map of Tag 08PN for the change of base ring from `A` to `B`, followed by the
comparison `L_{C/B} = Ω[R_•⁄B] ⊗ C ⟶ Ω[R̄_•⁄B] ⊗ C` induced by the pushout leg `R_• ⟶ R̄_•` of
Remark 08SE: the other map of simplicial `C`-modules out of `Ω[Q_•⁄A] ⊗ C`. -/
def baseRingCotangentComparison (f : B ⟶ C) :
    (cotangentSimplicialModule.{u, u} A C).object ⟶
      resolutionOver (relativeBaseChange f).hom ⋙ overDifferentialsFunctor :=
  baseRingCotangentSimplicialMap f ≫
    Functor.whiskerRight (resolutionOverMap (standardResolution ↥B (algebraOver f)).hom
      (relativeBaseChange f).hom (relativeBaseChangeLeg f)
      (relativeBaseChangeLeg_comp_hom f)) overDifferentialsFunctor

/-- **The two maps of simplicial `C`-modules into `Ω[R̄_•⁄B] ⊗ C` agree.** In each simplicial
degree this is `CommAlgCat.differentialSequenceSecondComponent_comp_baseChangedComparison`: both
sides carry the pure differential `1 ⊗ d q` to `1 ⊗ d (δ (v q))`. -/
theorem differentialSequenceSecondComparison_eq (f : B ⟶ C) :
    differentialSequenceSecondComparison f = baseRingCotangentComparison f := by
  refine NatTrans.ext (funext fun n => ?_)
  refine cotangentTerm_hom_ext.{u, u} A C n _ _ fun q => ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  exact differentialSequenceSecondComponent_comp_baseChangedComparison f n q

/-- The functoriality map of Tag 08PN for the change of base ring, read on complexes, is the
reindexed Moore complex of `CommAlgCat.baseRingCotangentSimplicialMap`: the two comparison
isomorphisms that `CommAlgCat.squareCotangentComplexMap` interposes are the identity, because
restriction of scalars along the identity of `C` is the identity functor. -/
private theorem squareCotangentComplexMap_eq_map_cochain (f : B ⟶ C) :
    (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
          (baseRingCotangentSimplicialMap f) =
      squareCotangentComplexMap.{u, u, u} (baseRingSquareTop f) := by
  symm
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rcases h : (ComplexShape.embeddingUpIntLE (0 : ℤ)).r i with _ | a
  · exact (HomologicalComplex.isZero_extend_X' _ _ i h).eq_of_src _ _
  · have hfa : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f a = i :=
      (ComplexShape.embeddingUpIntLE (0 : ℤ)).f_eq_of_r_eq_some h
    have hi : i = -(a : ℤ) := hfa.symm.trans (by simp)
    subst hi
    refine Eq.trans (squareCotangentComplexMap_f.{u, u, u} (baseRingSquareTop f) a) ?_
    exact (HomologicalComplex.extendMap_f
      ((alternatingFaceMapComplex (ModuleCat.{u} ↥C)).map (baseRingCotangentSimplicialMap f))
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) hfa).symm

end Second

section Derived

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

attribute [local instance] HasDerivedCategory.standard

/-- The identification of `L_{C/B}` with the complex of the standard resolution of `C` over `B`
is the identity: `CommAlgCat.overDifferentialsFunctor` evaluated on the standard resolution *is*
the cotangent simplicial module of Tag 08PN. -/
private theorem standardCotangentComplexIso_inv_eq_id (f : B ⟶ C) :
    (standardCotangentComplexIso f).inv = 𝟙 _ :=
  (congrArg ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
        (ModuleCat.{u} ↥(algebraOver f))).map
      ((alternatingFaceMapComplex (ModuleCat.{u} ↥(algebraOver f))).map_id _)).trans
    (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
      (ModuleCat.{u} ↥(algebraOver f))).map_id _)

/-- The first arrow of the comparison of Remark 08SE is the reindexed Moore complex of the map
induced by the pushout leg `R_• ⟶ R̄_•`. -/
private theorem relativeBaseChangeCotangentLeg_eq (f : B ⟶ C) :
    relativeBaseChangeCotangentLeg f =
      (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
        (Functor.whiskerRight (resolutionOverMap (standardResolution ↥B (algebraOver f)).hom
          (relativeBaseChange f).hom (relativeBaseChangeLeg f)
          (relativeBaseChangeLeg_comp_hom f)) overDifferentialsFunctor) :=
  (congrArg (fun z => z ≫ (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
        (Functor.whiskerRight (resolutionOverMap (standardResolution ↥B (algebraOver f)).hom
          (relativeBaseChange f).hom (relativeBaseChangeLeg f)
          (relativeBaseChangeLeg_comp_hom f)) overDifferentialsFunctor))
      (standardCotangentComplexIso_inv_eq_id f)).trans (Category.id_comp _)

/-- **The chain-level identity behind the second morphism.** The second map of the differential
sequence of Tag 08SD followed by the comparison induced by `Q̄_• ⟶ R̄_•` is the functoriality map
of Tag 08PN for the change of base ring followed by the comparison induced by `R_• ⟶ R̄_•`, as a
map of complexes of `C`-modules. This is
`CommAlgCat.differentialSequenceSecondComparison_eq` pushed through the reindexed Moore
complex. -/
theorem secondMap_comp_baseChangedCotangentComparison (f : B ⟶ C) :
    (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
          (differentialSequenceSecondMap A f) ≫ baseChangedCotangentComparison f =
      (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
          (baseRingCotangentSimplicialMap f) ≫ relativeBaseChangeCotangentLeg f := by
  have h₁ : (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
        (differentialSequenceSecondComparison f) =
      (alternatingFaceMapCochainComplex (ModuleCat.{u} ↥C)).map
        (baseRingCotangentComparison f) :=
    congrArg _ (differentialSequenceSecondComparison_eq f)
  refine Eq.trans ?_ (Eq.trans h₁ ?_)
  · exact (Functor.map_comp _ _ _).symm
  · exact (Functor.map_comp _ _ _).trans
      (congrArg (_ ≫ ·) (relativeBaseChangeCotangentLeg_eq f).symm)

/-- **The second morphism of the triangle of Tag 08SD, read through the identification of
Remark 08SE, is the functoriality map of the change of base ring.** The identification of
Remark 08SE is pinned down by its composite with the first arrow of the comparison
(`CommAlgCat.baseChangedCotangentComplexIso_hom_comp`), and that arrow is an isomorphism in
`D(C)`, so the chain-level identity
`CommAlgCat.secondMap_comp_baseChangedCotangentComparison` determines the composite outright. -/
theorem cotangentTriangle_mor₂_comp_baseChangedCotangentComplexIso (f : B ⟶ C)
    (hf : Function.Injective f.hom)
    (hεQ : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A f).hom (forget (CommAlgCat.{u} ↥B))))
    (hεR : SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B)))) :
    (cotangentTriangle A f hf).mor₂ ≫ (baseChangedCotangentComplexIso f hf hεQ hεR).hom =
      DerivedCategory.Q.map (squareCotangentComplexMap.{u, u, u} (baseRingSquareTop f)) := by
  refine Eq.trans ?_
    (congrArg DerivedCategory.Q.map (squareCotangentComplexMap_eq_map_cochain f))
  have : IsIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f)) :=
    isIso_q_relativeBaseChangeCotangentLeg f hf hεR
  refine (cancel_mono (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f))).1 ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg ((cotangentTriangle A f hf).mor₂ ≫ ·)
    (baseChangedCotangentComplexIso_hom_comp f hf hεQ hεR)) ?_
  exact (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map (secondMap_comp_baseChangedCotangentComparison f)).trans
      (DerivedCategory.Q.map_comp _ _))

end Derived

/-! ### The displayed triangle -/

section Tower

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

attribute [local instance] HasDerivedCategory.standard

/-- `L_{C/B}` formed along the map `B → C` of `CommAlgCat.algebraOver` is the display's third
vertex: two algebra structures with the same structure map are equal. -/
theorem q_cotangentComplex_algebraOver_eq :
    DerivedCategory.Q.obj
        (cotangentComplex.{u, u} B (algebraOver (towerHom A B C))) =
      fundamentalVertex₃.{u, u, u + 1} B C :=
  let F : Algebra B C → DerivedCategory (ModuleCat.{u} C) :=
    fun i => DerivedCategory.Q.obj (cotangentComplex.{u, u} B (@CommAlgCat.of B _ C _ i))
  congrArg F (Algebra.algebra_ext _ _ fun _ => rfl)

/-- **The third vertex of the triangle of Tag 08SD is the display's third vertex `L_{C/B}`**, by
the identification of Remark 08SE, for `B → C` injective. -/
def fundamentalDisplayVertex₃Iso (hf : Function.Injective (algebraMap B C)) :
    (cotangentTriangle A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf)).obj₃ ≅
      fundamentalVertex₃.{u, u, u + 1} B C :=
  baseChangedCotangentComplexIsoOfInjective (towerHom A B C)
      (show Function.Injective (towerHom A B C).hom from hf) ≪≫
    eqToIso (q_cotangentComplex_algebraOver_eq A B C)

/-- **The third displayed morphism** `L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)⟦1⟧` of the triangle of
Tag 08QS, on the display's own two vertices: the connecting morphism of the triangle of Tag 08SD,
transported along `CommAlgCat.cotangentTriangle_obj₁DerivedBaseChangeIso` and
`CommAlgCat.fundamentalDisplayVertex₃Iso`.

The injectivity of `B → C` is Tag 08SD's own hypothesis, and Tag 08QS assumes nothing, so the
`@[stacks 08QS]` registration of the third displayed morphism sits on
`CommAlgCat.productFundamentalMor₃` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, which assumes nothing either. -/
def fundamentalMor₃ (hf : Function.Injective (algebraMap B C)) :
    fundamentalVertex₃.{u, u, u + 1} B C ⟶
      (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C)⟦(1 : ℤ)⟧ :=
  (fundamentalDisplayVertex₃Iso A B C hf).inv ≫
    (cotangentTriangle A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf)).mor₃ ≫
      ((cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf)).hom)⟦(1 : ℤ)⟧'

/-- The second morphism of the triangle of Tag 08SD, read between the display's second and third
vertices. It **is** the display's own `CommAlgCat.fundamentalMor₂`, by
`CommAlgCat.fundamentalDisplayMor₂_eq_fundamentalMor₂`. -/
def fundamentalDisplayMor₂ (hf : Function.Injective (algebraMap B C)) :
    fundamentalVertex₂.{u, u, u + 1} A C ⟶ fundamentalVertex₃.{u, u, u + 1} B C :=
  (cotangentTriangle A (towerHom A B C)
      (show Function.Injective (towerHom A B C).hom from hf)).mor₂ ≫
    (fundamentalDisplayVertex₃Iso A B C hf).hom

/-- Two commutative squares of ring maps with the same two maps are equal. -/
private theorem algebraSquare_ext' {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    {D : CommAlgCat.{u} R} {X : CommAlgCat.{u} R'}
    {sq sq' : AlgebraSquare.{u, u, u} R R' D X}
    (hb : sq.base = sq'.base) (hm : sq.map = sq'.map) : sq = sq' := by
  obtain ⟨b, m, hbm⟩ := sq
  obtain ⟨b', m', hbm'⟩ := sq'
  subst hb
  subst hm
  rfl

/-- The functoriality map of a square of ring maps depends on the square's target algebra only
through the square: two squares with the same two maps whose targets are equal induce the same
map of cotangent complexes, up to the transport along that equality. -/
private theorem heq_squareCotangentComplexMap {R : Type u} [CommRing R] {R' : Type u}
    [CommRing R'] {D : CommAlgCat.{u} R} {X Y : CommAlgCat.{u} R'} (h : X = Y)
    (sq : AlgebraSquare.{u, u, u} R R' D X) (sq' : AlgebraSquare.{u, u, u} R R' D Y)
    (hb : sq.base = sq'.base) (hm : sq.map ≍ sq'.map) :
    squareCotangentComplexMap.{u, u, u} sq ≍ squareCotangentComplexMap.{u, u, u} sq' := by
  subst h
  obtain rfl := algebraSquare_ext' (sq := sq) (sq' := sq') hb (eq_of_heq hm)
  rfl

/-- The complex of the standard resolution of `C` over `B` formed along the map `B → C` of
`CommAlgCat.algebraOver` is the complex of `L_{C/B}`: two algebra structures with the same
structure map are equal. -/
private theorem cotangentComplex_algebraOver_eq :
    cotangentComplex.{u, u} ↥(CommAlgCat.of A B) (algebraOver (towerHom A B C)) =
      cotangentComplex.{u, u} B (CommAlgCat.of B C) :=
  let F : Algebra B C → CochainComplex (ModuleCat.{u} C) ℤ :=
    fun i => cotangentComplex.{u, u} B (@CommAlgCat.of B _ C _ i)
  congrArg F (Algebra.algebra_ext _ _ fun _ => rfl)

/-- **The functoriality map of the change of base ring, read at the augmentation point of the
base-changed resolution, is the chain-level second displayed morphism.** The two squares
`CommAlgCat.baseRingSquareTop` at `A → B → C` and `CommAlgCat.displaySquare₂` have the same base
map `A → B` and the same map `𝟙_C`; they differ only in which of the two equal `B`-algebra
structures on `C` their target carries. -/
private theorem squareCotangentComplexMap_baseRingSquareTop_eq :
    squareCotangentComplexMap.{u, u, u} (baseRingSquareTop (towerHom A B C)) ≫
        eqToHom (cotangentComplex_algebraOver_eq A B C) =
      cotangentComplexBaseRingMap A B C :=
  eq_of_heq ((comp_eqToHom_heq _ (cotangentComplex_algebraOver_eq A B C)).trans
    (heq_squareCotangentComplexMap (baseChangedStandardResolution_right_eq A B C)
      (baseRingSquareTop (towerHom A B C)) (displaySquare₂ A B C) rfl HEq.rfl))

/-- The same identity in `D(C)`: the transport of the functoriality map of the change of base ring
along the identification of the two `B`-algebra structures on `C` is the display's second
morphism `CommAlgCat.fundamentalMor₂`. -/
private theorem q_map_squareCotangentComplexMap_baseRingSquareTop_eq :
    DerivedCategory.Q.map
          (squareCotangentComplexMap.{u, u, u} (baseRingSquareTop (towerHom A B C))) ≫
        eqToHom (q_cotangentComplex_algebraOver_eq A B C) =
      fundamentalMor₂.{u} A B C := by
  refine Eq.trans (congrArg (fun z => DerivedCategory.Q.map
        (squareCotangentComplexMap.{u, u, u} (baseRingSquareTop (towerHom A B C))) ≫ z)
      (eqToHom_map DerivedCategory.Q (cotangentComplex_algebraOver_eq A B C)).symm) ?_
  refine Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_
  exact congrArg DerivedCategory.Q.map (squareCotangentComplexMap_baseRingSquareTop_eq A B C)

/-- **The second morphism of the assembled triangle is the display's own second morphism.** The
second morphism of the triangle of Tag 08SD, read between the display's second and third vertices
through the identification of Remark 08SE, is the functoriality map
`CommAlgCat.fundamentalMor₂` of Tag 08PN for the square `(A → B, 𝟙_C)`.

This is `CommAlgCat.cotangentTriangle_mor₂_comp_baseChangedCotangentComplexIso`, whose content is
the degreewise identity
`CommAlgCat.differentialSequenceSecondComponent_comp_baseChangedComparison`, followed by the
transport between the two equal `B`-algebra structures on `C`. -/
theorem fundamentalDisplayMor₂_eq_fundamentalMor₂ (hf : Function.Injective (algebraMap B C)) :
    fundamentalDisplayMor₂ A B C hf = fundamentalMor₂.{u} A B C := by
  have hf' : Function.Injective (towerHom A B C).hom := hf
  have hd := cotangentTriangle_mor₂_comp_baseChangedCotangentComplexIso (towerHom A B C) hf'
    (trivialKanFibrations_baseChangedStandardResolution_of_injective (towerHom A B C) hf')
    (trivialKanFibrations_relativeBaseChange_of_injective (towerHom A B C) hf')
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine eq_of_heq ((comp_eqToHom_heq _ (q_cotangentComplex_algebraOver_eq A B C)).trans ?_)
  refine (heq_of_eq hd).trans ?_
  exact (comp_eqToHom_heq _ (q_cotangentComplex_algebraOver_eq A B C)).symm.trans
    (heq_of_eq (q_map_squareCotangentComplexMap_baseRingSquareTop_eq A B C))

/-- Three isomorphisms onto the objects of a distinguished triangle, together with the
identification of the conjugates of its first two morphisms, give a distinguished triangle on the
three targets with those two morphisms for its first two. -/
lemma distTriang_of_iso_eq {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
    {X Y Z : D} (T : Triangle D) (hT : T ∈ distTriang D)
    (d₁ : T.obj₁ ≅ X) (d₂ : T.obj₂ ≅ Y) (d₃ : T.obj₃ ≅ Z) {α : X ⟶ Y} {β : Y ⟶ Z}
    (hα : d₁.inv ≫ T.mor₁ ≫ d₂.hom = α) (hβ : d₂.inv ≫ T.mor₂ ≫ d₃.hom = β) :
    Triangle.mk α β (d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦(1 : ℤ)⟧') ∈ distTriang D := by
  subst hα
  subst hβ
  exact isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ d₁.symm d₂.symm d₃.symm (by simp) (by simp) (by simp))

/-- **The first morphism of the triangle of Tag 08SD is the first displayed morphism.** Read out
of the display's first vertex `L_{B/A} ⊗^𝐋_B C` through
`CommAlgCat.cotangentTriangle_obj₁DerivedBaseChangeIso`, the first morphism of the triangle of
Tag 08SD is the functoriality map `CommAlgCat.fundamentalMor₁` of Tag 08PN. -/
theorem cotangentTriangle_mor₁_eq_fundamentalMor₁ (hf : Function.Injective (algebraMap B C)) :
    (cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C)
          (show Function.Injective (towerHom A B C).hom from hf)).inv ≫
        (cotangentTriangle A (towerHom A B C)
          (show Function.Injective (towerHom A B C).hom from hf)).mor₁ =
      fundamentalMor₁.{u} A B C := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (towerHom A B C).hom.toRingHom).comparison.app
            (cotangentComplex.{u, u} A (CommAlgCat.of A B)) ≫ z)
      (DerivedCategory.Q.map_comp
        (cotangentDifferentialComplexesX₁Iso A (towerHom A B C)).inv
        ((alternatingFaceMapCochainComplex (ModuleCat.{u} C)).map
          (differentialSequenceFirstMap A (towerHom A B C)))).symm) ?_
  exact congrArg (fun z =>
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (towerHom A B C).hom.toRingHom).comparison.app
            (cotangentComplex.{u, u} A (CommAlgCat.of A B)) ≫ DerivedCategory.Q.map z)
    ((Iso.inv_comp_eq _).2
      (cotangentDifferentialComplexesX₁Iso_hom_comp (towerHom A B C)).symm)

/-- **The displayed triangle of Tag 08QS, on its own three vertices and with its own first two
morphisms, is distinguished — for `B → C` injective.** Let `A → B → C` be ring maps with `B → C`
injective. Then

`L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`

is a distinguished triangle in `D(C)` whose first morphism is the display's own
`CommAlgCat.fundamentalMor₁` and whose second is the display's own
`CommAlgCat.fundamentalMor₂` — the two functoriality maps of Tag 08PN for the two commutative
squares of the tower — and whose third morphism is `CommAlgCat.fundamentalMor₃`, out of the
display's third vertex `L_{C/B}` and into the display's `(L_{B/A} ⊗^𝐋_B C)⟦1⟧`.

The injectivity of `B → C` is Tag 08SD's own hypothesis, and Tag 08QX assumes nothing, so the
`@[stacks 08QX]` registration sits on `CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, which is this statement for arbitrary
`A → B → C`, obtained from this one by the passage to `A → B → B × C` of Remark 08SD and the
product decomposition of Tag 08SC. -/
theorem fundamentalTriangle_distinguished (hf : Function.Injective (algebraMap B C)) :
    Triangle.mk (fundamentalMor₁.{u} A B C) (fundamentalMor₂.{u} A B C)
        (fundamentalMor₃ A B C hf) ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) := by
  refine distTriang_of_iso_eq _
    (cotangentTriangle_distinguished A (towerHom A B C)
      (show Function.Injective (towerHom A B C).hom from hf))
    (cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C)
      (show Function.Injective (towerHom A B C).hom from hf))
    (Iso.refl _) (fundamentalDisplayVertex₃Iso A B C hf) ?_ ?_
  · refine Eq.trans (congrArg (fun z =>
      (cotangentTriangle_obj₁DerivedBaseChangeIso A (towerHom A B C)
        (show Function.Injective (towerHom A B C).hom from hf)).inv ≫ z)
        (Category.comp_id _)) ?_
    exact cotangentTriangle_mor₁_eq_fundamentalMor₁ A B C hf
  · exact (Category.id_comp _).trans (fundamentalDisplayMor₂_eq_fundamentalMor₂ A B C hf)

end Tower

end CommAlgCat

end
