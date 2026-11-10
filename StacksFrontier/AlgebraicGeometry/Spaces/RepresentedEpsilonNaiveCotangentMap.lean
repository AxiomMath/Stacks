module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentToposModel
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiNaiveCotangentCompare
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPushforward

/-!
# The canonical map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` of Stacks 0D0X

Let `S` be a scheme, let `φ : U ⟶ V` be a morphism of objects of the big fppf site over `S`, let
`f₀ : X₀ ⟶ Y₀` be the morphism of the underlying schemes, and let `X = h_U`, `Y = h_V` be the
algebraic spaces they represent, `f = h_φ`.  Write `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X₀})` for
the comparison morphism of Stacks 08H7, presented by the continuous functor
`AlgebraicGeometry.Space.representedEpsilonFunctor` reading a Zariski open of `X₀` as an étale
chart of `X`.

This file constructs the canonical map of Stacks 0D0X,

`ε^* NL_{𝒪_{X₀} / f_0^{-1}𝒪_{Y₀}} ⟶ NL_{X/Y}`,

of complexes of sheaves of `𝒪_X`-modules with sections in `Type (u + 1)`, as the adjunct, under
`ε^* ⊣ ε_*` (`AlgebraicGeometry.Space.representedEpsilonModuleAdjunction`), of the composite

`NL_{𝒪_{X₀} / f_0^{-1}𝒪_{Y₀}} ⟶ NL_{ε_*𝒪_X / ε_*f^{-1}𝒪_Y} ⟶ ε_* NL_{𝒪_X / f^{-1}𝒪_Y}`

of the chain map of Stacks 08TX attached to the square of sheaves of commutative rings on the
Zariski site of `X₀`

```
𝒪_{X₀} ──────ε^♯──────▸ ε_*𝒪_X
  ▲                       ▲
  │ f_0^♯                 │ ε_*(f^♯)
f_0^{-1}𝒪_{Y₀} ────────▸ ε_*f^{-1}𝒪_Y
```

with the comparison `Stacks.SheafOfModules.naiveCotangentComplexPushforwardMap` of the naive
cotangent complex along a continuous functor.  The bottom edge is the adjunct of the
identification `ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ f^{-1}𝒪_Y` of the square of ringed topoi of Stacks 08GH
(`AlgebraicGeometry.Space.representedEpsilonBaseRingMap`), and the square commutes because its
adjunct is the square `AlgebraicGeometry.Space.representedEpsilonNaiveCotangentSquare_commutes`.

## Main definitions

* `AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct`: the bottom edge of the square.
* `AlgebraicGeometry.Space.representedZariskiToposNaiveCotangentComplex`:
  `NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}}` with module sections in `Type (u + 1)`, `f_0^{-1}𝒪_{Y₀}` being the
  inverse image of sheaves of commutative rings along the morphism of Zariski topoi of `f₀`.
* `AlgebraicGeometry.Space.representedEpsilonNaiveCotangentPushforwardMap`: the composite
  `NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}} ⟶ ε_* NL_{X/Y}`.
* `AlgebraicGeometry.Space.representedEpsilonNaiveCotangentMap`: its adjunct
  `ε^* NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}} ⟶ NL_{X/Y}`.
* `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexIso`: the source complex is the
  universe lift of `NL_{X₀/Y₀}` of Stacks 0D0H.

## Main results

* `AlgebraicGeometry.Space.representedEpsilonPushforwardSquare_commutes`: the square commutes.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- `ε_*` on sheaves of commutative rings, in its site form: restriction along
`AlgebraicGeometry.Space.representedEpsilonFunctor`. -/
abbrev representedEpsilonCommRingPushforward (U : BigFppfOver B S hS) :
    Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J CommRingCat.{u} ⥤
      Sheaf ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J CommRingCat.{u} :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (representedEpsilonFunctor B S hS U) CommRingCat.{u}
    _ _ _ (isContinuous_representedEpsilonFunctor B S hS U)

/-- **The bottom edge `f_0^{-1}𝒪_{Y₀} ⟶ ε_*f^{-1}𝒪_Y`** of the square on the Zariski site of
`X₀`: the adjunct, under `ε⁻¹ ⊣ ε_*` on sheaves of commutative rings, of
`AlgebraicGeometry.Space.representedEpsilonBaseRingMap`, read in the site form of `ε_*`. -/
def representedEpsilonBaseRingAdjunct :
    (inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ⟶
      (representedEpsilonCommRingPushforward B S hS U).obj
        ((inverseImageCommRingFunctor
            (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O) :=
  ((commRingImageAdjunction (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).homEquiv
      _ _ (representedEpsilonBaseRingMap B S hS φ)) ≫
    (@restrictionCommRingIso _ _ _ _ ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J _
      (representedEpsilonFunctor B S hS U) (isContinuous_representedEpsilonFunctor B S hS U)
      ((inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).hom

/-- **A square transported along an adjunction**, over abstract objects of abstract categories.
If `L.map p ≫ s♭ = g ≫ h` for the adjunct `s♭` of `s : X ⟶ R(P)`, then `p ≫ s = g♯ ≫ R(h)`, and
the same after composing with a comparison `ι` of `R` with another functor `G` which is natural
at `h`. -/
theorem comp_eq_of_adjunct_square {D₀ D : Type*} [Category D₀] [Category D] {L : D₀ ⥤ D}
    {R : D ⥤ D₀} (adj : L ⊣ R) {A X : D₀} {Q P : D} (p : A ⟶ X) (s : X ⟶ R.obj P)
    (g : L.obj A ⟶ Q) (h : Q ⟶ P) {GQ GP : D₀} (ιQ : R.obj Q ⟶ GQ) (ιP : R.obj P ⟶ GP)
    (Gh : GQ ⟶ GP) (hnat : ιQ ≫ Gh = R.map h ≫ ιP)
    (key : L.map p ≫ (adj.homEquiv _ _).symm s = g ≫ h) :
    p ≫ (s ≫ ιP) = (adj.homEquiv _ _ g ≫ ιQ) ≫ Gh := by
  have hps : p ≫ s = adj.homEquiv _ _ g ≫ R.map h := by
    rw [← adj.homEquiv_naturality_right, ← key, adj.homEquiv_naturality_left,
      Equiv.apply_symm_apply]
  rw [← Category.assoc, hps, Category.assoc, Category.assoc, hnat]

/-- **The square on the Zariski site of `X₀` commutes**: `f_0^♯` followed by `ε^♯` is the bottom
edge `AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct` followed by `ε_*(f^♯)`. -/
theorem representedEpsilonPushforwardSquare_commutes :
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage ≫
        (representedToZariskiRingedToposSiteHom B S hS U).fSharp =
      representedEpsilonBaseRingAdjunct B S hS φ ≫
        (representedEpsilonCommRingPushforward B S hS U).map
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage :=
  comp_eq_of_adjunct_square
    (commRingImageAdjunction (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom)
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage
    (representedToSchemeZariskiRingedToposHom B S hS U).fSharp
    (representedEpsilonBaseRingMap B S hS φ)
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage
    (@restrictionCommRingIso.{u} _ _ _ _ _ _ _ (representedEpsilonFunctor B S hS U)
      (isContinuous_representedEpsilonFunctor B S hS U) _).hom
    (@restrictionCommRingIso.{u} _ _ _ _ _ _ _ (representedEpsilonFunctor B S hS U)
      (isContinuous_representedEpsilonFunctor B S hS U) _).hom
    ((representedEpsilonCommRingPushforward B S hS U).map
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage)
    (@restrictionCommRingIso_naturality _ _ _ _
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J _ _ _
      (representedEpsilonFunctor B S hS U) (isContinuous_representedEpsilonFunctor B S hS U) _ _
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage).symm
    (representedEpsilonNaiveCotangentSquare_commutes B S hS φ)

/-- **`NL_{𝒪_{X₀} / f_0^{-1}𝒪_{Y₀}}` with module sections in `Type (u + 1)`**, on the Zariski site
of `X₀`, for `f_0^{-1}𝒪_{Y₀}` the inverse image of sheaves of commutative rings along the
morphism of Zariski topoi of `f₀` and `f_0^♯` the structure map of `f₀` in inverse-image form. -/
def representedZariskiToposNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u + 1}
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
    ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage

/-- `NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}}` with module sections in `Type (u + 1)` is the topos model
`AlgebraicGeometry.Scheme.Hom.toposNaiveCotangentComplex` of `NL_{X₀/Y₀}` for `f₀`. -/
theorem representedZariskiNaiveCotangentComplex_eq :
    representedZariskiToposNaiveCotangentComplex B S hS φ =
      Scheme.Hom.toposNaiveCotangentComplex.{u + 1} ((BigFppfOver.toScheme B S hS).map φ) :=
  rfl

/-- **`NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}}` with module sections in `Type (u + 1)` is the universe lift of
`NL_{X₀/Y₀}`** of Stacks 0D0H (`AlgebraicGeometry.Scheme.naiveCotangentComplex`):
`AlgebraicGeometry.Scheme.Hom.toposNaiveCotangentComplexULiftIso` for `f₀`. -/
def representedZariskiNaiveCotangentComplexIso :
    representedZariskiToposNaiveCotangentComplex B S hS φ ≅
      ((_root_.SheafOfModules.uliftFunctor.{u, u, u, u, u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (Scheme.naiveCotangentComplex ((BigFppfOver.toScheme B S hS).map φ)) :=
  Scheme.Hom.toposNaiveCotangentComplexULiftIso ((BigFppfOver.toScheme B S hS).map φ)

/-- **`NL_{X/Y}`, written out**: the naive cotangent complex, on the small étale site of `X`, of
the structure map of `f_{small}` in inverse-image form.  This is
`AlgebraicGeometry.Space.naiveCotangentComplex` of `h_φ`
(`AlgebraicGeometry.Space.representedSpaceNaiveCotangentComplex_eq`). -/
abbrev representedSpaceNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    ((inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage

/-- **The chain map `NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}} ⟶ ε_* NL_{X/Y}`**: the chain map of Stacks 08TX
attached to the square `AlgebraicGeometry.Space.representedEpsilonPushforwardSquare_commutes`,
into `NL_{ε_*𝒪_X / ε_*f^{-1}𝒪_Y}`, followed by the comparison
`Stacks.SheafOfModules.naiveCotangentComplexPushforwardMap` of the naive cotangent complex along
the continuous functor `AlgebraicGeometry.Space.representedEpsilonFunctor`. -/
def representedEpsilonNaiveCotangentPushforwardMap :
    representedZariskiToposNaiveCotangentComplex B S hS φ ⟶
      ((representedEpsilonModulePushforward B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (representedSpaceNaiveCotangentComplex B S hS φ) :=
  @Stacks.SheafOfModules.naiveCotangentComplexPushforwardSquareMap.{u, u, u, u + 1, u, u}
    _ _ _ _
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (representedEpsilonFunctor B S hS U) (isContinuous_representedEpsilonFunctor B S hS U)
    _ _ _
    ((inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).fSharpInverseImage
    ((inverseImageCommRingFunctor (representedZariskiSchemeHom B S hS φ).toToposHom).obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage
    (representedEpsilonBaseRingAdjunct B S hS φ)
    (representedToZariskiRingedToposSiteHom B S hS U).fSharp
    (representedEpsilonPushforwardSquare_commutes B S hS φ)

/-- Sheafification of abelian presheaves with sections in `Type (u + 1)` on the Zariski site of
`X₀`. -/
instance hasSheafify_representedZariski_addCommGrpCat (U : BigFppfOver B S hS) :
    HasSheafify ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
      AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _

/-- Weak equivalences of abelian presheaves with sections in `Type (u + 1)` on the Zariski site
of `X₀` are the locally bijective morphisms. -/
instance wEqualsLocallyBijective_representedZariski_addCommGrpCat (U : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J.WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _

/-- **The canonical map `ε^* NL_{𝒪_{X₀}/f_0^{-1}𝒪_{Y₀}} ⟶ NL_{X/Y}` of Stacks 0D0X**, of complexes
of sheaves of `𝒪_X`-modules with sections in `Type (u + 1)`: the adjunct, under the termwise
adjunction `ε^* ⊣ ε_*` of Stacks 03D7, of
`AlgebraicGeometry.Space.representedEpsilonNaiveCotangentPushforwardMap`. -/
def representedEpsilonNaiveCotangentMap :
    ((representedEpsilonModulePullback B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (representedZariskiToposNaiveCotangentComplex B S hS φ) ⟶
      representedSpaceNaiveCotangentComplex B S hS φ :=
  ((@Adjunction.mapHomologicalComplex _ _ _
      (SheafOfModules.instAbelian.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)) _
      (SheafOfModules.instAbelian.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O))
      _ _ _ _ (representedEpsilonModuleAdjunction B S hS U) _
      (ComplexShape.up ℤ)).homEquiv _ _).symm
    (representedEpsilonNaiveCotangentPushforwardMap B S hS φ)

end AlgebraicGeometry.Space

end

