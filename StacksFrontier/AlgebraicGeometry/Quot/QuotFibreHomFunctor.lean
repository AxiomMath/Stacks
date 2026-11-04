module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStackOneMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable

/-!
# The relative Hom functor attached to an object of `Coh_{X/B}`

In the proof of Stacks 09TU, the fibre of `Quot_{F/X/B} ⟶ Coh_{X/B}` over an object `(T, 𝒢)` of
`Coh_{X/B}` is the functor of surjections `F_{T'} ⟶ 𝒢_{T'}`, an open subfunctor of the relative
Hom functor `Hom(F_T, 𝒢)` of Stacks 08JT for the morphism `X_T ⟶ T`.  That relative Hom functor
lives on the schemes over `T` and pulls back along the iterated base changes
`X_T ×_T T' ⟶ X_T`, whereas the quotients of `Quot_{F/X/B}` and the objects of `Coh_{X/B}` live
on the base changes `X ×_B T'`.  This file provides the relative Hom situation and identifies its
Hom functor, restricted to the test schemes over `T`, with the Hom functor read on the base
changes `X ×_B T'`: the two base changes are pullbacks of one cospan, so they are isomorphic
over `X_T`, naturally in `T'`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.fibreHomSituation`: the relative Hom situation of
  Stacks 08JT for the morphism `X_T ⟶ T` and the modules `F_T` and `𝒢`.
* `AlgebraicGeometry.Space.QuotSituation.fibreTestFunctor`: a test scheme over `T` read as a
  scheme over the base of that situation.
* `AlgebraicGeometry.Space.QuotSituation.fibreRelativeFunctor`: a test scheme over `T` read as the
  base change `X ×_B T'` over `X_T`.
* `AlgebraicGeometry.Space.QuotSituation.fibreRelativeIso`: the two readings agree, naturally.
* `AlgebraicGeometry.Space.QuotSituation.fibreHomIso`: the relative Hom functor, restricted to
  the test schemes over `T`, is the Hom functor on the base changes `X ×_B T'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)
  (A : CoherentObject D.toCoherentSituation)

/-- **The relative Hom situation attached to an object `(T, 𝒢)` of `Coh_{X/B}`**: the morphism
`X_T ⟶ T` and the modules `F_T` and `𝒢` on `X_T`, as in the proof of Stacks 09TU. -/
abbrev fibreHomSituation : HomSituation B S hS where
  X := D.space A.T
  base := (schemeSpaceFunctor B S hS).obj A.T.left
  f := D.projection A.T
  F := D.baseChangeModule A.T
  G := A.F
  quasicoherent_F := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F
    D.quasicoherent
  quasicoherent_G := A.quasicoherent

/-- A test scheme over the test scheme of `A`, read as a scheme over the base of
`AlgebraicGeometry.Space.QuotSituation.fibreHomSituation`. -/
def fibreTestFunctor : Over A.T ⥤ (D.fibreHomSituation A).SchemesOver where
  obj Z := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map Z.hom.left)
  map {Z₁ Z₂} k := CostructuredArrow.homMk k.left.left (by
    change (schemeSpaceFunctor B S hS).map k.left.left ≫
      (schemeSpaceFunctor B S hS).map Z₂.hom.left = (schemeSpaceFunctor B S hS).map Z₁.hom.left
    rw [← CategoryTheory.Functor.map_comp, ← CostructuredArrow.comp_left, Over.w k])
  map_id _ := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

/-- A test scheme over the test scheme of `A`, read as the base change `X ×_B T'` over `X_T`. -/
def fibreRelativeFunctor : Over A.T ⥤ Over (D.space A.T) where
  obj Z := Over.mk (D.relativeMap Z.hom)
  map {Z₁ Z₂} k := Over.homMk (D.relativeMap k.left) (by
    change baseChangeMap D.f k.left ≫ baseChangeMap D.f Z₂.hom = baseChangeMap D.f Z₁.hom
    rw [← baseChangeMap_comp, Over.w k])
  map_id Z := Over.OverMorphism.ext (baseChangeMap_id D.f Z.left)
  map_comp k l := Over.OverMorphism.ext (baseChangeMap_comp D.f k.left l.left)

/-- The base change `X ×_B T'` is a pullback of `X_T ⟶ T` along `T' ⟶ T`. -/
theorem isPullback_fibreRelative (Z : Over A.T) :
    IsPullback (D.relativeMap Z.hom) (D.projection Z.left) (D.projection A.T)
      ((schemeSpaceFunctor B S hS).map Z.hom.left) :=
  isPullback_overBaseChangeMap D.f ((schemesOverToOver D.Y).map Z.hom)

/-- The base change of `X_T ⟶ T` along `T' ⟶ T` is a pullback of the same cospan. -/
theorem isPullback_fibreTest (Z : Over A.T) :
    IsPullback (overProjection (D.fibreHomSituation A).f
        ((schemesOverToOver _).obj ((D.fibreTestFunctor A).obj Z)))
      (overInclusion (D.fibreHomSituation A).f
        ((schemesOverToOver _).obj ((D.fibreTestFunctor A).obj Z)))
      (D.projection A.T) ((schemeSpaceFunctor B S hS).map Z.hom.left) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS (D.fibreHomSituation A).f
    ((schemesOverToOver _).obj ((D.fibreTestFunctor A).obj Z)).hom

/-- The comparison `X ×_B T' ≅ X_T ×_T T'` of the two base changes at one test scheme. -/
def fibreSpaceIso (Z : Over A.T) :
    D.space Z.left ≅ overBaseChange (D.fibreHomSituation A).f
      ((schemesOverToOver _).obj ((D.fibreTestFunctor A).obj Z)) :=
  (D.isPullback_fibreRelative A Z).isoIsPullback _ _ (D.isPullback_fibreTest A Z)

/-- The comparison `fibreSpaceIso` followed by the projection to `X_T` is the map
`X ×_B T' ⟶ X ×_B T` induced by `T' ⟶ T`. -/
@[reassoc]
theorem fibreSpaceIso_hom_fst (Z : Over A.T) :
    (D.fibreSpaceIso A Z).hom ≫ overProjection (D.fibreHomSituation A).f
      ((schemesOverToOver _).obj ((D.fibreTestFunctor A).obj Z)) = D.relativeMap Z.hom :=
  (D.isPullback_fibreRelative A Z).isoIsPullback_hom_fst _ _ (D.isPullback_fibreTest A Z)

/-- The comparison `fibreSpaceIso` followed by the projection to `T'` is the projection
`X ×_B T' ⟶ T'`. -/
@[reassoc]
theorem fibreSpaceIso_hom_snd (Z : Over A.T) :
    (D.fibreSpaceIso A Z).hom ≫ overInclusion (D.fibreHomSituation A).f
      ((schemesOverToOver _).obj ((D.fibreTestFunctor A).obj Z)) = D.projection Z.left :=
  (D.isPullback_fibreRelative A Z).isoIsPullback_hom_snd _ _ (D.isPullback_fibreTest A Z)

/-- The comparison of the two base changes at one test scheme, over `X_T`. -/
def fibreRelativeIsoApp (Z : Over A.T) :
    (D.fibreRelativeFunctor A).obj Z ≅
      (baseChangeOver (D.fibreHomSituation A).f).obj ((D.fibreTestFunctor A).obj Z) :=
  Over.isoMk (D.fibreSpaceIso A Z) (D.fibreSpaceIso_hom_fst A Z)

/-- **The two readings of a test scheme over `T` agree over `X_T`, naturally**: the base change
`X ×_B T'` and the iterated base change `X_T ×_T T'` are pullbacks of one cospan. -/
def fibreRelativeIso :
    D.fibreRelativeFunctor A ≅ D.fibreTestFunctor A ⋙ baseChangeOver (D.fibreHomSituation A).f :=
  NatIso.ofComponents (D.fibreRelativeIsoApp A) (by
    intro Z₁ Z₂ k
    refine Over.OverMorphism.ext ?_
    change D.relativeMap k.left ≫ (D.fibreSpaceIso A Z₂).hom =
      (D.fibreSpaceIso A Z₁).hom ≫ overBaseChangeMap (D.fibreHomSituation A).f
        ((schemesOverToOver _).map ((D.fibreTestFunctor A).map k))
    refine (D.isPullback_fibreTest A Z₂).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, fibreSpaceIso_hom_fst,
        overBaseChangeMap_comp_projection, fibreSpaceIso_hom_fst]
      change baseChangeMap D.f k.left ≫ baseChangeMap D.f Z₂.hom = baseChangeMap D.f Z₁.hom
      rw [← baseChangeMap_comp, Over.w k]
    · rw [Category.assoc, Category.assoc, fibreSpaceIso_hom_snd,
        overBaseChangeMap_comp_inclusion, fibreSpaceIso_hom_snd_assoc]
      exact baseChangeMap_comp_inclusion D.f k.left)

/-- **The Hom functor on the base changes `X ×_B T'`**: a test scheme `T' ⟶ T` goes to the
homomorphisms `(X_{T'} ⟶ X_T)^* F_T ⟶ (X_{T'} ⟶ X_T)^* 𝒢`. -/
def fibreHomFunctor (hc : ModulePushforwardCoherence B S hS) : (Over A.T)ᵒᵖ ⥤ Type (u + 1) :=
  (D.fibreRelativeFunctor A).op ⋙ moduleHomOver hc (D.baseChangeModule A.T) A.F

/-- **The relative Hom functor of Stacks 08JT for `X_T ⟶ T`, restricted to the test schemes
over `T`, is the Hom functor on the base changes `X ×_B T'`.** -/
def fibreHomIso (hc : ModulePushforwardCoherence B S hS) :
    D.fibreHomFunctor A hc ≅ (D.fibreTestFunctor A).op ⋙ (D.fibreHomSituation A).homFunctor hc :=
  Functor.isoWhiskerRight (NatIso.op (D.fibreRelativeIso A)).symm _

end AlgebraicGeometry.Space.QuotSituation

end
