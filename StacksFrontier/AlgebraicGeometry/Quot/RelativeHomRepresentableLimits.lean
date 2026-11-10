module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineFinitePresentationFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions

/-!
# Finite limits of algebraic spaces affine and of finite presentation over a base

`AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver Y R` says that a functor
`R` on the test schemes over an algebraic space `Y` is an algebraic space affine and of finite
presentation over `Y`.  This file proves that the functors with this property are closed under
fibre products of functors on the test schemes, and that the terminal functor has it.

These are the two facts which turn the identification
`Isom(E, E') = (H' ×_B H) ×_{c, I ×_B I', σ} B` of the proofs of Stacks 08K9 and Stacks 0DPW
into the conclusion that `Isom(E, E')` is affine and of finite presentation over `B` once the
four Hom functors are: `H' ×_B H` is the fibre product of `H'` and `H` over the terminal
functor, and `Isom(E, E')` is the fibre product of `c` and `σ`.

## Main definitions

* `AlgebraicGeometry.Space.schemesOverEquivCostructuredArrow`: the test schemes over `Y` are the
  costructured arrows of the Yoneda embedding to the presheaf underlying `Y`.
* `AlgebraicGeometry.Space.overPointsEquivalence`: the equivalence between presheaves over `Y`
  and functors on the test schemes over `Y`, sending `p : H ⟶ Y` to its functor of points over
  `Y` (Kashiwara–Schapira, Lemma 1.4.12, as
  `CategoryTheory.overEquivPresheafCostructuredArrow`).

## Main results

* `AlgebraicGeometry.Space.overPointsEquivalenceObjIso`: on an algebraic space over `Y` this
  equivalence is `AlgebraicGeometry.Space.spacePointsOver`.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.of_isPullback`: a fibre
  product of functors on the test schemes over `Y` which are algebraic spaces affine and of
  finite presentation over `Y` is again one.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.of_isTerminal`: the
  terminal functor on the test schemes over `Y` is an algebraic space affine and of finite
  presentation over `Y`, represented by `Y` itself.

## Implementation notes

The proof transports the fibre product along an equivalence.  The functor of points over `Y`
is the restriction of `CategoryTheory.overEquivPresheafCostructuredArrow` along the
equivalence `AlgebraicGeometry.Space.schemesOverEquivCostructuredArrow`, so it is an
equivalence from presheaves over `Y` to functors on the test schemes; composed with the
universe lift it remains fully faithful and preserves limits.  Hence every morphism between
functors of points comes from a morphism of presheaves over `Y`, and a fibre product of
functors of points is the functor of points of the fibre product of presheaves, which is
computed in presheaves because the forgetful functor from the over category preserves
pullbacks.  What remains is that the fibre product of algebraic spaces affine and of finite
presentation over `Y` is again one, which is
`AlgebraicGeometry.Space.isAffineHom_comp_of_isPullback` and
`AlgebraicGeometry.Space.isFinitePresentation_comp_of_isPullback`.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 0DPW](https://stacks.math.columbia.edu/tag/0DPW)
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 1.4.12
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PointsEquivalence

variable (Y : AlgebraicSpaces B S hS)

/-- The test schemes over an algebraic space `Y` are the costructured arrows of the Yoneda
embedding to the presheaf underlying `Y`: the inclusion of the algebraic spaces into the
presheaves is fully faithful. -/
def schemesOverEquivCostructuredArrow :
    SchemesOver Y ≌ CostructuredArrow (yoneda : BigFppfOver B S hS ⥤ _) Y.obj :=
  (CostructuredArrow.post (schemeSpaceFunctor B S hS)
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    Y).asEquivalence

/-- **The functor of points over `Y` as an equivalence**: presheaves over `Y` are the same as
functors on the test schemes over `Y`.  A presheaf `p : H ⟶ Y` is sent to the functor whose
value at a test scheme `T` is the set of sections of `H` over `T` lying over the section of `Y`
that `T` is. -/
def overPointsEquivalence : Over Y.obj ≌ ((SchemesOver Y)ᵒᵖ ⥤ Type u) :=
  (overEquivPresheafCostructuredArrow Y.obj).trans
    (schemesOverEquivCostructuredArrow Y).op.symm.congrLeft

/-- On an algebraic space over `Y`, the functor of points over `Y` of
`AlgebraicGeometry.Space.overPointsEquivalence` is
`AlgebraicGeometry.Space.spacePointsOver`. -/
def overPointsEquivalenceObjIso (W : Over Y.obj) (hW : IsAlgebraicSpace B S hS W.left) :
    (overPointsEquivalence Y).functor.obj W ≅
      spacePointsOver (H := ⟨W.left, hW⟩) (ObjectProperty.homMk W.hom) :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun x => ⟨x.1, x.2.app⟩
        invFun := fun x => ⟨x.1, ⟨x.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- The functor of points over `Y`, followed by the universe lift to the value universe of the
relative Hom functors. -/
abbrev overPointsULift : Over Y.obj ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) :=
  (overPointsEquivalence Y).functor ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}

/-- The functor of points over `Y` followed by the universe lift preserves the limits of small
shape: it is an equivalence followed by the universe lift, applied objectwise. -/
instance (J : Type) [SmallCategory J] : PreservesLimitsOfShape J (overPointsULift Y) :=
  inferInstance

/-- The functor of points over `Y` followed by the universe lift is fully faithful. -/
def overPointsULiftFullyFaithful : (overPointsULift Y).FullyFaithful :=
  (overPointsEquivalence Y).fullyFaithfulFunctor.comp
    ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight _)

/-- On an algebraic space `p : H ⟶ Y`, the lifted functor of points over `Y` is the universe
lift of `AlgebraicGeometry.Space.spacePointsOver p`. -/
def overPointsULiftObjIso {H : AlgebraicSpaces B S hS} (p : H ⟶ Y) :
    (overPointsULift Y).obj (Over.mk p.hom) ≅ spacePointsOver p ⋙ uliftFunctor.{u + 1, u} :=
  Functor.isoWhiskerRight (overPointsEquivalenceObjIso Y (Over.mk p.hom) H.property) _

end PointsEquivalence

variable {Y : AlgebraicSpaces B S hS}

/-- **A fibre product of algebraic spaces affine and of finite presentation over `Y` is one.**
If `F` is the fibre product of `c : P ⟶ Q` and `σ : Z ⟶ Q` in the functors on the test schemes
over `Y`, and `P`, `Q`, `Z` are algebraic spaces affine and of finite presentation over `Y`, then
so is `F`.

The morphisms `c` and `σ` come from morphisms of presheaves over `Y`, because the functor of
points is fully faithful; the fibre product of those presheaves is an algebraic space affine and
of finite presentation over `Y`
(`AlgebraicGeometry.Space.isAffineHom_comp_of_isPullback`,
`AlgebraicGeometry.Space.isFinitePresentation_comp_of_isPullback`), and its functor of points is
`F`, because the functor of points preserves fibre products. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.of_isPullback
    {F P Q Z : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ P} {b : F ⟶ Z} {c : P ⟶ Q}
    {σ : Z ⟶ Q} (sq : IsPullback a b c σ)
    (hP : IsAffineFinitePresentationAlgebraicSpaceOver Y P)
    (hQ : IsAffineFinitePresentationAlgebraicSpaceOver Y Q)
    (hZ : IsAffineFinitePresentationAlgebraicSpaceOver Y Z) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y F := by
  obtain ⟨HP, pP, haP, hfP, ⟨eP⟩⟩ := hP
  obtain ⟨HQ, pQ, haQ, hfQ, ⟨eQ⟩⟩ := hQ
  obtain ⟨HZ, pZ, haZ, hfZ, ⟨eZ⟩⟩ := hZ
  let hΨ := overPointsULiftFullyFaithful Y
  let iP : (overPointsULift Y).obj (Over.mk pP.hom) ≅ P := overPointsULiftObjIso Y pP ≪≫ eP
  let iQ : (overPointsULift Y).obj (Over.mk pQ.hom) ≅ Q := overPointsULiftObjIso Y pQ ≪≫ eQ
  let iZ : (overPointsULift Y).obj (Over.mk pZ.hom) ≅ Z := overPointsULiftObjIso Y pZ ≪≫ eZ
  let c' : Over.mk pP.hom ⟶ Over.mk pQ.hom := hΨ.preimage (iP.hom ≫ c ≫ iQ.inv)
  let σ' : Over.mk pZ.hom ⟶ Over.mk pQ.hom := hΨ.preimage (iZ.hom ≫ σ ≫ iQ.inv)
  have hcmap : (overPointsULift Y).map c' = iP.hom ≫ c ≫ iQ.inv := hΨ.map_preimage _
  have hσmap : (overPointsULift Y).map σ' = iZ.hom ≫ σ ≫ iQ.inv := hΨ.map_preimage _
  have : HasPullback c' σ' := hasLimit_of_created (cospan c' σ') (Over.forget Y.obj)
  have sqO := IsPullback.of_hasPullback c' σ'
  have sqL := (Over.forget Y.obj).map_isPullback sqO
  have := sqL.hasPullback
  have hW : IsAlgebraicSpace B S hS (pullback c' σ').left :=
    (isAlgebraicSpace_pullback B S hS c'.left σ'.left HP.property HZ.property
      HQ.property).of_iso sqL.isoPullback.symm
  have hc : c'.left ≫ pQ.hom = pP.hom := Over.w c'
  have hσ : σ'.left ≫ pQ.hom = pZ.hom := Over.w σ'
  have hsnd : (pullback.snd c' σ').left ≫ pZ.hom = (pullback c' σ').hom := Over.w _
  have sq' : IsPullback ((overPointsULift Y).map (pullback.fst c' σ') ≫ iP.hom)
      ((overPointsULift Y).map (pullback.snd c' σ') ≫ iZ.hom) c σ :=
    ((overPointsULift Y).map_isPullback sqO).of_iso (Iso.refl _) iP iZ iQ (by simp) (by simp)
      (by rw [hcmap]; simp) (by rw [hσmap]; simp)
  refine ⟨⟨(pullback c' σ').left, hW⟩, ObjectProperty.homMk (pullback c' σ').hom, ?_, ?_,
    ⟨(overPointsULiftObjIso Y (H := ⟨(pullback c' σ').left, hW⟩)
      (ObjectProperty.homMk (pullback c' σ').hom)).symm ≪≫ sq'.isoIsPullback _ _ sq⟩⟩
  · rw [← hsnd]
    exact isAffineHom_comp_of_isPullback HQ.property Y.property sqL hc haP haQ haZ
  · rw [← hsnd]
    exact isFinitePresentation_comp_of_isPullback hW HP.property HQ.property HZ.property
      Y.property sqL hc hfP hfQ hfZ

/-- **The terminal functor on the test schemes over `Y` is an algebraic space affine and of
finite presentation over `Y`**, represented by the identity of `Y`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.of_isTerminal
    {Z : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} (hZ : IsTerminal Z) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y Z := by
  have h : IsTerminal ((overPointsULift Y).obj (Over.mk (𝟙 Y.obj))) :=
    (Over.mkIdTerminal (X := Y.obj)).isTerminalObj (overPointsULift Y)
  exact ⟨Y, 𝟙 Y, isAffineHom_id (B := B) (S := S) (hS := hS) Y.obj,
    isFinitePresentation_id B S hS Y.property,
    ⟨(overPointsULiftObjIso Y (𝟙 Y)).symm ≪≫ h.uniqueUpToIso hZ⟩⟩

/-- **A product of algebraic spaces affine and of finite presentation over `Y` is one.**  The
pointwise product of two functors on the test schemes over `Y` is their fibre product over the
terminal functor, which is the fibre product over `Y` of the representing spaces. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.prod
    {F G : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
    (hF : IsAffineFinitePresentationAlgebraicSpaceOver Y F)
    (hG : IsAffineFinitePresentationAlgebraicSpaceOver Y G) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y (FunctorToTypes.prod F G) := by
  have hT : IsTerminal ((Functor.const (SchemesOver Y)ᵒᵖ).obj PUnit.{u + 2}) :=
    IsTerminal.ofUniqueHom (fun K => { app := fun X => Types.isTerminalPUnit.from (K.obj X) })
      (fun K m => NatTrans.ext (funext fun X => Types.isTerminalPUnit.hom_ext _ _))
  have sq : IsPullback (FunctorToTypes.prod.fst (F := F) (G := G)) FunctorToTypes.prod.snd
      (hT.from F) (hT.from G) :=
    IsPullback.of_forall_isPullback_app fun T => (Types.isPullback_iff _ _ _ _).2
      ⟨Types.isTerminalPUnit.hom_ext _ _, fun x y h => Prod.ext h.1 h.2,
        fun x z _ => ⟨(x, z), rfl, rfl⟩⟩
  exact of_isPullback sq hF (of_isTerminal hT) hG

end AlgebraicGeometry.Space

end
