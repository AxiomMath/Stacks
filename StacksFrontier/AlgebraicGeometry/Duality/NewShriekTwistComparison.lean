module

public import StacksFrontier.AlgebraicGeometry.Duality.InvertibleTwistInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionCurry
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingComplexUniqueness

/-!
# Changing the dualizing complexes in `f_new^!`

Let `f : X ⟶ Y` be a morphism of Noetherian schemes, `ω_Y`, `ω_Y'` dualizing complexes on `Y`
and `ω_X`, `ω_X'` complexes on `X`. Write `f_new^! = D_X ∘ Lf^* ∘ D_Y` with
`D_X = R𝓗om(-, ω_X)`, `D_Y = R𝓗om(-, ω_Y)`, and `f_new'^!` for the same with the primed
complexes. Put `N = R𝓗om(ω_Y', ω_Y)`. If

`ω_X' ≅ f_new^! ω_Y' = R𝓗om(Lf^* N, ω_X)`,

then `f_new'^! ≅ f_new^!` as functors. The computation is the one of [Stacks, Tag 0BV3]:

`R𝓗om(Lf^* R𝓗om(M, ω_Y'), R𝓗om(Lf^* N, ω_X)) = R𝓗om(Lf^* R𝓗om(M, ω_Y') ⊗ Lf^* N, ω_X)`
`= R𝓗om(Lf^* (R𝓗om(M, ω_Y') ⊗ N), ω_X) = R𝓗om(Lf^* R𝓗om(M, ω_Y' ⊗ N), ω_X)`
`= R𝓗om(Lf^* R𝓗om(M, ω_Y), ω_X)`,

using that `N` is invertible and that the evaluation `N ⊗ ω_Y' ⟶ ω_Y` is an isomorphism
([Stacks, Tag 0ATP]), and that `Lf^*` carries tensor products to tensor products
([Stacks, Tag 079U]).

## Main definitions

* `Stacks.Duality.dualIntoIhomIso` — `R𝓗om(-, R𝓗om(L, Z)) ≅ R𝓗om(- ⊗ L, Z)`, natural in the
  contravariant variable, in any closed braided monoidal category.
* `Stacks.Duality.dualIntoTensorRightIso` — `R𝓗om(-, ω ⊗ N) ≅ R𝓗om(-, ω) ⊗ N` for invertible `N`.
* `Stacks.Duality.dualConjTwistIso` — the abstract form of the computation above.
* `Stacks.Duality.fNewShriekStdIsoOfIso` — the computation for `f_new^!` at the standard model.

## References

* [Stacks Project, Tag 0BV3](https://stacks.math.columbia.edu/tag/0BV3)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed Opposite

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Duality

/-! ### Closed monoidal bookkeeping -/

section Closed

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The comparison `L ⊗ (K ⊗ T) ≅ (K ⊗ L) ⊗ T`, natural in `K` and `T`. -/
def tensorLeftBraidAssoc [BraidedCategory C] (L : C) :
    curriedTensor C ⋙ (Functor.whiskeringRight C C C).obj (MonoidalCategory.tensorLeft L) ≅
      MonoidalCategory.tensorRight L ⋙ curriedTensor C :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun T => (α_ L K T).symm ≪≫ whiskerRightIso (β_ L K) T)
      (by
        intros
        dsimp
        simp only [whiskerRightIso_hom, Category.assoc]
        rw [associator_inv_naturality_right_assoc, whisker_exchange]))
    (by
      intro K K' φ
      ext T
      dsimp
      simp only [whiskerRightIso_hom, Category.assoc]
      rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, ← comp_whiskerRight,
        BraidedCategory.braiding_naturality_right])

/-- **`R𝓗om(K, R𝓗om(L, Z)) ≅ R𝓗om(K ⊗ L, Z)` as an isomorphism of bifunctors** in a closed
braided monoidal category: both are parametrized right adjoints of `L ⊗ (K ⊗ T)` and
`(K ⊗ L) ⊗ T`, which the braiding and associator identify. -/
def ihomIhomIsoBifunctor [BraidedCategory C] (L : C) :
    internalHom (C := C) ⋙ (Functor.whiskeringLeft C C C).obj (ihom L) ≅
      (MonoidalCategory.tensorRight L).op ⋙ internalHom (C := C) :=
  parametrizedRightAdjointUniq
    (parametrizedOfNatIsoLeft
      (parametrizedCompTarget internalHomAdjunction₂ (ihom.adjunction L))
      (tensorLeftBraidAssoc L))
    (parametrizedCompParam internalHomAdjunction₂ (MonoidalCategory.tensorRight L))

/-- `R𝓗om(-, R𝓗om(L, Z)) ≅ R𝓗om(- ⊗ L, Z)`, natural in the contravariant variable. -/
def dualIntoIhomIso [BraidedCategory C] (L Z : C) :
    dualInto ((ihom L).obj Z) ≅ (MonoidalCategory.tensorRight L).op ⋙ dualInto Z :=
  NatIso.ofComponents (fun K => ((ihomIhomIsoBifunctor L).app K).app Z)
    (fun φ => NatTrans.congr_app ((ihomIhomIsoBifunctor L).hom.naturality φ) Z)

/-- `R𝓗om(-, ω ⊗ N) ≅ R𝓗om(-, ω) ⊗ N` for an invertible `N`, natural in the contravariant
variable. -/
def dualIntoTensorRightIso (ω : C) {N : C} (h : HasInverse N) :
    dualInto (ω ⊗ N) ≅ dualInto ω ⋙ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents (fun K => ((ihomTensorRightCommBifunctor h).app K).app ω)
    (fun φ => NatTrans.congr_app ((ihomTensorRightCommBifunctor h).hom.naturality φ) ω)

end Closed

/-! ### The abstract computation -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [MonoidalClosed D]

/-- **Changing the complexes in `D_X ∘ P ∘ D_Y`.** For a functor `P : D ⥤ C`, an invertible
`N` with `P(- ⊗ N) ≅ P(-) ⊗ P N`, `ε : ω_Y ≅ ω_Y' ⊗ N` and `κ : ω_X' ≅ R𝓗om(P N, ω_X)`,

`R𝓗om(P R𝓗om(-, ω_Y'), ω_X') ≅ R𝓗om(P R𝓗om(-, ω_Y), ω_X)`

as functors. -/
def dualConjTwistIso (P : D ⥤ C) {N : D} (hN : HasInverse N)
    (μ : MonoidalCategory.tensorRight N ⋙ P ≅ P ⋙ MonoidalCategory.tensorRight (P.obj N))
    {ωY ωY' : D} (ε : ωY ≅ ωY' ⊗ N) {ωX ωX' : C} (κ : ωX' ≅ (ihom (P.obj N)).obj ωX) :
    dualConj (dualInto ωX') (dualInto ωY') P ≅ dualConj (dualInto ωX) (dualInto ωY) P :=
  Functor.isoWhiskerLeft ((dualInto ωY').rightOp ⋙ P.op)
      (dualIntoMapIso κ ≪≫ dualIntoIhomIso (P.obj N) ωX) ≪≫
    Functor.isoWhiskerLeft (dualInto ωY').rightOp
      (Functor.isoWhiskerRight (NatIso.op μ) (dualInto ωX)) ≪≫
    Functor.isoWhiskerRight
      ((Functor.rightOpComp (dualInto ωY') (MonoidalCategory.tensorRight N)).symm ≪≫
        natIsoRightOp (dualIntoMapIso ε ≪≫ dualIntoTensorRightIso ωY' hN).symm)
      (P.op ⋙ dualInto ωX)

end Abstract

/-! ### The computation at the standard model -/

section Std

open Stacks.Duality.TwistedInverseImageDuality (Std pull IsDualizing stdMonoidal stdSymmetric
  stdMonoidalClosed pullTensorIso pullTensorIso_naturality_left)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable {X Y : Scheme.{u}}

/-- `Lf^*(- ⊗ N) ≅ Lf^*(-) ⊗ Lf^* N`, the comparison of [Stacks, Tag 079U] in its first
variable. -/
def pullTensorRightIso (f : X ⟶ Y) (N : Std Y) :
    MonoidalCategory.tensorRight N ⋙ pull f ≅
      pull f ⋙ MonoidalCategory.tensorRight ((pull f).obj N) :=
  NatIso.ofComponents (fun A => pullTensorIso f A N)
    (fun g => pullTensorIso_naturality_left f g N)

variable [IsLocallyNoetherian Y] {ωY ωY' : Std Y}

/-- For dualizing complexes `ω_Y`, `ω_Y'` the object `R𝓗om(ω_Y', ω_Y)` is invertible
([Stacks, Tag 0ATP]); a chosen inverse. -/
def dualizingHomHasInverse (hωY : IsDualizing ωY) (hωY' : IsDualizing ωY') :
    HasInverse ((ihom ωY').obj ωY) :=
  Classical.choice (isInvertible_derivedSheafHom_of_isDualizingComplex ωY' ωY hωY' hωY)

/-- `ω_Y ≅ ω_Y' ⊗ R𝓗om(ω_Y', ω_Y)` for dualizing complexes, the evaluation of
[Stacks, Tag 0ATP] followed by the symmetry. -/
def dualizingHomTensorIso (hωY : IsDualizing ωY) (hωY' : IsDualizing ωY') :
    ωY ≅ ωY' ⊗ (ihom ωY').obj ωY :=
  (@asIso _ _ _ _ (RingedSite.derivedSheafHomCounit (Stacks.SheafOfModules.ringedSite Y.sheaf)
    ωY' ωY) (isIso_derivedSheafHomCounit_of_isDualizingComplex ωY' ωY hωY' hωY)).symm ≪≫
    β_ _ _

/-- **Changing the dualizing complexes in `f_new^!`.** For dualizing complexes `ω_Y`, `ω_Y'` on
`Y` and complexes `ω_X`, `ω_X'` on `X` with `ω_X' ≅ f_new^! ω_Y'` (formed with `ω_X`, `ω_Y`),
the functors `f_new^!` formed with the primed and with the unprimed complexes are isomorphic. -/
def fNewShriekStdIsoOfIso (f : X ⟶ Y) {ωX ωX' : Std X}
    (hωY : IsDualizing ωY) (hωY' : IsDualizing ωY')
    (κ : ωX' ≅ (fNewShriekStd f ωX ωY).obj ωY') :
    fNewShriekStd f ωX' ωY' ≅ fNewShriekStd f ωX ωY :=
  dualConjTwistIso (pull f) (dualizingHomHasInverse hωY hωY') (pullTensorRightIso f _)
    (dualizingHomTensorIso hωY hωY') κ

end Std

end Stacks.Duality

end
