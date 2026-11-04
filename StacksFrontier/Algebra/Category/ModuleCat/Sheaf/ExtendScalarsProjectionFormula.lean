module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsRestrictTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality

/-!
# The projection formula for extension of scalars

Let `α : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`, let `H` be a
sheaf of `O₁`-modules and `G` a sheaf of `O₂`-modules. The adjunction of **Stacks 03CZ** between
extension and restriction of scalars has a projection-formula map

`H ⊗_{O₁} G|_{O₁} ⟶ (O₂ ⊗_{O₁} H) ⊗_{O₂} G`,

the adjoint transpose of the base change of **Stacks 03CU** followed by the counit in the second
factor. This file proves it is an isomorphism, which sectionwise is
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.

This is the change-of-rings half of the projection formula of a morphism of ringed topoi: the
pullback of Stacks 03D6 part (2) is the inverse image of Stacks 03D2 followed by extension of
scalars along `f♯`, so by
`Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp` the projection-formula map of a morphism
of ringed topoi splits into the inverse-image factor and the factor treated here.

## Main definitions

* `Stacks.ExtendScalarsProjection.extendScalarsTensorNatTrans`: the base change of Stacks 03CU as a
  natural transformation `(- ⊗ -) ⋙ extendScalars ⟶ (extendScalars × extendScalars) ⋙ (- ⊗ -)`,
  which is the shape `Stacks.ProjectionFormula.adjunctionTensorMapSnd` consumes.
* `Stacks.ExtendScalarsProjection.extendScalarsProjectionMap`: the projection-formula map above.

## Main results

* `Stacks.ExtendScalarsProjection.isIso_sheafification_map_presheafCancelComparison'`: the
  sheafification of the presheaf-level cancellation comparison is an isomorphism.
* `ExtendScalarsProjection.extendScalarsProjectionMap_comp_restrictScalarsSheafificationIso`: the
  projection-formula map **is** the cancellation of the base change, read through the commutation
  of restriction of scalars with sheafification.
* `Stacks.ExtendScalarsProjection.isIso_extendScalarsProjectionMap`: **the projection-formula map
  is an isomorphism.**

## Implementation notes

Invertibility is *not* an instance of
`Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd`: that criterion asks for the counit of the
adjunction at `G` and its unit at `H ⊗ G|` to be invertible, and neither is, already for
`O₁ = ℤ` and `O₂ = ℤ[t]` constant — the counit there is the multiplication `ℤ[t] ⊗_ℤ G ⟶ G`,
which is not injective. What makes the map invertible is the cancellation of a base change, so
what is proved is the identification of the map with the one the cancellation supplies,
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`. The half of that identification
which is purely about the cancellation is
`isIso_sheafification_map_presheafCancelComparison'`; the other half is one computation on the
image of a pure tensor of local sections, after which
`Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext` identifies the two morphisms, both
being morphisms out of a tensor product sheaf. Its inputs are:

* the adjoint transpose is the unit followed by the restriction of scalars of the comparison,
  `CategoryTheory.Adjunction.homEquiv_unit`;
* the unit of Stacks 03CZ followed by the base change of Stacks 03CU carries the image of
  `a ⊗ b` to the image of `(1 ⊗ a) ⊗ (1 ⊗ b)`, which is
  `Stacks.SheafOfModules.RingedToposPullback.extendScalarsTensorIso_hom_val_app_unit_tmul`;
* the counit in the second factor undoes the unit there, by the right triangle identity;
* the cancellation carries `a ⊗ b` to `(1 ⊗ a) ⊗ b`, which is
  `Stacks.FlatChangeOfRings.presheafCancelComparison'_apply`, and
  `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'_hom` exhibits the cancellation as
  the sheafification of that comparison.

The two morphisms do not literally have the same target: the projection-formula map lands in the
restriction of scalars of a sheafification and the cancellation in the sheafification of a
restriction of scalars. The comparison of the two is
`AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso`, which is the identity on
sections; `Stacks.SheafOfModules.ExtendScalarsTensor.sheafifyRestrictIso` is the same comparison
under the stronger `HasSheafify` hypothesis of its section, which is why the weaker spelling is
the one used here.

**Why the computation is a term and not a rewrite.** The two spellings of the sheaf of rings
underlying a sheaf of commutative rings — `CategoryTheory.sheafCompose` applied to it, and the
pair of its underlying presheaf of rings with the sheaf condition — are definitionally equal only
at *default* transparency, so the statements this file composes are not simultaneously
type-correct at the `implicit` transparency level that `rw` checks its motives at. Each step is
therefore a `congrArg` glued with `Eq.trans`, where the defeq is discharged by the elaborator at
the seams; the one rewrite that is used, of the decomposition of the adjoint transpose named at
bare categories just below, is applied with its right-hand side left to unification rather than
written out, since writing the composite of the Stacks 03CU comparison with the counit in the
second factor exhausts the elaborator at these spellings.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe v u w

namespace Stacks.ExtendScalarsProjection

open Stacks Stacks.PresheafOfModules.ChangeOfRings
open Stacks.FlatChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The sheaf condition on the underlying presheaf of rings of a sheaf of commutative rings, at
the spelling the change-of-rings adjunction of Stacks 03CZ takes it in. -/
lemma isSheaf_ringPresheaf_obj (O : Sheaf J CommRingCat.{w}) :
    Presheaf.IsSheaf J (ringPresheaf O.obj) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf O).cond

/-- **The base change of Stacks 03CU as a natural transformation of bifunctors**: the shape
`Stacks.ProjectionFormula.adjunctionTensorMapSnd` takes its comparison in. Its components are
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` and its naturality is
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_naturality`. -/
def extendScalarsTensorNatTrans :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O₁)) ⋙
        Stacks.Sheaves.RingedToposModules.extendScalars J α.hom (isSheaf_ringPresheaf_obj O₁)
          (isSheaf_ringPresheaf_obj O₂) ⟶
      Functor.prod
            (Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
              (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂))
            (Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
              (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂)) ⋙
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O₂)) where
  app PQ := (extendScalarsTensorIso α.hom (isSheaf_ringPresheaf_obj O₁)
    (isSheaf_ringPresheaf_obj O₂) PQ.1 PQ.2).hom
  naturality {PQ PQ'} uv := by
    obtain ⟨P, Q⟩ := PQ
    obtain ⟨P', Q'⟩ := PQ'
    obtain ⟨u, v⟩ := uv
    exact (congrArg (fun t ↦ (Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
            (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂)).map t ≫
          (extendScalarsTensorIso α.hom (isSheaf_ringPresheaf_obj O₁)
            (isSheaf_ringPresheaf_obj O₂) P' Q').hom)
        (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map O₁ u v)).trans
      ((extendScalarsTensorIso_hom_naturality α.hom (isSheaf_ringPresheaf_obj O₁)
          (isSheaf_ringPresheaf_obj O₂) u v).trans
        (congrArg (fun t ↦ (extendScalarsTensorIso α.hom (isSheaf_ringPresheaf_obj O₁)
            (isSheaf_ringPresheaf_obj O₂) P Q).hom ≫ t)
          (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map O₂
            ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
              (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂)).map u)
            ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
              (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂)).map v))).symm)

/-- **The projection-formula map of the adjunction of Stacks 03CZ**,
`H ⊗_{O₁} G|_{O₁} ⟶ ((O₂ ⊗_{O₁} H) ⊗_{O₂} G)|_{O₁}`: the adjoint transpose of the base change
of Stacks 03CU followed by the counit in the second tensor factor. -/
def extendScalarsProjectionMap (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O₁))).obj
        (H, (SheafOfModules.restrictScalars (commRingSheafMap J α.hom
          (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂))).obj G) ⟶
      (SheafOfModules.restrictScalars (commRingSheafMap J α.hom (isSheaf_ringPresheaf_obj O₁)
        (isSheaf_ringPresheaf_obj O₂))).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O₂))).obj
          ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom (isSheaf_ringPresheaf_obj O₁)
            (isSheaf_ringPresheaf_obj O₂)).obj H, G)) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd
    (extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
      (isSheaf_ringPresheaf_obj O₂))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O₁)))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O₂)))
    (extendScalarsTensorNatTrans α) H G

/-- **The sheafification of the cancellation comparison is an isomorphism.** The comparison of
presheaves of `O₁`-modules of `Stacks.FlatChangeOfRings.presheafCancelComparison'` is not itself
invertible — its second factor is a sheafification unit — but its sheafification is, because on
underlying sheaves of abelian groups it is
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`, and `SheafOfModules.toSheaf`
reflects isomorphisms. -/
lemma isIso_sheafification_map_presheafCancelComparison'
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    IsIso ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁) (𝟙 _)).map
      (presheafCancelComparison' α H G)) := by
  have h : (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁)).map
        ((PresheafOfModules.sheafification
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁) (𝟙 _)).map
          (presheafCancelComparison' α H G)) =
      (cancelExtendScalarsTensorSheafIso' α H G).hom := by
    rw [cancelExtendScalarsTensorSheafIso'_hom]
    rfl
  have : IsIso ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁)).map
      ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁) (𝟙 _)).map
        (presheafCancelComparison' α H G))) := by
    rw [h]
    exact (cancelExtendScalarsTensorSheafIso' α H G).isIso_hom
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁))

/-- **The projection-formula map at a bifunctor given in curried form**, decomposed into the unit
of the adjunction and the restriction of the comparison followed by the counit in the second
factor, the counit factor being the action of the *partially applied* bifunctor `B.obj (L H)`.

Trading the uncurried action on the product morphism `𝟙 (L H) ×ₘ counit` for the curried action of
`B.obj (L H)` is the one step of the computation below that is not definitional: the uncurried
action is by construction `(B.map f₁).app _ ≫ (B.obj _).map f₂`, so an identity first component
has to be carried through `CategoryTheory.Functor.map_id`.

It is stated here over bare categories, where both sides are small and no spelling of the sheaf of
rings occurs. At the concrete sheaves of rings below, the two spellings
`Stacks.SheafOfModules.Tensor.ringSheaf O₂` and
`Stacks.Sheaves.RingedToposModules.commRingSheaf J O₂.obj _` of one sheaf of rings meet inside the
product morphism — `Stacks.ProjectionFormula.adjunctionTensorMapSnd` takes its category from the
adjunction and its bifunctor from `Stacks.SheafOfModules.Tensor.sheafTensor` — so the product
morphism there is not type-correct at the `implicit` transparency that `rw` and `simp` match at,
and neither of them fires on it. -/
private lemma adjunctionTensorMapSnd_uncurry {C' D' : Type*} [Category C'] [Category D']
    {Lf : C' ⥤ D'} {Rf : D' ⥤ C'} (adj : Lf ⊣ Rf) (A : C' × C' ⥤ C') (B : D' ⥤ D' ⥤ D')
    (β : A ⋙ Lf ⟶ Lf.prod Lf ⋙ Functor.uncurry.obj B) (H : C') (G : D') :
    Stacks.ProjectionFormula.adjunctionTensorMapSnd adj A (Functor.uncurry.obj B) β H G =
      adj.unit.app (A.obj (H, Rf.obj G)) ≫
        Rf.map (β.app (H, Rf.obj G) ≫ (B.obj (Lf.obj H)).map (adj.counit.app G)) := by
  have h : (Functor.uncurry.obj B).map (Prod.mkHom (𝟙 (Lf.obj H)) (adj.counit.app G)) =
      (B.obj (Lf.obj H)).map (adj.counit.app G) := by
    simp [Functor.uncurry]
  unfold Stacks.ProjectionFormula.adjunctionTensorMapSnd
  rw [Adjunction.homEquiv_unit, h]

open Stacks.SheafOfModules.RingedToposPullback in
/-- **The projection-formula map of Stacks 03CZ is the cancellation of a base change.** Composed
with the comparison of restriction of scalars with sheafification, the map

`H ⊗_{O₁} G|_{O₁} ⟶ ((O₂ ⊗_{O₁} H) ⊗_{O₂} G)|_{O₁}`

is the sheafification of `Stacks.FlatChangeOfRings.presheafCancelComparison'`, whose underlying
morphism of sheaves of abelian groups is
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`.

Both sides are morphisms out of a tensor product sheaf, so it is enough to compare them on the
image of a pure tensor `x ⊗ y` of local sections. There the left-hand side is the unit of
Stacks 03CZ followed by the base change of Stacks 03CU, which carries that image to the image of
`(1 ⊗ x) ⊗ (1 ⊗ y)`, followed by the counit in the second factor, which returns `y`; and the
right-hand side carries it to the image of `(1 ⊗ x) ⊗ y`. -/
theorem extendScalarsProjectionMap_comp_restrictScalarsSheafificationIso
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    extendScalarsProjectionMap α H G ≫
        (AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso _ _).hom =
      (PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁) (𝟙 _)).map
        (presheafCancelComparison' α H G) := by
  refine Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext O₁ H
    ((SheafOfModules.restrictScalars (commRingSheafMap J α.hom
      (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂))).obj G) _ ?_
  intro U x y
  have key : extendScalarsProjectionMap α H G = _ :=
    adjunctionTensorMapSnd_uncurry
      (extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
        (isSheaf_ringPresheaf_obj O₂)) _ _ (extendScalarsTensorNatTrans α) H G
  rw [key]
  have e1 := extendScalarsTensorIso_hom_val_app_unit_tmul α.hom
    (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂) H
    ((SheafOfModules.restrictScalars (commRingSheafMap J α.hom
      (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂))).obj G) U x y
  have e2 := Stacks.SheafOfModules.FlatSquareZero.tensorLeft_map_tmul O₂
    ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
      (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂)).obj H)
    ((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
      (isSheaf_ringPresheaf_obj O₂)).counit.app G) U
    (((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
      (isSheaf_ringPresheaf_obj O₂)).unit.app H).val.app U x)
    (((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
      (isSheaf_ringPresheaf_obj O₂)).unit.app
        ((SheafOfModules.restrictScalars (commRingSheafMap J α.hom
          (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂))).obj G)).val.app U y)
  have e3 : ((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
        (isSheaf_ringPresheaf_obj O₂)).counit.app G).val.app U
      (((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
        (isSheaf_ringPresheaf_obj O₂)).unit.app
          ((SheafOfModules.restrictScalars (commRingSheafMap J α.hom
            (isSheaf_ringPresheaf_obj O₁)
            (isSheaf_ringPresheaf_obj O₂))).obj G)).val.app U y) = y :=
    congrArg (fun k ↦ k.val.app U y)
      ((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
        (isSheaf_ringPresheaf_obj O₂)).right_triangle_components G)
  have e4 := (extendRestrictScalarsAdjunction_unit_val_app α.hom
      (isSheaf_ringPresheaf_obj O₁) (isSheaf_ringPresheaf_obj O₂) H U x).trans
    (congrArg (fun z ↦ ((PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J O₂.obj (isSheaf_ringPresheaf_obj O₂)) (𝟙 _)).unit.app
      ((changeOfRings α.hom).obj H.val)).app U z)
      (changeOfRingsAdjunction_unit_app_apply α.hom H.val U x))
  have e5 := sheafificationUnit_naturality_app (isSheaf_ringPresheaf_obj O₁)
    (presheafCancelComparison' α H G) U (x ⊗ₜ[O₁.obj.obj U] y)
  have e6 := presheafCancelComparison'_apply α H G U x y
  exact ((((congrArg (fun z ↦ (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) O₂).obj
                ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
                  (isSheaf_ringPresheaf_obj O₁)
                  (isSheaf_ringPresheaf_obj O₂)).obj H)).map
              ((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
                (isSheaf_ringPresheaf_obj O₂)).counit.app G)).val.app U z) e1).trans e2).trans
          (congrArg (fun q ↦ ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
                (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
              (PresheafOfModules.tensorObj (O := O₂.obj)
                ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
                  (isSheaf_ringPresheaf_obj O₁)
                  (isSheaf_ringPresheaf_obj O₂)).obj H).val G.val)).app U
            ((((extendRestrictScalarsAdjunction J α.hom (isSheaf_ringPresheaf_obj O₁)
              (isSheaf_ringPresheaf_obj O₂)).unit.app H).val.app U x) ⊗ₜ[O₂.obj.obj U] q))
            e3)).trans
        (congrArg (fun p ↦ ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
              (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
            (PresheafOfModules.tensorObj (O := O₂.obj)
              ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
                (isSheaf_ringPresheaf_obj O₁)
                (isSheaf_ringPresheaf_obj O₂)).obj H).val G.val)).app U
          (p ⊗ₜ[O₂.obj.obj U] y)) e4)).trans
      ((congrArg (fun z ↦ ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₂.obj)
            ((Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
              (isSheaf_ringPresheaf_obj O₁)
              (isSheaf_ringPresheaf_obj O₂)).obj H).val G.val)).app U z)
        e6.symm).trans e5.symm)

/-- **The projection-formula map of the adjunction of Stacks 03CZ is an isomorphism**:

`H ⊗_{O₁} G|_{O₁} ≅ ((O₂ ⊗_{O₁} H) ⊗_{O₂} G)|_{O₁}`

for every sheaf of `O₁`-modules `H` and every sheaf of `O₂`-modules `G`. No hypothesis on `α` and
none on `H` or `G` enters; sectionwise this is
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.

By `extendScalarsProjectionMap_comp_restrictScalarsSheafificationIso` the map becomes, after
composition with an isomorphism, the sheafification of the cancellation comparison, which is
invertible by `isIso_sheafification_map_presheafCancelComparison'`. -/
theorem isIso_extendScalarsProjectionMap
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    IsIso (extendScalarsProjectionMap α H G) := by
  have hiso : IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁) (𝟙 _)).map
        (presheafCancelComparison' α H G)) :=
    isIso_sheafification_map_presheafCancelComparison' α H G
  obtain ⟨e, he⟩ : ∃ e : _ ≅ _, extendScalarsProjectionMap α H G ≫ e.hom =
      (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁) (𝟙 _)).map
        (presheafCancelComparison' α H G) :=
    ⟨_, extendScalarsProjectionMap_comp_restrictScalarsSheafificationIso α H G⟩
  have he' : IsIso e.hom := e.isIso_hom
  have h1 : IsIso (extendScalarsProjectionMap α H G ≫ e.hom) := by rw [he]; exact hiso
  exact IsIso.of_isIso_comp_right _ e.hom

end Stacks.ExtendScalarsProjection

end
