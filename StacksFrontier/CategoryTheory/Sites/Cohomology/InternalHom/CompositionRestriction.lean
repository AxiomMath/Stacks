module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomRestrictionIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# The composition morphism of Stacks 0A91 and restriction to a localized ringed site

Let `X` be a ringed site, `U` an object of its underlying category and `K`, `L`, `M` complexes of
`O`-modules. The composition morphism of Stacks 0A91

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`

is compatible with restriction to the localized ringed site of Stacks 04IX: its restriction to
the site over `U` is the composition morphism formed there, out of the restrictions of `K`, `L`
and `M`, read through the comparisons identifying the restriction of each complex involved with
the corresponding complex formed over `U`.

This is the chain-level half of the restriction compatibility that the sections
"What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`,
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing` record as missing for the
third assertion of Stacks 08JJ. The derived half is still absent; see "What this file does not
contain" below.

## Main results

* `AlgebraicGeometry.RingedSite.compositionMap_restrict_square`: the square.

## Implementation notes

The square is stated with the three Hom comparisons on the same side rather than inverted, as
`AlgebraicGeometry.RingedSite.evaluationMap_restrict_square` is: the two comparisons of the
tensor factors are the two arguments of `tensorTotalMap` over `U`, and the comparison of the
target is applied to the restriction of the ambient composition morphism. A consumer that needs
the two sides identified as morphisms out of the restriction of the ambient source inverts the
comparisons by `AlgebraicGeometry.RingedSite.isIso_of_isInternalHomRestrictionMap`.

The proof is `AlgebraicGeometry.RingedSite.tensorTotalHomSection_ext`: a morphism out of a total
tensor complex into an internal Hom complex is determined by the evaluations of the images of the
homogeneous local pure tensors. Each side is then computed by the formula pinning the morphism it
is built from — the composition morphism by `compositionMap_tensorTotalSection` together with
`compositionSection_applyOver`, the tensor comparison by
`tensorTotalOverIso_inv_tensorTotalSectionAt`, the three Hom comparisons by
`DerivedHomRestriction.complexMap_apply`, and the functoriality by
`tensorTotalMap_tensorTotalSection` — and both come to the same thing: the restricted
`SheafHom(L, M)`-section evaluated on the value of the restricted `SheafHom(K, L)`-section on the
restricted `K`-section. Unlike the evaluation square there is no Koszul sign on either side:
`compositionSection_applyOver` has none.

## What this file does not contain

The derived analogue is **absent**: no declaration states that the composition morphism of
Stacks 0A98, `AlgebraicGeometry.RingedSite.derivedSheafHomComposition`, commutes with the derived
restriction functor `D(O) ⟶ D(O|_U)`, and hence none states it for the canonical map
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` of Stacks 08JD either. Transporting the
square below to the derived category needs a **derived tensor product analogue of Stacks 08JB** —
an isomorphism `(A ⊗^L_O B)|_U ≅ A|_U ⊗^L_{O|_U} B|_U` natural in both variables — and **that is
now available**, as
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction`; the
isomorphism alone is
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso`, public since
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASlice`. (It used to
occur only as a `private def` inside the proof of Stacks 09JB in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedTensorProduct`, which is what this
paragraph used to record.) What is still absent is the derived form of the square below itself:
until the composition morphism of Stacks 0A98 is known to commute with the derived restriction
functor, the locality step
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` cannot be applied to the canonical
map of Stacks 08JD, and no assertion of Stacks 08JJ follows from the square below. No
`@[stacks]` attribute is therefore attached: Stacks 0A91 asserts only that the composition
morphism exists.

**Where the derived form is now blocked.** Transporting the square below needs the restriction
compatibility of `AlgebraicGeometry.RingedSite.derivedEvaluationSourceComparison`, which is the
identification that seats derived composition between classes of complexes. That comparison is
built from the canonical map to the ordinary total tensor product and *not* from the two-sided
K-flat comparison of Stacks 06YU — its left tensor factor is an internal Hom complex, which is
K-injective and not K-flat — so the natural isomorphism
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` does not apply to it
directly. The statement that transports that isomorphism across the canonical map is now
available, as
`Stacks.DerivedTensor.SliceRestriction.toTensor_restrict_square` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToTensorRestriction`, for an
arbitrary pair of complexes. What the evaluation-source square still owes beyond it is the
restriction compatibility of `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, the
chain-level identification of the two spellings of the total tensor complex, and the
compatibility of the K-injective model comparison of Stacks 0A97 with
`(AlgebraicGeometry.RingedSite.derivedHomRestriction X U).iso`, which is
`AlgebraicGeometry.RingedSite.derivedHomRestriction_model` read inside the tensor factor.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor Stacks.SheafOfModules.UliftTensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.tensorComplex
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor X.O).Additive] [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive] [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]

/-- Restricting a morphism out of a total tensor complex and applying it to the image of a pure
tensor over `U` under the tensor comparison gives the morphism applied to the pure tensor on `X`. -/
private theorem restrict_apply_tensorTotalOverIso_inv_tensorTotalSectionAt
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : tensorTotal X A B ⟶ C) (W : (X.over U).C) (t r : ℤ)
    (a : ((restrictComplex X A U).X t).val.obj (op W))
    (b : ((restrictComplex X B U).X r).val.obj (op W)) :
    ((((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex (ComplexShape.up ℤ)).map φ).f (t + r)).val.app (op W)
      (((tensorTotalOverIso X U A B).inv.f (t + r)).val.app (op W)
        (tensorTotalSectionAt (X.over U) (restrictComplex X A U) (restrictComplex X B U)
          W t r (t + r) rfl a b)) =
      (φ.f (t + r)).val.app (op W.left) (tensorTotalSectionAt X A B W.left t r (t + r) rfl a b) :=
  congrArg _ (tensorTotalOverIso_inv_tensorTotalSectionAt X U A B W t r (t + r) rfl a b)

/-- **The restriction comparison of the total tensor complex is natural in both factors.**
Restricting `tensorTotalMap X g h` to the site over `U` and identifying its target with the total
tensor complex formed there is the same as identifying its source and then applying the total
tensor morphism of the restrictions of `g` and `h`.

Both sides are morphisms out of a total tensor complex over `U`, once the source comparison is
moved to the other side, so they are determined by their values on the homogeneous local pure
tensors; on such a tensor each side is the pure tensor of the two restricted images, in the same
total degree and with no sign. -/
theorem tensorTotalOverIso_naturality
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : A ⟶ A') (h : B ⟶ B') :
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (tensorTotalMap X g h) ≫
        (tensorTotalOverIso X U A' B').hom =
      (tensorTotalOverIso X U A B).hom ≫
        tensorTotalMap (X.over U)
          (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g)
          (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map h) := by
  apply (Iso.inv_comp_eq (tensorTotalOverIso X U A B)).mp
  refine tensorTotal_hom_ext (X.over U) fun W t r a b ↦ ?_
  refine Eq.trans (congrArg (((tensorTotalOverIso X U A' B').hom.f (t + r)).val.app
    (op W)) (restrict_apply_tensorTotalOverIso_inv_tensorTotalSectionAt X U
      (tensorTotalMap X g h) W t r a b)) ?_
  refine Eq.trans (congrArg (fun y ↦ (((tensorTotalOverIso X U A' B').hom.f (t + r)).val.app
      (op W)) y) (tensorTotalMap_tensorTotalSectionAt X g h W.left t r (t + r) rfl a b)) ?_
  refine Eq.trans (tensorTotalOverIso_hom_tensorTotalSectionAt X U A' B' W t r (t + r) rfl
    ((g.f t).val.app (op W.left) a) ((h.f r).val.app (op W.left) b)) ?_
  exact (tensorTotalMap_tensorTotalSection (X.over U)
    (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g)
    (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map h) W t r a b).symm

variable (K L M :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The composition morphism of Stacks 0A91 commutes with restriction to a localized ringed
site.** Restricting

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`

to the site over `U` and following it with the comparison identifying the restriction of its
target with an internal Hom complex over `U` is the same as first identifying the restriction of
its source with `Tot(SheafHom(L|_U, M|_U) ⊗ SheafHom(K|_U, L|_U))` — which is the comparison of
the tensor product together with the comparison of each of the two tensor factors — and then
applying the composition morphism formed over `U`. -/
theorem compositionMap_restrict_square :
    (tensorTotalOverIso X U (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj).inv ≫
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (compositionMap X K L M) ≫
          (derivedHomRestriction X U).complexMap K M =
      tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap L M)
          ((derivedHomRestriction X U).complexMap K L) ≫
        compositionMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
          (restrictComplex X M U) := by
  refine tensorTotalHomSection_ext (X.over U) fun W₁ W₂ i t r a q haq x y z ↦ ?_
  have tensorImages := tensorTotalMap_tensorTotalSection (X.over U)
    ((derivedHomRestriction X U).complexMap L M) ((derivedHomRestriction X U).complexMap K L)
    W₁ t r x y
  have compositionImages := (congrArg
    (((compositionMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
      (restrictComplex X M U)).f (t + r)).val.app (op W₁)) tensorImages).trans
        (compositionMap_tensorTotalSection (X.over U) (restrictComplex X K U)
          (restrictComplex X L U) (restrictComplex X M U) W₁ t r
          ((((derivedHomRestriction X U).complexMap L M).f t).val.app (op W₁) x)
          ((((derivedHomRestriction X U).complexMap K L).f r).val.app (op W₁) y))
  refine Eq.trans ?_ (congrArg (fun sectionValue => applyHomSectionOver (X.over U)
    (sheafHomComplex (X.over U) (restrictComplex X K U) (restrictComplex X M U))
    W₁ W₂ i (t + r) a q haq sectionValue z) compositionImages).symm
  refine Eq.trans ?_ (compositionSection_applyOver (X.over U) W₁ W₂ i t r (t + r)
    a (a + r) q rfl rfl (by omega)
    ((((derivedHomRestriction X U).complexMap L M).f t).val.app (op W₁) x)
    ((((derivedHomRestriction X U).complexMap K L).f r).val.app (op W₁) y) z).symm
  refine Eq.trans (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U)
    K M (op W₁) (op (Over.mk i)) (t + r) a q haq _ z) ?_
  refine Eq.trans (congrArg (fun sectionValue => applyHomSectionOver X
    (sheafHomComplex X K M) (Over.left W₁) (Over.left W₂) (Over.Hom.left i)
    (t + r) a q haq sectionValue z)
    (restrict_apply_tensorTotalOverIso_inv_tensorTotalSectionAt X U (compositionMap X K L M)
      W₁ t r x y)) ?_
  refine Eq.trans (congrArg (fun w ↦ applyHomSectionOver X (sheafHomComplex X K M)
    (Over.left W₁) (Over.left W₂) (Over.Hom.left i) (t + r) a q haq w z)
    (compositionMap_tensorTotalSection X K L M (Over.left W₁) t r x y)) ?_
  refine Eq.trans (compositionSection_applyOver X (Over.left W₁) (Over.left W₂)
    (Over.Hom.left i) t r (t + r) a (a + r) q rfl rfl (by omega) x y z) ?_
  refine Eq.trans ?_ (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U)
    L M (op W₁) (op (Over.mk i)) t (a + r) q (by omega) x _).symm
  refine congrArg (fun w ↦ applyHomSectionOver X (sheafHomComplex X L M) (Over.left W₁)
    (Over.left W₂) (Over.Hom.left i) t (a + r) q (by omega) x w) ?_
  exact (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U) K L
    (op W₁) (op (Over.mk i)) r a (a + r) rfl y z).symm

/-- The square of `compositionMap_restrict_square` with the source comparison moved to the right:
restricting the composition morphism and then identifying the target is the source comparison
followed by the comparisons of the two tensor factors and the composition morphism over `U`. -/
theorem compositionMap_restrict_square_hom :
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (compositionMap X K L M) ≫
        (derivedHomRestriction X U).complexMap K M =
      (tensorTotalOverIso X U (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj).hom ≫
        tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap L M)
            ((derivedHomRestriction X U).complexMap K L) ≫
          compositionMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
            (restrictComplex X M U) :=
  (Iso.inv_comp_eq _).1 (compositionMap_restrict_square X U K L M)

end AlgebraicGeometry.RingedSite

end
