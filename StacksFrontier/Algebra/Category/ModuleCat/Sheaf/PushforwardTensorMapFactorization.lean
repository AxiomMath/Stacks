module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsProjectionFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ProjectionFormulaComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorFactorization

/-!
# The projection formula of a morphism of ringed topoi, reduced to its inverse-image factor

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, `F` a sheaf of
`O_D`-modules and `G` a sheaf of `O_C`-modules. The canonical map of
`Stacks.SheafOfModules.pushforwardTensorMap`,

`F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)`,

is the projection-formula map of the adjunction of **Stacks 03D7**, which is by construction the
composite of the adjunction of **Stacks 03D4** between the inverse image and the direct image with
the adjunction of **Stacks 03CZ** between extension and restriction of scalars along `f♯`. By
`Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_comp` it is therefore invertible as soon as
the projection-formula maps of the two factors are, and the change-of-rings one always is
(`Stacks.ExtendScalarsProjection.isIso_extendScalarsProjectionMap`). So only the inverse-image
factor is left, and that is what this file records.

## Main results

* `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isIso_inverseImageProjectionMap`: the
  canonical map is an isomorphism as soon as the projection-formula map of the inverse-image
  adjunction is.

## Implementation notes

The hypothesis `hα` of `Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_comp` — that the
comparison of **Stacks 03EL** has the componentwise form `L₂(α₁) ≫ α₂` — is
`Stacks.SheafOfModules.pullbackTensorIso_hom_app_eq`: the second factor `α₂` there is the base
change of **Stacks 03CU** at the inverse images, which is exactly the component of
`Stacks.ExtendScalarsProjection.extendScalarsTensorNatTrans` at the comm-ring-sheaf form
`Stacks.Sheaves.RingedToposModules.fSharpCommRingSheaf` of the structure map.

Nothing here is specific to a closed immersion: the inverse-image factor is left as a hypothesis
precisely because its invertibility is where the geometry enters.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
  Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section Factorization

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The canonical map `F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)` is an isomorphism as soon as the
projection-formula map of the inverse-image adjunction of Stacks 03D4 is.**

The pullback of Stacks 03D6, part (2) is the inverse image of Stacks 03D2 followed by extension of
scalars along `f♯`, and the adjunction of Stacks 03D7 is the composite of the two adjunctions
accordingly; the comparison of Stacks 03EL factors to match
(`Stacks.SheafOfModules.pullbackTensorIso_hom_app_eq`). So the canonical map factors into the
projection-formula map of the inverse image at `G|_{f⁻¹O_D}` and the direct image of the
change-of-rings one at `f⁻¹F`, and the latter is always invertible. -/
theorem isIso_pushforwardTensorMap_of_isIso_inverseImageProjectionMap
    (F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (h : IsIso (Stacks.ProjectionFormula.adjunctionTensorMapSnd
      (inverseImageAdjDirectImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)))
      (inverseImageTensorBifunctor f)
      (inverseImageTensorIso f).hom F
      ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj G))) :
    IsIso (pushforwardTensorMap f F G) :=
  Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_comp
    (inverseImageAdjDirectImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)))
    (inverseImageTensorBifunctor f)
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)))
    (inverseImageTensorIso f).hom
    (Stacks.ExtendScalarsProjection.extendScalarsTensorNatTrans (fSharpCommRingSheaf f))
    (pullbackTensorIso f).hom
    (fun P Q ↦ pullbackTensorIso_hom_app_eq f P Q) F G h
    (Stacks.ExtendScalarsProjection.isIso_extendScalarsProjectionMap _ _ _)

end Factorization

end Stacks.SheafOfModules

end
