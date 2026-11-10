module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCompEssentiallySmall

/-!
# The pullback of a unital homomorphism of sheaves of graded algebras is unital

The pullback of sheaves of graded algebras along a morphism of ringed topoi (part (2) of
Stacks 0FQX) is a functor on the category of sheaves of graded algebras, whose morphisms
(`SheafOfModules.GradedAlgebra.Hom`) need not preserve the unit. This file proves that the
pullback of a unital homomorphism is unital, so that the pullback is also a functor on unital
homomorphisms.

The pullback is the inverse image followed by extension of scalars, and each step carries units
to units: the inverse image of the unit is the image of the unit section along the inverse-image
functor, which is natural; the unit of an extension of scalars is the image of `1 ⊗ 1` under the
unit of the sheafification, which is natural too.

## Main results

* `Stacks.Sheaves.GradedAlgebraInverseImage.transportHom_map_one`: the transport of a unital
  homomorphism is unital.
* `Stacks.Sheaves.GradedAlgebraExtendScalars.extendScalarsGradedAlgebraHom_map_one`: the
  extension of scalars of a unital homomorphism is unital.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPull_map_one`: the pullback of a unital
  homomorphism is unital.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.unitalGradedPull`: the pullback of a unital
  homomorphism, as a unital homomorphism.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry TensorProduct Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.RingedToposModules

universe w v u w' v' u'

namespace Stacks.Sheaves.GradedAlgebraInverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} {A B : SheafOfModules.GradedAlgebra.{w', w'} O} (g : A ⟶ B)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- A unital homomorphism carries the unit section of the source to that of the target, as
morphisms out of the terminal sheaf of sets. -/
public theorem oneSheafHom_comp_map
    (hg : ∀ X : Dᵒᵖ, (g.app 0).val.app X (A.one.eval X) = B.one.eval X) :
    oneSheafHom A ≫ (moduleSheafFunctor O).map (g.app 0) = oneSheafHom B := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun X => ?_))
  ext z
  exact hg X

/-- **The transport of a unital homomorphism is unital.** -/
public theorem transportHom_map_one
    (hg : ∀ X : Dᵒᵖ, (g.app 0).val.app X (A.one.eval X) = B.one.eval X) (X : Cᵒᵖ) :
    ((transportHom J Φ g).app 0).val.app X ((transportGradedAlgebra J Φ A).one.eval X) =
      (transportGradedAlgebra J Φ B).one.eval X := by
  change (Φ ⋙ sectionsFunctor J X).map ((moduleSheafFunctor O).map (g.app 0))
      ((Φ ⋙ sectionsFunctor J X).map (oneSheafHom A) default) =
    (Φ ⋙ sectionsFunctor J X).map (oneSheafHom B) default
  rw [← oneSheafHom_comp_map g hg, Functor.map_comp]
  rfl

end Stacks.Sheaves.GradedAlgebraInverseImage

namespace Stacks.Sheaves.GradedAlgebraExtendScalars

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (J : GrothendieckTopology C)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf O₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf O₂))
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)} (g : A ⟶ B)

/-- **The extension of scalars of a unital homomorphism is unital.** -/
public theorem extendScalarsGradedAlgebraHom_map_one
    (hg : ∀ X : Cᵒᵖ, (g.app 0).val.app X (A.one.eval X) = B.one.eval X) (X : Cᵒᵖ) :
    ((extendScalarsGradedAlgebraHom θ J h₁ h₂ g).app 0).val.app X
        ((extendScalarsGradedAlgebra θ J h₁ h₂ A).one.eval X) =
      (extendScalarsGradedAlgebra θ J h₁ h₂ B).one.eval X := by
  let := (θ.app X).hom.toAlgebra
  rw [extendScalarsGradedAlgebra_one_eval, extendScalarsGradedAlgebra_one_eval]
  refine (PresheafOfModules.unit_naturality_apply (α := 𝟙 (commRingSheaf J O₂ h₂).obj)
    ((changeOfRings θ).map (g.app 0).val) X _).trans ?_
  refine congrArg (fun z => PresheafOfModules.Hom.app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheaf J O₂ h₂).obj)).unit.app
      ((changeOfRings θ).obj (B.piece 0).val)) X z) ?_
  exact (cofHom_app_tmul θ (g.app 0).val X 1 (A.one.eval X)).trans
    (congrArg (fun t => (1 : O₂.obj X) ⊗ₜ[O₁.obj X] t) (hg X))

end Stacks.Sheaves.GradedAlgebraExtendScalars

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

variable {X Y : AlgebraicGeometry.RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- **The pullback of a unital homomorphism of sheaves of graded algebras is unital.** -/
public theorem gradedPull_map_one (f : AlgebraicGeometry.RingedToposHom X Y)
    {A B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (g : A ⟶ B) (hg : ∀ U, (g.app 0).val.app U (A.one.eval U) = B.one.eval U) (U : X.Cᵒᵖ) :
    (((gradedPull f).map g).app 0).val.app U (((gradedPull f).obj A).one.eval U) =
      ((gradedPull f).obj B).one.eval U :=
  GradedAlgebraExtendScalars.extendScalarsGradedAlgebraHom_map_one _ _ _ _ _
    (GradedAlgebraInverseImage.transportHom_map_one _ _ g hg) U

/-- **The pullback of a unital homomorphism of sheaves of graded algebras**, as a unital
homomorphism. -/
public noncomputable def unitalGradedPull (f : AlgebraicGeometry.RingedToposHom X Y)
    {A B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (g : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    SheafOfModules.GradedAlgebra.UnitalHom ((gradedPull f).obj A) ((gradedPull f).obj B) where
  app n := ((gradedPull f).map g.toHom).app n
  map_mul := ((gradedPull f).map g.toHom).map_mul
  map_one := gradedPull_map_one f g.toHom g.map_one

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- The components of `unitalGradedPull f g` are those of the pullback of the underlying
homomorphism of `g`. -/
@[simp] theorem unitalGradedPull_app (f : AlgebraicGeometry.RingedToposHom X Y)
    {A B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (g : SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℤ) :
    (unitalGradedPull f g).app n = ((gradedPull f).map g.toHom).app n := rfl

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
