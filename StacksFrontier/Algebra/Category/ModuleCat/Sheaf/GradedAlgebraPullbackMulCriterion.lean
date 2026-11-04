module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraCounitEssentiallySmall

/-!
# Homomorphisms out of a pullback of a sheaf of graded algebras, tested on inverse images

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `B` be a sheaf of graded
`O_D`-algebras and `A` a sheaf of graded `O_C`-algebras, and let
`e_n : f^*(B_n) ⟶ A_n` be a family of morphisms of sheaves of `O_C`-modules.  Each `e_n` has an
underlying morphism of sheaves of sets out of the inverse image `f⁻¹B_n`: the change-of-rings
unit `x ↦ 1 ⊗ x` followed by `e_n`.  This file proves that **the family `e` preserves products of
homogeneous local sections as soon as those underlying morphisms of sheaves of sets commute with
the multiplications**, the one of `B` carried along `f⁻¹`.

This is the argument which makes the counit of the graded pullback–pushforward adjunction
multiplicative (`Stacks.Sheaves.GradedAlgebraEssentiallySmall.counitApp`), with the counit
replaced by an arbitrary family: a pullback is an extension of scalars, so two bilinear maps out
of it agree once they agree on pure tensors `1 ⊗ x`, and on those the family is its underlying
morphism of sheaves of sets.  The multiplicativity condition is an equation between morphisms of
sheaves of sets on `C`, so it can be checked wherever the inverse image is understood — for an
étale morphism of algebraic spaces, where the inverse image is a restriction.

## Main definitions

* `pullbackSetMap`: the underlying morphism of sheaves of sets `f⁻¹B_n ⟶ A_n` of a degreewise
  family out of a pullback.
* `IsInverseImageMultiplicative`: those morphisms commute with the multiplications.
* `homOfInverseImageMultiplicative`: **the family as a homomorphism of sheaves of graded algebras
  `f^*B ⟶ A`.**

## Main results

* `pullbackSetMap_mul_inverseImageSections`: the condition read on a pair of local sections of the
  inverse images.
* `map_mul_scalarUnit_of_isInverseImageMultiplicative`: the family is multiplicative on pure
  tensors.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraExtendScalars
open Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraPullback

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

variable {X Y : RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposHom X Y)
  (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (e : ∀ n : ℤ, f.toRingedToposModulesHom.pullbackModules.obj (B.piece n) ⟶ A.piece n)

/-- **The underlying morphism of sheaves of sets of a degreewise family out of a pullback**: the
change-of-rings unit `x ↦ 1 ⊗ x` from the inverse image `f⁻¹B_n` to the pullback `f^*B_n`,
followed by `e_n`. -/
public noncomputable abbrev pullbackSetMap (n : ℤ) :
    f.toToposHom.inverseImage.obj (Stacks.underlyingModuleSheaf Y.J (B.piece n)) ⟶
      Stacks.underlyingModuleSheaf X.J (A.piece n) :=
  pullbackScalarUnit f (B.piece n) ≫
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map (e n)

/-- **The underlying morphisms of sheaves of sets of a degreewise family out of a pullback commute
with the multiplications**: the inverse image of the multiplication of `B`, followed by the
underlying morphism in the sum degree, is the pair of underlying morphisms followed by the
multiplication of `A`. -/
public def IsInverseImageMultiplicative : Prop :=
  ∀ i j : ℤ,
    f.toToposHom.inverseImage.map (mulSheafHom B i j) ≫ pullbackSetMap f B A e (i + j) =
      Limits.prod.lift
          (f.toToposHom.inverseImage.map (Limits.prod.fst :
              Stacks.underlyingModuleSheaf Y.J (B.piece i) ⨯
                Stacks.underlyingModuleSheaf Y.J (B.piece j) ⟶ _) ≫
            pullbackSetMap f B A e i)
          (f.toToposHom.inverseImage.map (Limits.prod.snd :
              Stacks.underlyingModuleSheaf Y.J (B.piece i) ⨯
                Stacks.underlyingModuleSheaf Y.J (B.piece j) ⟶ _) ≫
            pullbackSetMap f B A e j) ≫
        mulSheafHom A i j

variable {f B A e}

/-- **The multiplicativity condition, read on local sections of the inverse images.**  The
multiplication of an inverse image is the inverse image of the multiplication, read on a pair of
sections through the sections functor; this is the condition read through the same functor. -/
public theorem pullbackSetMap_mul_inverseImageSections
    (he : IsInverseImageMultiplicative f B A e) (i j : ℤ) (U : X.Cᵒᵖ)
    (x : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i).val.obj U)
    (y : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j).val.obj U) :
    (pullbackSetMap f B A e (i + j)).hom.app U
        (((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app U x y) =
      (A.mul i j).app U ((pullbackSetMap f B A e i).hom.app U x)
        ((pullbackSetMap f B A e j).hom.app U y) := by
  have happ := congrArg
    (fun k => (Sheaf.sectionsFunctor X.J U).map k
      (CategoryTheory.Functor.prodObjMk
        (P := transportSections X.J f.toToposHom.inverseImage U) x y))
    (he i j)
  refine Eq.trans ?_ (Eq.trans happ ?_)
  · exact (((Sheaf.sectionsFunctor X.J U).map_comp_apply _ _ _).trans
      (Sheaf.sectionsFunctor_map_apply _ _)).symm
  · have hcomp : ∀ {Z W : X.Topos}
        (p : f.toToposHom.inverseImage.obj (Stacks.underlyingModuleSheaf Y.J (B.piece i) ⨯
          Stacks.underlyingModuleSheaf Y.J (B.piece j)) ⟶ Z) (q : Z ⟶ W),
        (Sheaf.sectionsFunctor X.J U).map (p ≫ q)
          (CategoryTheory.Functor.prodObjMk
            (P := transportSections X.J f.toToposHom.inverseImage U) x y) =
          q.hom.app U ((Sheaf.sectionsFunctor X.J U).map p
            (CategoryTheory.Functor.prodObjMk
              (P := transportSections X.J f.toToposHom.inverseImage U) x y)) :=
      fun p q => ((Sheaf.sectionsFunctor X.J U).map_comp_apply _ _ _).trans
        (Sheaf.sectionsFunctor_map_apply _ _)
    have hx := (hcomp (f.toToposHom.inverseImage.map Limits.prod.fst)
      (pullbackSetMap f B A e i)).trans
      (congrArg (fun t => (pullbackSetMap f B A e i).hom.app U t)
        (CategoryTheory.Functor.map_fst_prodObjMk
          (P := transportSections X.J f.toToposHom.inverseImage U) x y))
    have hy := (hcomp (f.toToposHom.inverseImage.map Limits.prod.snd)
      (pullbackSetMap f B A e j)).trans
      (congrArg (fun t => (pullbackSetMap f B A e j).hom.app U t)
        (CategoryTheory.Functor.map_snd_prodObjMk
          (P := transportSections X.J f.toToposHom.inverseImage U) x y))
    refine Eq.trans ((Sheaf.sectionsFunctor X.J U).map_comp_apply _ _ _) ?_
    refine Eq.trans ?_ (sections_mulSheafHom A i j U
      ((pullbackSetMap f B A e i).hom.app U x) ((pullbackSetMap f B A e j).hom.app U y))
    refine congrArg ((Sheaf.sectionsFunctor X.J U).map (mulSheafHom A i j)) ?_
    refine Eq.trans (CategoryTheory.Functor.map_lift_apply _ _ _) ?_
    exact congrArg₂ (fun a b => CategoryTheory.Functor.prodObjMk
      (P := Sheaf.sectionsFunctor X.J U)
      (A := Stacks.underlyingModuleSheaf X.J (A.piece i))
      (B := Stacks.underlyingModuleSheaf X.J (A.piece j)) a b) hx hy

/-- The underlying morphism of sheaves of sets of a degreewise family, on a section of the inverse
image: the family applied to the pure tensor `1 ⊗ x`. -/
public theorem pullbackSetMap_hom_app (n : ℤ) (V : X.Cᵒᵖ)
    (z : ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      (B.piece n)).val.obj V) :
    (pullbackSetMap f B A e n).hom.app V z =
      (e n).val.app V ((pullbackScalarUnit f (B.piece n)).hom.app V z) :=
  sheafHom_comp_app_apply X.J (pullbackScalarUnit f (B.piece n))
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map (e n)) V z

/-- **A degreewise family satisfying the multiplicativity condition preserves products of pure
tensors.**  The product of two pure tensors `1 ⊗ a` and `1 ⊗ b` of a pullback is the pure tensor
`1 ⊗ ab` of the product in the inverse image, and on pure tensors the family is its underlying
morphism of sheaves of sets. -/
public theorem map_mul_scalarUnit_of_isInverseImageMultiplicative
    (he : IsInverseImageMultiplicative f B A e) (i j : ℤ) (V : X.Cᵒᵖ)
    (a : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i).val.obj V)
    (b : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j).val.obj V) :
    (e (i + j)).val.app V
        (((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).mul i j).app V
          ((pullbackScalarUnit f (B.piece i)).hom.app V a)
          ((pullbackScalarUnit f (B.piece j)).hom.app V b)) =
      (A.mul i j).app V
        ((e i).val.app V ((pullbackScalarUnit f (B.piece i)).hom.app V a))
        ((e j).val.app V ((pullbackScalarUnit f (B.piece j)).hom.app V b)) := by
  refine Eq.trans (congrArg (fun t => (e (i + j)).val.app V t)
    (pullbackScalarUnit_mul f B i j V a b).symm) ?_
  refine Eq.trans (pullbackSetMap_hom_app (e := e) (i + j) V _).symm ?_
  refine Eq.trans (pullbackSetMap_mul_inverseImageSections he i j V a b) ?_
  exact congrArg₂ (fun s t => (A.mul i j).app V s t)
    (pullbackSetMap_hom_app (e := e) i V a) (pullbackSetMap_hom_app (e := e) j V b)

variable (f B A e) in
/-- **A degreewise family out of a pullback which satisfies the multiplicativity condition, as a
homomorphism of sheaves of graded algebras `f^*B ⟶ A`.**  Both sides of multiplicativity are
bilinear maps of two extensions of scalars, so it is enough to check them on pure tensors, which
is `map_mul_scalarUnit_of_isInverseImageMultiplicative`. -/
public noncomputable def homOfInverseImageMultiplicative
    (he : IsInverseImageMultiplicative f B A e) :
    toposPullbackGradedAlgebra f.toRingedToposModulesHom B ⟶ A where
  app := e
  map_mul i j U x y :=
    scalarExtension_bilinear_ext f
      ((inverseImageGradedAlgebra f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i)
      ((inverseImageGradedAlgebra f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j)
      (A.piece (i + j))
      (bilinearPostcomp
        (M := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i)).val)
        (N := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j)).val)
        (P := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece (i + j))).val)
        (Q := (A.piece (i + j)).val)
        ((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).mul i j) (e (i + j)).val)
      (Stacks.BilinearMap.compRight
        (Stacks.BilinearMap.compLeft
          (M := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i)).val)
          (A.mul i j) (e i).val)
        (N := (scalarExtend f ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j)).val)
        (e j).val)
      (map_mul_scalarUnit_of_isInverseImageMultiplicative he i j) U x y

/-- The degreewise components of `homOfInverseImageMultiplicative` are the given family. -/
public theorem homOfInverseImageMultiplicative_app (he : IsInverseImageMultiplicative f B A e)
    (n : ℤ) : (homOfInverseImageMultiplicative f B A e he).app n = e n :=
  rfl

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
