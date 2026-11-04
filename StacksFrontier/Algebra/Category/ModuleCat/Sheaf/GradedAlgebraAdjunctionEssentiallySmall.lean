module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The direct image of sheaves of graded algebras as a functor, at unrelated universes

The direct image of sheaves of graded algebras along a morphism of ringed topoi, as a functor, and
the pullback-pushforward adjunction of sheaves of graded algebras, with the objects, the morphisms
and the sections of the structure sheaf of the ringed topos in three unrelated universes, as for
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, a `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`.
The site of `Y` is assumed `CategoryTheory.EssentiallySmall.{w}`.

## Main definitions

* `pushforwardGradedAlgebraHom` and `pushforwardGradedAlgebraFunctor`: the direct image of a
  homomorphism of sheaves of graded algebras, and the direct image as a functor.
* `pullFunctor` and `pushFunctor` name the two functors the adjunction is between.

## Main results

* `adjunctionOfGradedUnitCounit`: from homomorphisms of sheaves of graded algebras whose
  degreewise components are the unit and the counit of the Stacks 03D7 adjunction for sheaves of
  modules, pullback of sheaves of graded algebras is left adjoint to the direct image.

## Implementation notes

The two ringed topoi share their three universes, as they do in
`Stacks.Sheaves.GradedAlgebraPullback`: the pullback of sheaves of graded algebras is stated for
a morphism between ringed topoi with the same universes, and the adjunction is between that
pullback and the direct image. The direct image itself,
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebra`, is available for two
ringed topoi with six unrelated universes.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
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
  [EssentiallySmall.{w} Y.C]

/-- **The direct image of a homomorphism of sheaves of graded algebras.** It acts degreewise by
the direct image of sheaves of modules. -/
public noncomputable def pushforwardGradedAlgebraHom
    (f : AlgebraicGeometry.RingedToposHom X Y)
    {A A' : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : A ⟶ A') :
    pushforwardGradedAlgebra f A ⟶ pushforwardGradedAlgebra f A' where
  app n := f.pushforwardModules.map (g.app n)
  map_mul i j U left right := by
    apply (pushedSectionEquiv f (A'.piece (i + j)) U).injective
    refine Eq.trans (pushedSectionEquiv_map f (g.app (i + j)) U
      (transposedMultiplicationAt f A i j U left right)) ?_
    ext V element
    exact ((congrArg ((g.app (i + j)).val.app V)
        (transposedMultiplicationAt_apply f A i j U left right V element)).trans
      ((g.map_mul i j V _ _).trans
        ((congrArg₂ (fun a b => ((A'.mul i j).app V a) b)
          (congrArg (fun k => k.hom.app V element)
            (pushedSectionEquiv_map f (g.app i) U left)).symm
          (congrArg (fun k => k.hom.app V element)
            (pushedSectionEquiv_map f (g.app j) U right)).symm).trans
          (transposedMultiplicationAt_apply f A' i j U _ _ V element).symm)))

/-- **The direct image of sheaves of graded algebras along a morphism of ringed topoi, as a
functor.** Its value on a sheaf of graded algebras is `pushforwardGradedAlgebra`, and its
degreewise components are the direct images of the degreewise components. -/
public noncomputable def pushforwardGradedAlgebraFunctor
    (f : AlgebraicGeometry.RingedToposHom X Y) :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) where
  obj A := pushforwardGradedAlgebra f A
  map g := pushforwardGradedAlgebraHom f g
  map_id A := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    exact f.pushforwardModules.map_id (A.piece n)
  map_comp g h := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    exact f.pushforwardModules.map_comp (g.app n) (h.app n)

section Adjunction

variable (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The pullback functor of sheaves of graded algebras of Stacks 0FQX part (2). -/
public noncomputable abbrev pullFunctor :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  toposPullbackGradedAlgebraFunctor f.toRingedToposModulesHom

/-- The direct-image functor of sheaves of graded algebras of Stacks 0FQX part (1). -/
public noncomputable abbrev pushFunctor :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  pushforwardGradedAlgebraFunctor f

/-- **Part (3) of Stacks 0FQX, reduced to the two degreewise multiplicativity facts.** Given
homomorphisms of sheaves of graded algebras whose degreewise components are the unit and the
counit of the Stacks 03D7 adjunction for sheaves of modules, pullback of sheaves of graded
algebras is left adjoint to the direct image, and the right adjoint has the direct-image graded
algebras as its values on objects. -/
public noncomputable def adjunctionOfGradedUnitCounit
    (gradedUnit : ∀ B : SheafOfModules.GradedAlgebra.{w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      B ⟶ (pushFunctor f).obj ((pullFunctor f).obj B))
    (gradedCounit : ∀ A : SheafOfModules.GradedAlgebra.{w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (pullFunctor f).obj ((pushFunctor f).obj A) ⟶ A)
    (gradedUnit_app : ∀ B n, (gradedUnit B).app n =
      f.pullbackAdjPushforwardModulesViaComparison.unit.app (B.piece n))
    (gradedCounit_app : ∀ A n, (gradedCounit A).app n =
      f.pullbackAdjPushforwardModulesViaComparison.counit.app (A.piece n)) :
    Σ G : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      { _adj : (gradedAlgebraPullbackSpecification f.toRingedToposModulesHom).1 ⊣ G //
        ∀ A, G.obj A = pushforwardGradedAlgebra f A } :=
  ⟨pushFunctor f,
    { unit :=
        { app := gradedUnit
          naturality := fun B B' g => by
            refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
            refine Eq.trans (congrArg (fun k => g.app n ≫ k) (gradedUnit_app B' n)) ?_
            refine Eq.trans ?_ (congrArg (fun k => k ≫
              f.pushforwardModules.map ((f.toRingedToposModulesHom.pullbackModules).map (g.app n)))
              (gradedUnit_app B n)).symm
            exact f.pullbackAdjPushforwardModulesViaComparison.unit.naturality (g.app n) }
      counit :=
        { app := gradedCounit
          naturality := fun A A' g => by
            refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
            refine Eq.trans (congrArg (fun k => (f.toRingedToposModulesHom.pullbackModules).map
                (f.pushforwardModules.map (g.app n)) ≫ k)
              (gradedCounit_app A' n)) ?_
            refine Eq.trans ?_
              (congrArg (fun k => k ≫ g.app n) (gradedCounit_app A n)).symm
            exact f.pullbackAdjPushforwardModulesViaComparison.counit.naturality (g.app n) }
      left_triangle_components := fun B => by
        refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
        refine Eq.trans
          (congrArg₂ (fun a b => (f.toRingedToposModulesHom.pullbackModules).map a ≫ b)
          (gradedUnit_app B n)
          (gradedCounit_app ((pullFunctor f).obj B) n)) ?_
        exact f.pullbackAdjPushforwardModulesViaComparison.left_triangle_components (B.piece n)
      right_triangle_components := fun A => by
        refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
        refine Eq.trans (congrArg₂ (fun a b => a ≫ f.pushforwardModules.map b)
          (gradedUnit_app ((pushFunctor f).obj A) n) (gradedCounit_app A n)) ?_
        exact f.pullbackAdjPushforwardModulesViaComparison.right_triangle_components (A.piece n) },
    fun _ => rfl⟩

end Adjunction

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
