module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# The compositor of degreewise pullbacks on homotopy categories, at the quotient of a complex

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of ringed topoi and a complex `N` of `𝒪_Z`-modules,
the compositor
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso` of degreewise
pullbacks on the unbounded homotopy categories, at the quotient of `N`, is the quotient of the
compositor `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of Stacks 03D6 applied
degreewise.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

noncomputable section

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

omit [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The compositor of degreewise pullbacks on homotopy categories, at the quotient of a
complex**, followed by an isomorphism `t` out of the pullback along the composite, is the
quotient of `τ` applied degreewise, for any `τ` equal to the inverse of the compositor
`RingedToposHom.pullbackModulesCompIso f g` followed by `t`. -/
theorem pullbackMapHomotopyCompIso_trans_hom_app_quotient {P : SheafOfModules.{w''}
      (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
        SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    [P.Additive] (t : (g.comp f).toModulesHom.pullbackModules ≅ P)
    (N : CochainComplex (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (τ : g.toModulesHom.pullbackModules ⋙ f.toModulesHom.pullbackModules ⟶ P)
    (hτ : ((RingedToposHom.pullbackModulesCompIso f g).symm ≪≫ t).hom = τ) :
    (pullbackMapHomotopyCompIso f g ≪≫
        Stacks.Homology.mapHomotopyCategoryIso t (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app N) := by
  subst hτ
  change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso (RingedToposHom.pullbackModulesCompIso f g).symm
        (ComplexShape.up ℤ)).hom.app N) ≫
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex t.hom (ComplexShape.up ℤ)).app N) = _
  rw [← Functor.map_comp]
  congr 1

end

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
