module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.AcyclicComplexInvertibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.FlatBaseChange

/-!
# The flat base change map at a module computing both direct images

Let

```
(Sh(C'), O_{C'}) --g'--> (Sh(C), O_C)
      |                       |
      f'                      f
      v                       v
(Sh(D'), O_{D'}) --g-->  (Sh(D), O_D)
```

be a commutative square of ringed topoi with `g` and `g'` flat, and let `F` be an
`O_C`-module.  If `F` is right acyclic for `f_*`, its inverse image `(g')^*F` is right acyclic
for `f'_*`, and the underived base change map `g^*f_*F ⟶ f'_*(g')^*F` is invertible, then the
base change map `g^*Rf_*F ⟶ Rf'_*(g')^*F` of [Stacks, Tag 0736] is invertible at `F[0]`: both
derived direct images are then computed by the underived ones.

The base change map commutes with the shift, so the objects of `D⁺(O_C)` at which it is
invertible form a triangulated subcategory; in particular invertibility at two vertices of a
distinguished triangle gives invertibility at the third.  This is how invertibility is
propagated from the objects at which it is computed to the others.

## Main results

* `Stacks.Cohomology.ToposBaseChange.isIso_baseChangeMap_app_single_of_rightAcyclic`.
* `Stacks.Cohomology.ToposBaseChange.natTransCommShift_baseChangeMap`: the base change map
  commutes with the shift.
* `Stacks.Cohomology.ToposBaseChange.isTriangulated_isIso_baseChangeMap_app`: its invertibility
  locus is a triangulated subcategory.

## References

* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.Sheaves.RingedToposModules

namespace Stacks.Cohomology.ToposBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w

variable {C : RingedTopos.{v₁, u₁, w}} {C' : RingedTopos.{v₂, u₂, w}}
  {D : RingedTopos.{v₃, u₃, w}} {D' : RingedTopos.{v₄, u₄, w}}
  [C.J.HasSheafCompose (forget RingCat.{w})] [C'.J.HasSheafCompose (forget RingCat.{w})]
  [D.J.HasSheafCompose (forget RingCat.{w})] [D'.J.HasSheafCompose (forget RingCat.{w})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify C.J AddCommGrpCat.{w}] [HasSheafify C'.J AddCommGrpCat.{w}]
  [HasSheafify D.J AddCommGrpCat.{w}] [HasSheafify D'.J AddCommGrpCat.{w}]
  [C.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [C'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C'.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))]
  (f : AlgebraicGeometry.RingedToposHom C D)
  (f' : AlgebraicGeometry.RingedToposHom C' D')
  (g : AlgebraicGeometry.RingedToposHom D' D)
  (g' : AlgebraicGeometry.RingedToposHom C' C)
  (comm : pushforwardModules g'.toRingedToposModulesHom ⋙
      pushforwardModules f.toRingedToposModulesHom ≅
    pushforwardModules f'.toRingedToposModulesHom ⋙
      pushforwardModules g.toRingedToposModulesHom)
  (hg : g.IsFlat) (hg' : g'.IsFlat)

/-- **The flat base change map is invertible at a module computing both direct images.**  If
`F` is right acyclic for `f_*`, `(g')^*F` is right acyclic for `f'_*` and the underived base
change map is invertible at `F`, then the base change map `g^*Rf_* ⟶ Rf'_*(g')^*` of
[Stacks, Tag 0736] is invertible at `F[0]`. -/
theorem isIso_baseChangeMap_app_single_of_rightAcyclic
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C.O))
    (hF : (pushforwardModules f.toRingedToposModulesHom).rightAcyclic F)
    (hτ : IsIso ((moduleBaseChange f f' g g' comm).app F))
    (hF' : (pushforwardModules f'.toRingedToposModulesHom).rightAcyclic
      (g'.toRingedToposModulesHom.pullbackModules.obj F)) :
    IsIso ((baseChangeMap f f' g g' comm hg hg').app
      ((DerivedCategory.Plus.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) 0).obj
        F)) := by
  have : IsIso g'.toRingedToposModulesHom.pullbackModules.rightDerivedFunctorPlusUnit :=
    inferInstanceAs (IsIso (flatPullbackComparison g' hg').hom)
  exact Stacks.Cohomology.BaseChange.isIso_derived_app_single_of_rightAcyclic
    (pushforwardModules f.toRingedToposModulesHom)
    (pushforwardModules f'.toRingedToposModulesHom)
    g.toRingedToposModulesHom.pullbackModules
    g'.toRingedToposModulesHom.pullbackModules
    (moduleBaseChange f f' g g' comm) (flatPullbackComparison g hg) F hF hτ hF'

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **The base change map commutes with the shift.**  It is the descent of a comparison on
bounded below homotopy categories each of whose factors commutes with the shift: the underived
base change map applied degreewise, two coherence isomorphisms of degreewise functors, and the
derived-functor units of `R g^*`, `R(g')^*` and `Rf'_*`. -/
theorem natTransCommShift_baseChangeMap :
    NatTrans.CommShift (baseChangeMap f f' g g' comm hg hg') ℤ :=
  Stacks.Cohomology.BaseChange.natTransCommShift_derived _ _ _ _ _ _
    (Stacks.Cohomology.BaseChange.natTransCommShift_onHomotopy _ _ _ _ _ _
      (Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
        g.toRingedToposModulesHom.pullbackModules)
      (Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus _)
      (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso _)
      (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso _))

/-- **The objects at which the base change map is invertible form a triangulated
subcategory** of `D⁺(O_C)`: the base change map is a shift-compatible transformation between
triangulated functors. -/
theorem isTriangulated_isIso_baseChangeMap_app :
    ObjectProperty.IsTriangulated
      (fun E : DerivedCategory.Plus
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) =>
        IsIso ((baseChangeMap f f' g g' comm hg hg').app E)) :=
  let := natTransCommShift_baseChangeMap f f' g g' comm hg hg'
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated _ _ _

end Stacks.Cohomology.ToposBaseChange

end
