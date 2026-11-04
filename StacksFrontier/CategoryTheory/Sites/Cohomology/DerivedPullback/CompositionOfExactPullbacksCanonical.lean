module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfExactPullbacks

/-!
# Composition of derived pullbacks with exact pullbacks of modules, canonical form

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` be morphisms of ringed topoi with
`e : (g ∘ f)^* ≅ h^*`, and suppose the three pullbacks of modules are exact. Then the
identifications `Lφ^* ≅ D(φ^*)` carry the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ Lh^*`
of Stacks 0D6D to the composition isomorphism `D(g^*) ⋙ D(f^*) ≅ D(h^*)` induced by
`g^* ⋙ f^* ≅ (g ∘ f)^* ≅ h^*`. This is
`derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategoryOfIso` with the pullbacks of
modules themselves as the exact functors. The declarations are in the namespace
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`.

## Main results

* `derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategory`: the composition
  isomorphism of derived pullbacks, read through `Lφ^* ≅ D(φ^*)`, is the one induced by the
  composition of the exact pullbacks of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

-- The modules over a ringed topos with independent universes carry no global
-- `HasDerivedCategory` instance; the derived pullbacks are built at the standard model.
attribute [local instance] HasDerivedCategory.standard

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
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-- **Derived pullbacks along morphisms with exact pullbacks of modules compose as those
pullbacks.** The composition isomorphism `Lg^* ⋙ Lf^* ≅ Lh^*` of Stacks 0D6D, read through
`Lφ^* ≅ D(φ^*)`, is the composition isomorphism `D(g^*) ⋙ D(f^*) ≅ D(h^*)`. -/
theorem derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategory
    {h : RingedToposHom X Z}
    (e : (g.comp f).toModulesHom.pullbackModules ≅ h.toModulesHom.pullbackModules)
    [g.toModulesHom.pullbackModules.Additive] [f.toModulesHom.pullbackModules.Additive]
    [h.toModulesHom.pullbackModules.Additive]
    [PreservesFiniteLimits g.toModulesHom.pullbackModules]
    [PreservesFiniteColimits g.toModulesHom.pullbackModules]
    [PreservesFiniteLimits f.toModulesHom.pullbackModules]
    [PreservesFiniteColimits f.toModulesHom.pullbackModules]
    [PreservesFiniteLimits h.toModulesHom.pullbackModules]
    [PreservesFiniteColimits h.toModulesHom.pullbackModules] :
    (derivedPullbackCompIso f g ≪≫ derivedPullbackIsoOfPullbackModulesIso e).hom ≫
        (Stacks.Homology.leftDerivedIsoMapDerivedCategory _ (derivedPullback h)
          (derivedPullbackComparison h)).hom =
      Functor.whiskerRight (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
          (derivedPullback g) (derivedPullbackComparison g)).hom (derivedPullback f) ≫
        Functor.whiskerLeft g.toModulesHom.pullbackModules.mapDerivedCategory
          (Stacks.Homology.leftDerivedIsoMapDerivedCategory _
            (derivedPullback f) (derivedPullbackComparison f)).hom ≫
        (Stacks.Homology.mapDerivedCategoryCompIso g.toModulesHom.pullbackModules
          f.toModulesHom.pullbackModules h.toModulesHom.pullbackModules
          ((RingedToposHom.pullbackModulesCompIso f g).symm ≪≫ e)).hom :=
  derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategoryOfIso f g e _ _ _
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ((RingedToposHom.pullbackModulesCompIso f g).symm ≪≫ e)
    (by simp)

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
