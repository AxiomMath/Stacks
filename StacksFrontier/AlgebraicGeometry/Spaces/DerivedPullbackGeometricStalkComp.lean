module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineDegreewise
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackStalkFunctorIsoComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import
    StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompChase
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Tactic.HEqCongr

/-!
# Composition of derived pullback-stalk comparisons

For morphisms `g₁ : X'' ⟶ X'` and `g₂ : X' ⟶ X` of algebraic spaces and a geometric point `x̄` of
`X''`, the comparison `K_{x̄} ⊗ᴸ 𝒪_{X'',x̄} ⟶ (L(g₁ ≫ g₂)^*K)_x̄` of
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedPullbackGeometricStalk.lean` is the comparison along
`g₂`, extended along the stalk map of `g₁`, followed by the comparison along `g₁`, once
`L(g₁ ≫ g₂)^*` is identified with `Lg₁^* ∘ Lg₂^*`.

## Main results

* `AlgebraicGeometry.Space.derivedPullbackGeometricStalkMap_comp`: the composition law.
* `AlgebraicGeometry.Space.derivedPullbackGeometricStalkComplexMap_comp`: its form on complexes.

## Implementation notes

The law is checked after the counit of `L(g₁ ≫ g₂)^*` on classes of complexes, where it is the
generic chase `CochainComplex.DerivedExtensionScalars.comparison_comp_chase`. The spaces-level
statements are kept small: heavy terms enter the chase through the types of separately proved
lemmas, and the naturality step is stated as the type of the generic lemma it instantiates.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] HasDerivedCategory.standard


namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


variable {B S hS} in
/-- The derived pullback-stalk comparison at the class of a complex, followed by the stalk of the
comparison of `Lg^*`, is the comparison on the homotopy category. -/
theorem derivedPullbackGeometricStalkMap_app_comp_map_comparison_app
    {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X) (x' : GeometricPoint B S hS X'.1)
    (L : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (derivedPullbackGeometricStalkMap g x').app (DerivedCategory.Qh.obj L) ≫
        (geometricDerivedStalk B S hS x').map
          ((smallEtaleDerivedModulePullbackComparison B S hS g).app L) =
      (derivedPullbackGeometricStalkHomotopyMap g x').app L :=
  (congrArg (_ ≫ ·) (Category.id_comp _).symm).trans (derivedPullbackGeometricStalkMap_fac g x' L)


variable {B S hS} in
/-- The comparison on complexes, written out. -/
theorem derivedPullbackGeometricStalkComplexMap_app_eq {X' X : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) (y : GeometricPoint B S hS X'.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (derivedPullbackGeometricStalkComplexMap g y).app P =
      ((geometricStalkDerivedExtension g y).functor.map
          ((geometricDerivedStalk B S hS (geometricPointMap g.hom y)).map
            ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS X))).hom.app P)) ≫
        (geometricStalkDerivedExtension g y).functor.map
          ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 (geometricPointMap g.hom y)
                    X.2)
            (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryFactors.hom.app P)) ≫
        (geometricStalkDerivedExtension g y).comparison.app
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
                      (geometricPointMap g.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        ((eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
          (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g y))).hom.app P ≫
        DerivedCategory.Q.map ((pullbackStalkComplexNatIso g y).inv.app P) ≫
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 y X'.2)
          (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.inv.app
            (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
        (geometricDerivedStalk B S hS y).map ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS X'))).inv.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        (geometricDerivedStalk B S hS y).map (DerivedCategory.Qh.map
          (((smallEtaleRingedToposHom B S hS
                    g).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app P))) :=
  (derivedPullbackGeometricStalkComplexMap_app g y P).trans
    (CategoryTheory.Functor.comp_comp_congr _ (derivedExtensionGeometricStalkComplexIso_hom_app g y
            P)
      (extensionGeometricStalkComplexIso_hom_app g y P))

variable {B S hS} in
/-- The comparison on complexes along a composite, written out at the image of the point. -/
theorem derivedPullbackGeometricStalkComplexMap_comp_app_eq {X'' X' X : AlgebraicSpaces B S hS}
    (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X) (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (derivedPullbackGeometricStalkComplexMap (g₁ ≫ g₂) x).app P =
      ((geometricStalkDerivedExtension (g₁ ≫ g₂) x).functor.map
          ((geometricDerivedStalk B S hS (geometricPointMap g₂.hom
                    (geometricPointMap g₁.hom x))).map
            ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS X))).hom.app P)) ≫
        (geometricStalkDerivedExtension (g₁ ≫ g₂) x).functor.map
          ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
                    (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
            (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryFactors.hom.app P)) ≫
        (geometricStalkDerivedExtension (g₁ ≫ g₂) x).comparison.app
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
                      (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        ((eqToIso (congrArg (fun φ => (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
          (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived (g₁ ≫ g₂) x))).hom.app
              P ≫
        DerivedCategory.Q.map ((pullbackStalkComplexNatIso (g₁ ≫ g₂) x).inv.app P) ≫
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
          (smallEtaleRingedTopos B S hS X'').O).mapDerivedCategoryFactors.inv.app
            (((smallEtaleRingedToposHom B S hS
                      (g₁ ≫ g₂)).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
        (geometricDerivedStalk B S hS x).map ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS X''))).inv.app
          (((smallEtaleRingedToposHom B S hS
                    (g₁ ≫ g₂)).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        (geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
          (((smallEtaleRingedToposHom B S hS
                    (g₁ ≫ g₂)).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app P))) :=
  (derivedPullbackGeometricStalkComplexMap_app_eq (g₁ ≫ g₂) x P).trans (eq_of_heq (by heq_congr))

/-- Two terms equal up to casts are equal if the terms they are cast from are. -/
private theorem eq_of_heq_of_eq_of_heq.{w} {α β : Sort w} {a b : α} {x y : β} (h : x = y)
    (h₁ : HEq a x) (h₂ : HEq y b) : a = b :=
  eq_of_heq (h₁.trans ((heq_of_eq h).trans h₂))

section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose
attribute [local instance 10000] AlgebraicGeometry.Space.hasSheafCompose_smallEtale_forget₂_ringCat

variable {B S hS} in
/-- Stacks 05V5 for complexes along a composite `g₁ ≫ g₂`: its inverse is the composite of the
inverses along `g₂` and along `g₁`, through the composition of extensions of scalars. -/
theorem pullbackStalkComplexNatIso_comp_inv_app {X'' X' X : AlgebraicSpaces B S hS}
    (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X) (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
    (pullbackStalkComplexNatIso (g₁ ≫ g₂) x).inv.app P =
      eqToHom (congrArg (fun χ => ((ModuleCat.extendScalars χ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((Stacks.sheafModuleFiberOfCommRing
                (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))
                  X.2) (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))
          (smallEtaleStalkPullbackRingMap_comp g₁ g₂ x)) ≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp
              (smallEtaleStalkPullbackRingMap B S hS g₂ (geometricPointMap g₁.hom x))
              (smallEtaleStalkPullbackRingMap B S hS g₁ x))
        (ComplexShape.up ℤ)).hom.app (((Stacks.sheafModuleFiberOfCommRing
                (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))
                  X.2) (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
      ((ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g₁ x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
        ((pullbackStalkComplexNatIso g₂ (geometricPointMap g₁.hom x)).inv.app P) ≫
      (pullbackStalkComplexNatIso g₁ x).inv.app (((smallEtaleRingedToposHom B S hS
                g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
                (smallEtaleRingedTopos B S hS X'').O).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((Functor.mapHomologicalComplexCompIso (RingedToposHom.pullbackModulesCompIso
                    (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂)).symm
                  (ComplexShape.up ℤ)).hom.app P) ≫ ((NatTrans.mapHomologicalComplex
                  (pullbackModulesCompTransport B S hS g₁ g₂).hom (ComplexShape.up ℤ)).app
                P))) := by
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
  have := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
    (smallEtaleRingedTopos B S hS X).O
  have := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
        (smallEtaleRingedTopos B S hS X').O
  have := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
    (smallEtaleRingedTopos B S hS X'').O
  have k := CochainComplex.DerivedExtensionScalars.mapHomologicalComplex_comp_inv_app_eq
    (R₀ := Stacks.ringFiber (etaleSitePoint B S hS X.1
      (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2) (smallEtaleRingedTopos B S hS
          X).O.obj)
    (R' := Stacks.ringFiber (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
      (smallEtaleRingedTopos B S hS X').O.obj)
    (R'' := Stacks.ringFiber (etaleSitePoint B S hS X''.1 x X''.2)
      (smallEtaleRingedTopos B S hS X'').O.obj)
    (pre := SheafOfModules.instPreadditive _) (pre' := SheafOfModules.instPreadditive _)
    (pre'' := SheafOfModules.instPreadditive _)
    (smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules
        (smallEtaleRingedToposHom B S hS g₁).toModulesHom.pullbackModules
    (smallEtaleRingedToposHomComp B S hS g₁ g₂).toModulesHom.pullbackModules
        (smallEtaleRingedToposHom B S hS (g₁ ≫ g₂)).toModulesHom.pullbackModules
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
          (smallEtaleRingedTopos B S hS X).O) (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
          (smallEtaleRingedTopos B S hS X').O) (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X''.1 x X''.2) (smallEtaleRingedTopos B S hS X'').O)
    (smallEtaleStalkPullbackRingMap B S hS g₂ (geometricPointMap g₁.hom x))
        (smallEtaleStalkPullbackRingMap B S hS g₁ x) (smallEtaleStalkPullbackRingMap B S hS
          (g₁ ≫ g₂) x) (smallEtaleStalkPullbackRingMap_comp g₁ g₂ x)
    (pullbackStalkFunctorIso g₂ (geometricPointMap g₁.hom x)) (pullbackStalkFunctorIso g₁ x)
    (pullbackStalkFunctorIso (g₁ ≫ g₂) x)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g₁)
      (smallEtaleRingedToposHom B S hS g₂)).symm
    (pullbackModulesCompTransport B S hS g₁ g₂)
    (fun M => eq_of_heq_of_eq_of_heq (pullbackStalkFunctorIso_comp_inv_app g₁ g₂ x M)
      (by heq_congr) (by heq_congr))
    (pullbackStalkComplexNatIso g₂ (geometricPointMap g₁.hom x))
    (pullbackStalkComplexNatIso.eq_1 g₂ (geometricPointMap g₁.hom x))
    (pullbackStalkComplexNatIso g₁ x) (pullbackStalkComplexNatIso.eq_1 g₁ x)
    (pullbackStalkComplexNatIso (g₁ ≫ g₂) x)
    ((pullbackStalkComplexNatIso.eq_1 (g₁ ≫ g₂) x).trans (eq_of_heq (by heq_congr))) P
  exact eq_of_heq_of_eq_of_heq k (by heq_congr) (by heq_congr)

end

variable {B S hS} in
/-- The identification of the derived stalk of a pulled back complex with its stalk complex,
followed by its inverse, is the identity. -/
theorem derivedPullbackGeometricStalk_cancel {X'' X' X : AlgebraicSpaces B S hS}
    (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X) (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x)
            X'.2) (smallEtaleRingedTopos B S hS X').O).mapDerivedCategoryFactors.inv.app
        (((smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫ (geometricDerivedStalk B S hS
          (geometricPointMap g₁.hom x)).map ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))).inv.app
          (((smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
      (geometricDerivedStalk B S hS (geometricPointMap g₁.hom x)).map
          (DerivedCategory.Qh.map (((smallEtaleRingedToposHom B S hS
                  g₂).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app P)) ≫
      (geometricDerivedStalk B S hS (geometricPointMap g₁.hom x)).map
          ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
                (ringedToposStructureRingSheaf B S hS X'))).hom.app
            (((smallEtaleRingedToposHom B S hS
                  g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              P)) ≫ (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1
              (geometricPointMap g₁.hom x) X'.2) (smallEtaleRingedTopos B S hS
              X').O).mapDerivedCategoryFactors.hom.app (((smallEtaleRingedToposHom B S hS
                g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
          𝟙 _ :=
  CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_comp_cancel
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x)
          X'.2) (smallEtaleRingedTopos B S hS X').O) (((smallEtaleRingedToposHom B S hS
            g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    ((geometricDerivedStalk B S hS (geometricPointMap g₁.hom x)).map
          (DerivedCategory.Qh.map (((smallEtaleRingedToposHom B S hS
                  g₂).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app P))) (CategoryTheory.Functor.map_map_eq_id _ _ _ rfl)

variable {B S hS} in
/-- The naturality of the inverse identification of derived stalks with stalk complexes along the
composition of degreewise pullbacks, at the stalk at `x̄`. -/
theorem derivedPullbackGeometricStalk_comp_naturality {X'' X' X : AlgebraicSpaces B S hS}
    (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X) (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    type_of% (CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_comp_map
      (ab := SheafOfModules.instAbelian _) (pre := SheafOfModules.instPreadditive _)
      (pre' := SheafOfModules.instPreadditive _)
      (hp₁₂' := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂))
      (hF := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
        (smallEtaleRingedTopos B S hS X'').O)
      (smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules
          (smallEtaleRingedToposHom B S hS g₁).toModulesHom.pullbackModules
          (smallEtaleRingedToposHomComp B S hS g₁ g₂).toModulesHom.pullbackModules
          (smallEtaleRingedToposHom B S hS (g₁ ≫ g₂)).toModulesHom.pullbackModules
          (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
            (smallEtaleRingedTopos B S hS X'').O)
      (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g₁)
        (smallEtaleRingedToposHom B S hS g₂)).symm
      (pullbackModulesCompTransport B S hS g₁ g₂) P
      ((geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
              (((smallEtaleRingedToposHom B S hS
                    g₁).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app (((smallEtaleRingedToposHom B S hS
                  g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              P)))) (CategoryTheory.Functor.map_map_eq_id _ _ _ rfl)
      ((geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
              (((smallEtaleRingedToposHom B S hS
                    (g₁ ≫ g₂)).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app P))) (CategoryTheory.Functor.map_map_eq_id _ _ _ rfl)) :=
  CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_comp_map
    (ab := SheafOfModules.instAbelian _) (pre := SheafOfModules.instPreadditive _)
    (pre' := SheafOfModules.instPreadditive _)
    (hp₁₂' := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂))
    (hF := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
      (smallEtaleRingedTopos B S hS X'').O)
    (smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules
        (smallEtaleRingedToposHom B S hS g₁).toModulesHom.pullbackModules
        (smallEtaleRingedToposHomComp B S hS g₁ g₂).toModulesHom.pullbackModules
        (smallEtaleRingedToposHom B S hS (g₁ ≫ g₂)).toModulesHom.pullbackModules
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
          (smallEtaleRingedTopos B S hS X'').O)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g₁)
      (smallEtaleRingedToposHom B S hS g₂)).symm
    (pullbackModulesCompTransport B S hS g₁ g₂) P
    ((geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
            (((smallEtaleRingedToposHom B S hS
                  g₁).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app (((smallEtaleRingedToposHom B S hS
                g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)))) (CategoryTheory.Functor.map_map_eq_id _ _ _ rfl)
    ((geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
            (((smallEtaleRingedToposHom B S hS
                  (g₁ ≫ g₂)).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app P))) (CategoryTheory.Functor.map_map_eq_id _ _ _ rfl)

variable {B S hS} in
/-- The composition law of the derived pullback-stalk comparison on complexes along `g₁ ≫ g₂`. -/
theorem derivedPullbackGeometricStalkComplexMap_comp {X'' X' X : AlgebraicSpaces B S hS}
    (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X) (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
    (derivedPullbackGeometricStalkComplexMap (g₁ ≫ g₂) x).app P =
      eqToHom
          (congrArg
            (fun φ => (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor.obj
        ((geometricDerivedStalk B S hS (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))).obj
              (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))))
            (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv.app _ ≫
          (geometricStalkDerivedExtension g₁ x).functor.map
          ((derivedPullbackGeometricStalkComplexMap g₂ (geometricPointMap g₁.hom x)).app P) ≫
          (derivedPullbackGeometricStalkComplexMap g₁ x).app
          (((smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
      (geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
            ((Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
                (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂) ≪≫
                Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
                (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                P))) := by
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
  refine (derivedPullbackGeometricStalkComplexMap_comp_app_eq g₁ g₂ x P).trans
    (Eq.trans ?_ (CategoryTheory.Functor.comp_map_comp_congr
            (geometricStalkDerivedExtension g₁ x).functor _ _
      (derivedPullbackGeometricStalkComplexMap_app_eq g₂ (geometricPointMap g₁.hom x) P).symm
      (derivedPullbackGeometricStalkComplexMap_app_eq g₁ x
            (((smallEtaleRingedToposHom B S hS
                  g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              P)).symm _))
  have key := CochainComplex.DerivedExtensionScalars.comparison_comp_chase
    (R₀ := Stacks.ringFiber (etaleSitePoint B S hS X.1
      (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2) (smallEtaleRingedTopos B S hS
          X).O.obj)
    (R' := Stacks.ringFiber (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
      (smallEtaleRingedTopos B S hS X').O.obj)
    (R'' := Stacks.ringFiber (etaleSitePoint B S hS X''.1 x X''.2)
      (smallEtaleRingedTopos B S hS X'').O.obj)
    (pre₀ := SheafOfModules.instPreadditive _) (pre' := SheafOfModules.instPreadditive _)
    (hF₀ := Stacks.instAdditiveSheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
          (smallEtaleRingedTopos B S hS X).O)
    (hF' := Stacks.instAdditiveSheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
          (smallEtaleRingedTopos B S hS X').O) (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
          (smallEtaleRingedTopos B S hS X).O) (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
          (smallEtaleRingedTopos B S hS X').O) P (((smallEtaleRingedToposHom B S hS
              g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
        (smallEtaleStalkPullbackRingMap B S hS g₂ (geometricPointMap g₁.hom x))
        (stalkStructureMap B S hS g₁ x).hom (smallEtaleStalkPullbackRingMap B S hS g₁ x)
        (stalkStructureMap B S hS (g₁ ≫ g₂) x).hom (smallEtaleStalkPullbackRingMap B S hS (g₁ ≫ g₂)
          x)
    (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g₂
          (geometricPointMap g₁.hom x))
    (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived g₁ x)
    (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived (g₁ ≫ g₂) x)
    (stalkStructureMap_comp_hom B S hS g₁ g₂ x) (smallEtaleStalkPullbackRingMap_comp g₁ g₂ x)
    ((geometricStalkDerivedExtension g₂ (geometricPointMap g₁.hom x)).comparison.app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
                  (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
                (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)) rfl
    ((geometricStalkDerivedExtension g₁ x).comparison.app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x)
                  X'.2) (smallEtaleRingedTopos B S hS X').O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (((smallEtaleRingedToposHom B S hS
                  g₂).toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              P))) rfl
    ((geometricStalkDerivedExtension (g₁ ≫ g₂) x).comparison.app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
                  (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
                (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)) rfl
    ((geometricDerivedStalk B S hS (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))).map
          ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
                (ringedToposStructureRingSheaf B S hS X))).hom.app P))
        ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1
              (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
            (smallEtaleRingedTopos B S hS X).O).mapDerivedCategoryFactors.hom.app P)
    _ _ _ _ _ _
    (derivedPullbackGeometricStalk_cancel g₁ g₂ x P)
    _ _ _
    (pullbackStalkComplexNatIso_comp_inv_app g₁ g₂ x P)
    _ _ _ _ _ _ _
    (derivedPullbackGeometricStalk_comp_naturality g₁ g₂ x P)
  exact eq_of_heq_of_eq_of_heq key (by heq_congr) (by heq_congr)

open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
/-- The composition law of the derived pullback-stalk comparison on the homotopy category, at
the class of a complex. -/
theorem derivedPullbackGeometricStalkHomotopyMap_comp {X'' X' X : AlgebraicSpaces B S hS}
    (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X) (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
    (derivedPullbackGeometricStalkHomotopyMap (g₁ ≫ g₂) x).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) =
      eqToHom (congrArg (fun φ =>
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj ((geometricDerivedStalk B S hS
                (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))).obj
                  (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                          P))))
            (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv.app _ ≫
        (geometricStalkDerivedExtension g₁ x).functor.map
            ((derivedPullbackGeometricStalkHomotopyMap g₂ (geometricPointMap g₁.hom x)).app
                  ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackGeometricStalkHomotopyMap g₁ x).app
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (smallEtaleRingedToposHom B S hS g₂)).obj
                  ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
          ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS g₁)
              (smallEtaleRingedToposHom B S hS g₂) ≪≫
            Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
              (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                  P))) := by
  have h₁ : (derivedPullbackGeometricStalkHomotopyMap g₁ x).app
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
      (smallEtaleRingedToposHom B S hS g₂)).obj ((HomotopyCategory.quotient _
            (ComplexShape.up ℤ)).obj P)) = (derivedPullbackGeometricStalkComplexMap g₁ x).app
          (((smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
    (eq_of_heq (by heq_congr)).trans (derivedPullbackGeometricStalkHomotopyMap_app g₁ x
          (((smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))
  exact (derivedPullbackGeometricStalkHomotopyMap_app (g₁ ≫ g₂) x P).trans
    ((derivedPullbackGeometricStalkComplexMap_comp g₁ g₂ x P).trans
      (CategoryTheory.Functor.comp_map_comp_congr (geometricStalkDerivedExtension g₁ x).functor _ _
        (derivedPullbackGeometricStalkHomotopyMap_app g₂ (geometricPointMap g₁.hom x) P).symm
        h₁.symm _))

/-- The compositor `L(g₁ ≫ g₂)^* ≅ Lg₁^* ∘ Lg₂^*` followed by the comparison of `L(g₁ ≫ g₂)^*` on
the homotopy category, through the comparisons of `Lg₁^*` and `Lg₂^*`. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_comp_comparison_app
    {X'' X' X : AlgebraicSpaces B S hS} (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (L : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
    (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂).hom.app
          (DerivedCategory.Qh.obj L) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (g₁ ≫ g₂)).app L =
          (smallEtaleDerivedModulePullback B S hS g₁).map
            ((smallEtaleDerivedModulePullbackComparison B S hS g₂).app L) ≫
          (smallEtaleDerivedModulePullbackComparison B S hS g₁).app
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (smallEtaleRingedToposHom B S hS g₂)).obj L) ≫
          DerivedCategory.Qh.map
            ((Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
                (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂) ≪≫
              Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
                (ComplexShape.up ℤ)).hom.app L) :=
  open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
  (Category.assoc _ _ _).trans
    (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
      (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂)
      (h := smallEtaleRingedToposHom B S hS (g₁ ≫ g₂)) (pullbackModulesCompTransport B S hS g₁ g₂)
      L)

variable {B S hS} {X'' X' X : AlgebraicSpaces B S hS}

/-- The compositor followed by the counit of `L(g₁ ≫ g₂)^*`, at the derived stalk at `x̄`. -/
theorem derivedPullbackGeometricStalkMap_comp_aux_θα (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (L : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
    (Functor.isoWhiskerRight (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂)
          (geometricDerivedStalk B S hS x)).hom.app (DerivedCategory.Qh.obj L) ≫
        (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app L =
        (geometricDerivedStalk B S hS x).map ((smallEtaleDerivedModulePullback B S hS g₁).map
          ((smallEtaleDerivedModulePullbackComparison B S hS g₂).app L)) ≫
        (geometricDerivedStalk B S hS x).map ((smallEtaleDerivedModulePullbackComparison B S hS
            g₁).app ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (smallEtaleRingedToposHom B S hS g₂)).obj L)) ≫ (geometricDerivedStalk B S hS x).map
        (DerivedCategory.Qh.map
          ((Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
              (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂) ≪≫
              Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
              (ComplexShape.up ℤ)).hom.app L)) :=
  (congrArg (_ ≫ ·) (Category.id_comp _)).trans (((geometricDerivedStalk B S hS x).map_comp _
          _).symm.trans
    ((congrArg (geometricDerivedStalk B S hS x).map
      (smallEtaleDerivedModulePullbackCompIso_hom_app_comp_comparison_app B S hS g₁ g₂ L)).trans
      (((geometricDerivedStalk B S hS x).map_comp _ _).trans
            (congrArg (_ ≫ ·) ((geometricDerivedStalk B S hS x).map_comp _ _)))))

/-- The comparison along `g₁` followed by the stalk of the comparison of `Lg₁^*`. -/
theorem derivedPullbackGeometricStalkMap_comp_aux_h₁ (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (L : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (derivedPullbackGeometricStalkMap g₁ x).app ((smallEtaleModulePullbackOnHomotopy B S hS g₂).obj
          L) ≫ (geometricDerivedStalk B S hS x).map ((smallEtaleDerivedModulePullbackComparison B S
            hS g₁).app ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (smallEtaleRingedToposHom B S hS g₂)).obj L)) =
        (derivedPullbackGeometricStalkHomotopyMap g₁ x).app
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (smallEtaleRingedToposHom B S hS g₂)).obj L) :=
  derivedPullbackGeometricStalkMap_app_comp_map_comparison_app g₁ x
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (smallEtaleRingedToposHom B S hS g₂)).obj L)

/-- The comparison along `g₂`, extended along `g₁`, followed by the stalk of the comparison of
`Lg₂^*`. -/
theorem derivedPullbackGeometricStalkMap_comp_aux_h₂ (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (L : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (geometricStalkDerivedExtension g₁ x).functor.map ((derivedPullbackGeometricStalkMap g₂
            (geometricPointMap g₁.hom x)).app (DerivedCategory.Qh.obj L)) ≫
        (geometricStalkDerivedExtension g₁ x).functor.map
        ((geometricDerivedStalk B S hS (geometricPointMap g₁.hom x)).map
          ((smallEtaleDerivedModulePullbackComparison B S hS g₂).app L)) =
        (geometricStalkDerivedExtension g₁ x).functor.map
        ((derivedPullbackGeometricStalkHomotopyMap g₂ (geometricPointMap g₁.hom x)).app L) :=
  ((geometricStalkDerivedExtension g₁ x).functor.map_comp _ _).symm.trans
      (congrArg (geometricStalkDerivedExtension g₁ x).functor.map
    (derivedPullbackGeometricStalkMap_app_comp_map_comparison_app g₂ _ L))

/-- The comparison along `g₁ ≫ g₂` followed by its counit, at the class of a complex. -/
theorem derivedPullbackGeometricStalkMap_comp_aux_L (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
    (derivedPullbackGeometricStalkMap (g₁ ≫ g₂) x).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) =
        (eqToHom (congrArg (fun φ => (geometricDerivedStalk B S hS
                (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
              (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
          (stalkStructureMap B S hS g₁ x).hom).inv.app ((geometricDerivedStalk B S hS
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ≫
        (geometricStalkDerivedExtension g₁ x).functor.map
        ((derivedPullbackGeometricStalkHomotopyMap g₂ (geometricPointMap g₁.hom x)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackGeometricStalkHomotopyMap g₁ x).app
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (smallEtaleRingedToposHom B S hS g₂)).obj ((HomotopyCategory.quotient _
              (ComplexShape.up ℤ)).obj P)) ≫ (geometricDerivedStalk B S hS x).map
        (DerivedCategory.Qh.map
          ((Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
              (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂) ≪≫
              Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
              (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              P))) :=
  (derivedPullbackGeometricStalkMap_fac _ _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          P)).trans
    ((derivedPullbackGeometricStalkHomotopyMap_comp B S hS g₁ g₂ x P).trans
      (congrArg (· ≫ _) (eqToHom_app
        (congrArg (fun φ => (geometricDerivedStalk B S hS
                  (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
                (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x))
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                P))).symm))

/-- The components of the composite of the comparisons along `g₂` and `g₁`. -/
theorem derivedPullbackGeometricStalkMap_comp_aux_Γ (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (eqToHom (congrArg (fun φ => (geometricDerivedStalk B S hS
                (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
              (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
      Functor.whiskerLeft (geometricDerivedStalk B S hS
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)))
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x))
          (geometricStalkDerivedExtension g₁ x).functor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS g₂)
          (derivedPullbackGeometricStalkMap g₁ x) ≫
      (Functor.associator _ _ _).inv).app K = (eqToHom (congrArg
            (fun φ => (geometricDerivedStalk B S hS (geometricPointMap g₂.hom
                  (geometricPointMap g₁.hom x))) ⋙
              (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x))).app K ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv.app
          ((geometricDerivedStalk B S hS (geometricPointMap g₂.hom
                (geometricPointMap g₁.hom x))).obj K) ≫
          (geometricStalkDerivedExtension g₁ x).functor.map
          ((derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x)).app K) ≫
          (derivedPullbackGeometricStalkMap g₁ x).app ((smallEtaleDerivedModulePullback B S hS
              g₂).obj K) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id]

/-- Both sides of the composition law agree after the counit of `L(g₁ ≫ g₂)^*`, at the class of
a complex. -/
theorem derivedPullbackGeometricStalkMap_comp_aux (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (L : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ))
    (hL : haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁
            g₂)
      (derivedPullbackGeometricStalkMap (g₁ ≫ g₂) x).app (DerivedCategory.Qh.obj L) ≫
          (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app L =
          (eqToHom (congrArg (fun φ => (geometricDerivedStalk B S hS
                  (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
                (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x))).app
          (DerivedCategory.Qh.obj L) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv.app
          ((geometricDerivedStalk B S hS (geometricPointMap g₂.hom
                (geometricPointMap g₁.hom x))).obj (DerivedCategory.Qh.obj L)) ≫
          (geometricStalkDerivedExtension g₁ x).functor.map
          ((derivedPullbackGeometricStalkHomotopyMap g₂ (geometricPointMap g₁.hom x)).app L) ≫
          (derivedPullbackGeometricStalkHomotopyMap g₁ x).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (smallEtaleRingedToposHom B S hS g₂)).obj L) ≫ (geometricDerivedStalk B S hS x).map
          (DerivedCategory.Qh.map
            ((Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
                (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂) ≪≫
                Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
                (ComplexShape.up ℤ)).hom.app L))) :
    (derivedPullbackGeometricStalkMap (g₁ ≫ g₂) x).app (DerivedCategory.Qh.obj L) ≫
        (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app L =
      (eqToHom (congrArg (fun φ => (geometricDerivedStalk B S hS
                  (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
                (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
      Functor.whiskerLeft (geometricDerivedStalk B S hS
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)))
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x))
          (geometricStalkDerivedExtension g₁ x).functor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS g₂)
          (derivedPullbackGeometricStalkMap g₁ x) ≫
      (Functor.associator _ _ _).inv).app (DerivedCategory.Qh.obj L) ≫ (Functor.isoWhiskerRight
          (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂)
          (geometricDerivedStalk B S hS x)).hom.app (DerivedCategory.Qh.obj L) ≫
          (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app L := by
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g₁ g₂)
  exact CategoryTheory.comp_chase_of_eq _ _ _ _ ((eqToHom
          (congrArg (fun φ => (geometricDerivedStalk B S hS
                (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
              (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x))).app
        (DerivedCategory.Qh.obj L))
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
          (stalkStructureMap B S hS g₁ x).hom).inv.app ((geometricDerivedStalk B S hS
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))).obj
          (DerivedCategory.Qh.obj L))) ((geometricStalkDerivedExtension g₁ x).functor.map
        ((derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x)).app
          (DerivedCategory.Qh.obj L))) ((derivedPullbackGeometricStalkMap g₁ x).app
        ((smallEtaleDerivedModulePullback B S hS g₂).obj (DerivedCategory.Qh.obj L)))
    (derivedPullbackGeometricStalkMap_comp_aux_Γ g₁ g₂ x (DerivedCategory.Qh.obj L))
    ((geometricDerivedStalk B S hS x).map ((smallEtaleDerivedModulePullback B S hS g₁).map
            ((smallEtaleDerivedModulePullbackComparison B S hS g₂).app L)))
        ((geometricDerivedStalk B S hS x).map ((smallEtaleDerivedModulePullbackComparison B S hS
              g₁).app ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
                (smallEtaleRingedToposHom B S hS g₂)).obj L)))
        ((geometricDerivedStalk B S hS x).map (DerivedCategory.Qh.map
            ((Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
                (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂) ≪≫
                Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g₁ g₂)
                (ComplexShape.up ℤ)).hom.app L))) (derivedPullbackGeometricStalkMap_comp_aux_θα g₁
          g₂ x L)
    ((geometricStalkDerivedExtension g₁ x).functor.map ((geometricDerivedStalk B S hS
              (geometricPointMap g₁.hom x)).map ((smallEtaleDerivedModulePullbackComparison B S hS
                g₂).app L))) ((derivedPullbackGeometricStalkMap g₁ x).app
          ((smallEtaleModulePullbackOnHomotopy B S hS g₂).obj L))
        ((derivedPullbackGeometricStalkMap g₁ x).naturality
          ((smallEtaleDerivedModulePullbackComparison B S hS g₂).app L)).symm
    ((geometricStalkDerivedExtension g₁ x).functor.map ((derivedPullbackGeometricStalkHomotopyMap g₂
              (geometricPointMap g₁.hom x)).app L)) (derivedPullbackGeometricStalkMap_comp_aux_h₂ g₁
          g₂ x L)
    ((derivedPullbackGeometricStalkHomotopyMap g₁ x).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
              (smallEtaleRingedToposHom B S hS g₂)).obj L))
        (derivedPullbackGeometricStalkMap_comp_aux_h₁ g₁ g₂ x L)
    hL



/-- Both sides of the composition law agree after the counit of `L(g₁ ≫ g₂)^*`, at the class of
a complex. -/
theorem derivedPullbackGeometricStalkMap_comp_aux_quotient (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (derivedPullbackGeometricStalkMap (g₁ ≫ g₂) x).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) =
      (eqToHom (congrArg (fun φ => (geometricDerivedStalk B S hS
                  (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
                (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                  φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
      Functor.whiskerLeft (geometricDerivedStalk B S hS
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)))
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x))
          (geometricStalkDerivedExtension g₁ x).functor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS g₂)
          (derivedPullbackGeometricStalkMap g₁ x) ≫
      (Functor.associator _ _ _).inv).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫ (Functor.isoWhiskerRight
          (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂)
          (geometricDerivedStalk B S hS x)).hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) := by
  refine derivedPullbackGeometricStalkMap_comp_aux g₁ g₂ x _ ?_
  exact eq_of_heq_of_eq_of_heq (derivedPullbackGeometricStalkMap_comp_aux_L g₁ g₂ x P)
    (by heq_congr) (by heq_congr)

variable (B S hS) in
/-- **The derived pullback-stalk comparison composes.** For `g₁ : X'' ⟶ X'`, `g₂ : X' ⟶ X` and
a geometric point `x̄` of `X''`, the comparison along `g₁ ≫ g₂`, transported along
`L(g₁ ≫ g₂)^* ≅ Lg₁^* ∘ Lg₂^*`, is the comparison along `g₂` extended along `g₁` followed by the
comparison along `g₁`. -/
theorem derivedPullbackGeometricStalkMap_comp (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
      (x : GeometricPoint B S hS X''.1)
      (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
      (derivedPullbackGeometricStalkMap (g₁ ≫ g₂) x).app K ≫
          (geometricDerivedStalk B S hS x).map
            ((smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂).inv.app K) =
        eqToHom (congrArg (fun φ =>
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              φ).functor.obj ((geometricDerivedStalk B S hS
                (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))).obj K))
            (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv.app _ ≫
          (geometricStalkDerivedExtension g₁ x).functor.map
            ((derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x)).app K) ≫
          (derivedPullbackGeometricStalkMap g₁ x).app
            ((smallEtaleDerivedModulePullback B S hS g₂).obj K) :=
  (Functor.leftDerived_ext_comp_inv_app (W := smallEtaleModuleQuasiIso B S hS X)
    (derivedPullbackGeometricStalkCounit (g₁ ≫ g₂) x) (derivedPullbackGeometricStalkMap (g₁ ≫ g₂) x)
        (eqToHom (congrArg (fun φ => (geometricDerivedStalk B S hS
                (geometricPointMap g₂.hom (geometricPointMap g₁.hom x))) ⋙
              (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                φ).functor) (stalkStructureMap_comp_hom B S hS g₁ g₂ x)) ≫
      Functor.whiskerLeft (geometricDerivedStalk B S hS
            (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)))
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            (stalkStructureMap B S hS g₂ (geometricPointMap g₁.hom x)).hom
            (stalkStructureMap B S hS g₁ x).hom).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPullbackGeometricStalkMap g₂ (geometricPointMap g₁.hom x))
          (geometricStalkDerivedExtension g₁ x).functor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS g₂)
          (derivedPullbackGeometricStalkMap g₁ x) ≫
      (Functor.associator _ _ _).inv) (Functor.isoWhiskerRight
          (smallEtaleDerivedModulePullbackCompIso B S hS g₁ g₂) (geometricDerivedStalk B S hS x))
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (derivedPullbackGeometricStalkMap_comp_aux_quotient g₁ g₂ x) K).trans
    ((derivedPullbackGeometricStalkMap_comp_aux_Γ g₁ g₂ x K).trans
      (congrArg (· ≫ _) (eqToHom_app _ K)))

end AlgebraicGeometry.Space
