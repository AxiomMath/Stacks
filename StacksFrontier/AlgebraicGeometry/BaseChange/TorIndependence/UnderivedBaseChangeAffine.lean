module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMapUnderived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeTorIndependent
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange

/-!
# The underived base change map of a square of schemes

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the underived base change map `g^* f_* ⟶ f'_* g'^*` on the homotopy categories is, on the class of
a complex, the class of the degreewise base change morphism of modules of Stacks 02KG.  When the
square is cartesian and `f` is affine it is therefore invertible at every complex of
quasi-coherent modules.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.underivedBaseChangeSquare_app_quotient`: the component at
  the class of a complex.
* `Stacks.Cohomology.DerivedBaseChange.isIso_underivedBaseChangeSquare_app_quotient`: the
  invertibility for an affine `f`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedBaseChange

universe u

/-- Transport along an equality of morphisms of ringed spaces, on the homotopy category. -/
theorem eqToIso_mapHomotopyCategory_hom_app {A B : RingedSpace.{u, u}} {a b : A ⟶ B}
    (e : a = b)
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing B)) (ComplexShape.up ℤ)) :
    (eqToIso (congrArg (fun h : A ⟶ B =>
        (modulePullback h).mapHomotopyCategory (ComplexShape.up ℤ)) e)).hom.app W =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (eqToHom (congrArg (fun h : A ⟶ B => modulePullback h) e))
          (ComplexShape.up ℤ)).app W.as) := by
  subst e
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, eqToHom_refl]
  exact ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_id _).symm

section

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g)

/-- The degreewise mate of the composition isomorphisms of pullback, the module-level form of the
underived base change map. -/
def moduleBaseChange :
    modulePushforward f ⋙ modulePullback g ⟶ modulePullback g' ⋙ modulePushforward f' :=
  (mateEquiv (modulePullbackPushforwardAdjunction f) (modulePullbackPushforwardAdjunction f')
    (TwoSquare.mk _ _ _ _ ((Stacks.DerivedPullback.Composition.modulePullbackComp f' g).hom ≫
      eqToHom (congrArg (fun h : X' ⟶ S => modulePullback h) sq.symm) ≫
      (Stacks.DerivedPullback.Composition.modulePullbackComp g' f).inv)))

/-- The unit of the induced adjunction on homotopy categories, at an object. -/
theorem homotopyPullbackPushforwardAdjunction_unit_app {A B : RingedSpace.{u, u}} (p : A ⟶ B)
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing B)) (ComplexShape.up ℤ)) :
    (DerivedAdjunctionOnRingedSpaces.homotopyPullbackPushforwardAdjunction p).unit.app W =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction p)
          (ComplexShape.up ℤ)).unit.app W.as) :=
  rfl

/-- The counit of the induced adjunction on homotopy categories, at an object. -/
theorem homotopyPullbackPushforwardAdjunction_counit_app {A B : RingedSpace.{u, u}} (p : A ⟶ B)
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing A)) (ComplexShape.up ℤ)) :
    (DerivedAdjunctionOnRingedSpaces.homotopyPullbackPushforwardAdjunction p).counit.app W =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction p)
          (ComplexShape.up ℤ)).counit.app W.as) :=
  rfl

/-- The pullback-composition isomorphism on homotopy categories, at an object. -/
theorem pullbackOnHomotopyCompIso_hom_app {A B C : RingedSpace.{u, u}} (a : A ⟶ B) (b : B ⟶ C)
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing C)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a b).hom.app W =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (Stacks.DerivedPullback.Composition.modulePullbackComp a b)
          (ComplexShape.up ℤ)).hom.app W.as) :=
  rfl

/-- The inverse of the pullback-composition isomorphism on homotopy categories, at an object. -/
theorem pullbackOnHomotopyCompIso_inv_app {A B C : RingedSpace.{u, u}} (a : A ⟶ B) (b : B ⟶ C)
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing C)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a b).inv.app W =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (Stacks.DerivedPullback.Composition.modulePullbackComp a b)
          (ComplexShape.up ℤ)).inv.app W.as) :=
  rfl

/-- **The underived base change map at the class of a complex** is the class of the degreewise
module-level base change map. -/
theorem underivedBaseChangeSquare_app_quotient_eq
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (underivedBaseChangeSquare g' f' f g sq).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (moduleBaseChange g' f' f g sq)
          (ComplexShape.up ℤ)).app C) := by
  rw [underivedBaseChangeSquare, Stacks.Cohomology.ClosedImmersionBaseChange.mateEquiv_app_eq,
    Mate.twoSquare_mk_app, NatTrans.comp_app,
    pullbackOnHomotopyCompIsoLeft, Iso.trans_hom, NatTrans.comp_app,
    eqToIso_mapHomotopyCategory_hom_app, homotopyPullbackPushforwardAdjunction_unit_app,
    homotopyPullbackPushforwardAdjunction_counit_app, pullbackOnHomotopyCompIso_hom_app,
    pullbackOnHomotopyCompIso_inv_app]
  · dsimp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as]
    simp only [← Functor.map_comp]
    congr 1
  · exact sq.symm

end

section Schemes

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- For a commutative square of schemes the module-level base change map is the base change
morphism of Stacks 02KG. -/
theorem moduleBaseChange_eq (w : g' ≫ f = f' ≫ g) :
    moduleBaseChange g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm w) =
      Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w := by
  rw [Stacks.Modules.baseChangeNatTrans_eq_mateEquiv, moduleBaseChange]
  congr 2

/-- **The underived base change map of a cartesian square with affine right-hand morphism is
invertible at the class of a complex of quasi-coherent modules.** -/
theorem isIso_underivedBaseChangeSquare_app_quotient (sq : IsPullback g' f' f g) [IsAffineHom f]
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) ℤ)
    (hC : ∀ n, (C.X n).IsQuasicoherent) :
    IsIso ((underivedBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) := by
  rw [underivedBaseChangeSquare_app_quotient_eq, moduleBaseChange_eq sq.w]
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w)
      (ComplexShape.up ℤ)).app C).f n) := fun n =>
    @Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      _ _ _ _ _ _ _ _ sq _ (C.X n) (hC n)
  have h : IsIso ((NatTrans.mapHomologicalComplex
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w)
      (ComplexShape.up ℤ)).app C) := HomologicalComplex.Hom.isIso_of_components _
  exact ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso (@asIso _ _ _ _ _ h)).isIso_hom

end Schemes

end Stacks.Cohomology.DerivedBaseChange
