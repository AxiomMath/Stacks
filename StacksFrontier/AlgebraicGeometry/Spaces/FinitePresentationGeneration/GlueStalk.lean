module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparisonStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroConservative
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkSheafExact

/-!
# Stalk computations for glueing modules across an elementary distinguished square

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, write `(-)|_X` for
restriction of modules along `f` and `f_!` for extension by zero, with unit `M ⟶ (f_!M)|_X`.
This file collects the stalk statements that the glueing of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Glue` checks its two
comparison maps with:

* a map of sheaves of modules is invertible on the module stalk at a geometric point exactly
  when it is on the stalk of the underlying abelian sheaves;
* the stalk at a lift `t` of `x̄` of the restriction of a map is its stalk at `x̄`
  (Equation 08GT), so either is invertible exactly when the other is;
* at a geometric point `x̄` of `Y` with exactly one lift to `X`, invertibility of the stalk at
  `x̄` of `f_!` of a map gives invertibility of the stalk of the map at that lift (Equation
  08GU read backwards), and as a consequence the unit of `f_! ⊣ (-)|_X` is invertible on the
  stalk at that lift.

## Main results

* `AlgebraicGeometry.Space.isIso_sheafFiber_of_isIso_edsModuleStalk`: from the module stalk
  to the abelian stalk.
* `AlgebraicGeometry.Space.isIso_sheafFiber_etaleModulePullback_map_iff`: the stalk of a
  restriction of a map.
* `AlgebraicGeometry.Space.isIso_sheafFiber_of_isIso_sheafFiber_etaleModuleShriek_map`: the
  backwards reading of Equation 08GU at a point with a unique lift.
* `AlgebraicGeometry.Space.isIso_sheafFiber_etaleModuleUnit_of_unique`: the unit of extension
  by zero is invertible on the stalk at a lift of a point with a unique lift.

## Implementation notes

The unit is handled through the triangle identity `f_!(η_M) ≫ ε_{f_!M} = 𝟙`: the counit is
invertible on the stalk at a point with a unique lift by
`AlgebraicGeometry.Space.EtaleShriekStalk.isIso_sheafFiber_counit_of_unique`, so `f_!(η_M)` is,
and Equation 08GU (through Tag 0798) carries this back to `η_M` on the summand of the unique
lift.  No germ computation for the unit is needed.

## References

* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A map of sheaves of modules invertible on a module stalk is invertible on the stalk of
the underlying abelian sheaves**: the two stalks differ by the forgetful functor from modules
to abelian groups, which preserves isomorphisms. -/
theorem isIso_sheafFiber_of_isIso_edsModuleStalk {Z : AlgebraicSpaces B S hS}
    [HasSheafify (smallEtaleRingedSite B S hS Z.1 Z.2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS Z.1 Z.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (g : M ⟶ N) (x : GeometricPoint B S hS Z.1)
    (h : IsIso ((edsModuleStalk B S hS x).map g)) :
    IsIso ((etaleSitePoint B S hS Z.1 x Z.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Z)).map g)) := by
  have h' : IsIso ((edsModuleStalk B S hS x ⋙
      forget₂ (ModuleCat.{u} (((etaleSitePoint B S hS Z.1 x Z.2).presheafFiber
        (A := RingCat.{u})).obj (etaleRingSheaf B S hS Z).obj)) AddCommGrpCat.{u}).map g) :=
    Functor.map_isIso (forget₂ (ModuleCat.{u} (((etaleSitePoint B S hS Z.1 x Z.2).presheafFiber
        (A := RingCat.{u})).obj (etaleRingSheaf B S hS Z).obj)) AddCommGrpCat.{u})
      ((edsModuleStalk B S hS x).map g)
  exact (NatIso.isIso_map_iff (Stacks.sheafModuleFiberCompForget₂
    (etaleSitePoint B S hS Z.1 x Z.2) (etaleRingSheaf B S hS Z)) g).1 h'

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- The abelian sheaf underlying the restriction of a sheaf of modules along an étale morphism is
the restriction of the underlying abelian sheaf: both are restriction of sections along
postcomposition of étale charts, so the two functors agree on the nose. -/
def etaleModulePullbackToSheafIso :
    etaleModulePullback.{u, u} B S hS f hf ⋙ SheafOfModules.toSheaf (etaleRingSheaf B S hS X) ≅
      SheafOfModules.toSheaf (etaleRingSheaf B S hS Y) ⋙ abelianEtaleRestriction B S hS f hf :=
  Iso.refl _

/-- **Equation 08GT on maps.**  At a lift `t` of a geometric point `x̄` of `Y` along an étale
`f : X ⟶ Y`, the restriction along `f` of a map of sheaves of `𝒪_Y`-modules is invertible on
the stalk at `t` exactly when the map is invertible on the stalk at `x̄`. -/
theorem isIso_sheafFiber_etaleModulePullback_map_iff {x : GeometricPoint B S hS Y.1}
    (t : GeometricPointLift B S hS f.hom x) {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (g : M ⟶ N) :
    IsIso ((liftSitePoint B S hS f t).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map
          ((etaleModulePullback.{u, u} B S hS f hf).map g))) ↔
      IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map g)) :=
  NatIso.isIso_map_iff (Functor.isoWhiskerRight (etaleModulePullbackToSheafIso B S hS f hf) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft
      (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)) (restrictionSheafFiberIso B S hS f hf t)) g

/-- **Equation 08GU read backwards at a point with a unique lift.**  If a geometric point `x̄`
of `Y` has exactly one lift `t` along an étale `f : X ⟶ Y`, a map of sheaves of `𝒪_X`-modules
whose extension by zero is invertible on the stalk at `x̄` is invertible on the stalk at `t`:
the stalk of the extension by zero is the direct sum over the lifts, which has the single
summand at `t`. -/
theorem isIso_sheafFiber_of_isIso_sheafFiber_etaleModuleShriek_map
    (x : GeometricPoint B S hS Y.1) [Unique (GeometricPointLift B S hS f.hom x)]
    (t : GeometricPointLift B S hS f.hom x) {M N : Modules.{u, u} B S hS X.1 X.2}
    (α : M ⟶ N)
    (h : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriek B S hS f hf).map α)))) :
    IsIso ((liftSitePoint B S hS f t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α)) := by
  have h₁ : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZero B S hS f hf).map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α))) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (etaleModuleShriekForgetIso B S hS f hf)
      ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u}))) α).2 h
  have h₂ : IsIso ((EtaleShriekStalk.stalkFamily B S hS f x ⋙
      Sigma.functor (GeometricPointLift B S hS f.hom x)).map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α)) :=
    (NatIso.isIso_map_iff (EtaleShriekStalk.extensionStalkIso B S hS f hf x)
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α)).1 h₁
  have hι := EtaleShriekStalk.liftedStalkι_map_assoc B S hS f x
    ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α) t (𝟙 _)
  rw [Category.comp_id, Category.comp_id] at hι
  have hιM : IsIso (EtaleShriekStalk.liftedStalkι B S hS f x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M) t) :=
    EtaleShriekStalk.isIso_sigma_ι_of_unique _ t
  have hιN : IsIso (EtaleShriekStalk.liftedStalkι B S hS f x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj N) t) :=
    EtaleShriekStalk.isIso_sigma_ι_of_unique _ t
  have hc : IsIso ((liftSitePoint B S hS f t).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map α) ≫
      EtaleShriekStalk.liftedStalkι B S hS f x
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj N) t) := by
    rw [← hι]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (EtaleShriekStalk.liftedStalkι B S hS f x
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj N) t)

/-- **The unit of extension by zero is invertible on the stalk at a lift of a point with a
unique lift.**  The counit at `f_!M` is invertible on the stalk at such a point, so by the
triangle identity `f_!(η_M) ≫ ε_{f_!M} = 𝟙` so is `f_!(η_M)`, and Equation 08GU carries this
back to `η_M` at the lift. -/
theorem isIso_sheafFiber_etaleModuleUnit_of_unique
    (x : GeometricPoint B S hS Y.1) [Unique (GeometricPointLift B S hS f.hom x)]
    (t : GeometricPointLift B S hS f.hom x) (M : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((liftSitePoint B S hS f t).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M))) := by
  refine isIso_sheafFiber_of_isIso_sheafFiber_etaleModuleShriek_map B S hS f hf x t _ ?_
  have hε : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
          ((etaleModuleLowerShriek B S hS f hf).obj M)))) :=
    isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS f hf x _
      (EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS f hf x _)
  have htri : (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriek B S hS f hf).map
            ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M))) ≫
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
            ((etaleModuleLowerShriek B S hS f hf).obj M))) = 𝟙 _ := by
    exact ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y) ⋙
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u})).map_comp
          ((etaleModuleLowerShriek B S hS f hf).map
            ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M))
          ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
            ((etaleModuleLowerShriek B S hS f hf).obj M))).symm.trans
      ((congrArg (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y) ⋙
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u})).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).left_triangle_components M)).trans
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y) ⋙
          (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u})).map_id _))
  have hc : IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriek B S hS f hf).map
            ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M))) ≫
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
          ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
            ((etaleModuleLowerShriek B S hS f hf).obj M)))) := by
    rw [htri]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
          ((etaleModuleLowerShriek B S hS f hf).obj M))))

/-- **At a lift of a point with a unique lift the counit of extension by zero is invertible on
stalks, for an arbitrary sheaf of modules**: the module form of
`AlgebraicGeometry.Space.EtaleShriekStalk.isIso_sheafFiber_counit_of_unique`. -/
theorem isIso_sheafFiber_etaleModuleCounit_of_unique
    (x : GeometricPoint B S hS Y.1) [Unique (GeometricPointLift B S hS f.hom x)]
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app N))) :=
  isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS f hf x N
    (EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS f hf x _)

/-- **At a point with no lift the extension by zero of an arbitrary sheaf of modules has
vanishing stalk.** -/
theorem isZero_sheafFiber_etaleModuleShriek_of_isEmpty
    (x : GeometricPoint B S hS Y.1) [IsEmpty (GeometricPointLift B S hS f.hom x)]
    (M : Modules.{u, u} B S hS X.1 X.2) :
    IsZero ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
        ((etaleModuleLowerShriek B S hS f hf).obj M))) :=
  isZero_sheafFiber_toSheaf_etaleModuleShriek B S hS f hf x M
    (EtaleShriekStalk.isZero_stalkExtensionByZero_of_isEmpty B S hS f hf x _)

end AlgebraicGeometry.Space

end
