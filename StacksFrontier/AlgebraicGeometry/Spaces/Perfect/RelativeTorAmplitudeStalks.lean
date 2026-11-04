module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianStalkRingTensorFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StalkPullbackComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullbackEtaleLocalRing
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkOverTorAmplitude

/-!
# Relative Tor amplitude at the stalks of an algebraic space

Let `φ : Z ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `z̄` be a geometric
point of `Z`.  The Tor clause of relative perfectness (Stacks 0DKN) reads an object of `D(𝒪_Z)`
through restriction of scalars along `φ⁻¹𝒪_Y ⟶ 𝒪_Z`.  At the point of the small étale site of
`Z` determined by `z̄`, the stalk of `φ⁻¹𝒪_Y` is the stalk `𝒪_{Y, φ(z̄)}` of the structure sheaf
of `Y` (Stacks 05V1), and the stalk of a restriction of scalars is the restriction of scalars of
the stalk.  So the stalk at `z̄` of a complex of `𝒪_Z`-modules, read over `φ⁻¹𝒪_Y`, has Tor
amplitude in `[a, b]` exactly when the stalk of the complex, read over `𝒪_{Y, φ(z̄)}` through the
stalk map `𝒪_{Y, φ(z̄)} ⟶ 𝒪_{Z, z̄}` of Stacks 05V5, has Tor amplitude in `[a, b]`.  This is the
identification through which the source computes relative Tor amplitude at stalks in the proofs
of Stacks 0DKD and Stacks 0DKT.

## Main results

* `AlgebraicGeometry.Space.scalarRestrictionStalkComplexIso`: the stalk of the restriction of
  scalars of a complex is the restriction of scalars of its stalk along the stalk of
  `φ⁻¹𝒪_Y ⟶ 𝒪_Z`.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_scalarRestriction_stalk_iff`: the
  equivalence of the two Tor-amplitude conditions above.
* `AlgebraicGeometry.Space.pullbackModulesStalkComplexIso`: Stacks 05V5 for complexes, with the
  pullback of modules spelled through the morphism of small étale ringed topoi, as the derived
  pullback of a K-flat complex computes it.

## References

* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z Y : AlgebraicSpaces B S hS}

/-- **The stalk of a restriction of scalars along `φ⁻¹𝒪_Y ⟶ 𝒪_Z`, for complexes.** The stalk at
a geometric point `z̄` of the restriction of scalars of a complex of `𝒪_Z`-modules is the
restriction of scalars of its stalk along the stalk at `z̄` of `φ⁻¹𝒪_Y ⟶ 𝒪_Z`. -/
def scalarRestrictionStalkComplexIso (φ : Z ⟶ Y) (z : GeometricPoint B S hS Z.1)
    (M : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
        (inverseImageRingedSite B S hS φ).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarRestriction B S hS φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅
      ((ModuleCat.restrictScalars.{u} (Stacks.Sheaves.StalkPullback.fSharpStalk
          (smallEtaleRingedToposModulesHom B S hS φ)
          (etaleSitePoint B S hS Z.1 z Z.2))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
          (smallEtaleRingedTopos B S hS Z).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso
      (etaleSitePoint B S hS Z.1 z Z.2)
      (Stacks.Sheaves.RingedToposModules.fSharpCommRing (smallEtaleRingedToposModulesHom B S hS φ))
      _ _).app (M.X i))
    (fun i j _ => ((Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso
      (etaleSitePoint B S hS Z.1 z Z.2)
      (Stacks.Sheaves.RingedToposModules.fSharpCommRing (smallEtaleRingedToposModulesHom B S hS φ))
      _ _).hom.naturality (M.d i j)).symm)

/-- **Relative Tor amplitude at a stalk.** The stalk at a geometric point `z̄` of a complex of
`𝒪_Z`-modules, read over `φ⁻¹𝒪_Y`, has Tor amplitude in `[a, b]` over the stalk of `φ⁻¹𝒪_Y`
exactly when the stalk of the complex, read over `𝒪_{Y, φ(z̄)}` through the stalk map
`𝒪_{Y, φ(z̄)} ⟶ 𝒪_{Z, z̄}`, has Tor amplitude in `[a, b]`.

The stalk of a restriction of scalars is the restriction of scalars of the stalk,
`AlgebraicGeometry.Space.scalarRestrictionStalkComplexIso`, and the stalk of `φ⁻¹𝒪_Y` is
identified with `𝒪_{Y, φ(z̄)}` by the ring isomorphism of Stacks 05V1, across which Tor
amplitude is unchanged. -/
theorem hasTorAmplitudeCanonical_scalarRestriction_stalk_iff (φ : Z ⟶ Y)
    (z : GeometricPoint B S hS Z.1) (M : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ)
    (a b : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u}
      (((etaleSitePoint B S hS Z.1 z Z.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS φ).O.obj))
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (structureStalkRing B S hS Y (geometricPointMap φ.hom z)))
    HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS Z.1 z Z.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS φ).O.obj)
        (DerivedCategory.Q.obj
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
              (inverseImageRingedSite B S hS φ).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((scalarRestriction B S hS φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
        a b ↔
      HasTorAmplitudeCanonical (structureStalkRing B S hS Y (geometricPointMap φ.hom z))
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars.{u}
              (smallEtaleStalkPullbackRingMap B S hS φ z)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
            (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
              (smallEtaleRingedTopos B S hS Z).O).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M))) a b := by
  let := HasDerivedCategory.standard (ModuleCat.{u}
    (((etaleSitePoint B S hS Z.1 z Z.2).presheafFiber (A := CommRingCat.{u})).obj
      (inverseImageRingedSite B S hS φ).O.obj))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (structureStalkRing B S hS Y (geometricPointMap φ.hom z)))
  let f := smallEtaleRingedToposModulesHom B S hS φ
  let Φ := etaleSitePoint B S hS Z.1 z Z.2
  let e := Stacks.Sheaves.StalkPullback.commRingStalkEquiv f Φ
    (etaleSitePoint B S hS Y.1 (geometricPointMap φ.hom z) Y.2)
    (smallEtaleInverseImageFiberIso B S hS φ z)
  let N := ((Stacks.sheafModuleFiberOfCommRing Φ
    (smallEtaleRingedTopos B S hS Z).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  let g := Stacks.Sheaves.StalkPullback.fSharpStalk f Φ
  have hcomp : smallEtaleStalkPullbackRingMap B S hS φ z = g.comp e.toRingHom := rfl
  refine (hasTorAmplitudeCanonical_iff_of_iso
    (DerivedCategory.Q.mapIso (scalarRestrictionStalkComplexIso B S hS φ z M)) a b).trans ?_
  refine (hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff e _ a b).trans ?_
  exact hasTorAmplitudeCanonical_iff_of_iso (DerivedCategory.Q.mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i => ModuleCat.restrictScalarsComp'App e.toRingHom g _ hcomp (N.X i))
      (fun i j _ => (ModuleCat.restrictScalarsComp'App_hom_naturality e.toRingHom g _ hcomp
          (N.d i j)).symm)).symm) a b

/-- The degreewise pullback of a complex of `𝒪_Y`-modules is the same complex whether the
pullback of modules is read through the morphism of small étale ringed topoi of Stacks 03G8 or
as the pullback of Stacks 03LU. -/
theorem pullbackModules_mapHomologicalComplex_obj_eq (f : Z ⟶ Y)
    (K : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K =
      ((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (@mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (pullbackModules_smallEtaleRingedToposHom_additive B S hS f))
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (modulePullback B S hS f) (additive_modulePullback B S hS f))
    (pullbackModules_eq_modulePullback B S hS f) K (fun L =>
      ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K = L)).1 rfl

/-- **Stacks 05V5 for complexes, in the spelling of the derived pullback.** The stalk at `x̄` of
the degreewise pullback of a complex of `𝒪_Y`-modules, the pullback of modules being read
through the morphism of small étale ringed topoi of Stacks 03G8 as the derived pullback of a
K-flat complex computes it, is the degreewise extension of scalars of its stalk at `f(x̄)`. -/
def pullbackModulesStalkComplexIso (f : Z ⟶ Y) (x : GeometricPoint B S hS Z.1)
    (K : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 x Z.2)
        (smallEtaleRingedTopos B S hS Z).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 x Z.2)
      (smallEtaleRingedTopos B S hS Z).O).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (eqToIso (pullbackModules_mapHomologicalComplex_obj_eq B S hS f K)) ≪≫
    modulePullbackStalkComplexIso B S hS f x K

end AlgebraicGeometry.Space

end
