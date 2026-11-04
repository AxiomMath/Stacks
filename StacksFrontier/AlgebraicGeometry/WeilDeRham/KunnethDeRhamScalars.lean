module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethDeRhamCross

/-!
# The pullback of de Rham cohomology is semilinear

For a commutative square `g' ≫ f = f' ≫ g` of schemes the pullback
`H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of [Stacks, Section 0FL6], read in the realization by derived
global sections of modules (`Stacks.WeilDeRham.deRhamPull`), is semilinear along the map
`Γ(X, f^{-1}𝒪_S) ⟶ Γ(X', f'^{-1}𝒪_{S'})` of global sections of the base ring sheaves. For a
square over the identity of `S` this map is compatible with the two maps from `Γ(S, 𝒪_S)`, so
the pullback is `Γ(S, 𝒪_S)`-linear.

## Main results

* `Stacks.WeilDeRham.homologyPullback_smul`: pullback of classes along a morphism of ringed spaces
  is semilinear along its map on global sections.
* `Stacks.WeilDeRham.deRhamPull_smul`: **the de Rham pullback is semilinear.**
* `Stacks.WeilDeRham.globalRingHom_inverseImageBaseMap_comp`: for a square over the identity of
  `S`, the map on global sections of the base ring sheaves is compatible with the maps from
  `Γ(S, 𝒪_S)`.

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing

universe u


namespace Stacks.WeilDeRham

/-- **Pullback of classes along a morphism of ringed spaces `h` is semilinear** along
`h^♯ : Γ(W, 𝒪_W) ⟶ Γ(Z, 𝒪_Z)`. -/
theorem homologyPullback_smul {Z W : RingedSpace.{u, u}} (h : Z ⟶ W)
    (N : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) (n : ℤ)
    (r : baseRing W) (x : letI := @HasDerivedCategory.standard.{u, u + 1}; cohomologyModule N n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    Stacks.Cohomology.HomologyPullback.homologyPullback h N n (r • x) =
      (globalRingHom h).hom r • Stacks.Cohomology.HomologyPullback.homologyPullback h N n x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  refine (congrArg (lerayCohomologyIso h ((derivedPullback h).obj N) n).hom.hom
    (LinearMap.map_smul ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing W)) n).map
      ((baseSections W).map ((derivedAdjunction h).unit.app N))).hom r x)).trans ?_
  exact (lerayCohomologyIso h ((derivedPullback h).obj N) n).hom.hom.map_smul r _

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The de Rham pullback is the pullback of classes followed by the comparison of forms.** -/
theorem deRhamPull_eq (m : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    deRhamPull g' f f' g w m x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f'))) m).map
          ((baseSections (inverseImageBase f')).map
            (deRhamPullbackComparisonQ g' f' f g w))).hom
        (Stacks.Cohomology.HomologyPullback.homologyPullback (inverseImageBaseMap g' f' f g w)
          (DerivedCategory.Q.obj (deRhamComplexInt f)) m x) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have h := deRhamCohomologyPullback_eq_homologyPullback g' f' f g w m
    ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
      m).inv.hom x)
  have h₄ := congrArg (fun t =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f'))) m).map
      ((baseSections (inverseImageBase f')).map (deRhamPullbackComparisonQ g' f' f g w))).hom
      (Stacks.Cohomology.HomologyPullback.homologyPullback (inverseImageBaseMap g' f' f g w)
        (DerivedCategory.Q.obj (deRhamComplexInt f)) m t))
    ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
      m).inv_hom_id_apply x)
  exact h.trans h₄

/-- **The de Rham pullback is semilinear** along the map of global sections of the base ring
sheaves of the induced morphism of inverse-image ringed spaces. -/
theorem deRhamPull_smul (m : ℤ) (r : baseRing (inverseImageBase f))
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    deRhamPull g' f f' g w m (r • x) =
      (globalRingHom (inverseImageBaseMap g' f' f g w)).hom r • deRhamPull g' f f' g w m x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  rw [deRhamPull_eq g' f f' g w m (r • x), homologyPullback_smul, map_smul]
  exact congrArg _ (deRhamPull_eq g' f f' g w m x).symm

/-- **The add-monoid map underlying the de Rham pullback.** -/
theorem deRhamPull_add (m : ℤ)
    (x y : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    deRhamPull g' f f' g w m (x + y) = deRhamPull g' f f' g w m x + deRhamPull g' f f' g w m y := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  rw [deRhamPull_eq g' f f' g w m (x + y), map_add, map_add]
  exact congrArg₂ (· + ·) (deRhamPull_eq g' f f' g w m x).symm (deRhamPull_eq g' f f' g w m y).symm

/-- **For a square over the identity of `S`, the map on global sections of the base ring sheaves
is compatible with the two maps from `Γ(S, 𝒪_S)`.** -/
theorem globalRingHom_inverseImageBaseMap_comp {X X' S : Scheme.{u}} (g' : X' ⟶ X) (f : X ⟶ S)
    (f' : X' ⟶ S) (w : g' ≫ f = f' ≫ 𝟙 S) :
    globalRingHom (inverseImageBaseProjection f) ≫
        globalRingHom (inverseImageBaseMap g' f' f (𝟙 S) w) =
      globalRingHom (inverseImageBaseProjection f') := by
  have h := congrArg globalRingHom
    (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f (𝟙 S) w)
  exact h.trans (Category.id_comp _)

end Stacks.WeilDeRham

end
