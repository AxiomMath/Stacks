module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized

/-!
# Modules of rank one at the local rings of a scheme

A sheaf of modules which is finite locally free of rank one becomes the structure sheaf when
pulled back to the spectrum of a local ring of the scheme: the only open subset of that spectrum
containing its closed point is the whole of it, so a trivializing neighbourhood of the point
pulls back to a trivialization over the whole spectrum.

Consequently the generic-point contribution `j_{η, *} j_η^* L` of such a module at a generic
point of an irreducible component does not depend on the module, which is the step turning the
product decomposition of the sheaf of meromorphic sections into a comparison between a module of
rank one and the structure sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_one_of_isInvertible`: an invertible
  module is finite locally free of rank one at every point.
* `AlgebraicGeometry.nonempty_pullback_fromSpecStalk_iso_unit`: the pullback of a module of rank
  one to the spectrum of a local ring is the unit module.
* `AlgebraicGeometry.nonempty_genericPointStalkModuleOf_iso_unit`: the generic-point contribution
  of a module of rank one agrees with that of the structure sheaf.

## References

* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.GenericPointDecomposition (genericPointStalkModuleOf)

universe u

namespace AlgebraicGeometry

/-- An invertible sheaf of modules on a scheme is finite locally free of rank one at every point:
the two notions agree on a space whose structure-sheaf stalks are local rings, and the pointwise
form of finite local freeness agrees with the single-datum form. -/
theorem Scheme.Modules.isFiniteLocallyFreeOfRank_one_of_isInvertible {X : Scheme.{u}}
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank L 1 :=
  (Scheme.Modules.isFiniteLocallyFreeOfRank_iff L 1).mpr <|
    (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L).mp <|
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf
        X.ringCatSheaf.property L).mpr ‹_›

/-- The structure sheaf of a scheme, read as a module over itself, is finite locally free of
rank one at every point. -/
theorem Scheme.Modules.isFiniteLocallyFreeOfRank_one_unit (X : Scheme.{u}) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank (SheafOfModules.unit X.ringCatSheaf) 1 := fun _ =>
  ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι ≪≫
    (Stacks.SheafOfModules.Invertible.freeUniqueIso (ULift.{u, 0} (Fin 1))).symm⟩⟩

/-- **A module of rank one becomes the structure sheaf on the spectrum of a local ring of the
scheme.** The spectrum of the local ring at `x` maps to `X` through every open neighbourhood of
`x`, because the only open subset of that spectrum containing its closed point is the whole of
it; so a trivialization of `M` near `x` pulls back to a trivialization over the whole
spectrum. -/
theorem nonempty_pullback_fromSpecStalk_iso_unit {X : Scheme.{u}} (M : X.Modules)
    (hM : Scheme.Modules.IsFiniteLocallyFreeOfRank M 1) (x : X) :
    Nonempty ((Scheme.Modules.pullback (X.fromSpecStalk x)).obj M ≅
      SheafOfModules.unit (Spec (X.presheaf.stalk x)).ringCatSheaf) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM x
  have hpre : (Opens.map (X.fromSpecStalk x).base).obj U = ⊤ := by
    refine (IsLocalRing.closedPoint_mem_iff _).mp ?_
    show (X.fromSpecStalk x).base (IsLocalRing.closedPoint (X.presheaf.stalk x)) ∈ U
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hxU
  have hrange : Set.range (X.fromSpecStalk x).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, (by simp [hpre] : z ∈ (Opens.map (X.fromSpecStalk x).base).obj U)⟩, rfl⟩
  let g : Spec (X.presheaf.stalk x) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (X.fromSpecStalk x) hrange
  have hgf : g ≫ U.ι = X.fromSpecStalk x := IsOpenImmersion.lift_fac U.ι _ hrange
  let I := ULift.{u, 0} (Fin 1)
  exact ⟨(Scheme.Modules.pullbackCongr hgf.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp g U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjFreeIso g I ≪≫
    Stacks.SheafOfModules.Invertible.freeUniqueIso I⟩

/-- **The generic-point contribution of a module of rank one is that of the structure sheaf.**
Both are the direct image along `Spec 𝒪_{X, η} → X` of the unit module, by
`AlgebraicGeometry.nonempty_pullback_fromSpecStalk_iso_unit`. -/
theorem nonempty_genericPointStalkModuleOf_iso_unit {X : Scheme.{u}} (M : X.Modules)
    (hM : Scheme.Modules.IsFiniteLocallyFreeOfRank M 1) (η : genericPoints X) :
    Nonempty (genericPointStalkModuleOf X M η ≅
      genericPointStalkModuleOf X (SheafOfModules.unit X.ringCatSheaf) η) :=
  ⟨(Scheme.Modules.pushforward (X.fromSpecStalk η.1)).mapIso
    ((nonempty_pullback_fromSpecStalk_iso_unit M hM η.1).some ≪≫
      (nonempty_pullback_fromSpecStalk_iso_unit (SheafOfModules.unit X.ringCatSheaf)
        (Scheme.Modules.isFiniteLocallyFreeOfRank_one_unit X) η.1).some.symm)⟩

end AlgebraicGeometry

end
