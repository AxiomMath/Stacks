module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PowerTorsionRestrict

/-!
# The Mayer--Vietoris step for power torsion of morphisms, in the scheme language

Let `Z` be a scheme covered by two opens `U` and `V`, let `f ∈ Γ(Z, 𝒪_Z)` and let `E`, `F` be
objects of `D(𝒪_Z)`. If on each of `U`, `V` and `U ∩ V` every morphism out of each shift of the
restriction of `E` into the restriction of `F` is annihilated by a power of the restricted
section, then so is every morphism `E⟦n⟧ ⟶ F`. Here restriction is along the inclusion `U.ι` of
the open subscheme and the restricted section is `U.ι.appTop f`.

## Main results

* `Stacks.DerivedQCoh.restrictGlobalSection_globalScalar_ι`: the restriction to `U` of the
  global scalar of `f` is the global scalar of `U.ι.appTop f`.
* `Stacks.DerivedQCoh.homPowerTorsion_of_restrictions_ι`: the Mayer--Vietoris step, with
  every restriction read along the inclusion of an open subscheme.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.SiteModules
open Stacks.ExtensionByZero
open Stacks.Duality.OpenImmersion (derivedRestrict)
open scoped IsMulCommutative

universe u

namespace Stacks.DerivedQCoh

open Stacks.Koszul.PowerLift

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_restrictFunctor

/-- The restriction to `U` of the global scalar of `f` is the global scalar of the pullback
`U.ι.appTop f` of `f` along the inclusion of the open subscheme. -/
public theorem restrictGlobalSection_globalScalar_ι {Z : Scheme.{u}} (U : Z.Opens)
    (f : Γ(Z, ⊤)) :
    restrictGlobalSection U Z.ringCatSheaf (globalScalar Z.ringCatSheaf f) =
      globalScalar U.toScheme.ringCatSheaf (U.ι.appTop f) := by
  ext W
  refine (globalScalar_val_image U.ι f W.unop).trans ?_
  simp only [appIso_ι_inv U W.unop]
  rfl

/-- If, after restriction along `W.ι`, every morphism from the `m`-th shift of `E` to `F` is
annihilated by a power of `W.ι.appTop f`, then the same holds after restriction of `E` and `F` to
the open `W`, with the restriction of the global scalar of `f`. -/
private theorem homPowerTorsion_restriction_of_ι {Z : Scheme.{u}} (f : Γ(Z, ⊤)) (W : Z.Opens)
    (E F : DerivedCategory Z.Modules) (m : ℤ)
    (h : HomPowerTorsion (globalScalar W.toScheme.ringCatSheaf (W.ι.appTop f))
      (((derivedRestrict W.ι).obj E)⟦m⟧) ((derivedRestrict W.ι).obj F)) :
    HomPowerTorsion (restrictGlobalSection W Z.ringCatSheaf (globalScalar Z.ringCatSheaf f))
      (((derivedRestriction Z.ringCatSheaf W).obj E)⟦m⟧)
      ((derivedRestriction Z.ringCatSheaf W).obj F) := by
  rw [restrictGlobalSection_globalScalar_ι]
  exact HomPowerTorsion.of_iso_target ((derivedRestrictionIso W).app F).symm
    (HomPowerTorsion.of_iso
      ((shiftFunctor (DerivedCategory W.toScheme.Modules) m).mapIso
        ((derivedRestrictionIso W).app E).symm) h)

/-- Let `Z` be a scheme covered by two opens `U` and `V`, let `f` be a global section of `𝒪_Z`
and let `E` and `F` be objects of `D(𝒪_Z)`. If on each of `U`, `V` and `U ∩ V` every morphism from
each shift of the restriction of `E` into the restriction of `F` is annihilated by a power of the
pullback of `f` to that open subscheme, then every morphism `E⟦n⟧ ⟶ F` is annihilated by a power
of `f`. -/
public theorem homPowerTorsion_of_restrictions_ι {Z : Scheme.{u}} (f : Γ(Z, ⊤))
    (U V : Z.Opens) (hUV : U ⊔ V = ⊤) (E F : DerivedCategory Z.Modules)
    (hU : ∀ n : ℤ, HomPowerTorsion (globalScalar U.toScheme.ringCatSheaf (U.ι.appTop f))
      (((derivedRestrict U.ι).obj E)⟦n⟧) ((derivedRestrict U.ι).obj F))
    (hV : ∀ n : ℤ, HomPowerTorsion (globalScalar V.toScheme.ringCatSheaf (V.ι.appTop f))
      (((derivedRestrict V.ι).obj E)⟦n⟧) ((derivedRestrict V.ι).obj F))
    (hW : ∀ n : ℤ,
      HomPowerTorsion (globalScalar (U ⊓ V).toScheme.ringCatSheaf ((U ⊓ V).ι.appTop f))
      (((derivedRestrict (U ⊓ V).ι).obj E)⟦n⟧) ((derivedRestrict (U ⊓ V).ι).obj F))
    (n : ℤ) : HomPowerTorsion (globalScalar Z.ringCatSheaf f) (E⟦n⟧) F :=
  homPowerTorsion_of_restrictions Z.ringCatSheaf (globalScalar Z.ringCatSheaf f) U V hUV E F
    (fun m => homPowerTorsion_restriction_of_ι f U E F m (hU m))
    (fun m => homPowerTorsion_restriction_of_ι f V E F m (hV m))
    (fun m => homPowerTorsion_restriction_of_ι f (U ⊓ V) E F m (hW m)) n

/-! ### Example

The hypotheses of `Stacks.DerivedQCoh.homPowerTorsion_of_restrictions_ι` hold at `Spec ℤ` with
both opens the whole space, both objects the structure sheaf in degree zero and the section `0`.
-/

section Witness

private abbrev specZ : Scheme.{0} := Spec (CommRingCat.of ℤ)

private abbrev unitZ : DerivedCategory specZ.Modules :=
  (DerivedCategory.singleFunctor specZ.Modules 0).obj (SheafOfModules.unit specZ.ringCatSheaf)

private theorem homPowerTorsion_of_eq_zero {W : Scheme.{u}} (f : Γ(W, ⊤)) (hf : f = 0)
    (X E : DerivedCategory W.Modules) :
    HomPowerTorsion (globalScalar W.ringCatSheaf f) X E := fun _ => ⟨1, by
  rw [pow_one, hf, show globalScalar W.ringCatSheaf (0 : Γ(W, ⊤)) = 0 from
    map_zero (globalScalarHom W.ringCatSheaf), zero_smul]⟩

example : HomPowerTorsion (globalScalar specZ.ringCatSheaf 0) (unitZ⟦(0 : ℤ)⟧) unitZ :=
  homPowerTorsion_of_restrictions_ι (0 : Γ(specZ, ⊤)) ⊤ ⊤ (by simp) unitZ unitZ
    (fun _ => homPowerTorsion_of_eq_zero _ (map_zero _) _ _)
    (fun _ => homPowerTorsion_of_eq_zero _ (map_zero _) _ _)
    (fun _ => homPowerTorsion_of_eq_zero _ (map_zero _) _ _) 0

end Witness

end Stacks.DerivedQCoh

end
