module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PowerTorsionMayerVietoris

/-!
# Power torsion of morphisms in `D(𝒪_X)`: reduction to affine opens

Let `X` be a scheme, `f ∈ Γ(X, 𝒪_X)` and let `E`, `F` be objects of `D(𝒪_X)`. Say that the open
`W` of `X` *has `f`-power torsion morphisms* when every morphism from each shift of `E|_W` into
`F|_W` is annihilated by a power of `f|_W`; that is
`Stacks.DerivedQCoh.HomPowerTorsionOn f E F W`. The property passes from two opens and their
intersection to their union; hence it holds for every quasi-compact open of a quasi-separated
scheme as soon as it holds for every affine open, and on a quasi-compact quasi-separated scheme
every morphism `E⟦n⟧ ⟶ F` is then annihilated by a power of `f`.

## Main definitions

* `Stacks.DerivedQCoh.HomPowerTorsionOn`: every morphism from a shift of `E|_W` to `F|_W` is
  annihilated by a power of `f|_W`.

## Main results

* `Stacks.DerivedQCoh.homPowerTorsionOn_sup`: the Mayer--Vietoris step.
* `Stacks.DerivedQCoh.homPowerTorsionOn_of_isCompact_of_affine`: from the affine opens to every
  quasi-compact open of a quasi-separated scheme.
* `Stacks.DerivedQCoh.homPowerTorsion_of_compact_of_affine`: the same on a quasi-compact
  quasi-separated scheme, read on `X` itself.
* `Stacks.DerivedQCoh.derivedRestrictImageOpensIso` and
  `Stacks.DerivedQCoh.homPowerTorsion_restrict_imageOpens`: restriction to an open of an open
  subscheme is restriction to its image in the ambient scheme.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
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
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-! ### Restriction to an open of an open subscheme -/

/-- Composing `Stacks.DerivedQCoh.imageOpensIso` with the inclusion of the image is the
inclusion of the open of the open subscheme. -/
public theorem imageOpensIso_inv_comp {X : Scheme.{u}} (W : X.Opens) (U : W.toScheme.Opens) :
    (imageOpensIso W U).inv ≫ (U.ι ≫ W.ι) = (W.ι ''ᵁ U).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (by simp [Set.range_comp])

/-- Restriction of modules to an open of an open subscheme is restriction to its image, read
along `Stacks.DerivedQCoh.imageOpensIso`. -/
public def restrictFunctorImageOpensIso {X : Scheme.{u}} (W : X.Opens)
    (U : W.toScheme.Opens) :
    Scheme.Modules.restrictFunctor (W.ι ''ᵁ U).ι ≅
      (Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor U.ι) ⋙
        Scheme.Modules.restrictFunctor (imageOpensIso W U).inv :=
  Scheme.Modules.restrictFunctorCongr (imageOpensIso_inv_comp W U).symm ≪≫
    Scheme.Modules.restrictFunctorComp (imageOpensIso W U).inv (U.ι ≫ W.ι) ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorComp U.ι W.ι) _

/-- `Stacks.DerivedQCoh.restrictFunctorImageOpensIso` on the unbounded derived categories. -/
public def derivedRestrictImageOpensIso {X : Scheme.{u}} (W : X.Opens)
    (U : W.toScheme.Opens) :
    derivedRestrict (W.ι ''ᵁ U).ι ≅
      (derivedRestrict W.ι ⋙ derivedRestrict U.ι) ⋙
        derivedRestrict (imageOpensIso W U).inv :=
  mapDerivedCategoryCongr _ _ (restrictFunctorImageOpensIso W U) ≪≫
    mapDerivedCategoryComp _ _ ≪≫
      Functor.isoWhiskerRight (mapDerivedCategoryComp _ _) _

/-- Pulling a section back to an open of an open subscheme is pulling it back to the image and
then along `Stacks.DerivedQCoh.imageOpensIso`. -/
public theorem appTop_imageOpens {X : Scheme.{u}} (W : X.Opens) (U : W.toScheme.Opens)
    (f : Γ(X, ⊤)) :
    (imageOpensIso W U).inv.appTop (U.ι.appTop (W.ι.appTop f)) = (W.ι ''ᵁ U).ι.appTop f :=
  congrArg (fun φ : Γ(X, ⊤) ⟶ Γ((W.ι ''ᵁ U).toScheme, ⊤) => φ f)
    (congrArg (fun m : (W.ι ''ᵁ U).toScheme ⟶ X => m.appTop) (imageOpensIso_inv_comp W U))

/-- Power torsion over an open of an open subscheme follows from power torsion over its image in
the ambient scheme. -/
public theorem homPowerTorsion_restrict_imageOpens {X : Scheme.{u}} (f : Γ(X, ⊤))
    (W : X.Opens) (U : W.toScheme.Opens) (E F : DerivedCategory X.Modules) (n : ℤ)
    (h : HomPowerTorsion
      (globalScalar (W.ι ''ᵁ U).toScheme.ringCatSheaf ((W.ι ''ᵁ U).ι.appTop f))
      (((derivedRestrict (W.ι ''ᵁ U).ι).obj E)⟦n⟧) ((derivedRestrict (W.ι ''ᵁ U).ι).obj F)) :
    HomPowerTorsion (globalScalar U.toScheme.ringCatSheaf (U.ι.appTop (W.ι.appTop f)))
      (((derivedRestrict U.ι).obj ((derivedRestrict W.ι).obj E))⟦n⟧)
      ((derivedRestrict U.ι).obj ((derivedRestrict W.ι).obj F)) := by
  refine homPowerTorsion_of_derivedRestrict (imageOpensIso W U)
    (U.ι.appTop (W.ι.appTop f)) _ _ n ?_
  rw [appTop_imageOpens]
  exact HomPowerTorsion.of_iso_target ((derivedRestrictImageOpensIso W U).app F)
    (HomPowerTorsion.of_iso
      ((shiftFunctor (DerivedCategory (W.ι ''ᵁ U).toScheme.Modules) n).mapIso
        ((derivedRestrictImageOpensIso W U).app E)) h)

/-! ### The property of an open, and the induction -/

/-- Every morphism from each shift of the restriction of `E` to `W` into the restriction of `F`
to `W` is annihilated by a power of the restriction of `f`. -/
public def HomPowerTorsionOn {X : Scheme.{u}} (f : Γ(X, ⊤)) (E F : DerivedCategory X.Modules)
    (W : X.Opens) : Prop :=
  ∀ n : ℤ, HomPowerTorsion (globalScalar W.toScheme.ringCatSheaf (W.ι.appTop f))
    (((derivedRestrict W.ι).obj E)⟦n⟧) ((derivedRestrict W.ι).obj F)

/-- If two opens and their intersection have `f`-power torsion morphism groups, then so does
their union. -/
public theorem homPowerTorsionOn_sup {X : Scheme.{u}} (f : Γ(X, ⊤))
    (E F : DerivedCategory X.Modules) (U V : X.Opens) (hU : HomPowerTorsionOn f E F U)
    (hV : HomPowerTorsionOn f E F V) (hUV : HomPowerTorsionOn f E F (U ⊓ V)) :
    HomPowerTorsionOn f E F (U ⊔ V) := by
  intro n
  have hcover : ((U ⊔ V).ι ⁻¹ᵁ U) ⊔ ((U ⊔ V).ι ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup]
    exact Scheme.Opens.ι_preimage_self _
  have himU : (U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_sup_left : U ≤ U ⊔ V)]
  have himV : (U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_sup_right : V ≤ U ⊔ V)]
  have himW : (U ⊔ V).ι ''ᵁ (((U ⊔ V).ι ⁻¹ᵁ U) ⊓ ((U ⊔ V).ι ⁻¹ᵁ V)) = U ⊓ V := by
    rw [← Scheme.Hom.preimage_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (le_trans inf_le_left (le_sup_left : U ≤ U ⊔ V))]
  have hU2 : HomPowerTorsionOn f E F ((U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ U)) := by rwa [himU]
  have hV2 : HomPowerTorsionOn f E F ((U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ V)) := by rwa [himV]
  have hW2 : HomPowerTorsionOn f E F
      ((U ⊔ V).ι ''ᵁ (((U ⊔ V).ι ⁻¹ᵁ U) ⊓ ((U ⊔ V).ι ⁻¹ᵁ V))) := by rwa [himW]
  exact homPowerTorsion_of_restrictions_ι ((U ⊔ V).ι.appTop f)
    ((U ⊔ V).ι ⁻¹ᵁ U) ((U ⊔ V).ι ⁻¹ᵁ V) hcover
    ((derivedRestrict (U ⊔ V).ι).obj E) ((derivedRestrict (U ⊔ V).ι).obj F)
    (fun m => homPowerTorsion_restrict_imageOpens f (U ⊔ V) _ E F m (hU2 m))
    (fun m => homPowerTorsion_restrict_imageOpens f (U ⊔ V) _ E F m (hV2 m))
    (fun m => homPowerTorsion_restrict_imageOpens f (U ⊔ V) _ E F m (hW2 m)) n

/-- On a quasi-separated scheme, if every affine open has `f`-power torsion morphism groups for
`E` and `F`, then so does every quasi-compact open. -/
public theorem homPowerTorsionOn_of_isCompact_of_affine {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) (E F : DerivedCategory X.Modules)
    (haffine : ∀ V : X.Opens, IsAffineOpen V → HomPowerTorsionOn f E F V)
    (W : X.Opens) (hW : IsCompact (W : Set X)) : HomPowerTorsionOn f E F W :=
  Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
    (HomPowerTorsionOn f E F) haffine
    (fun U V _ _ hU hV hUV => homPowerTorsionOn_sup f E F U V hU hV hUV) W hW

/-- On a quasi-compact quasi-separated scheme, if every affine open has `f`-power torsion
morphism groups for `E` and `F`, then every morphism `E⟦n⟧ ⟶ F` is annihilated by a power of
`f`. -/
public theorem homPowerTorsion_of_compact_of_affine {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) (E F : DerivedCategory X.Modules)
    (haffine : ∀ V : X.Opens, IsAffineOpen V → HomPowerTorsionOn f E F V) (n : ℤ) :
    HomPowerTorsion (globalScalar X.ringCatSheaf f) (E⟦n⟧) F :=
  homPowerTorsion_of_derivedRestrict X.topIso.symm f E F n
    (homPowerTorsionOn_of_isCompact_of_affine f E F haffine ⊤
      (by simpa using isCompact_univ (X := X)) n)

/-! ### Non-vacuity

At `Spec ℤ`, with scalar `0` and both objects the structure sheaf in degree zero. -/

section Witness

private abbrev specZZ : Scheme.{0} := Spec (CommRingCat.of ℤ)

private theorem homPowerTorsion_of_zero {W : Scheme.{u}} (f : Γ(W, ⊤)) (hf : f = 0)
    (A B : DerivedCategory W.Modules) :
    HomPowerTorsion (globalScalar W.ringCatSheaf f) A B := fun _ => ⟨1, by
  rw [pow_one, hf, show globalScalar W.ringCatSheaf (0 : Γ(W, ⊤)) = 0 from
    map_zero (globalScalarHom W.ringCatSheaf), zero_smul]⟩

example : HomPowerTorsion (globalScalar specZZ.ringCatSheaf 0)
    ((DerivedCategory.singleFunctor specZZ.Modules 0).obj
      (SheafOfModules.unit specZZ.ringCatSheaf)⟦(0 : ℤ)⟧)
    ((DerivedCategory.singleFunctor specZZ.Modules 0).obj
      (SheafOfModules.unit specZZ.ringCatSheaf)) :=
  homPowerTorsion_of_compact_of_affine (0 : Γ(specZZ, ⊤)) _ _
    (fun _ _ _ => homPowerTorsion_of_zero _ (map_zero _) _ _) 0

end Witness

end Stacks.DerivedQCoh

end
