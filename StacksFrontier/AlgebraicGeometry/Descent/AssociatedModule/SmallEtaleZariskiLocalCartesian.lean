module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcoh
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# The cartesian condition on the small étale site is Zariski-local on the base

Let `S` be a scheme and `𝒢` a sheaf of modules on the small étale site of `S`.  This file proves
that the condition `AlgebraicGeometry.SmallEtale.IsCartesianOnAffines` — equivalently, by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffines`, quasi-coherence of
`𝒢` on the site — is local on `S` for the Zariski topology:  it holds as soon as it holds
after restriction to the slice of `S_étale` at each member of a family of opens of `S` covering
`S`, and in particular after restriction to each affine open of `S`.

## Main results

* `AlgebraicGeometry.SmallEtale.coversTop_affineOpens`:  the affine opens of a scheme cover the
  final object of its small Zariski site.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_coversTop_opens`:  quasi-coherence on
  the small étale site is Zariski-local on the base.
* `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_of_coversTop_opens` and
  `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_of_forall_affineOpens`:  the cartesian
  condition is Zariski-local on the base.
* `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_of_coversTop_opens`
  and `isCartesianOnAffines_rightDerived_pushforward_of_forall_affineOpens`:  the same
  statement for a higher direct image along `ε_a`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

section Locality

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine opens of a scheme cover the final object of its small Zariski site. -/
public theorem coversTop_affineOpens :
    (Opens.grothendieckTopology ↥S).CoversTop (fun U : S.affineOpens ↦ (U : S.Opens)) :=
  (Opens.coversTop_iff ↥S _).2 (iSup_affineOpens_eq_top S)

/-- Quasi-coherence on the small étale site of `S` is Zariski-local on `S`: a sheaf of modules
on `S_étale` whose restriction to the slice at each member of a Zariski covering of `S` is
quasi-coherent is quasi-coherent. -/
public theorem isQuasicoherentOnSite_of_coversTop_opens
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type u} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V)
    (hG : ∀ i, (G.over ((opensToSmallEtale B S hS).obj (V i))).IsQuasicoherentOnSite) :
    G.IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite G).2
    ⟨ULift.{u + 1} I, fun i ↦ (opensToSmallEtale B S hS).obj (V i.down),
      coversTop_opensToSmallEtale_ulift B S hS V hV, fun i ↦ hG i.down⟩

/-- A sheaf of modules on `S_étale` whose restriction to the slice at each affine open of `S` is
quasi-coherent is quasi-coherent. -/
public theorem isQuasicoherentOnSite_of_forall_affineOpens
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ∀ U : S.affineOpens,
      (G.over ((opensToSmallEtale B S hS).obj (U : S.Opens))).IsQuasicoherentOnSite) :
    G.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_coversTop_opens B S hS G (fun U : S.affineOpens ↦ (U : S.Opens))
    (coversTop_affineOpens S) hG

/-- If the restriction of `𝒢` to the slice of `S_étale` at each member of a Zariski covering of
`S` is quasi-coherent, then `𝒢` is cartesian between all pairs of affine objects of `S_étale`,
including those not lying over any single member of the covering. -/
public theorem isCartesianOnAffines_of_coversTop_opens
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type u} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V)
    (hG : ∀ i, (G.over ((opensToSmallEtale B S hS).obj (V i))).IsQuasicoherentOnSite) :
    IsCartesianOnAffines B S hS G :=
  isCartesianOnAffines_of_isQuasicoherentOnSite B S hS G
    (isQuasicoherentOnSite_of_coversTop_opens B S hS G V hV hG)

/-- `𝒢` is cartesian between the affine objects of `S_étale` as soon as its restriction to the
slice of `S_étale` at each affine open of `S` is quasi-coherent. -/
public theorem isCartesianOnAffines_of_forall_affineOpens
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : ∀ U : S.affineOpens,
      (G.over ((opensToSmallEtale B S hS).obj (U : S.Opens))).IsQuasicoherentOnSite) :
    IsCartesianOnAffines B S hS G :=
  isCartesianOnAffines_of_isQuasicoherentOnSite B S hS G
    (isQuasicoherentOnSite_of_forall_affineOpens B S hS G hG)

/-- The restriction of a module cartesian between the affine objects of `S_étale` to the slice at
an object is quasi-coherent. -/
public theorem isQuasicoherentOnSite_over_of_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G)
    (U : SmallEtale B S hS) : (G.over U).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherent_over G
    (isQuasicoherentOnSite_of_isCartesianOnAffines B S hS G hG) U

/-- Being cartesian between the affine objects of `S_étale` is equivalent to the restriction to
the slice at each member of a Zariski covering of `S` being quasi-coherent. -/
public theorem isCartesianOnAffines_iff_coversTop_opens
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type u} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    IsCartesianOnAffines B S hS G ↔
      ∀ i, (G.over ((opensToSmallEtale B S hS).obj (V i))).IsQuasicoherentOnSite :=
  ⟨fun hG _ ↦ isQuasicoherentOnSite_over_of_isCartesianOnAffines B S hS G hG _,
    isCartesianOnAffines_of_coversTop_opens B S hS G V hV⟩

end Locality

section HigherDirectImage

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- For every `n`, the sheaf `R ⁿ (ε_a)_*(𝓕)` on `Y_étale` is cartesian between the affine
objects as soon as its restriction to the slice of `Y_étale` at each member of a Zariski covering
of `Y` is quasi-coherent. -/
public theorem isCartesianOnAffines_rightDerived_pushforward_of_coversTop_opens
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (n : ℕ)
    {I : Type u} (V : I → Y.obj.Opens)
    (hV : (Opens.grothendieckTopology ↥Y.obj).CoversTop V)
    (hloc : ∀ i, ((((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
      ((opensToSmallEtale B Y.obj Y.property).obj (V i))).IsQuasicoherentOnSite) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) :=
  isCartesianOnAffines_of_coversTop_opens B Y.obj Y.property _ V hV hloc

/-- For every `n`, the sheaf `R ⁿ (ε_a)_*(𝓕)` on `Y_étale` is cartesian between the affine
objects as soon as its restriction to the slice of `Y_étale` at each affine open of `Y` is
quasi-coherent. -/
public theorem isCartesianOnAffines_rightDerived_pushforward_of_forall_affineOpens
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (n : ℕ)
    (hloc : ∀ U : Y.obj.affineOpens, ((((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).over
      ((opensToSmallEtale B Y.obj Y.property).obj (U : Y.obj.Opens))).IsQuasicoherentOnSite) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) :=
  isCartesianOnAffines_of_forall_affineOpens B Y.obj Y.property _ hloc

end HigherDirectImage

/-! ### Implementation notes

The reduction above is stated at the slice restriction `𝒢|_{S_étale/V}` and not at the small
étale site of `V`, because that is the shape in which quasi-coherence is local on a site.  The
two are the same thing by `AlgebraicGeometry.SmallEtale.objRestrictEquivalence`, and the
restricted higher direct image is the higher direct image along the base-changed morphism by
`AlgebraicGeometry.SmallEtale.rightDerivedLocalizedPushforwardObjIso`. -/

end AlgebraicGeometry.SmallEtale

end
