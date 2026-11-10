module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceOfUniv
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposReplacement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoefficientChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange

/-!
# Quasi-coherent modules on the spaces-étale site and on the small étale site

Let `Y` be an algebraic space over a scheme `S`.  The comparison functor of Stacks 03G1 from the
small étale site of `Y` to its spaces-étale site induces an equivalence of topoi.  This file
proves the corresponding statement for sheaves of modules, with the module sections in the
universe `u + 1` of the spaces-étale site: sheaves of modules on the ringed spaces-étale site of
`Y` are the same thing as `𝒪_Y`-modules on the small étale site of `Y` with sections in
`Type (u + 1)`, and quasi-coherence (Stacks 03DL (6)) corresponds on the two sides.  It also proves
that the small étale reading of a quasi-coherent module is cartesian on affine charts, the
forward implication of Descent, Proposition 03DX (2), read through the comparison.

## The three steps

* The comparison functor goes from a site with morphisms in `Type u` to one with morphisms in
  `Type (u + 1)`.  Raising the morphisms of the small étale site (`ULiftHom`) produces a site in
  the universes of the spaces-étale site on which the comparison is special cocontinuous, and
  there `Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff` applies.
* The raising of the morphisms is an equivalence of sites with the same objects, across which
  quasi-coherence is invariant by
  `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff`.
* The structure sheaf so obtained has its sections in `Type (u + 1)`, the structure sheaf of the
  small étale site in `Type u`; the two are identified sectionwise by
  `AlgebraicGeometry.Space.comparisonGlobalFunctionsRingEquiv`, and the change of coefficients is
  `Stacks.SheafOfModules.CoefficientChange.coefficientEquivalence`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtaleLifted`, `AlgebraicGeometry.Space.liftedComparisonFunctor`:
  the small étale site with its morphisms raised, and the comparison functor out of it.
* `AlgebraicGeometry.Space.readingEquivalence`: Stacks 03G1 for sheaves of modules, over the
  restricted structure sheaf.
* `AlgebraicGeometry.Space.smallEtaleModuleEquivalence`: the same over the structure sheaf of the
  small étale site, landing in `AlgebraicGeometry.Space.Modules.{u, u + 1}`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_smallEtale`: **quasi-coherence corresponds
  under `smallEtaleModuleEquivalence`.**
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleModule`: the reading of a
  quasi-coherent module is cartesian on affine charts.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-- The small étale site of `Y` with its morphisms raised to the universe `u + 1`. -/
abbrev SmallEtaleLifted := ULiftHom.{u + 1} (SmallEtale B S hS Y.obj)

/-- The equivalence raising the morphisms of the small étale site. -/
abbrev smallEtaleLiftedEquiv : SmallEtale B S hS Y.obj ≌ SmallEtaleLifted B S hS Y :=
  ULiftHom.equiv

/-- The étale topology on `SmallEtaleLifted`. -/
abbrev smallEtaleLiftedTopology : GrothendieckTopology (SmallEtaleLifted B S hS Y) :=
  (smallEtaleLiftedEquiv B S hS Y).inverse.inducedTopology (SmallEtale.topology B S hS Y.obj)

/-- The comparison functor of Stacks 03G1, out of the lifted small étale site. -/
abbrev liftedComparisonFunctor : SmallEtaleLifted B S hS Y ⥤ SpacesEtale B S hS Y :=
  (smallEtaleLiftedEquiv B S hS Y).inverse ⋙ comparisonFunctor B S hS Y

/-- Lowering the morphisms back is a dense subsite inclusion for the transported topology. -/
instance : (smallEtaleLiftedEquiv B S hS Y).inverse.IsDenseSubsite
    (smallEtaleLiftedTopology B S hS Y) (SmallEtale.topology B S hS Y.obj) := inferInstance

/-- Lowering the morphisms back is cocontinuous: its right adjoint preserves coverings. -/
instance : (smallEtaleLiftedEquiv B S hS Y).inverse.IsCocontinuous
    (smallEtaleLiftedTopology B S hS Y) (SmallEtale.topology B S hS Y.obj) :=
  ((smallEtaleLiftedEquiv B S hS Y).symm.toAdjunction.isCocontinuous_iff_coverPreserving
    (smallEtaleLiftedTopology B S hS Y) (SmallEtale.topology B S hS Y.obj)).2
    (Functor.IsDenseSubsite.coverPreserving (SmallEtale.topology B S hS Y.obj)
      (smallEtaleLiftedTopology B S hS Y) (smallEtaleLiftedEquiv B S hS Y).functor)

/-- The comparison functor out of the lifted small étale site is a dense subsite inclusion. -/
instance isDenseSubsite_liftedComparisonFunctor :
    (liftedComparisonFunctor B S hS Y).IsDenseSubsite (smallEtaleLiftedTopology B S hS Y)
      (SpacesEtale.topology B S hS Y) :=
  Functor.isDenseSubsite_comp _ (SmallEtale.topology B S hS Y.obj) _ _ _

/-- The comparison functor out of the lifted small étale site is cocontinuous. -/
instance isCocontinuous_liftedComparisonFunctor :
    (liftedComparisonFunctor B S hS Y).IsCocontinuous (smallEtaleLiftedTopology B S hS Y)
      (SpacesEtale.topology B S hS Y) :=
  have := (comparisonFunctor_specialCocontinuous B S hS Y).1
  isCocontinuous_comp _ _ (smallEtaleLiftedTopology B S hS Y) (SmallEtale.topology B S hS Y.obj)
    (L := SpacesEtale.topology B S hS Y)

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for module sheaves on the spaces-étale and lifted small étale sites is slow
/-- **Quasi-coherence on the spaces-étale site is quasi-coherence on the lifted small étale site.**
The comparison functor is special cocontinuous and the two sites share their universes, so this is
`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`. -/
theorem isQuasicoherentOnSite_iff_liftedComparison
    (M : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)) :
    M.IsQuasicoherentOnSite ↔
      ((Stacks.DenseSubsiteModules.moduleRestriction (smallEtaleLiftedTopology B S hS Y)
        (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
        (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).obj M).IsQuasicoherentOnSite :=
  Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff _ _ _ _ M

/-- Raising the morphisms of the small étale site is continuous. -/
instance : (smallEtaleLiftedEquiv B S hS Y).functor.IsContinuous
    (SmallEtale.topology B S hS Y.obj) (smallEtaleLiftedTopology B S hS Y) :=
  Functor.IsDenseSubsite.instIsContinuous _ _ _

/-- The structure sheaf of the spaces-étale site of `Y` read on the small étale site of `Y`:
restricted along the comparison functor of Stacks 03G1, through the lifted small étale site. -/
abbrev readingRing : Sheaf (SmallEtale.topology B S hS Y.obj) RingCat.{u + 1} :=
  Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS Y.obj)
    (smallEtaleLiftedEquiv B S hS Y)
    (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleLiftedTopology B S hS Y)
      (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
      (ringSheaf (spacesEtaleRingedSite B S hS Y).O))

/-- **Stacks 03G1 for sheaves of modules**: sheaves of modules on the ringed spaces-étale site of
`Y` are sheaves of modules on its small étale site, over the restricted structure sheaf. -/
def readingEquivalence :
    SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O) ≌
      SheafOfModules.{u + 1} (readingRing B S hS Y) :=
  (Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (smallEtaleLiftedTopology B S hS Y)
      (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
      (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).trans
    (Stacks.SheafOfModules.reindexEquivalence (smallEtaleLiftedEquiv B S hS Y)
      (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleLiftedTopology B S hS Y)
        (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
        (ringSheaf (spacesEtaleRingedSite B S hS Y).O)))

/-- **Quasi-coherence is invariant under the equivalence of Stacks 03G1 for sheaves of modules.**
The step from the lifted small étale site to the small étale site is an equivalence of sites with
the same objects and morphisms in different universes,
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff`. -/
theorem isQuasicoherentOnSite_iff_reading
    (M : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)) :
    M.IsQuasicoherentOnSite ↔
      ((readingEquivalence B S hS Y).functor.obj M).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_liftedComparison B S hS Y M).trans
    (Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff.{u + 1, u + 1, u,
      u + 1, u + 1} (smallEtaleLiftedEquiv B S hS Y)
      (Stacks.DenseSubsiteModules.ringRestriction (smallEtaleLiftedTopology B S hS Y)
        (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
        (ringSheaf (spacesEtaleRingedSite B S hS Y).O)) _).symm

/-- The structure ring of the small étale site of `Y` at a chart is the ring of global regular
functions of the algebraic space attached to the chart. -/
def smallEtaleRingEquiv (V : (SmallEtale B S hS Y.obj)ᵒᵖ) :
    (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O).obj.obj V ≃+*
      (readingRing B S hS Y).obj.obj V :=
  (comparisonGlobalFunctionsRingEquiv B S hS Y V.unop).symm

/-- The identification `smallEtaleRingEquiv` is compatible with restriction. -/
theorem smallEtaleRingEquiv_naturality {V V' : (SmallEtale B S hS Y.obj)ᵒᵖ} (f : V ⟶ V')
    (a : (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O).obj.obj V) :
    smallEtaleRingEquiv B S hS Y V'
        ((ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O).obj.map f a) =
      (readingRing B S hS Y).obj.map f (smallEtaleRingEquiv B S hS Y V a) :=
  (SmallEtale.chartStructureRingHom_naturality B S hS Y f.unop a).symm

/-- **Stacks 03G1 for sheaves of modules, over the structure sheaf of the small étale site.**
Sheaves of modules on the ringed spaces-étale site of `Y` are the `𝒪_Y`-modules on its small
étale site, with sections in the universe `u + 1`. -/
def smallEtaleModuleEquivalence :
    SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O) ≌
      Modules.{u, u + 1} B S hS Y.obj Y.2 :=
  (readingEquivalence B S hS Y).trans
    (Stacks.SheafOfModules.CoefficientChange.coefficientEquivalence.{u + 1, u, u + 1, u, u + 1}
      (readingRing B S hS Y) (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O)
      (smallEtaleRingEquiv B S hS Y) (smallEtaleRingEquiv_naturality B S hS Y))

/-- **A module on the ringed spaces-étale site of `Y` is quasi-coherent if and only if the
corresponding `𝒪_Y`-module on the small étale site is.** -/
theorem isQuasicoherentOnSite_iff_smallEtale
    (M : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)) :
    M.IsQuasicoherentOnSite ↔
      ((smallEtaleModuleEquivalence B S hS Y).functor.obj M).IsQuasicoherentOnSite := by
  rw [isQuasicoherentOnSite_iff_reading]
  refine ⟨fun h =>
    Stacks.SheafOfModules.CoefficientChange.isQuasicoherentOnSite_restrictCoefficients.{
      u + 1, u, u + 1, u + 1, u} (readingRing B S hS Y)
      (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O) (smallEtaleRingEquiv B S hS Y)
      (smallEtaleRingEquiv_naturality B S hS Y) _ h, fun h => ?_⟩
  let E := Stacks.SheafOfModules.CoefficientChange.coefficientEquivalence.{u + 1, u, u + 1, u,
    u + 1} (readingRing B S hS Y) (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O)
    (smallEtaleRingEquiv B S hS Y) (smallEtaleRingEquiv_naturality B S hS Y)
  have h' := Stacks.SheafOfModules.CoefficientChange.isQuasicoherentOnSite_restrictCoefficients.{
    u, u + 1, u + 1, u + 1, u} (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O)
    (readingRing B S hS Y) (fun V => (smallEtaleRingEquiv B S hS Y V).symm)
    (fun f a => by
      apply (smallEtaleRingEquiv B S hS Y _).injective
      rw [RingEquiv.apply_symm_apply]
      exact ((smallEtaleRingEquiv_naturality B S hS Y f _).trans
        (by rw [RingEquiv.apply_symm_apply])).symm) _ h
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (E.unitIso.app ((readingEquivalence B S hS Y).functor.obj M)).symm h'

/-- **The small étale reading of a quasi-coherent module is cartesian on affine charts.**  Its
base change comparison along a morphism of affine étale charts is the base change comparison of
the reading of the module on the affine étale site (Stacks 0H01), transported along the
identification of the lifted coordinate rings with the coordinate rings by
`Stacks.RingSquare.tensorMap`, and the latter is bijective by Stacks 0H04,
`AlgebraicGeometry.Space.SmallEtale.isIso_restrictionBaseChange_affineEtaleModule`. -/
theorem isCartesianOnAffineCharts_smallEtaleModule
    (M : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O))
    (hM : M.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts ((smallEtaleModuleEquivalence B S hS Y).functor.obj M) := by
  intro U V hU hV f
  let N := (smallEtaleModuleEquivalence B S hS Y).functor.obj M
  let Uaff : AffineEtale B S hS Y.obj := ⟨U, hU⟩
  let Vaff : AffineEtale B S hS Y.obj := ⟨V, hV⟩
  let g : Vaff ⟶ Uaff := ObjectProperty.homMk f
  let Naff := SmallEtale.affineEtaleModule B S hS Y M Y.2
  have hbij : Function.Bijective
      (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
        (R := (affineEtaleStructureSheaf B S hS Y.obj Y.2).obj) Naff.val g.op) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      (SmallEtale.isIso_restrictionBaseChange_affineEtaleModule B S hS Y M Y.2 hM g)
  let algUV : Algebra
      ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Uaff) : Type (u + 1))
      ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Vaff) : Type (u + 1)) :=
    (((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.map g.op).hom).toAlgebra
  let modUP : Module
      ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Uaff) : Type (u + 1))
      (N.val.obj (op U)) :=
    (Naff.val.obj (op Uaff)).isModule
  let := chartAlgebra (hF := Y.2) f
  let a := chartRestrict (hF := Y.2) f
  let b := (((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.map g.op).hom)
  let α : chartRing B S hS Y.obj Y.2 U ≃+*
      ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Uaff) : Type (u + 1)) :=
    ULift.ringEquiv.symm
  let β : chartRing B S hS Y.obj Y.2 V ≃+*
      ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Vaff) : Type (u + 1)) :=
    ULift.ringEquiv.symm
  have hsq : ∀ t, β (a t) = b (α t) := fun t => rfl
  have hA : ∀ (t : chartRing B S hS Y.obj Y.2 U) (c : chartRing B S hS Y.obj Y.2 V),
      t • c = a t * c := fun t c => rfl
  have hB : ∀ (s : ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Uaff) : Type (u + 1)))
      (d : ((affineEtaleStructureSheaf B S hS Y.obj Y.2).obj.obj (op Vaff) : Type (u + 1))),
      s • d = b s * d := fun s d => rfl
  have hP : ∀ (t : chartRing B S hS Y.obj Y.2 U) (x : N.val.obj (op U)), t • x = α t • x :=
    fun t x => rfl
  let T := Stacks.RingSquare.tensorMap a b α β hsq hA hB hP
  let rbc := Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
    (R := (affineEtaleStructureSheaf B S hS Y.obj Y.2).obj) Naff.val g.op
  have key : (sectionsBaseChange N f).toAddMonoidHom = rbc.hom.toAddMonoidHom.comp T := by
    refine Stacks.Sites.addHom_ext_tmul (Rr := chartRing B S hS Y.obj Y.2 U) (fun c m => ?_)
    exact (Stacks.PresheafOfModules.restrictionBaseChange_tmul.{u + 1, u, u + 1, u + 1}
      (R := (affineEtaleStructureSheaf B S hS Y.obj Y.2).obj) Naff.val g.op (β c) m).symm
  have : ⇑(sectionsBaseChange N f) = ⇑rbc.hom ∘ ⇑T :=
    congrArg (fun φ : _ →+ _ => (φ : _ → _)) key
  rw [this]
  exact hbij.comp (Stacks.RingSquare.bijective_tensorMap a b α β hsq hA hB hP)

end AlgebraicGeometry.Space
