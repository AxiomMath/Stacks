module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitShifts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceModulesAbelian
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafSpelling
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# [Stacks, Tag 08EU] is local on the base

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, `E ∈ D_QCoh(𝒪_X)`
and `K ∈ D_QCoh(𝒪_Y)`.  [Stacks, Tag 08EU] asserts that the projection-formula morphism of
[Stacks, Tag 0B53],

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

is an isomorphism.  The source's proof opens *"To check the map is an isomorphism we may work
locally on `Y`.  Hence we reduce to the case that `Y` is affine."*  This file carries out exactly
that sentence, and nothing else: it proves that the tag for an arbitrary base follows from the
tag for an **affine** base, for the same `f`, `E` and `K` and under no further hypothesis.

## Main results

* `isDQCoh_derivedPullback`: derived pullback along an arbitrary morphism of schemes preserves
  membership of `D_QCoh`.  This is [Stacks, Tag 08DW] part (1) read at the spelling the
  projection-formula morphism uses.
* `isIso_projectionFormulaMap_of_isDQCoh_of_affineBase`: **the reduction to an affine base.**
  Granted [Stacks, Tag 08EU] for every quasi-compact quasi-separated morphism of schemes whose
  target is affine, it holds for every quasi-compact quasi-separated morphism of schemes.

## No tag is attached here

The reduction takes the affine case as the hypothesis `haff`, which nothing in this development
yet concludes, so neither declaration states [Stacks, Tag 08EU] and neither carries its
attribute.  The two registrations of that tag stay where they are, on
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject` and
`isIso_projectionFormulaMap_unitShift_unconditional`.

## How the three ingredients fit

*Locality.*  `Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map` reduces invertibility
in `D(𝒪_Y)` to invertibility after restriction to each member of an open cover of `Y`; the cover
taken here is the family of **all** affine opens, which covers by
`AlgebraicGeometry.iSup_affineOpens_eq_top`.  Restriction to an open is derived pullback along the
inclusion of the open subspace, by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`, and for an open `V` of
a scheme the inclusion of the open subspace *is* the underlying morphism of ringed spaces of the
open immersion `V.ι` of schemes — `rfl`, which is what lets the next ingredient apply.

*Base change along an open immersion.*
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap`
([Stacks, Tag 0B6B] read for invertibility) says that on a Cartesian square of ringed spaces with
open-immersion horizontals, invertibility of the projection-formula morphism upstairs gives
invertibility of its derived pullback downstairs.  The square is the scheme-theoretic fibre
product `X ×_Y V`, which stays Cartesian in ringed spaces by
`Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion`.

*The hypotheses survive the base change.*  `pullback.snd f V.ι` is quasi-compact and
quasi-separated because both properties are stable under base change, `V` is affine because it is
an affine open (`AlgebraicGeometry.IsAffineOpen` is `IsAffine` of the open subscheme), and the two
complexes stay in `D_QCoh` by `isDQCoh_derivedPullback`.  So all four hypotheses of the affine case
are met, and `haff` is applied at the geometric data the localization produces rather than at
anything assumed.

## Implementation notes

*`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.*
The import closure contains the locally small instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory`; at
equal priority instance search picks one of those for `SheafOfModules.{u} (structureSheafRing _)`,
which changes the morphism universe of the derived category from `u + 1` to `u`.  The symptom is a
type mismatch between `IsIso.{u, u + 1}` and `IsIso.{u + 1, u + 1}` reported at the application of
the locality theorem, with nothing in the message naming the instance.  The same attribute at the
same priority is carried by
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` for the
same reason.

*`Stacks.DerivedQCoh.IsDQCoh` is applied with `R` explicit.*  Two occurrences of it in one
statement, over two different schemes, do not get independent universes if the first is left to
unification: the second is then elaborated at `DerivedCategory.{1, 0, 1}` and the statement is
rejected.  Writing `(R := structureSheafRing X.toRingedSpace)` pins each one.

*`Mod(𝒪_Z)` is abelian, named locally.*  As in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaPerfect.lean`, the
instance is stated at the `structureSheafRing Z` spelling that the declarations below use, because
the `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf` spelling is reached from it only through
`implicit_reducible`, which is not the transparency instance synthesis runs at.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaQCohLocalization

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- **[Stacks, Tag 08DW] part (1) in the projection formula's spelling.**  Derived pullback along
an arbitrary morphism of schemes carries a complex with quasi-coherent cohomology to a complex
with quasi-coherent cohomology.

This is `Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`, which is already
stated for an arbitrary morphism of schemes, at an arbitrary model of the two derived categories
and over `structureSheafRing _.toRingedSpace`; `Stacks.DerivedQCoh.IsDQCoh` is by definition the
universally quantified form of its conclusion. -/
theorem isDQCoh_derivedPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace)
      ((derivedPullback g.toLRSHom.toShHom).obj K) :=
  fun i => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g K hK i

/-- **[Stacks, Tag 08EU] is local on the base.**  Suppose the projection-formula morphism of
[Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is invertible for every quasi-compact quasi-separated morphism of schemes with **affine** target
and every pair of complexes with quasi-coherent cohomology.  Then it is invertible for every
quasi-compact quasi-separated morphism of schemes and every such pair.

This is the first sentence of the source's proof.  The cover of `Y` is its family of all affine
opens; over an affine open `V` the morphism is replaced by its base change
`pullback.snd f V.ι : X ×_Y V ⟶ V`, which is again quasi-compact and quasi-separated, and the two
complexes by their derived pullbacks, which are again quasi-coherent.  Nothing else about `f`,
`E` or `K` is used, and no boundedness or flatness enters. -/
theorem isIso_projectionFormulaMap_of_isDQCoh_of_affineBase
    (haff : ∀ (X' Y' : Scheme.{u}) (f' : X' ⟶ Y'), QuasiCompact f' → QuasiSeparated f' →
      IsAffine Y' →
      ∀ (E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
        (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))),
        Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X'.toRingedSpace) E' →
        Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y'.toRingedSpace) K' →
        IsIso (projectionFormulaMap f'.toLRSHom.toShHom E' K'))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) := by
  refine Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map
    (structureSheafRing Y.toRingedSpace)
    (fun V : Y.affineOpens => (V.1 : Y.Opens))
    (AlgebraicGeometry.iSup_affineOpens_eq_top Y) _ fun V => ?_
  refine (NatIso.isIso_map_iff
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
      Y.toRingedSpace (V.1 : Y.Opens)) _).mp ?_
  have : IsAffine (V.1 : Scheme.{u}) := V.2
  exact Stacks.Cohomology.ProjectionFormulaPerfect.isIso_derivedPullback_map_projectionFormulaMap
    (Limits.pullback.fst f V.1.ι).toLRSHom.toShHom
    (Limits.pullback.snd f V.1.ι).toLRSHom.toShHom
    f.toLRSHom.toShHom V.1.ι.toLRSHom.toShHom
    (Stacks.Cohomology.DerivedBaseChange.isPullback_toShHom_of_isOpenImmersion
      (Limits.pullback.fst f V.1.ι) (Limits.pullback.snd f V.1.ι) f V.1.ι
      (IsPullback.of_hasPullback f V.1.ι))
    E K
    (haff _ _ (Limits.pullback.snd f V.1.ι) inferInstance inferInstance inferInstance _ _
      (isDQCoh_derivedPullback (Limits.pullback.fst f V.1.ι) E hE)
      (isDQCoh_derivedPullback V.1.ι K hK))

end Stacks.Cohomology.ProjectionFormulaQCohLocalization

end

end
