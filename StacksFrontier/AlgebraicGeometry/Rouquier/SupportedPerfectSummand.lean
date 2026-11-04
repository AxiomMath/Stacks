module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.PerfectSummandOfRestriction
public import StacksFrontier.AlgebraicGeometry.Rouquier.SupportedGeneratorIsoSpec

/-!
# A supported perfect object on a quasi-compact open is a summand of a restriction

Let `X` be a quasi-compact quasi-separated scheme, `U ⊆ X` a quasi-compact open and `T ⊆ X` a
closed subset whose complement is retrocompact. Every perfect object `P` of `D(𝒪_U)` whose
cohomology is supported on `T ∩ U` is a direct summand of the restriction to `U` of a perfect
object of `D(𝒪_X)` whose cohomology is supported on `T`.

This is the supported form of [Stacks, Tag 09IQ], and it is
`Stacks.DerivedQCoh.AnyModel.exists_isPerfect_retract_derivedRestrict` with the support condition
carried along: both are [Stacks, Tag 09IM] applied to the zero object, the unsupported one at
`T` the whole space — where the support hypotheses are vacuous — and this one at the given `T`.
The compatibility `i ≫ β|_U = α` that 09IM's conclusion carries is discarded, `α` being zero.

**What has to be transported.** [Stacks, Tag 09IM] is proved at
`CategoryTheory.HasDerivedCategory.standard`, and the compact-generation cluster that consumes it
— and the base case of [Stacks, Tag 0A9A] in
`StacksFrontier/AlgebraicGeometry/Rouquier/AffineSupportedGenerator.lean` — is at the locally small
model. Three predicates therefore cross between the two models along the comparison equivalence
`StacksDraft.DerivedModel.modelEquiv`: perfectness by
`Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff`, the restriction functor by
`Stacks.DerivedQCoh.AnyModel.derivedRestrictStandardModelIso`, and the support condition by
`Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff`. The retract is carried by a
functor, so the equation `i ≫ p = 𝟙` transports by functoriality alone.

**The two spellings of support, and which one is a model.**
`AlgebraicGeometry.CohomologySupportedOn` — the `@[stacks 08DA]`-registered predicate, and the one
[Stacks, Tag 09IM] is stated with — pins `CategoryTheory.HasDerivedCategory.standard` by a
file-local instance and so cannot be *written* at the locally small model. The statement below
therefore uses the model-free
`Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn`; the two are the same
stalk-vanishing condition, which is exactly what
`Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff` carries across. Both names are
in scope under `open AlgebraicGeometry`, with a universe mismatch rather than an ambiguity error
if the wrong one is picked up, so both are always written out qualified.

## Main definitions

None.

## Main results

* `Stacks.Rouquier.exists_isPerfect_supported_retract_derivedRestrict` — the supported form of
  [Stacks, Tag 09IQ] for a quasi-compact quasi-separated scheme, at the locally small model.

## Implementation notes

**No `@[stacks]` attribute is attached.** Tag 09IQ is the unsupported statement and is registered
on `Stacks.DerivedQCoh.AnyModel.exists_isPerfect_retract_derivedRestrict`; what is below is a
different statement, the one the proof of [Stacks, Tag 0A9A] needs, and the source states it
inside the proof of 0A9A rather than as a numbered result. Tag 0A9A itself is the
quasi-compact quasi-separated *scheme* statement and is two steps further on, registered on
`Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported` of
`StacksFrontier/AlgebraicGeometry/Rouquier/SupportedGeneratorQcqs.lean`.

**The model is the locally small one** of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`:
no `CategoryTheory.HasDerivedCategory` binder appears below, so instance search supplies the
global instances. A free `[HasDerivedCategory.{w} _]` binder would not do, for the reason given in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AnyModel/PerfectSummandOfRestriction.lean`: such a
binder covers the spelling `AlgebraicGeometry.Scheme.Modules X` and not the spellings
`SheafOfModules X.ringCatSheaf` and `StrictlyPerfect.OXMod (ringedSpace X)` that the support and
perfectness predicates are stated at.

**The retrocompactness hypothesis is in [Stacks, Tag 09IM]'s own shape**, as the universal
quantification over quasi-compact opens `W` of compactness of `W ∩ Tᶜ`, rather than as
`IsCompact Tᶜ`. The two agree on a quasi-separated space, and leaving it in this shape keeps the
statement as general as the result it is deduced from.

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09IQ](https://stacks.math.columbia.edu/tag/09IQ)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.SchemeCohomology (ringedSpace)
open StacksDraft.DerivedModel
open ZeroObject

universe u

namespace Stacks.Rouquier

/-- **The supported form of [Stacks, Tag 09IQ].** Let `X` be a quasi-compact quasi-separated
scheme, `U ⊆ X` a quasi-compact open and `T ⊆ X` a closed subset with retrocompact complement.
Every perfect object `P` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` is a direct summand
-- a retract -- of the restriction to `U` of a perfect object of `D(𝒪_X)` whose cohomology is
supported on `T`.

This is [Stacks, Tag 09IM] applied to the zero object, transported from the model that tag is
proved at to the locally small one; see the module documentation for the three transports. -/
theorem exists_isPerfect_supported_retract_derivedRestrict {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X)) (T : Set X)
    (hT : IsClosed T)
    (hTc : ∀ W : X.Opens, IsCompact (W : Set X) → IsCompact ((W : Set X) ∩ Tᶜ))
    (P : DerivedCategory U.toScheme.Modules)
    (hP : IsPerfect (X := ringedSpace U.toScheme) P)
    (hPT : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      U.toScheme.ringCatSheaf (⇑U.ι.base ⁻¹' T) P) :
    ∃ R : DerivedCategory X.Modules, IsPerfect (X := ringedSpace X) R ∧
      Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf T R ∧
      ∃ (i : P ⟶ (Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj R)
        (p : (Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj R ⟶ P), i ≫ p = 𝟙 P := by
  classical
  let eX := modelEquiv (HasDerivedCategory.standard X.Modules)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
  let eU := modelEquiv (HasDerivedCategory.standard U.toScheme.Modules)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme)
  let P' := eU.inverse.obj P
  have hP' : @IsPerfect (ringedSpace U.toScheme) (HasDerivedCategory.standard _) P' :=
    (Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff (X := ringedSpace U.toScheme)
        (HasDerivedCategory.standard _)
        (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme) P').2
      (Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.of_iso
        (eU.counitIso.app P).symm hP)
  have hPT' : AlgebraicGeometry.CohomologySupportedOn U.toScheme.ringCatSheaf
      (⇑U.ι.base ⁻¹' T) P' := by
    intro i x hx
    refine (Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff
      U.toScheme.ringCatSheaf (HasDerivedCategory.standard _)
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme) P' i x).2 ?_
    exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _
      (eU.counitIso.app P).symm hPT i x hx
  obtain ⟨R', -, hR', hR'T, i', p', hip, -⟩ :=
    Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift U hU T hT hTc 0
      (by
        have := AlgebraicGeometry.containsZero_isQuasicoherent X
        let := HasDerivedCategory.standard X.Modules
        exact fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
          ((DerivedCategory.homologyFunctor X.Modules i).map_isZero (isZero_zero _)))
      P' hP' hPT' 0
  let c := Stacks.DerivedQCoh.AnyModel.derivedRestrictStandardModelIso U.ι
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme)
  refine ⟨eX.functor.obj R',
    (Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff (X := ringedSpace X)
      (HasDerivedCategory.standard _)
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X) R').1 hR',
    fun i x hx => (Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff
      X.ringCatSheaf (HasDerivedCategory.standard _)
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X) R' i x).1 (hR'T i x hx),
    (eU.counitIso.app P).inv ≫ eU.functor.map i' ≫ c.hom.app R',
    c.inv.app R' ≫ eU.functor.map p' ≫ (eU.counitIso.app P).hom, ?_⟩
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    hip, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (eU.counitIso.app P).inv_hom_id

end Stacks.Rouquier

end
