module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.RestrictAndPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.AlgebraicGeometry.Perfect.LiftingComplexes.General
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object on a quasi-compact open is a summand of a restriction

Let `X` be a quasi-compact quasi-separated scheme and `U ⊆ X` a quasi-compact open. Every perfect
object `P` of `D(𝒪_U)` is a direct summand of the restriction to `U` of a perfect object of
`D(𝒪_X)`. This is [Stacks, Tag 09IQ].

The source deduces it from [Stacks, Tag 09IM] applied with `T` the whole space and the zero
object, and that is what happens here. With `T = X` the closed subset is everything, so the
supported-cohomology hypotheses of 09IM hold vacuously and its retrocompactness hypothesis
reduces to compactness of the empty set; with `E = 0` the map `α` is zero and the compatibility
`i ≫ β|_U = α` the tag's conclusion carries is discarded.

## Main results

* `Stacks.DerivedQCoh.AnyModel.exists_isPerfect_retract_derivedRestrict`: **[Stacks, Tag
  09IQ]** for a quasi-compact quasi-separated scheme, at the locally small model.

## Implementation notes

**The statement is at the locally small model and 09IM is not.** The lifting results of
`StacksFrontier/AlgebraicGeometry/Perfect/LiftingComplexes/` install
`CategoryTheory.HasDerivedCategory.standard` as a file-local instance and take no model binder, so
they speak only about that model; the compact-generation statements of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/` are at the locally small model of
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which `D(𝒪_X)` has the direct sums
Brown representability asks for, and that is the model this statement is read at: no
`HasDerivedCategory` binder appears below, so the global instances are in force. A free
`[HasDerivedCategory.{w} _]` binder would not do, because such a binder covers the spelling
`X.Modules` and not the spellings `SheafOfModules X.ringCatSheaf` and
`StrictlyPerfect.OXMod (ringedSpace X)` that `Stacks.DerivedQCoh.IsDQCoh` and
`Stacks.Cohomology.PerfectComplexes.IsPerfect` are stated at, and
`AlgebraicGeometry.Scheme.Modules` is not reducible for instance search. The transport between the
two models is `Stacks.DerivedQCoh.AnyModel.derivedRestrictStandardModelIso` for the restriction
functor and `Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff` for perfectness, and the retract
is carried across by the comparison equivalence, a functor, so the one equation `i ≫ p = 𝟙`
transports by functoriality alone.

## References

* [Stacks Project, Tag 09IQ](https://stacks.math.columbia.edu/tag/09IQ)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
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

namespace Stacks.DerivedQCoh.AnyModel

/-- **[Stacks, Tag 09IQ].** Let `X` be a quasi-compact quasi-separated scheme and `U ⊆ X` a
quasi-compact open. Every perfect object `P` of `D(𝒪_U)` is a direct summand -- a retract -- of
the restriction to `U` of a perfect object of `D(𝒪_X)`.

This is [Stacks, Tag 09IM] with `T` the whole space and the zero object, transported from the
model that tag is proved at to the locally small one. -/
@[stacks 09IQ]
theorem exists_isPerfect_retract_derivedRestrict {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (P : DerivedCategory U.toScheme.Modules)
    (hP : IsPerfect (X := ringedSpace U.toScheme) P) :
    ∃ R : DerivedCategory X.Modules, IsPerfect (X := ringedSpace X) R ∧
      ∃ (i : P ⟶ (Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj R)
        (p : (Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj R ⟶ P), i ≫ p = 𝟙 P := by
  classical
  let eX := modelEquiv (HasDerivedCategory.standard X.Modules)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
  let eU := modelEquiv (HasDerivedCategory.standard U.toScheme.Modules)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme)
  let P' := eU.inverse.obj P
  have hP' : @IsPerfect (ringedSpace U.toScheme) (HasDerivedCategory.standard _) P' :=
    (isPerfect_modelEquiv_iff (X := ringedSpace U.toScheme) (HasDerivedCategory.standard _)
        (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme) P').2
      (Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.of_iso
        (eU.counitIso.app P).symm hP)
  have hTc : ∀ W : X.Opens, IsCompact (W : Set X) → IsCompact ((W : Set X) ∩ Set.univᶜ) := by
    intro W _
    simp
  have hPT : AlgebraicGeometry.CohomologySupportedOn U.toScheme.ringCatSheaf
      (⇑U.ι.base ⁻¹' (Set.univ : Set X)) P' := fun _ x hx =>
    absurd (Set.mem_univ (U.ι.base x)) hx
  obtain ⟨R', -, hR', -, i', p', hip, -⟩ :=
    Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift U hU Set.univ isClosed_univ hTc 0
      (by
        have := AlgebraicGeometry.containsZero_isQuasicoherent X
        let := HasDerivedCategory.standard X.Modules
        exact fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
          ((DerivedCategory.homologyFunctor X.Modules i).map_isZero (isZero_zero _)))
      P' hP' hPT 0
  let c := derivedRestrictStandardModelIso U.ι
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme)
  refine ⟨eX.functor.obj R',
    (isPerfect_modelEquiv_iff (X := ringedSpace X) (HasDerivedCategory.standard _)
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X) R').1 hR',
    (eU.counitIso.app P).inv ≫ eU.functor.map i' ≫ c.hom.app R',
    c.inv.app R' ≫ eU.functor.map p' ≫ (eU.counitIso.app P).hom, ?_⟩
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    hip, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (eU.counitIso.app P).inv_hom_id

end Stacks.DerivedQCoh.AnyModel

end
