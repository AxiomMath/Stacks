module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalenceSheafReduction
public import StacksFrontier.CategoryTheory.Sites.LocalSheafCondition

/-!
# Clause (1) of Stacks 03DX at a coarser `τ`, reduced to one global presentation

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalenceSheafReduction` shows
that clause (1) of Stacks 03DX at `τ` is **equivalent** to one sheaf condition,
`AlgebraicGeometry.BigFppfOver.IsSheafFppfOfIsQuasicoherentOnSite τ`: every quasi-coherent
`𝒪`-module on `(Sch/S)_τ` is a sheaf for the localized fppf topology.  **This file reduces that
sheaf condition further, to the same assertion about a single module with a *global*
presentation on a single slice** — with no covering, no descent datum and no gluing left in it.

Quasi-coherence in the sense of Stacks 03DL (6) says exactly that every object `U` of the site
has a `τ`-covering family `V i ⟶ U` on whose members the restricted module has a global
presentation.  So if a global presentation forces the fppf sheaf condition on the slice, then a
quasi-coherent module is an fppf sheaf *locally on a `τ`-covering of every object*, and
`CategoryTheory.Presheaf.isSheaf_of_locally_isSheaf_over_ofArrows` — the locality of the sheaf
condition for one topology with respect to another — turns that into the fppf sheaf condition
itself.  The locality lemma is what makes this step available at all; it is in neither Mathlib
nor this repository elsewhere, and it is proved in
`StacksFrontier/CategoryTheory/Sites/LocalSheafCondition.lean`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.IsSheafFppfOfHasGlobalPresentationOver`: a sheaf of modules on
  the slice of `(Sch/S)_τ` at an object `T` which has a global presentation there is a sheaf for
  the localized fppf topology on that slice.

## Main results

* `AlgebraicGeometry.BigFppfOver.isSheafFppfOfIsQuasicoherentOnSite_of_hasGlobalPresentation`:
  **the reduction** — that assertion gives
  `AlgebraicGeometry.BigFppfOver.IsSheafFppfOfIsQuasicoherentOnSite τ`, hence by
  `…isSheafFppfOfIsQuasicoherentOnSite_iff` the outstanding predicate of clause (1) at `τ`.
* `AlgebraicGeometry.BigFppfOver.isEquivalence_baseAssociatedModuleQcohOnSite_of_presentation`
  and `…baseAssociatedModuleEquivalenceOnSite_of_presentation`: **clause (1) of Stacks 03DX at
  `τ`, over that one assertion alone.**
* `AlgebraicGeometry.BigFppfOver.isSheafFppfOfHasGlobalPresentationOver_fppf`: it holds at
  `τ = fppf`, where it is the sheaf condition the module carries.

## Implementation notes

No `stacks` attribute is placed: everything below carries
`AlgebraicGeometry.BigFppfOver.IsSheafFppfOfHasGlobalPresentationOver` as a hypothesis, which is
discharged here at `τ = fppf` only, and a hypothesis is part of a citation.  **It is discharged
at every `τ` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity`**, by
`AlgebraicGeometry.BigFppfOver.isSheaf_fppf_over_of_hasGlobalPresentation`, and clause (1) is
registered there for every `τ`; the paragraph that follows describes what was left at the time
this file was written, and the route it sketches is the one that file takes — the slice
identification it calls missing is `AlgebraicGeometry.BigFppfOver.objEquiv`, Stacks 06WI for the
identity fibration, whose `τ`-topology instances are Mathlib's and whose ringed-site half is
`AlgebraicGeometry.BigFppfOver.baseReindexRing_objEquiv`, an `rfl`.

**What was left, stated so that it can be attacked without reading this chain.**  Fix a base `T`
of the big site and a sheaf of modules `M` on the slice at `T`, for the localized `τ`-topology,
which is a cokernel of a map between coproducts of copies of the structure sheaf — all three
colimits taken in `τ`-sheaves on the slice.  One must show `M` is a sheaf for the localized fppf
topology.  The mathematics is not descent: a coproduct of copies of the structure sheaf of the
big `τ`-site over `T` is the associated module of the corresponding free module on the scheme of
`T` (`AlgebraicGeometry.BigFppfOver.baseAssociatedModule` preserves colimits at every `τ`, being
a left adjoint), the cokernel of a map between two such is again an associated module (by
Stacks 0GN7 at `τ`, which is unconditional —
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh` — the map is `φ^a` for a
`φ` on the scheme), and an associated module is an fppf sheaf by Stacks 03DT
(`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`).  What
blocks writing that down is none of those three: it is the identification of the *restricted*
structure sheaf, that is, of the slice of `(Sch/S)_τ` at `T` carrying
`(FibredSite.baseRingStructureSheaf B S hS τ).over T` with the big `τ`-site of the scheme of `T`
carrying its own structure sheaf.  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentAssembly` record that
this identification is absent from the library even at `τ = fppf`, while the localization of
Stacks 06WI and the invariance of quasi-coherence under an equivalence of ringed sites are both
present.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A global presentation on a slice forces the fppf sheaf condition there.**  For every
object `T` of the big site, a sheaf of modules on the slice of `(Sch/S)_τ` at `T` which is a
cokernel of a map between coproducts of copies of the structure sheaf — the global presentation
of Stacks 03DE (6), taken in `τ`-sheaves on the slice — has an underlying presheaf of modules
which is a sheaf for the localized fppf topology on that slice. -/
public abbrev IsSheafFppfOfHasGlobalPresentationOver (τ : SiteKind) : Prop :=
  ∀ (T : BigFppfOver B S hS)
    (M : SheafOfModules.{u} ((FibredSite.baseRingStructureSheaf B S hS τ).over T)),
    M.HasGlobalPresentation →
      Presheaf.IsSheaf ((topology B S hS).over T) M.val.presheaf

/-- The assertion holds at `τ = fppf`, where the localized `τ`-topology on the slice *is* the
localized fppf topology and so the conclusion is the sheaf condition the module carries; the
global presentation is not used. -/
public theorem isSheafFppfOfHasGlobalPresentationOver_fppf :
    IsSheafFppfOfHasGlobalPresentationOver B S hS .fppf := fun _ M _ => M.isSheaf

/-- **The reduction of the fppf sheaf condition for the quasi-coherent modules of `(Sch/S)_τ` to
one global presentation.**  Quasi-coherence of Stacks 03DL (6) provides, for every object `U` of
the site, a `τ`-covering family `V i ⟶ U` on whose members the restricted module has a global
presentation; the hypothesis makes each of those restrictions an fppf sheaf on its slice, and
`CategoryTheory.Presheaf.isSheaf_of_locally_isSheaf_over_ofArrows` assembles the fppf sheaf
condition from that `τ`-covering.

The covering is given as a *family*, not as a sieve, and the hypothesis is available at the
`V i` only — which is why the locality lemma is used in its `ofArrows` form. -/
public theorem isSheafFppfOfIsQuasicoherentOnSite_of_hasGlobalPresentation (τ : SiteKind)
    (h : IsSheafFppfOfHasGlobalPresentationOver B S hS τ) :
    IsSheafFppfOfIsQuasicoherentOnSite B S hS τ := by
  intro M hM
  refine Presheaf.isSheaf_of_locally_isSheaf_over_ofArrows
    (K := baseOverTopology B S hS τ) M.isSheaf fun U => ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hM.locally_hasGlobalPresentation U
  exact ⟨I, V, f, hcov, fun i => h (V i) (M.over (V i)) (hpres i)⟩

/-- **Clause (1) of Stacks 03DX at `τ`, over the global-presentation assertion alone**:
`𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)`. -/
public theorem isEquivalence_baseAssociatedModuleQcohOnSite_of_presentation (τ : SiteKind)
    (h : IsSheafFppfOfHasGlobalPresentationOver B S hS τ) :
    (baseAssociatedModuleQcohOnSite B S hS τ).IsEquivalence :=
  isEquivalence_baseAssociatedModuleQcohOnSite_of_isSheafFppf B S hS τ
    (isSheafFppfOfIsQuasicoherentOnSite_of_hasGlobalPresentation B S hS τ h)

/-- **The equivalence of categories of clause (1) of Stacks 03DX at `τ`, over the
global-presentation assertion alone**, `QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)`. -/
public noncomputable def baseAssociatedModuleEquivalenceOnSite_of_presentation (τ : SiteKind)
    (h : IsSheafFppfOfHasGlobalPresentationOver B S hS τ) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ)).FullSubcategory :=
  baseAssociatedModuleEquivalenceOnSite_of_isSheafFppf B S hS τ
    (isSheafFppfOfIsQuasicoherentOnSite_of_hasGlobalPresentation B S hS τ h)

end AlgebraicGeometry.BigFppfOver

end
