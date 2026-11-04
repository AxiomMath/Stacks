module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpaceExtensions

/-!
# Restriction of quasi-coherent modules to the small étale site, over named inputs

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`.  **Stacks 0GQD** asserts that restriction to the small étale site of `X` — equation 075K read
on sheaves of modules — is an equivalence

```
QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X),   ℱ ↦ ℱ|_{X_étale}
```

with quasi-inverse `𝒢 ↦ π_X^*𝒢`.  This file names the quasi-inverse `π_X^*` as a functor and
proves both clauses at the module universe `max (u + 1) w m` over three named Props:

* `AlgebraicGeometry.Space.RestrictionPreservesQuasicoherent` (`hres`): restriction to the small
  étale site preserves quasi-coherence (Stacks 0GQC);
* `AlgebraicGeometry.Space.ProjectionPullbackPreservesQuasicoherent` (`hqcoh`): `π_X^*`
  corestricts to the quasi-coherent subcategories;
* `AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso` (`hcounit`): the counit of
  `π_X^* ⊣ i_X^*` is an isomorphism at every quasi-coherent `𝒪_𝒳`-module.

At the module universe `u`, for `𝒳 : Type (u + 1)` with `Category.{u} 𝒳`, all three are theorems
and both clauses hold unconditionally, as
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_unconditional` and
`AlgebraicGeometry.Space.nonempty_inv_toSiteModules_iso_projectionModulePullback_unconditional`.

## Main definitions

* `AlgebraicGeometry.Space.projectionModulePullback`: `π_X^*`, the chosen left adjoint of
  restriction to the small étale site of `X`, at the module universe `max u m`.
* `AlgebraicGeometry.Space.projectionModulePullbackAdjunction`: `π_X^* ⊣ i_X^*`.
* `AlgebraicGeometry.Space.ProjectionPullbackPreservesQuasicoherent`: `π_X^*` corestricts to the
  quasi-coherent subcategories.
* `AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso`: the counit of `π_X^* ⊣ i_X^*` is an
  isomorphism at every quasi-coherent module.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_descentInputs`: the
  equivalence clause of Stacks 0GQD, over `hres`, `hqcoh` and `hcounit`.
* `AlgebraicGeometry.Space.nonempty_inv_comp_toSiteModules_iso_projectionModulePullback`: the
  quasi-inverse clause of Stacks 0GQD — the inverse of that equivalence is `𝒢 ↦ π_X^*𝒢` — over
  the same three.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v w m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-! ### The quasi-inverse, named -/

/-- **The quasi-inverse `π_X^*` of Stacks 0GQD**, as a functor: the chosen left adjoint
(`CategoryTheory.Functor.leftAdjoint`) of restriction to the small étale site of the algebraic
space `X` representing `𝒳`, at the module universe `max u m`. -/
noncomputable def projectionModulePullback :
    Modules.{u, max u m} B S hS X.1 X.2 ⥤
      SheafOfModules.{max u m} (FibredSite.ringStructureSheafCore B S hS p hp .etale) :=
  letI := isRightAdjoint_moduleRestriction'.{u, v, w, m} B S hS X p hp e
  (moduleRestriction.{u, v, w, max u m} B S hS X p hp e).leftAdjoint

/-- The adjunction `π_X^* ⊣ i_X^*` between `AlgebraicGeometry.Space.projectionModulePullback` and
restriction to the small étale site of `X`. -/
noncomputable def projectionModulePullbackAdjunction :
    projectionModulePullback.{u, v, w, m} B S hS X p hp e ⊣
      moduleRestriction.{u, v, w, max u m} B S hS X p hp e :=
  letI := isRightAdjoint_moduleRestriction'.{u, v, w, m} B S hS X p hp e
  Adjunction.ofIsRightAdjoint _

/-- The unit of `π_X^* ⊣ i_X^*` is an isomorphism at the module universe `max (u + 1) w m`. -/
theorem isIso_unit_projectionModulePullbackAdjunction :
    IsIso (projectionModulePullbackAdjunction.{u, v, w, max (u + 1) w m}
      B S hS X p hp e).unit :=
  isIso_unit_moduleRestriction.{u, v, w, m} B S hS X p hp e _

/-! ### The two inputs on the quasi-inverse -/

/-- **`π_X^*` preserves quasi-coherence**: there is a functor `Pq : QCoh(𝒪_X) ⥤ QCoh(𝒪_𝒳)` whose
composite with the reading of a quasi-coherent fppf module as an étale sheaf of modules is `π_X^*`
on the underlying `𝒪_X`-modules.  Since `AlgebraicGeometry.FibredSite.toSiteModules` is fully
faithful and changes neither the underlying presheaf of modules nor the morphisms, this says that
`π_X^*𝒢` is quasi-coherent in the sense of Stacks 06WG for quasi-coherent `𝒢`. -/
abbrev ProjectionPullbackPreservesQuasicoherent : Prop :=
  ∃ Pq : QuasicoherentSheaves.{u, max u m} B S hS X.1 X.2 ⥤
      FibredSite.quasicoherentModules.{u, v, w, max u m} B S hS p hp,
    Nonempty (Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, max u m} B S hS X).ι ⋙
        projectionModulePullback.{u, v, w, m} B S hS X p hp e)

/-- **The counit of `π_X^* ⊣ i_X^*` is an isomorphism on quasi-coherent modules**: the counit
`π_X^*(ℱ|_{X_étale}) ⟶ ℱ` is an isomorphism at every quasi-coherent `𝒪_𝒳`-module `ℱ`. -/
abbrev ProjectionPullbackCounitIsIso : Prop :=
  ∀ M : FibredSite.quasicoherentModules.{u, v, w, max u m} B S hS p hp,
    IsIso ((projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).counit.app
      ((FibredSite.toSiteModules B S hS p hp .etale).obj M))

/-! ### Stacks 0GQD over those inputs -/

/-- **The equivalence clause of Stacks 0GQD, over named inputs.**  Given `hres`, `hqcoh` and
`hcounit`, restriction to the small étale site of `X` — equation 075K, corestricted to the
quasi-coherent modules by `hres` — is an equivalence `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X)` for a category
fibred in groupoids representable by the algebraic space `X`. -/
theorem isEquivalence_quasicoherentRestriction_of_descentInputs
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, max (u + 1) w m} B S hS X p hp e)
    (hqcoh : ProjectionPullbackPreservesQuasicoherent.{u, v, w, max (u + 1) w m}
      B S hS X p hp e)
    (hcounit : ProjectionPullbackCounitIsIso.{u, v, w, max (u + 1) w m} B S hS X p hp e) :
    (quasicoherentRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e hres).IsEquivalence := by
  obtain ⟨Pq, ⟨hPq⟩⟩ := hqcoh
  exact isEquivalence_quasicoherentRestriction_of_hcounit.{u, v, w, m} B S hS X p hp e hres
    (projectionModulePullbackAdjunction.{u, v, w, max (u + 1) w m} B S hS X p hp e) Pq hPq
    hcounit

/-- **The quasi-inverse clause of Stacks 0GQD, over named inputs.**  Given `hres`, `hqcoh` and
`hcounit`, composing the inverse of the equivalence
`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_descentInputs` with the reading
of a quasi-coherent fppf module as an étale sheaf of modules gives `π_X^*` on the underlying
`𝒪_X`-modules. -/
theorem nonempty_inv_comp_toSiteModules_iso_projectionModulePullback
    (hres : RestrictionPreservesQuasicoherent.{u, v, w, max (u + 1) w m} B S hS X p hp e)
    (hqcoh : ProjectionPullbackPreservesQuasicoherent.{u, v, w, max (u + 1) w m}
      B S hS X p hp e)
    (hcounit : ProjectionPullbackCounitIsIso.{u, v, w, max (u + 1) w m} B S hS X p hp e) :
    letI := isEquivalence_quasicoherentRestriction_of_descentInputs.{u, v, w, m}
      B S hS X p hp e hres hqcoh hcounit
    Nonempty ((quasicoherentRestriction.{u, v, w, max (u + 1) w m} B S hS X p hp e hres).inv ⋙
        FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, max (u + 1) w m} B S hS X).ι ⋙
        projectionModulePullback.{u, v, w, max (u + 1) w m} B S hS X p hp e) := by
  obtain ⟨Pq, ⟨hPq⟩⟩ := hqcoh
  let := isIso_unit_projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e
  obtain ⟨i⟩ := nonempty_inv_iso_quasicoherentInverse.{u, v, w, max (u + 1) w m}
    B S hS X p hp e hres
    (projectionModulePullbackAdjunction.{u, v, w, max (u + 1) w m} B S hS X p hp e) Pq hPq
    (fun _ => NatIso.isIso_app_of_isIso _ _) hcounit
  exact ⟨Functor.isoWhiskerRight i (FibredSite.toSiteModules B S hS p hp .etale) ≪≫ hPq⟩

end AlgebraicGeometry.Space

end
