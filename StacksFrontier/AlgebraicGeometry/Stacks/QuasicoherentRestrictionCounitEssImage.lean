module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionDescentInputs

/-!
# The counit of `π_X^* ⊣ i_X^*`

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`, and let `π_X^* ⊣ i_X^*` be the adjunction
`AlgebraicGeometry.Space.projectionModulePullbackAdjunction`, whose right adjoint is restriction
to the small étale site of `X` (equation 075K).  If the unit is an isomorphism (`hunit`), then:

* the counit, restricted along `u_X : X_étale ⥤ 𝒳`, is the inverse of the unit at the
  restriction, for every `𝒪_𝒳`-module, so it is an isomorphism after restriction;
* the counit is invertible at `ℱ` exactly when `ℱ` lies in the essential image of `π_X^*`.

The counit is also invertible at `ℱ` exactly when restriction is bijective on the morphisms out
of `ℱ`, without `hunit`.  Consequently `AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso` —
the counit `π_X^*(ℱ|_{X_étale}) ⟶ ℱ` is an isomorphism at every quasi-coherent `𝒪_𝒳`-module
`ℱ` — is equivalent to `AlgebraicGeometry.Space.ProjectionPullbackEssImage`: every
quasi-coherent `𝒪_𝒳`-module is isomorphic to `π_X^*` of an `𝒪_X`-module.

Everything is stated at the module universe `max u m`, with `u` the universe of the schemes and
`v`, `w` the two universes of `𝒳`, and with `hunit` as a hypothesis; `hunit` holds by
`AlgebraicGeometry.Space.isIso_unit_projectionModulePullbackAdjunction` above `u + 1` and by
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction'` at `u`.

## Main definitions

* `AlgebraicGeometry.Space.ProjectionPullbackEssImage`: every quasi-coherent `𝒪_𝒳`-module lies
  in the essential image of `π_X^*`.

## Main results

* `AlgebraicGeometry.Space.moduleRestriction_map_projectionPullbackCounit_comp_unit`: the counit,
  restricted to the small étale site of `X`, is the inverse of the unit there.
* `AlgebraicGeometry.Space.isIso_moduleRestriction_map_projectionPullbackCounit`: hence it is an
  isomorphism after restriction, at every module and with no hypothesis beyond `hunit`.
* `AlgebraicGeometry.Space.isIso_projectionPullbackCounit_iff_mem_essImage` and
  `AlgebraicGeometry.Space.isIso_projectionPullbackCounit_iff_bijective_moduleRestriction_map`:
  two characterizations of invertibility of the counit at a module.
* `AlgebraicGeometry.Space.projectionPullbackCounitIsIso_iff_essImage`:
  `AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso` is equivalent to
  `AlgebraicGeometry.Space.ProjectionPullbackEssImage`.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
* [Stacks Project, Tag 0GQC](https://stacks.math.columbia.edu/tag/0GQC)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 03DR](https://stacks.math.columbia.edu/tag/03DR)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
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

/-! ### The restricted counit -/

/-- **Restricted to the small étale site of `X`, the counit of `π_X^* ⊣ i_X^*` followed by the
unit is the identity**, at every `𝒪_𝒳`-module, provided the unit is an isomorphism.  Together with
the right triangle of the adjunction, the unit at the restriction is a two-sided inverse of the
restricted counit. -/
theorem moduleRestriction_map_projectionPullbackCounit_comp_unit
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (ℱ : SheafOfModules.{max u m}
      (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)) :
    (moduleRestriction.{u, v, w, max u m} B S hS X p hp e).map
          ((projectionModulePullbackAdjunction.{u, v, w, m}
            B S hS X p hp e).counit.app ℱ) ≫
        (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit.app
          ((moduleRestriction.{u, v, w, max u m} B S hS X p hp e).obj ℱ) =
      𝟙 _ := by
  let := hunit
  let : IsIso ((projectionModulePullbackAdjunction.{u, v, w, m}
    B S hS X p hp e).unit.app
      ((moduleRestriction.{u, v, w, max u m} B S hS X p hp e).obj ℱ)) :=
    NatIso.isIso_app_of_isIso _ _
  rw [← IsIso.inv_eq_of_hom_inv_id
      ((projectionModulePullbackAdjunction.{u, v, w, m}
        B S hS X p hp e).right_triangle_components ℱ),
    IsIso.inv_hom_id]

/-- **The counit of `π_X^* ⊣ i_X^*` becomes an isomorphism after restriction to the small étale
site of `X`**, at every `𝒪_𝒳`-module, provided the unit is an isomorphism; its inverse is the
unit at the restriction. -/
theorem isIso_moduleRestriction_map_projectionPullbackCounit
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (ℱ : SheafOfModules.{max u m}
      (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)) :
    IsIso ((moduleRestriction.{u, v, w, max u m} B S hS X p hp e).map
      ((projectionModulePullbackAdjunction.{u, v, w, m}
        B S hS X p hp e).counit.app ℱ)) :=
  ⟨⟨(projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit.app
      ((moduleRestriction.{u, v, w, max u m} B S hS X p hp e).obj ℱ),
    moduleRestriction_map_projectionPullbackCounit_comp_unit.{u, v, w, m}
      B S hS X p hp e hunit ℱ,
    (projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).right_triangle_components ℱ⟩⟩

/-! ### Two characterizations of invertibility of the counit -/

/-- **The counit of `π_X^* ⊣ i_X^*` is an isomorphism at an `𝒪_𝒳`-module exactly when that module
lies in the essential image of `π_X^*`**, provided the unit is an isomorphism. -/
theorem isIso_projectionPullbackCounit_iff_mem_essImage
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (ℱ : SheafOfModules.{max u m}
      (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)) :
    IsIso ((projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).counit.app ℱ) ↔
      (projectionModulePullback.{u, v, w, m} B S hS X p hp e).essImage ℱ := by
  let := hunit
  let := (Adjunction.fullyFaithfulLOfIsIsoUnit
    (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e)).full
  let := (Adjunction.fullyFaithfulLOfIsIsoUnit
    (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e)).faithful
  exact Adjunction.isIso_counit_app_iff_mem_essImage
    (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e)

/-- **The counit of `π_X^* ⊣ i_X^*` is an isomorphism at an `𝒪_𝒳`-module exactly when restriction
to the small étale site of `X` is bijective on the morphisms out of that module.** -/
theorem isIso_projectionPullbackCounit_iff_bijective_moduleRestriction_map
    (ℱ : SheafOfModules.{max u m}
      (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale)) :
    IsIso ((projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).counit.app ℱ) ↔
      ∀ T : SheafOfModules.{max u m}
          (FibredSite.ringStructureSheafCore B S hS p hp SiteKind.etale),
        Function.Bijective fun f : ℱ ⟶ T =>
          (moduleRestriction.{u, v, w, max u m} B S hS X p hp e).map f := by
  refine ⟨fun h T => Adjunction.bijective_map_of_isIso_counit
    (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e) h, fun h => ?_⟩
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have key : ∀ f : ℱ ⟶ T,
      (projectionModulePullbackAdjunction.{u, v, w, m}
        B S hS X p hp e).counit.app ℱ ≫ f =
        ((projectionModulePullbackAdjunction.{u, v, w, m}
          B S hS X p hp e).homEquiv _ T).symm
          ((moduleRestriction.{u, v, w, max u m} B S hS X p hp e).map f) := by
    intro f
    rw [Adjunction.homEquiv_counit]
    exact ((projectionModulePullbackAdjunction.{u, v, w, m}
      B S hS X p hp e).counit_naturality f).symm
  refine ⟨fun f₁ f₂ hf => (h T).1 (((projectionModulePullbackAdjunction.{u, v, w, m}
    B S hS X p hp e).homEquiv _ T).symm.injective ((key f₁).symm.trans (hf.trans (key f₂)))),
    fun g => ?_⟩
  obtain ⟨f, hf⟩ := (h T).2 ((projectionModulePullbackAdjunction.{u, v, w, m}
    B S hS X p hp e).homEquiv _ T g)
  exact ⟨f, (key f).trans ((congrArg _ hf).trans (Equiv.symm_apply_apply _ _))⟩

/-! ### The essential image of `π_X^*` -/

/-- Every quasi-coherent `𝒪_𝒳`-module is isomorphic to `π_X^*` of an `𝒪_X`-module, that is, lies
in the essential image of `AlgebraicGeometry.Space.projectionModulePullback`. -/
abbrev ProjectionPullbackEssImage : Prop :=
  ∀ M : FibredSite.quasicoherentModules.{u, v, w, max u m} B S hS p hp,
    (projectionModulePullback.{u, v, w, m} B S hS X p hp e).essImage
      ((FibredSite.toSiteModules B S hS p hp SiteKind.etale).obj M)

/-- **`AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso` is equivalent to
`AlgebraicGeometry.Space.ProjectionPullbackEssImage`**: provided the unit of `π_X^* ⊣ i_X^*` is an
isomorphism, the counit `π_X^*(ℱ|_{X_étale}) ⟶ ℱ` is an isomorphism at every quasi-coherent
`𝒪_𝒳`-module if and only if every quasi-coherent `𝒪_𝒳`-module is `π_X^*` of an `𝒪_X`-module. -/
theorem projectionPullbackCounitIsIso_iff_essImage
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit) :
    ProjectionPullbackCounitIsIso.{u, v, w, m} B S hS X p hp e ↔
      ProjectionPullbackEssImage.{u, v, w, m} B S hS X p hp e :=
  forall_congr' fun M => isIso_projectionPullbackCounit_iff_mem_essImage.{u, v, w, m}
    B S hS X p hp e hunit ((FibredSite.toSiteModules B S hS p hp SiteKind.etale).obj M)

/-- `AlgebraicGeometry.Space.ProjectionPullbackEssImage` implies
`AlgebraicGeometry.Space.ProjectionPullbackCounitIsIso`, provided the unit of `π_X^* ⊣ i_X^*` is
an isomorphism. -/
theorem projectionPullbackCounitIsIso_of_essImage
    (hunit : IsIso (projectionModulePullbackAdjunction.{u, v, w, m} B S hS X p hp e).unit)
    (h : ProjectionPullbackEssImage.{u, v, w, m} B S hS X p hp e) :
    ProjectionPullbackCounitIsIso.{u, v, w, m} B S hS X p hp e :=
  (projectionPullbackCounitIsIso_iff_essImage.{u, v, w, m} B S hS X p hp e hunit).mpr h

end AlgebraicGeometry.Space

end
