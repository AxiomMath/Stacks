module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity

/-!
# The associated module on the small étale site, read as pullback sections

Let `S` be a scheme contained in a chosen big étale site `B` and let `𝓕` be a quasi-coherent
`𝒪_S`-module.  Stacks 070S (2) says that the small-étale module `𝓕^a` associated to `𝓕` by the
functor of Stacks 03DU (4) is the pullback-sections sheaf `(g : T → S) ↦ Γ(T, g⁺𝓕)` of
Stacks 03DS, restricted to the small étale site.

That identification is already available in this development, but only at a big *fppf* site:
`AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedModuleIsoSheaf` is stated for
`B : BigFppfSite` and its associated big étale site `B.toBigEtaleSite`.  Both of the big étale
sites that occur in practice — `B.toBigEtaleSite` and
`AlgebraicGeometry.associatedBigEtaleSite B` — are built from a big fppf site, but they are
distinct declarations, so a consumer holding the second one cannot use that identification.
Every ingredient of it is already stated for an arbitrary `B : BigEtaleSite`, so this module
simply records the identification at that generality.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedSectionsSheaf` is the pullback-sections sheaf
  `(g : T → S) ↦ Γ(T, g⁺𝓕)` on the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf` identifies the associated
  module `𝓕^a` with it.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), part (2).
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS), the pullback-sections
  presheaf `(g : T → S) ↦ Γ(T, g⁺𝓕)`.
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT), its sheaf condition.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  associated-module functor.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

/-- **`𝓕^a` on the small étale site of `S`, as a sheaf of sections.**  The pullback-sections
presheaf of modules `(g : T → S) ↦ Γ(T, g⁺𝓕)` of Stacks 03DS, restricted to the small étale
site of `S`, where Stacks 03DT makes it a sheaf. -/
public noncomputable def associatedSectionsSheaf :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  ⟨sectionsPresheafOfModules B S hS F, isSheaf_sectionsPresheafOfModules B S hS F⟩

/-- The sections of `associatedSectionsSheaf` are the pullback sections of Stacks 03DS. -/
@[simp]
public theorem associatedSectionsSheaf_val :
    (associatedSectionsSheaf B S hS F).val = sectionsPresheafOfModules B S hS F :=
  rfl

/-- **Stacks 070S (2), for an arbitrary big étale site.**  The associated module `𝓕^a` of a
quasi-coherent module on the scheme `S` is the pullback-sections sheaf
`(g : T → S) ↦ Γ(T, g⁺𝓕)` of Stacks 03DS on the small étale site: the associated module is the
sheafification of the presheaf-level pullback, the comparison of Stacks 070S (2) sheafifies to
an isomorphism, and the sections presheaf is already a sheaf. -/
public noncomputable def associatedModuleIsoSectionsSheaf :
    (associatedModule B S hS).obj F ≅ associatedSectionsSheaf B S hS F :=
  (associatedModuleSheafificationIso B S hS).app F ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_sectionsComparison B S hS F) ≪≫
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheaf B S hS).obj)).counit)).app (associatedSectionsSheaf B S hS F)

end AlgebraicGeometry.SmallEtale

end
