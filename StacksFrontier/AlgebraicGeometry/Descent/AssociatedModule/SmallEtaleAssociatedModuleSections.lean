module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity

/-!
# The associated module on the small étale site is the sheafified pullback-sections presheaf

Let `S` be a scheme contained in a big étale site and let `𝓕` be a quasi-coherent
`𝒪_S`-module. **Stacks 070S** says that `𝓕^a` is the `τ`-sheafification of the pullback-sections
presheaf `(f : T → S) ↦ Γ(T, f⁺𝓕)` of **Stacks 03DS**. This file records that statement on the
small étale site of `S`, with no hypothesis.

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` is the same statement on each of
the five big sites. The small étale site is not one of those — it is not a localization of the
big fppf category over `S` — so the statement has to be made again, and its two inputs are now
available there:

* `AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso`, which presents `𝓕 ↦ 𝓕^a` as
  the sheafification of the pullback of *presheaves* of modules along the structure map of the
  morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`, and
* `AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`, which is **Stacks 070S (2)**
  itself and is proved with no hypothesis in
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity`.

## Main results

* `AlgebraicGeometry.SmallEtale.associatedModuleIsoSections`: **`𝓕^a` is the étale
  sheafification of the pullback-sections presheaf of `𝓕`**, on the small étale site of `S`.

## Implementation notes

The statement is about the *sheafification* of the pullback-sections presheaf and not about that
presheaf itself, exactly as the big-site statement is, even though
`AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules` says the presheaf is already a
sheaf here. Stripping the sheafification would mean composing with the inverse of the
sheafification unit, whose target carries a `CategoryTheory.PresheafOfModules.restrictScalars`
along an identity that is not the identity functor; that bookkeeping belongs with whoever needs
the sections, not here.

No natural-transformation form is given. `AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules`
takes quasi-coherence as an instance argument, so a functor form would first have to be packaged
on the full subcategory of quasi-coherent modules.

That objection applies only to the functor form. The Stacks 076T chain needs naturality in the
module as well as in the arrow of `𝒳` — its cocycle condition compares two arrows lying over two
different schemes, and the vertical map at this stage is
`AlgebraicGeometry.SmallEtale.associatedModule` applied to a morphism of modules — but it needs
it only for one morphism at a time, which is statable pointwise with both quasi-coherence
instances in scope and needs no packaging. That is
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module`.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 070S for the small étale site of `S`.** The associated module `𝓕^a` of a
quasi-coherent `𝒪_S`-module `𝓕` is the étale sheafification of the pullback-sections presheaf
`(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS.

`AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso` presents `𝓕^a` as the
sheafification of the presheaf-level pullback along the structure map, and
`AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso` — Stacks 070S (2), with no
hypothesis — says the comparison of that pullback with the pullback-sections presheaf becomes an
isomorphism after sheafification. -/
@[stacks 070S "part (2), in the shape of part (1): 𝓕^a is the étale sheafification of the \
pullback-sections presheaf of Stacks 03DS"]
public noncomputable def associatedModuleIsoSections (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModule B S hS).obj F ≅
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
        (sectionsPresheafOfModules B S hS F) :=
  (associatedModuleSheafificationIso B S hS).app F ≪≫
    @asIso _ _ _ _ _ (sectionsComparisonSheafifiesToIso B S hS F)

end AlgebraicGeometry.SmallEtale

end
