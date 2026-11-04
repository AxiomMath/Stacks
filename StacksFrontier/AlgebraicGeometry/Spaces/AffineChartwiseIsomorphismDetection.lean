module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseIsomorphismDetection
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective

/-!
# Affine étale charts detect isomorphisms of modules on an algebraic space

`AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_chartToSpace` detects an
isomorphism of `𝒪_Y`-modules on the small étale site of an algebraic space `Y` from its
restrictions to *every* étale scheme chart.  That is more than a reduction to an affine base
supplies:  a statement about `𝒪_Y`-modules available over the *affine* charts says nothing
about the charts whose underlying scheme is not affine, and an étale scheme over an affine
scheme need not be affine.  This file supplies the test over the affine charts alone.

The geometric input is already available:  the affine charts have enough objects in the small
étale topology, with the index type in the morphism universe of the site, which is
`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`.  What is added here is the sheaf
theory — a morphism of sheaves of modules which is bijective on sections over a family of
objects covering every object is locally bijective, hence invertible.  Bijectivity on sections
over an affine chart is *not* inherited by the arbitrary charts lying over it, and local
bijectivity is what invertibility actually needs.

## Main results

* `Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app`: a morphism of sheaves of
  modules on an arbitrary site which is bijective on sections over a family of objects covering
  every object is invertible.
* `AlgebraicGeometry.Space.isIso_of_forall_bijective_val_app_affine_chart`: a morphism of
  `𝒪_Y`-modules which is bijective on sections over every affine étale chart is invertible.
* `AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_affine_chartToSpace`:
  **affine étale charts detect isomorphisms**, in the form that matches the all-charts
  statement — a morphism of `𝒪_Y`-modules whose restriction along the structure morphism of
  every *affine* étale scheme chart of `Y` is invertible is itself invertible.

## Implementation notes

*The site-level statement goes through sheaves of abelian groups.*  The two halves of local
bijectivity are `CategoryTheory.Presheaf.isLocallyInjective_of_hasEnoughObjects_injective` and
`CategoryTheory.Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective`, which are stated
for presheaves valued in a concrete category;  they are applied to the image of the morphism
under `SheafOfModules.toSheaf`, whose components are the components of the morphism of sheaves
of modules read through `forget₂ (ModuleCat _) AddCommGrpCat`, and `SheafOfModules.toSheaf`
reflects isomorphisms.  Nothing is assumed of the module universe.

*Why `HasEnoughObjects` and not `CoversTop`.*
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts` concludes
`CategoryTheory.GrothendieckTopology.CoversTop`, whose sieve at a chart `W` contains every arrow
whose *source* admits some morphism to an affine chart;  such a source is an arbitrary chart, so
that form cannot feed a hypothesis about affine charts only.  `HasEnoughObjects` quantifies over
the generating family instead, and `hasEnoughObjects_isAffineChart` produces a generating family
of affine charts indexed in the morphism universe, which is what the two local-bijectivity
lemmas ask for.

*No Stacks tag is carried.*  Stacks 0H6Y is the statement for a map of *presheaves* and its
sheafification,
`CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective`;  condition
(4) of Stacks 03M0 is the affine-chart test for quasi-coherence, not for invertibility.  The
statements below are neither, and none of them is any clause of a tag.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.SheafOfModules

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **Bijectivity on a family of objects covering every object makes a morphism of sheaves of
modules invertible.**  If every object of the site has a covering by objects with `P`, and the
morphism `φ` is bijective on sections over every object with `P`, then `φ` is invertible.

Bijectivity on sections over the members of a covering of each object gives local injectivity
and local surjectivity of the underlying morphism of sheaves of abelian groups, by
`CategoryTheory.Presheaf.isLocallyInjective_of_hasEnoughObjects_injective` and
`CategoryTheory.Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective`;  a locally
bijective morphism of sheaves is invertible, and `SheafOfModules.toSheaf` reflects
isomorphisms.

Bijectivity over the objects with `P` is *not* promoted to bijectivity over every object on the
way:  sections over an object not in the family are reached only through the sheaf condition,
which is what `Sheaf.isLocallyBijective_iff_isIso` supplies. -/
theorem isIso_of_hasEnoughObjects_bijective_val_app
    [(CategoryTheory.forget AddCommGrpCat.{m}).ReflectsIsomorphisms]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{m})]
    {M N : _root_.SheafOfModules.{m} R} (φ : M ⟶ N) {P : ObjectProperty C}
    (hP : J.HasEnoughObjects P)
    (hbij : ∀ ⦃U : C⦄, P U → Function.Bijective (φ.val.app (op U)).hom) :
    IsIso φ := by
  set ψ := (_root_.SheafOfModules.toSheaf R).map φ with hψ
  have happ : ∀ ⦃U : C⦄, P U → Function.Bijective
      (ConcreteCategory.hom (ψ.hom.app (op U))) := by
    intro U hU
    exact hbij hU
  have : Presheaf.IsLocallyInjective J ψ.hom :=
    Presheaf.isLocallyInjective_of_hasEnoughObjects_injective J ψ.hom hP
      fun _ h => (happ h).injective
  have : Presheaf.IsLocallySurjective J ψ.hom :=
    Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective J ψ.hom hP
      fun _ h => (happ h).surjective
  have hs : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨inferInstance, inferInstance⟩
  exact @isIso_of_reflects_iso _ _ _ _ _ _ φ (_root_.SheafOfModules.toSheaf R) hs inferInstance

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections over the affine étale charts detect isomorphisms of `𝒪_Y`-modules.**  A morphism
of `𝒪_Y`-modules which is bijective on sections over every étale scheme chart with affine
underlying scheme is invertible.

The affine charts have enough objects in the small étale topology
(`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`), so this is
`Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app` at that family. -/
theorem isIso_of_forall_bijective_val_app_affine_chart (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, m} B S hS Y.obj Y.property} (φ : M ⟶ N)
    (hφ : ∀ V : SmallEtale B S hS Y.obj, IsAffineChart B S hS Y.obj V →
      Function.Bijective (φ.val.app (op V)).hom) :
    IsIso φ :=
  Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app φ
    (hasEnoughObjects_isAffineChart B S hS Y.obj) fun _ h => hφ _ h

/-- **Affine étale charts detect isomorphisms of `𝒪_Y`-modules.**  A morphism of `𝒪_Y`-modules
whose restriction along the structure morphism of every étale scheme chart of `Y` with affine
underlying scheme is invertible is itself invertible.

This is the affine-chart counterpart of
`AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_chartToSpace`, and it is the
form in which invertibility of a comparison map of `𝒪_Y`-modules is reduced to a statement over
an affine base.  The restriction to `V` has, over the identity chart of the algebraic space that
`V` represents, the sections over `V` on the nose
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_map_val_app_idEtaleChart`), so the
hypothesis gives bijectivity on sections over each affine chart. -/
theorem isIso_of_forall_isIso_etaleModulePullback_affine_chartToSpace
    (Y : AlgebraicSpaces B S hS) {M N : Modules.{u, u} B S hS Y.obj Y.property} (φ : M ⟶ N)
    (hφ : ∀ V : SmallEtale B S hS Y.obj, IsAffineChart B S hS Y.obj V →
      IsIso ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).map φ)) :
    IsIso φ := by
  refine isIso_of_forall_bijective_val_app_affine_chart B S hS Y φ fun V hV => ?_
  have hiso : IsIso (φ.val.app (op V)) := by
    rw [← etaleModulePullback_chartToSpace_map_val_app_idEtaleChart B S hS φ V]
    have := hφ V hV
    exact Stacks.SheafOfModules.isIso_val_app_of_isIso_freeModuleUniverse _ _
  exact ConcreteCategory.bijective_of_isIso (φ.val.app (op V))

end AlgebraicGeometry.Space

end
