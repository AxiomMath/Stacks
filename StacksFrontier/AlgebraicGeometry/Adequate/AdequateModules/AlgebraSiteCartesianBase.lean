module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSheafAnyUniverse

/-!
# The algebras of an affine of the site, as a site of affine schemes

`Stacks.Adequate.affineSubsiteTopology` is a topology on the `A`-algebras of a chosen big site
over `Spec A`, and the module extensions `C ↦ C ⊗[A] M` are presheaves of modules on it.  To
apply `Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'` to them, that
category has to be presented the way the criterion expects: a category `C` with pullbacks, a
functor `C ⥤ Scheme` and a presheaf of commutative rings on `C`.

This file fixes those three names once, so that the facts about them proved elsewhere all speak
of the same objects.

## Main definitions

* `Stacks.Adequate.algebraSite` — the category the topology lives on, the opposite of the
  `A`-algebras of the site.
* `Stacks.Adequate.algebraSiteRings` — the tautological presheaf of *commutative* rings on it.
  The module-valued functors of the site are the presheaves of modules over its composite with
  `forget₂ CommRingCat RingCat`, which is `AdequateFunctor.algebraRingDiagramOn` on the nose.
* `Stacks.Adequate.algebraSiteScheme` — the spectrum functor, `C ↦ Spec C` read in `Scheme`.

## Main results

* `Stacks.Adequate.algebraSiteRings_comp_forget₂` — the composite of the presheaf of
  commutative rings with the forgetful functor to rings is the scalar diagram the module-valued
  functors of the site are presheaves of modules over.  True by definitional unfolding.
* `Stacks.Adequate.algebraSiteScheme_obj` — the spectrum functor sends an algebra of the site to
  the spectrum of its underlying ring.  True by definitional unfolding.
* `Stacks.Adequate.isAffine_algebraSiteScheme_obj` — the values of the spectrum functor are
  affine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The category the topology on the `A`-algebras of the site lives on: the opposite of the
category of `A`-algebras whose spectrum belongs to the site. -/
public abbrev algebraSite : Type (u + 1) :=
  (AdequateFunctor.AlgebrasInSite (A : Type u) (schemeSizeBelow B.cutoff))ᵒᵖ

/-- The tautological presheaf of commutative rings on the `A`-algebras of the site: an algebra
goes to its own underlying commutative ring. -/
public abbrev algebraSiteRings : (algebraSite B)ᵒᵖ ⥤ CommRingCat.{u} :=
  (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)).op.op ⋙
    unopUnop (CommAlgCat.{u} A) ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}

/-- The scalar diagram the module-valued functors of the site are presheaves of modules over is
the presheaf of commutative rings of the site, forgotten to rings.  By definitional
unfolding. -/
public theorem algebraSiteRings_comp_forget₂ :
    algebraSiteRings B ⋙ forget₂ CommRingCat RingCat =
      AdequateFunctor.algebraRingDiagramOn
        (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)) := rfl

/-- The spectrum functor on the `A`-algebras of the site, read in `Scheme`: the affine-spectrum
functor of the site at the identity structure morphism, followed by the two forgetful steps. -/
public noncomputable abbrev algebraSiteScheme : algebraSite B ⥤ Scheme.{u} :=
  affineSpecOver B A (𝟙 (Spec A)) ⋙ B.toOver ⋙ Over.forget (Spec A)

/-- The spectrum functor of the site sends an algebra to the spectrum of its underlying ring. -/
public theorem algebraSiteScheme_obj (X : algebraSite B) :
    (algebraSiteScheme B).obj X =
      Spec (CommRingCat.of ((AdequateFunctor.siteAlgebraInclusion (A : Type u)
        (schemeSizeBelow B.cutoff)).obj X.unop)) := rfl

/-- The values of the spectrum functor of the site are affine. -/
public instance isAffine_algebraSiteScheme_obj (X : algebraSite B) :
    IsAffine ((algebraSiteScheme B).obj X) := by
  rw [algebraSiteScheme_obj]
  infer_instance

end Stacks.Adequate

end
