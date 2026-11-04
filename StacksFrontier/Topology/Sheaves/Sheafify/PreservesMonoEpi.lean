module

public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Sheafification preserves injective and surjective maps of presheaves of sets (Stacks 0H7I)

Let `X` be a topological space.  A morphism `φ : F ⟶ G` of presheaves of sets on `X` is
*injective* (resp. *surjective*) when every component `φ.app U : F(U) → G(U)` is injective
(resp. surjective); for presheaves there is no topology to localise against, so these are
the plain componentwise conditions and no definition is needed to record them.

For *sheaves* of sets the two notions are no longer symmetric, and it is Mathlib's site-level
vocabulary that names them: a morphism of sheaves is injective when it is injective on
sections, which for a sheaf is the same as `CategoryTheory.Sheaf.IsLocallyInjective` (two
sections with equal images agree locally, hence agree), and surjective when every section of
the target is locally in the image, which is
`CategoryTheory.Sheaf.IsLocallySurjective`.  For sheaves of sets on a space the latter is in
turn equivalent to surjectivity of all the maps on stalks.  The two are also exactly the
monomorphisms and epimorphisms of the category of sheaves of sets.

## Main results

* `TopCat.Presheaf.isLocallyInjective_presheafToSheaf_map_of_injective`: the sheafification of a
  componentwise injective morphism of presheaves of sets is locally injective.
* `TopCat.Presheaf.isLocallySurjective_presheafToSheaf_map_of_surjective`: the sheafification of
  a componentwise surjective morphism of presheaves of sets is locally surjective.
* `TopCat.Presheaf.mono_presheafToSheaf_map_of_injective`,
  `TopCat.Presheaf.epi_presheafToSheaf_map_of_surjective`: the sheafified morphism is a
  monomorphism, resp. an epimorphism, of sheaves of sets.

## Implementation notes

Sheafification is the abstract functor `CategoryTheory.presheafToSheaf` for
`TopologicalSpace.Opens.grothendieckTopology X`. Everything is stated at an arbitrary universe `u`:
the site `(Opens X)ᵒᵖ` for `X : TopCat.{u}` is `u`-small with `u`-small hom types, so `Type u` is
the right value category.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {F G : X.Presheaf (Type u)} (φ : F ⟶ G)

/-- The sheafification of an injective morphism of presheaves of sets is injective: if every
`φ.app U` is injective, then the sheafified morphism is locally injective, which for a morphism of
sheaves is injectivity (see `TopCat.Presheaf.injective_app_presheafToSheaf_map_of_injective`). -/
@[stacks 0H7I]
theorem isLocallyInjective_presheafToSheaf_map_of_injective
    (hφ : ∀ U, Function.Injective (φ.app U)) :
    Sheaf.IsLocallyInjective
      ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ) :=
  (CategoryTheory.Presheaf.isLocallyInjective_presheafToSheaf_map_iff
      (Opens.grothendieckTopology X) φ).2
    (CategoryTheory.Presheaf.isLocallyInjective_of_injective _ φ hφ)

/-- The sheafification of a surjective morphism of presheaves of sets is surjective: if every
`φ.app U` is surjective, then every section of the sheafification of `G` is locally in the image of
the sheafification of `φ`. -/
@[stacks 0H7I]
theorem isLocallySurjective_presheafToSheaf_map_of_surjective
    (hφ : ∀ U, Function.Surjective (φ.app U)) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ) :=
  (CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      (Opens.grothendieckTopology X) φ).2
    (CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ φ hφ)

/-- The sheafification of a componentwise injective morphism of presheaves of sets is injective
on sections over every open. -/
theorem injective_app_presheafToSheaf_map_of_injective
    (hφ : ∀ U, Function.Injective (φ.app U)) (U : (Opens X)ᵒᵖ) :
    Function.Injective
      (((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ).hom.app U) :=
  (Sheaf.isLocallyInjective_iff_injective _).1
    (isLocallyInjective_presheafToSheaf_map_of_injective φ hφ) U

/-- The sheafification of a componentwise surjective morphism of presheaves of sets induces a
surjection on the stalk at every point. -/
theorem surjective_stalkFunctor_map_presheafToSheaf_map_of_surjective
    (hφ : ∀ U, Function.Surjective (φ.app U)) (x : X) :
    Function.Surjective ((stalkFunctor (Type u) x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ).hom) :=
  (locally_surjective_iff_surjective_on_stalks _).1
    (isLocallySurjective_presheafToSheaf_map_of_surjective φ hφ) x

/-- Sheafification carries an injective morphism of presheaves of sets to a monomorphism of
sheaves of sets. -/
theorem mono_presheafToSheaf_map_of_injective (hφ : ∀ U, Function.Injective (φ.app U)) :
    Mono ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ) :=
  have := isLocallyInjective_presheafToSheaf_map_of_injective φ hφ
  Sheaf.mono_of_isLocallyInjective _

/-- Sheafification carries a surjective morphism of presheaves of sets to an epimorphism of
sheaves of sets. -/
theorem epi_presheafToSheaf_map_of_surjective (hφ : ∀ U, Function.Surjective (φ.app U)) :
    Epi ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map φ) :=
  have := isLocallySurjective_presheafToSheaf_map_of_surjective φ hφ
  inferInstance

end TopCat.Presheaf
