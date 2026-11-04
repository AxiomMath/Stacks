module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Inverse image of sheaves of modules on small étale sites

Let `f : X ⟶ Y` be an arbitrary morphism of schemes and let `Λ` be a ring.  Direct image
`f_*` of sheaves of `Λ`-modules for the small étale topologies is precomposition with base
change, so it has a left adjoint `f^{-1}`, the sheafified left Kan extension along the opposite
of base change.  This file constructs that left adjoint, proves it exact, and draws the
consequence that `f_*` preserves injective objects.

The last statement is what makes `Rf_*` compose: the comparison `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` of
[Stacks, Tag 05T2] is invertible exactly when `f_*` carries injectives to injectives.  It held
in this development only for sheaves of sets and of abelian groups, and for module coefficients
only on a big étale site, so every consumer of the composition comparison for module
coefficients carried the preservation as a named condition.  With the instance below they no
longer need to.

Exactness is proved as in
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`, which is the same
statement for the small étale site cut out of a chosen big étale site: base change preserves
finite limits, hence is representably flat, hence the comma categories computing the left Kan
extension pointwise are filtered, and filtered colimits of modules are left exact.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImage` — the inverse image `f^{-1}` of sheaves of
  `Λ`-modules along a morphism of schemes, for the small étale topologies.
* `Stacks.EtaleCohomology.etaleModuleInverseImageAdj` — the adjunction `f^{-1} ⊣ f_*`.

## Main results

* `Stacks.EtaleCohomology.preservesFiniteLimits_lan_op_smallEtaleBaseChange_module` — the left
  Kan extension along the opposite of base change is left exact at the coefficient universe
  that sheaves of modules on the small étale site use.
* `Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits` and
  `Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits` — `f^{-1}` is exact.
* `Stacks.EtaleCohomology.etaleModuleDirectImage_preservesInjectiveObjects` — **`f_*`
  preserves injective sheaves of modules**, for an arbitrary morphism of schemes.

## Implementation notes

`Stacks.Topology.lan_preservesFiniteLimits_of_flat` is used rather than Mathlib's
`CategoryTheory.Functor.lan_preservesFiniteLimits_of_flat`: the latter lives in a section
fixing `[SmallCategory C] [SmallCategory D]` and a value category whose carrier types live in
the universe of the morphisms of the site, which the small étale site of a scheme in
`Scheme.{u}` — objects in `Type (u + 1)`, morphisms in `Type u` — does not satisfy.  Likewise
`CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits` is used rather than the
instance of the same name in `CategoryTheory.Functor.SmallCategories`.

The filteredness of each comma category `CostructuredArrow (smallEtaleBaseChange f).op Z` is
supplied by name through `CategoryTheory.structuredArrowOpEquivalence` and
`Stacks.EtaleCohomology.smallEtaleBaseChange_representablyFlat`, because it is what makes the
forgetful functor preserve colimits of that shape.  The two forgetful functors are taken apart:
`ModuleCat.forget₂PreservesColimitsOfSize` gives the passage to abelian groups all colimits of
the relevant size, and only the passage from abelian groups to types needs the colimit to be
filtered.  Both instances have their universes written out, since a competing instance for the
same functor names the coefficient universe differently and unifying the two leaves the universe
solver with an unsolved `max`.

The inverse image is the abstract left adjoint `CategoryTheory.Functor.sheafPullback`, not the
Kan-extension construction of
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`; the construction supplies the
right-adjointness instance that makes the abstract one available, and the two are canonically
isomorphic.  Stating the definition abstractly is what makes
`Stacks.EtaleCohomology.etaleModuleInverseImageAdj` an adjunction with
`Stacks.EtaleCohomology.etaleModuleDirectImage` on the nose.

These declarations carry no tag: they are the infrastructure of the composition comparison, and
the covering sets of the tags they serve are elsewhere.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Exactness of the left Kan extension -/

/-- **The left Kan extension along the opposite of small étale base change is left exact**, for
coefficients in `ModuleCat.{max (u + 1) r} Λ`.  Base change is representably flat, so the
costructured-arrow categories computing the extension pointwise are filtered; the forgetful
functor from `Λ`-modules preserves filtered colimits of that size, and a filtered colimit of
modules is therefore left exact. -/
theorem preservesFiniteLimits_lan_op_smallEtaleBaseChange_module :
    PreservesFiniteLimits ((smallEtaleBaseChange f).op.lan :
      (Y.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) ⥤ _) := by
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun Z => ?_
  have : IsFiltered (CostructuredArrow (smallEtaleBaseChange f).op Z) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallEtaleBaseChange f) (Opposite.unop Z))
  have : PreservesColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r, u, u + 1} Λ
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u + 1} _
  exact inferInstanceAs (PreservesColimitsOfShape
    (CostructuredArrow (smallEtaleBaseChange f).op Z)
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ⋙
      forget AddCommGrpCat.{max (u + 1) r}))

attribute [local instance] preservesFiniteLimits_lan_op_smallEtaleBaseChange_module

/-! ### The inverse image functor -/

/-- Inverse image `f^{-1}` of sheaves of modules along a morphism of schemes, for the small
étale topologies: the left adjoint of direct image, realised by the sheafified left Kan
extension along the opposite of base change. -/
abbrev etaleModuleInverseImage :
    EtaleModules.{u, r} Λ Y ⥤ EtaleModules.{u, r} Λ X :=
  (smallEtaleBaseChange f).sheafPullback
    (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- **`f^{-1} ⊣ f_*` for sheaves of modules on small étale sites.**  This is the adjunction that
makes direct image a right derived functor's underlying functor and inverse image the thing whose
exactness controls it. -/
def etaleModuleInverseImageAdj :
    etaleModuleInverseImage.{u, r} Λ f ⊣ etaleModuleDirectImage.{u, r} Λ f :=
  (smallEtaleBaseChange f).sheafAdjunctionContinuous
    (ModuleCat.{max (u + 1) r} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- **Inverse image of sheaves of modules on small étale sites is left exact.**  It is
sheafification of the left Kan extension of the underlying presheaf, and both steps are left
exact. -/
theorem etaleModuleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleInverseImage.{u, r} Λ f) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image of sheaves of modules is right exact, being a left adjoint; with left
exactness this makes it exact. -/
theorem etaleModuleInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleInverseImage.{u, r} Λ f) :=
  let : (etaleModuleInverseImage.{u, r} Λ f).IsLeftAdjoint :=
    (etaleModuleInverseImageAdj.{u, r} Λ f).isLeftAdjoint
  inferInstance

/-- Inverse image of sheaves of modules is additive, being a left adjoint of an additive
functor. -/
instance etaleModuleInverseImage_additive :
    (etaleModuleInverseImage.{u, r} Λ f).Additive :=
  (etaleModuleInverseImageAdj.{u, r} Λ f).left_adjoint_additive

/-! ### Direct image preserves injectives -/

/-- **Direct image of sheaves of modules on small étale sites preserves injective objects**, for
an arbitrary morphism of schemes.  Its left adjoint `f^{-1}` is left exact, hence preserves
monomorphisms, and a right adjoint of a monomorphism-preserving functor carries injectives to
injectives.

This is the condition that the composition comparison `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` of
[Stacks, Tag 05T2] needs in order to be invertible, so it is what lets the derived composition
isomorphism for module coefficients be stated with no hypothesis on `f`. -/
instance etaleModuleDirectImage_preservesInjectiveObjects :
    (etaleModuleDirectImage.{u, r} Λ f).PreservesInjectiveObjects :=
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ f
  have : (etaleModuleInverseImage.{u, r} Λ f).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (etaleModuleInverseImageAdj.{u, r} Λ f)

end Stacks.EtaleCohomology

end
