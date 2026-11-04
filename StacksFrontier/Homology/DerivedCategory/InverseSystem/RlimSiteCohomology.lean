module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Inverse limits as cohomology of the chaotic site

Endow a small category `C` with the chaotic topology, the bottom Grothendieck topology, for which
every presheaf is a sheaf. Under the canonical equivalence between abelian sheaves on `(C, ⊥)`
and diagrams of abelian groups on `Cᵒᵖ`, the global-sections functor of the site is the limit
functor, and for every `p` the `p`-th cohomology functor of the site is the `p`-th right derived
functor of the limit. Applied to the ordered category `ℕ` this identifies the derived inverse
limits of an inverse system of abelian groups with the cohomology groups of the chaotic site.

## Main definitions

There are no new definitions. The equivalence is Mathlib's `sheafBotEquivalence`, and the site
functors are `Stacks.Cohomology.CompositeRightDerived.siteSections` and
`Stacks.Cohomology.CompositeRightDerived.siteCohomology`.

## Main results

* `Rlim.ChaoticSite.diagramLimitAndRightDerivedIsoSiteCohomology`: global sections and all their
  right derived functors on the chaotic site are the limit functor and its right derived
  functors, naturally in the diagram.

## Implementation notes

The result is stated for an arbitrary small category, of which the inverse systems of the source
are the case of the ordered category `ℕ`. Both the sheaf category and the diagram category need
enough injectives for their right derived functors to exist; for sheaves this is the
Grothendieck-abelian structure, and for diagrams it is transported along the equivalence. Since
the equivalence is the canonical forgetful one, the comparison for global sections is the
identity, and the comparison in degree `p` is the natural isomorphism relating the right derived
functor of a composite with an exact equivalence on the left.

## References

* [Stacks Project, Tag 091A](https://stacks.math.columbia.edu/tag/091A)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace Rlim.ChaoticSite

universe u

/-- The category of abelian sheaves on the chaotic site of a small category has enough
injectives. -/
noncomputable local instance {C : Type u} [SmallCategory C] :
    EnoughInjectives.{u} (Sheaf (⊥ : GrothendieckTopology C) Ab.{u}) :=
  (Sheaf.instIsGrothendieckAbelian (⊥ : GrothendieckTopology C) Ab.{u}).enoughInjectives

/-- The category of diagrams of abelian groups on the opposite of a small category has enough
injectives. -/
noncomputable local instance {C : Type u} [SmallCategory C] :
    EnoughInjectives.{u} (Cᵒᵖ ⥤ Ab.{u}) :=
  EnoughInjectives.of_equivalence (sheafBotEquivalence (C := C) Ab.{u}).inverse

/-- The equivalence between abelian sheaves on the chaotic site and diagrams of abelian groups
is additive. -/
local instance {C : Type u} [SmallCategory C] :
    (sheafBotEquivalence (C := C) Ab.{u}).functor.Additive where
  map_add := by intros; rfl

/-- On the chaotic site on a small category, abelian sheaves are diagrams of abelian groups on
its opposite category. Under the canonical equivalence, global sections are naturally isomorphic
to the limit functor, and for every `p` the site-cohomology functor is naturally isomorphic to
`R^p lim`. -/
@[stacks 091A]
public noncomputable def diagramLimitAndRightDerivedIsoSiteCohomology
    {C : Type u} [SmallCategory C] :
    let J : GrothendieckTopology C := ⊥
    let e := sheafBotEquivalence (C := C) Ab.{u}
    (e.functor ⋙ (lim : (Cᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u}) ≅
      Stacks.Cohomology.CompositeRightDerived.siteSections J) ×
      (∀ p : ℕ,
        e.functor ⋙ (lim : (Cᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u}).rightDerived p ≅
          Stacks.Cohomology.CompositeRightDerived.siteCohomology J p) := by
  dsimp [Stacks.Cohomology.CompositeRightDerived.siteSections,
    Stacks.Cohomology.CompositeRightDerived.siteCohomology]
  exact ⟨Iso.refl _, fun p ↦
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (sheafBotEquivalence (C := C) Ab.{u}).functor
      (lim : (Cᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u}) p).symm⟩

end Rlim.ChaoticSite

end
