module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion

/-!
# Isomorphisms of the unbounded derived category are detected on geometric stalks

Let `Z` be a scheme. A morphism `φ : M ⟶ N` of the unbounded derived category `D(Z_étale)` of
abelian sheaves on the small étale site of `Z` is an isomorphism as soon as its stalk at every
geometric point of `Z` is one.

A morphism of a derived category is an isomorphism exactly when all its cohomology maps are. The
stalk at a geometric point is an exact functor, so it commutes with taking cohomology, and the
stalks at geometric points detect isomorphisms of abelian étale sheaves
(`Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb`). This is the form of
[Stacks, Tag 03PU] that the argument of [Stacks, Tag 0GJU] uses.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_smallEtaleDerivedStalkAb` — a morphism of `D(Z_étale)`
  whose derived stalks at all geometric points are isomorphisms is an isomorphism.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Isomorphy in `D(Z_étale)` is detected on geometric stalks.** A morphism of the unbounded
derived category of abelian sheaves on the small étale site of a scheme `Z` whose stalk at every
geometric point of `Z` is an isomorphism is itself an isomorphism.

Each cohomology map of the morphism is a morphism of abelian sheaves whose stalks are the
cohomology maps of the derived stalks, the stalk functor being exact; these are isomorphisms, so
the cohomology maps are, and a morphism of a derived category all of whose cohomology maps are
isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_smallEtaleDerivedStalkAb {Z : Scheme.{u}}
    {M N : smallEtaleDerivedCategory Z} (φ : M ⟶ N)
    (h : ∀ z : GeometricPoint Z, IsIso ((smallEtaleDerivedStalkAb z.hom).map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rw [isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro z
  have := h z
  exact ((smallEtaleStalkAb z.hom).isIso_mapDerivedCategory_map_iff φ).1 this n

end Stacks.EtaleCohomology

end
