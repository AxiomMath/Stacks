module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion

/-!
# Derived stalks detect isomorphisms in `D(X_étale)`

A morphism `φ : M ⟶ N` of the unbounded derived category of abelian sheaves on the small étale
site of a scheme `X` is an isomorphism as soon as its derived stalk `φ_x : M_x ⟶ N_x` is an
isomorphism at every geometric point `x` of `X`. This is Tag 03PU (stalks at geometric points
detect isomorphisms of abelian étale sheaves) passed to the unbounded derived category.

The argument is the standard one. A morphism of the derived category is an isomorphism exactly
when it induces isomorphisms on all cohomology sheaves (`DerivedCategory.isIso_iff`). The stalk
functor at a geometric point is exact, so it commutes with taking cohomology
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`); hence the stalk of `Hⁿ(φ)` at `x` is
`Hⁿ(φ_x)`, an isomorphism. Tag 03PU for abelian sheaves
(`Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb`) makes `Hⁿ(φ)` an
isomorphism.

## Main results

* `Stacks.EtaleCohomology.isIso_of_forall_isIso_smallEtaleDerivedStalkAb` — Tag 03PU on the
  unbounded derived category: derived stalks at geometric points detect isomorphisms.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Derived stalks detect isomorphisms in `D(X_étale)`.** A morphism `φ : M ⟶ N` of the
unbounded derived category of abelian sheaves on the small étale site of a scheme `X` whose
derived stalk `φ_x` is an isomorphism at every geometric point `x` of `X` is an isomorphism.

Each cohomology sheaf map `Hⁿ(φ)` has stalk `Hⁿ(φ_x)` at `x`, the stalk functor being exact, so
it is an isomorphism by Tag 03PU for abelian sheaves; and a morphism of the derived category
inducing isomorphisms on all cohomology sheaves is an isomorphism. -/
theorem isIso_of_forall_isIso_smallEtaleDerivedStalkAb {X : Scheme.{u}}
    {M N : smallEtaleDerivedCategory X} (φ : M ⟶ N)
    (h : ∀ x : GeometricPoint X, IsIso ((smallEtaleDerivedStalkAb x.hom).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rw [isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro x
  exact ((smallEtaleStalkAb x.hom).isIso_homologyFunctor_map_mapDerivedCategory_map_iff φ n).1
    inferInstance

end Stacks.EtaleCohomology

end
