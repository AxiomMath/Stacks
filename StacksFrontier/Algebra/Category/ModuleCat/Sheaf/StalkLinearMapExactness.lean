module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Exactness of the stalk maps of sheaves of modules

Let `(X, O_X)` be a ringed space. The stalk at a point `x` of a sheaf of `O_X`-modules is a module
over the local ring `O_{X,x}`, and a morphism of sheaves of modules induces an `O_{X,x}`-linear map
of stalks, `Stacks.SheafOfModules.FlatShortExact.stalkLinearMap`. Taking stalks is exact: an exact
short complex of sheaves of modules has exact stalk maps at every point, and an epimorphism of
sheaves of modules has surjective stalk maps at every point.

## Main results

* `Stacks.SheafOfModules.FlatShortExact.exact_stalkLinearMap`: the stalk maps of an exact short
  complex of sheaves of `O_X`-modules are exact as functions, at every point.
* `Stacks.SheafOfModules.FlatShortExact.surjective_stalkLinearMap`: the stalk maps of an
  epimorphism of sheaves of `O_X`-modules are surjective, at every point.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Limits

namespace Stacks.SheafOfModules.FlatShortExact

universe u

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The additive stalk functor `stalkF x` preserves finite colimits. -/
theorem stalkF_preservesFiniteColimits (x : X.carrier) :
    PreservesFiniteColimits (stalkF (X := X) x) :=
  compPFC (SheafOfModules.toSheaf (structureSheafRing X))
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    (toSheafColim X) (forgetStalkColim x)

/-- **Exactness of stalks.** The stalk maps at `x` of an exact short complex of sheaves of
`O_X`-modules are exact as a pair of functions; they are `O_{X,x}`-linear for the canonical
`stalkModule` structure on each stalk. -/
theorem exact_stalkLinearMap (S : ShortComplex (SheafOfModules (structureSheafRing X)))
    (hS : S.Exact) (x : X.carrier) :
    Function.Exact (stalkLinearMap S.f x) (stalkLinearMap S.g x) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
      (structureSheafRing X) S).mp hS x)

/-- **Surjectivity of stalks.** The stalk maps at `x` of an epimorphism of sheaves of
`O_X`-modules are surjective. -/
theorem surjective_stalkLinearMap {F G : SheafOfModules (structureSheafRing X)} (φ : F ⟶ G)
    (hφ : Epi φ) (x : X.carrier) :
    Function.Surjective (stalkLinearMap φ x) := by
  have := (stalkF_preservesFiniteColimits x).preservesFiniteColimits WalkingSpan
  exact (AddCommGrpCat.epi_iff_surjective _).mp (preserves_epi_of_preservesColimit (stalkF x) φ)

end Stacks.SheafOfModules.FlatShortExact
