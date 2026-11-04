module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveRepresentative
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.Homology.Ext.DerivedCoyonedaLinear
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveRepresentativeSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinearSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear

/-!
# Hypercohomology is `Ext` out of the structure sheaf, `k`-linearly

Let `k` be a field, `f : X ⟶ Spec k` a scheme over `k` and `K` an object of `D(𝒪_X)`. Derived
global sections are corepresented by the structure sheaf: for every integer `i`,

`H^i(X, K) = Ext^i_{D(𝒪_X)}(𝒪_X[0], K)`,

and this file proves that identification **as an isomorphism of `k`-vector spaces**, which is what
makes it compare dimensions over `k`.

The reason the statement is wanted is clause (4) of [Stacks, Tag 0BS2]. That clause,
`Stacks.Duality.extDualityLinearEquiv`, computes `Ext^i_X(K, ω_X^•)`; at `K = 𝒪_X[0]` its left
side is the hypercohomology `H^i(X, ω_X^•)` of the dualizing complex, which is what
[Stacks, Tag 0BS5] sums, and the identification below is what turns the one into the other.

## Main results

* `AlgebraicGeometry.unitHomLinearEquivGlobalSections_naturality`:
  `Hom_{𝒪_X}(𝒪_X, ℳ) ≃ₗ[k] Γ(X, ℳ)` is natural in `ℳ`.
* `Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit`:
  **`H^i(X, K) ≃ₗ[k] Ext^i_{D(𝒪_X)}(𝒪_X[0], K)`.**
* `Stacks.Duality.finrank_derivedCohomologyOverField_eq_finrank_extUnit`: the equality of
  dimensions it gives.

## How it is proved

A K-injective complex `I` representing `K` is chosen
(`CategoryTheory.exists_isKInjective_representative_atModel`, with the K-injective resolutions of
`AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective`). On such a complex a right
derived functor is computed by the functor itself (`CategoryTheory.rightDerivedObjIsoAtModel`), so
`RΓ(X, K)` is the class of the complex of `k`-linear global sections of `I`, and the degree-`i`
cohomology of that class is the degree-`i` cohomology of the complex
(`DerivedCategory.homologyFunctorFactors`). That cohomology is the `Ext`-group by
`StacksDraft.DerivedCoyoneda.homologyLinearEquivDerivedHom`, whose hypothesis
`Hom_{𝒪_X}(𝒪_X, -) ≃ₗ[k] Γ(X, -)` is
`AlgebraicGeometry.unitHomLinearEquivGlobalSections` together with its naturality.

Both the choice of `I` and the isomorphism `Q(I) ≅ K` are choices, so only the existence of the
`k`-linear equivalence is asserted; the equality of dimensions, which is what the consumers want,
does not remember them.

## Implementation notes

*The model of the derived category.* Everything is at the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`, which is
where `Stacks.Duality.derivedCohomologyOverField` and the duality of [Stacks, Tag 0BS2] live.
`CategoryTheory.exists_isKInjective_representative_atModel` and
`CategoryTheory.rightDerivedObjIsoAtModel` carry free universe binders for exactly this reason.

*The `k`-linear structure.* `CategoryTheory.Linear k X.Modules` cannot be an instance — the base
ring is not determined by the scheme — so the statements below take it and
`CategoryTheory.Functor.Linear k (AlgebraicGeometry.globalSectionsOver f)` as instance arguments,
as `StacksFrontier/AlgebraicGeometry/Duality/ProperOverFieldDualityLinear.lean` does. A consumer
discharges both with `AlgebraicGeometry.Scheme.Modules.linearOverBase` and
`AlgebraicGeometry.globalSectionsOver_linear_linearOverBase`.

*Naturality is `rfl`.* `AlgebraicGeometry.unitHomLinearEquivGlobalSections` is
`CategoryTheory.SheafOfModules.unitHomEquiv` followed by evaluation at the terminal open, and
`CategoryTheory.SheafOfModules.unitHomEquiv_comp_apply` is itself an equality by definition.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

/-- **`Hom_{𝒪_X}(𝒪_X, ℳ) ≃ₗ[k] Γ(X, ℳ)` is natural in `ℳ`**: it turns postcomposition with
`g : ℳ ⟶ 𝒩` into `Γ(X, g)`. Both sides evaluate a morphism out of `𝒪_X` on the section `1` over
the whole space, so the two agree by definition. -/
public theorem unitHomLinearEquivGlobalSections_naturality {M N : X.Modules}
    (a : Stacks.Ample.unitModule X ⟶ M) (g : M ⟶ N) :
    unitHomLinearEquivGlobalSections f N (a ≫ g) =
      (globalSectionsOver f).map g (unitHomLinearEquivGlobalSections f M a) := rfl

end AlgebraicGeometry

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

/-- **`H^i(X, K) ≃ₗ[k] Ext^i_{D(𝒪_X)}(𝒪_X[0], K)`**: derived global sections of a scheme over a
field are corepresented by the structure sheaf, as an isomorphism of `k`-vector spaces.

The equivalence depends on a choice of K-injective representative of `K`, so only its existence
is asserted; `Stacks.Duality.finrank_derivedCohomologyOverField_eq_finrank_extUnit` is the
consequence that does not. -/
public theorem nonempty_derivedCohomologyOverFieldLinearEquivExtUnit
    (K : DerivedCategory X.Modules) (i : ℤ) :
    Nonempty (derivedCohomologyOverField f K i ≃ₗ[k]
      DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Stacks.Ample.unitModule X)) K i) := by
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_isKInjective_representative_atModel
    (Scheme.Modules.exists_quasiIso_isKInjective X) K
  have := hI
  let eG := rightDerivedObjIsoAtModel (Scheme.Modules.exists_quasiIso_isKInjective X)
    (globalSectionsOver f) inferInstance (derivedGlobalSectionsOver f)
    (derivedGlobalSectionsOverUnit f) inferInstance I hI
  let e1 : derivedCohomologyOverField f K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
        (DerivedCategory.Q.obj (((globalSectionsOver f).mapHomologicalComplex (.up ℤ)).obj I)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso
      ((derivedGlobalSectionsOver f).mapIso eI.symm ≪≫ eG.symm)
  let e2 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) i).app
    (((globalSectionsOver f).mapHomologicalComplex (.up ℤ)).obj I)
  exact ⟨e1.toLinearEquiv.trans (e2.toLinearEquiv.trans
    ((StacksDraft.DerivedCoyoneda.homologyLinearEquivDerivedHom (Stacks.Ample.unitModule X)
        (globalSectionsOver f) (unitHomLinearEquivGlobalSections f)
        (fun a g => unitHomLinearEquivGlobalSections_naturality f a g) I i).trans
      (CategoryTheory.Linear.homCongr k
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
          (Stacks.Ample.unitModule X)).symm
        ((CategoryTheory.shiftFunctor (DerivedCategory X.Modules) i).mapIso eI))))⟩

/-- **`dim_k H^i(X, K) = dim_k Ext^i_{D(𝒪_X)}(𝒪_X[0], K)`**, the dimension count carried by
`Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit`. -/
public theorem finrank_derivedCohomologyOverField_eq_finrank_extUnit
    (K : DerivedCategory X.Modules) (i : ℤ) :
    Module.finrank k (derivedCohomologyOverField f K i) =
      Module.finrank k (DerivedCategory.Ext ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Stacks.Ample.unitModule X)) K i) :=
  (nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f K i).some.finrank_eq

end Stacks.Duality

end
