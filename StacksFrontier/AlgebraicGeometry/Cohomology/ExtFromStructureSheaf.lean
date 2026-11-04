module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Extensions.ExtFromStructureSheaf

/-!
# Morphisms out of the structure sheaf of a scheme compute sheaf cohomology

For a scheme `X` and a sheaf of `𝒪_X`-modules `ℱ` the group of morphisms
`𝒪_X ⟶ ℱ[i]` in the derived category of `𝒪_X`-modules is the sheaf cohomology `H^i(X, ℱ)`:

$$ \operatorname{Hom}_{D(\mathcal O_X)}(\mathcal O_X, \mathcal F[i]) = H^i(X, \mathcal F) . $$

The cohomology on the right is the one the development uses, the `i`-th right derived functor of
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` valued in `Γ(X, 𝒪_X)`-modules, and for a
scheme over a field the same module read over the field is
`AlgebraicGeometry.cohomologyOverField`.

## Main results

* `AlgebraicGeometry.derivedHomStructureSheafEquivCohomology`:
  `Hom_{D(𝒪_X)}(𝒪_X, ℱ⟦i⟧) ≃+ H^i(X, ℱ)`.
* `AlgebraicGeometry.derivedHomStructureSheafEquivCohomologyOverField`: the same with the
  cohomology read as a module over the base field, that is against
  `AlgebraicGeometry.cohomologyOverField`.

## Implementation notes

A scheme is a ringed space, so both statements are
`Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology` at `R = X.ringCatSheaf` and
`U = ⊤`. Restriction of scalars along `k ≅ Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)` does not change the
underlying additive group, which is why the second statement is the first one retyped.

The morphism group is `CategoryTheory.Abelian.zExt`, `Hom_{D(𝒪_X)}(𝒪_X[0], ℱ[0]⟦i⟧)`, taken at
`CategoryTheory.HasDerivedCategory.standard`: that is the model
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/Cohomology.lean` and the derived-duality
statements of [Stacks, Tag 0BS2] are written against. The cohomology side mentions no derived
category at all — `CategoryTheory.Functor.rightDerived` is computed from injective resolutions —
so the choice of model constrains only the left-hand side.

No `@[stacks]` attribute is placed; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/ExtFromUnit.lean`.

## References

* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

/-- **Morphisms out of the structure sheaf in the derived category compute sheaf cohomology.**
For a scheme `X` and a sheaf of `𝒪_X`-modules `ℱ`, the group of morphisms `𝒪_X ⟶ ℱ[i]` in the
derived category of `𝒪_X`-modules is canonically `H^i(X, ℱ)`, the `i`-th right derived functor
of global sections. -/
public def derivedHomStructureSheafEquivCohomology (X : Scheme.{u}) (F : X.Modules) (i : ℕ) :
    Abelian.zExt (SheafOfModules.unit X.ringCatSheaf) F (i : ℤ) ≃+
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived i).obj F :=
  Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology X.ringCatSheaf F i

/-- **Morphisms out of the structure sheaf compute the cohomology of a scheme over a field.**
For a scheme `X` over a field `k` and a sheaf of `𝒪_X`-modules `ℱ`, the group of morphisms
`𝒪_X ⟶ ℱ[i]` in the derived category of `𝒪_X`-modules is the underlying additive group of the
`k`-vector space `AlgebraicGeometry.cohomologyOverField k f ℱ i`.

Restricting scalars along the structure morphism changes the scalars and not the group, so this
is `derivedHomStructureSheafEquivCohomology`. -/
public def derivedHomStructureSheafEquivCohomologyOverField (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) (i : ℕ) :
    Abelian.zExt (SheafOfModules.unit X.ringCatSheaf) F (i : ℤ) ≃+
      cohomologyOverField k f F i :=
  derivedHomStructureSheafEquivCohomology X F i

end AlgebraicGeometry

end
