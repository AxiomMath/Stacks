module

public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyOfAProduct
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerCohomologyFinite

/-!
# Acyclicity for a functor is closed under finite products

`Stacks.RightDerivedComp.acyclic G` is the property that every positive right derived functor of
`G` vanishes at an object.  This file proves that it is closed under **finite** products.

The proof is the only one available: `R ⁿ G` is additive
(`Stacks.LocalCohomology.rightDerived_additive`), an additive functor preserves finite products
(`CategoryTheory.Functor.preservesFiniteProductsOfAdditive`), and a product of zero objects is
zero (`Stacks.Cohomology.ModuleComparison.isZero_pi`).

**Finiteness is used and is not removable.**  An additive functor need not preserve infinite
products, and `R ⁿ G` does not: the statement below is false for an arbitrary index type.  So a
consumer that needs acyclicity of a product must first make the index type finite.

**Why this is not `Stacks.RightAcyclicProduct.rightAcyclic_pi`.**  That statement is the same
closure property for `CategoryTheory.Functor.rightAcyclic`, the derived-category formulation,
and the two predicates agree only under `Stacks.RightDerivedComp.rightAcyclic_iff_acyclic`,
which asks for `HasDerivedCategory` on both the source and the target abelian category.  The
statements below ask for neither, which is what makes them usable on a category of sheaves of
modules over a site whose objects live one universe above its morphisms.

## Main results

* `Stacks.RightDerivedComp.acyclic_pi`: acyclicity is closed under products over a finite index
  type.
* `Stacks.RightDerivedComp.acyclic_of_isLimit_fan`: the same for a product presented by an
  arbitrary limit fan, which is the shape a Čech term takes.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] (G : C ⥤ D) [G.Additive]

/-- **A product of `G`-acyclic objects over a finite index type is `G`-acyclic.**

`R ⁿ G` is additive, hence preserves the finite product, and a product of zero objects is
zero.  Finiteness of the index type is used and is not removable. -/
theorem acyclic_pi {ι : Type*} [Finite ι] (A : ι → C) [HasProduct A]
    (hA : ∀ i, acyclic G (A i)) : acyclic G (∏ᶜ A) := by
  intro n hn
  have : (G.rightDerived n).Additive := Stacks.LocalCohomology.rightDerived_additive G n
  have : PreservesLimitsOfShape (Discrete ι) (G.rightDerived n) :=
    preservesLimitsOfShape_of_discrete _
  exact (Stacks.Cohomology.ModuleComparison.isZero_pi
    (fun i => hA i n hn)).of_iso (PreservesProduct.iso (G.rightDerived n) A)

/-- **The same, for a product presented by an arbitrary limit fan.**  This is the form a Čech
term takes: it is a product of the values of the coefficient presheaf, but it is not
syntactically `∏ᶜ`. -/
theorem acyclic_of_isLimit_fan {ι : Type*} [Finite ι] {A : ι → C} {c : Fan A}
    (hc : IsLimit c) (hA : ∀ i, acyclic G (A i)) : acyclic G c.pt := by
  have : HasProduct A := ⟨⟨⟨c, hc⟩⟩⟩
  intro n hn
  exact ((acyclic_pi G A hA) n hn).of_iso
    ((G.rightDerived n).mapIso (hc.conePointUniqueUpToIso (limit.isLimit (Discrete.functor A))))

end Stacks.RightDerivedComp

end
