module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit

/-!
# Moving a tensor factor past another one

Let `(C, 𝒪)` be a ringed site and let `T` be a derived tensor product on `D(𝒪)`. For objects
`G`, `K`, `A` of `D(𝒪)` there is an isomorphism

`G ⊗^𝐋_𝒪 (K ⊗^𝐋_𝒪 A) ≅ K ⊗^𝐋_𝒪 (G ⊗^𝐋_𝒪 A)`

which moves the outer factor `G` past `K`: the associativity constraint of [Stacks, Tag 0FPT],
then the commutativity constraint of [Stacks, Tag 0FPT] on the two outer factors, then the
associativity constraint again. It is the interchange that the tensor–Hom diagonal of
[Stacks, Tag 0BYS] is built from when the tensor–Hom adjunction tensors on the *left*:
`CategoryTheory.Adjunction.tensorHomDiagonal` takes exactly a morphism of this type.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso`: the isomorphism.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso_hom`: its forward map is
  the displayed composite of the three constraints, so it is not an arbitrary isomorphism
  between the two objects.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso_hom_naturality_right`:
  naturality in the innermost object `A`, from naturality of the associativity constraint in its
  third variable and naturality of the commutativity constraint.

## Implementation notes

The braiding is not avoidable here and no symmetry is assumed away. The commutativity constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` is used on the pair `(G, K)`
and nothing below needs it to be involutive, which is as well: involutivity is one of the
coherence clauses of [Stacks, Tag 0FPT] that
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DerivedSymmetryAndUnit.lean` records
as not proved in this development.

Naturality is stated in the innermost variable only, which is the variable the diagonal of
[Stacks, Tag 0BYS] is functorial in on this side. Naturality in `G` and in `K` is the same
pasting of three squares, with `associator_naturality_left`, `_naturality_middle` and
`braidingIso_hom_naturality` in place of the lemmas used below; it is not needed by any consumer
and is not stated.

The associativity constraint comes from
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator`, which re-seats the monoidal
structure of [Stacks, Tag 0FPT] onto the prescribed bifunctor, and nothing below describes the
isomorphism on complexes. Its compatibility with the K-flat comparisons is available: on K-flat
complexes the associator is
`Stacks.SheafOfModules.DerivedMonoidal.kFlatTensorComparison_associator` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/AssociatorOnKFlatComplexes.lean`,
which is the clause
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison_associator` of [Stacks, Tag 0FPT] carried
across the re-seating. It is stated over
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison`, the tensorator of the monoidal
localization functor, and not over the `comparison` field of the given derived tensor product,
which is the comparison the commutativity constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` is built from; identifying
those two comparisons is what a description of `middleSwapIso` itself on K-flat complexes still
needs, and `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app` reduces
it to one equation. Nothing below claims any such description.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct X.O)

/-- **Moving the outer tensor factor past the middle one**:
`G ⊗^𝐋_𝒪 (K ⊗^𝐋_𝒪 A) ≅ K ⊗^𝐋_𝒪 (G ⊗^𝐋_𝒪 A)`. Reassociate, commute the two outer factors,
reassociate back. -/
def middleSwapIso (G K A : DerivedModules X.O) :
    (T.tensor.obj G).obj ((T.tensor.obj K).obj A) ≅
      (T.tensor.obj K).obj ((T.tensor.obj G).obj A) :=
  (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O T G K A).symm ≪≫
    (T.tensor.mapIso (T.braidingIso X G K)).app A ≪≫
      Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O T K G A

/-- The forward map of `middleSwapIso` is the displayed composite of the two associativity
constraints and the commutativity constraint. -/
theorem middleSwapIso_hom (G K A : DerivedModules X.O) :
    (middleSwapIso X T G K A).hom =
      (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O T G K A).inv ≫
        (T.tensor.map (T.braidingIso X G K).hom).app A ≫
          (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O T K G A).hom :=
  rfl

/-- **`middleSwapIso` is natural in the innermost object.** -/
theorem middleSwapIso_hom_naturality_right (G K : DerivedModules X.O)
    {A A' : DerivedModules X.O} (a : A ⟶ A') :
    (T.tensor.obj G).map ((T.tensor.obj K).map a) ≫ (middleSwapIso X T G K A').hom =
      (middleSwapIso X T G K A).hom ≫ (T.tensor.obj K).map ((T.tensor.obj G).map a) := by
  rw [middleSwapIso_hom, middleSwapIso_hom]
  have h₁ : (T.tensor.obj G).map ((T.tensor.obj K).map a) ≫
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O T G K A').inv =
      (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator X.O T G K A).inv ≫
        (T.tensor.obj ((T.tensor.obj G).obj K)).map a := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_right
      X.O T G K a).symm
  have h₂ := ((T.tensor.map (T.braidingIso X G K).hom).naturality a).symm
  have h₃ := Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_right
    X.O T K G a
  rw [reassoc_of% h₁]
  simp only [Category.assoc]
  rw [← h₃, reassoc_of% h₂]

end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

end
