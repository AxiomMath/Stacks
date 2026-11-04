module
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.Monoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive

/-!
# Additivity and total complexes for the tensor product of abelian étale sheaves

The tensor product of abelian groups `AddCommGrpCat.monoidalCategory` and the tensor product of
abelian sheaves on a small étale site `Stacks.EtaleCohomology.etaleAbelianMonoidalCategory` are
additive in each variable, and every double complex of abelian étale sheaves indexed by `ℤ × ℤ`
has a total complex. These are the instances the generic K-flat machinery
`CochainComplex.KFlatBifunctor` asks of a bifunctor before it can speak of K-flatness and of the
derived bifunctor.

## Main results

* `AddCommGrpCat.monoidalPreadditive_general`: the tensor product of abelian groups, at any
  universe, is additive in each variable. With Mathlib's instances this makes
  `curriedTensor AddCommGrpCat`, its flip and each of their values additive, and every
  `HasMapBifunctor` for it is found by instance search (abelian groups have all small colimits).
* `Stacks.EtaleCohomology.etaleAbelianMonoidalPreadditive`: the same for abelian sheaves on the
  small étale site, hence for `Stacks.EtaleCohomology.etaleAbelianTensor X`.
* `Stacks.EtaleCohomology.etaleAbelian_hasTotal`: every double complex of abelian étale sheaves
  has a total complex; in particular `etaleAbelianTensor_hasMapBifunctor`.

## Implementation notes

The total complex of a `ℤ × ℤ`-indexed double complex is a coproduct over each (countable)
antidiagonal. Instance search does not find these coproducts of abelian étale sheaves by itself
(see `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits`), so
`etaleAbelian_hasTotal` writes them down from
`AlgebraicGeometry.Scheme.hasColimit_sheaf_smallEtaleTopology`. Stated for an arbitrary double
complex, it also supplies the `HasTotal` instances of the transport of a derived bifunctor along
an additive functor between categories of abelian étale sheaves, whose double complexes are
images of total complexes of the tensor product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w u v

namespace AddCommGrpCat

attribute [local instance] AddCommGrpCat.monoidalCategory

/-- **The tensor product of abelian groups is additive in each variable**, at any universe: the
equivalence with modules over a copy of `ℤ` is monoidal, faithful and additive, and the tensor
product of modules is additive in each variable. -/
instance monoidalPreadditive_general : MonoidalPreadditive AddCommGrpCat.{w} := by
  letI : (uliftIntEquivalence.{w}).inverse.Monoidal := by
    change (Monoidal.equivalenceTransported (uliftIntEquivalence.{w})).inverse.Monoidal
    infer_instance
  letI : (uliftIntEquivalence.{w}).inverse.Additive :=
    (uliftIntEquivalence.{w}).inverse.additive_of_preserves_binary_products
  exact monoidalPreadditive_of_faithful (uliftIntEquivalence.{w}).inverse

end AddCommGrpCat

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.braidedCategoryGeneral
  AddCommGrpCat.monoidalClosedGeneral etaleAbelianMonoidalCategory

variable (X : Scheme.{u})

/-- **The tensor product of abelian sheaves on the small étale site is additive in each
variable.** -/
instance etaleAbelianMonoidalPreadditive :
    MonoidalPreadditive (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  letI := isMonoidal_W_smallEtale.{u, v} X
  Sheaf.monoidalPreadditive X.smallEtaleTopology

/-- **Every double complex of abelian étale sheaves has a total complex**: the antidiagonals of
`ℤ × ℤ` are countable, and abelian sheaves on the small étale site have countable coproducts. -/
instance etaleAbelian_hasTotal
    (K : HomologicalComplex₂ (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) :=
  fun _ ↦ Scheme.hasColimit_sheaf_smallEtaleTopology.{u, v} X _

/-- Total complexes of the tensor product of two complexes of abelian étale sheaves exist. -/
instance etaleAbelianTensor_hasMapBifunctor
    (K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (etaleAbelianTensor.{u, v} X) (ComplexShape.up ℤ) :=
  etaleAbelian_hasTotal.{u, v} X _

end Stacks.EtaleCohomology

end
