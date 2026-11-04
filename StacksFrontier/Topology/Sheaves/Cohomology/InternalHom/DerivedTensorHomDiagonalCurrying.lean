module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonal

/-!
# The two descriptions of the diagonal of [Stacks, Tag 0BYS] as morphisms of the same type

A ringed site carries two independently chosen derived tensor products of [Stacks, Tag 06YU],
and the two descriptions of the diagonal of [Stacks, Tag 0BYS] are stated over different ones.
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal` — the class of the complex-level morphism
of [Stacks, Tag 0BYR] between a chosen K-flat and a chosen K-injective representative — is
stated over `Stacks.SheafOfModules.derivedTensorProductFunctor`, the inhabitant the derived
internal Hom and [Stacks, Tag 08J8] use, while
`AlgebraicGeometry.RingedSite.curryTensorHomDiagonal` — the morphism obtained by adjointness from
[Stacks, Tag 08J8] — is stated over
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the inhabitant the symmetric
monoidal structure, the interchange and the projection formula use. So the two cannot be
compared as they stand.

This file carries the first along
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` so that they become
**morphisms of the same type**, and records the equation that would identify them, in the form in
which it is to be checked.

## Main definitions

* `AlgebraicGeometry.RingedSite.interfaceDerivedTensorHomDiagonal`: the complex-model diagonal of
  [Stacks, Tag 0BYS], conjugated into the tensor product the adjunction-theoretic one is stated
  over.

## Main results

* `AlgebraicGeometry.RingedSite.eq_interfaceDerivedTensorHomDiagonal`: the characterisation of
  the complex-model diagonal on representatives, read for the conjugated morphism; nothing else
  of its type satisfies it.
* `AlgebraicGeometry.RingedSite.interfaceDerivedTensorHomDiagonal_eq_curryTensorHomDiagonal_iff`:
  **the identification of the two descriptions is exactly one adjunction equation.** The
  complex-model diagonal is the adjunct of the interchange precisely when, tensored with `M` and
  composed with the derived evaluation morphism, it gives the interchange followed by
  `K ⊗^𝐋_O -` of that evaluation.

## What is proved and what is not

The displayed equation of the last result is **not discharged**, and no tag is placed below.
[Stacks, Tag 0BYS] is registered on `derivedTensorHomDiagonal` and its functorialities, and a
second registration on a morphism not compared with it would assert the identification that is
missing.

What the file supplies is that the identification is a single equation between two
constructed morphisms of one type, with the evaluation morphism in it named: by
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction_counit_app` the counit of
[Stacks, Tag 08J8] is the transpose of the identity under
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, so discharging the equation is computing
that bijection on a class of complexes — the currying isomorphism of [Stacks, Tag 0A90] against
the interchange of [Stacks, Tag 0BYT] — and involves no pushforward, no projection formula and
no closed immersion. The route through `Ri_*` of [Stacks, Tag 0E2N] needs this equation and one
other, the comparison of two evaluation morphisms.

**That is only half of what the equation contains, and the other half is not internal to the
derived internal Hom.** Its right-hand side carries
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso`, the interchange
`M ⊗^𝐋_O (K ⊗^𝐋_O -) ≅ K ⊗^𝐋_O (M ⊗^𝐋_O -)` built from the associativity and commutativity
constraints of [Stacks, Tag 0FPT]. The complex-model characterisation
`eq_interfaceDerivedTensorHomDiagonal` describes the left-hand morphism on representatives, so
checking the equation means describing that interchange on representatives too, and the
constraints of [Stacks, Tag 0FPT] are the only input of the equation that the
derived-internal-Hom development does not supply. The commutativity constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` is built on K-flat models
from the Koszul symmetry, and the associativity constraint on K-flat complexes is
`Stacks.SheafOfModules.DerivedMonoidal.kFlatTensorComparison_associator`; what is not yet
available is that the two are stated over two different K-flat comparisons — the `comparison`
field of the derived tensor product and the tensorator
`Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison` of the monoidal localization — so
`middleSwapIso` itself is not yet described on complexes. See the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/MiddleSwap.lean`.

## References

* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DerivedTensor.RingedSite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The complex-model diagonal of [Stacks, Tag 0BYS], read over the other derived tensor
product of the site.** `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal` conjugated by
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` at `K`, on the source
directly and on the target inside `RSheafHom(M, -)`.

This is the morphism that
`AlgebraicGeometry.RingedSite.curryTensorHomDiagonal` has to be compared with: the comparison
isomorphism is not a choice here, it is the only identification of the two tensor products the
library has, and the two morphisms have the same type only after it. -/
def interfaceDerivedTensorHomDiagonal
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor X.O).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((derivedTensorProductFunctor X.O).obj K).obj L) :=
  ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app K).inv.app
      (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≫
    derivedTensorHomDiagonal X K L M ≫
      ((derivedSheafHomBifunctor X).obj (op M)).map
        (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app K).hom.app L)

/-- The conjugated morphism is the complex-level morphism of [Stacks, Tag 0BYR] read through the
two model comparisons and the comparison of the two tensor products, so it is not an arbitrary
morphism between its two objects. -/
theorem interfaceDerivedTensorHomDiagonal_eq
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    interfaceDerivedTensorHomDiagonal X M K L =
      ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app K).inv.app
          (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≫
        derivedTensorHomDiagonal X K L M ≫
          ((derivedSheafHomBifunctor X).obj (op M)).map
            (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app K).hom.app
              L) :=
  rfl

/-- **The conjugated complex-model diagonal is determined by the characterisation of
[Stacks, Tag 0BYR] on representatives.** A morphism whose de-conjugation satisfies
`AlgebraicGeometry.RingedSite.eq_derivedTensorHomDiagonal` is this morphism. -/
theorem eq_interfaceDerivedTensorHomDiagonal
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {φ : ((derivedTensorProductFunctor X.O).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((derivedTensorProductFunctor X.O).obj K).obj L)}
    (hφ : ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app K).hom.app
            (((derivedSheafHomBifunctor X).obj (op M)).obj L) ≫ φ ≫
          ((derivedSheafHomBifunctor X).obj (op M)).map
            (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app
              K).inv.app L) =
        derivedTensorHomDiagonal X K L M) :
    φ = interfaceDerivedTensorHomDiagonal X M K L := by
  rw [interfaceDerivedTensorHomDiagonal, ← hφ]
  simp

/-- **The identification of the two descriptions of the diagonal of [Stacks, Tag 0BYS] is
exactly one adjunction equation.** The complex-model morphism of [Stacks, Tag 0BYR], conjugated
into the tensor product of the adjunction, is the adjunct
`AlgebraicGeometry.RingedSite.curryTensorHomDiagonal` of the interchange precisely when,
tensored with `M` and composed with the counit of [Stacks, Tag 08J8] — the derived evaluation
morphism of `derivedTensorSheafHomAdjunction_counit_app` — it gives the interchange followed by
`K ⊗^𝐋_O -` of that evaluation.

**The equation is not discharged.** What this says is that the identification is a single
equation between constructed morphisms of one type, and not a comparison of a morphism with a gap. -/
theorem interfaceDerivedTensorHomDiagonal_eq_curryTensorHomDiagonal_iff
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    interfaceDerivedTensorHomDiagonal X M K L = curryTensorHomDiagonal X M K L ↔
      ((derivedTensorProductFunctor X.O).obj M).map
            (interfaceDerivedTensorHomDiagonal X M K L) ≫
          (interfaceDerivedTensorSheafHomAdjunction X M).counit.app
            (((derivedTensorProductFunctor X.O).obj K).obj L) =
        (DerivedTensorProduct.middleSwapIso X (canonicalDerivedTensorProduct X.O) M K
              (((derivedSheafHomBifunctor X).obj (op M)).obj L)).hom ≫
          ((derivedTensorProductFunctor X.O).obj K).map
            ((interfaceDerivedTensorSheafHomAdjunction X M).counit.app L) :=
  Adjunction.eq_tensorHomDiagonal_iff (interfaceDerivedTensorSheafHomAdjunction X M) _ _

end AlgebraicGeometry.RingedSite

end
