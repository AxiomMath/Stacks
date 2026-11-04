module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksCore.Tactic.StacksAttribute

/-! # The derived tensor product with a differential graded bimodule exists

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tensoring with `N` on homotopy categories
(`- ⊗_A N : K(A, d) ⥤ K(B, d)`, Tag 09LM), followed by localization of the target at the
quasi-isomorphisms, is a functor `F : K(A, d) ⥤ D(B, d)`; its left derived functor with respect
to the quasi-isomorphisms of `K(A, d)` is the derived tensor product
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)`. This file proves that it exists, which is Stacks Tag 09LS, and
names the functor, its comparison with ordinary tensoring, and its universal property.

## Main definitions

* `DifferentialGraded.Bimodule.derivedTensorFunctor`: the derived tensor product
  `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)`.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCounit`: its comparison with ordinary
  tensoring, the counit of the Kan extension.

## Main results

* `DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic`: every differential graded
  `A`-module receives a quasi-isomorphism from a module orthogonal on the left to the acyclic
  modules. This is Tag 09KP followed by Tag 09KM, and it is the sole input of everything below.
* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory_isLeftDerivable`: Tag 09LS in the
  source's own sense, that the left derived functor is defined at every object (Tag 05SV).
* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory_hasLeftDerivedFunctor`: Tag 09LS in
  Mathlib's Kan extension sense, which is what names `- ⊗_A^𝐋 N` as a functor on `D(A, d)`.
* `DifferentialGraded.Bimodule.derivedTensorFunctor_isLeftDerivedFunctor`: the comparison
  exhibits `- ⊗_A^𝐋 N` as the left derived functor of `F`.

## Implementation notes

*What is new here.* Both existence statements were already proved from the resolution hypothesis
in `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensor.lean`, by way of the
specialisation of Tag 06XN in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedFunctorCriterion.lean`. The content added
below is the discharge of that hypothesis, which is
`DifferentialGradedModule.exists_propertyP_resolution` (Tag 09KP) composed with
`DifferentialGradedModule.leftOrthogonal_acyclic_of_propertyP` (Tag 09KM); the rest is naming.

*How this differs from the Stacks proof.* The source applies Tag 06XN with the collection of
objects with property (P), checking its hypothesis (2) by Tag 09KY: a quasi-isomorphism between
modules with property (P) is a homotopy equivalence. The form of Tag 06XN that is available here
instead asks for the resolving objects to lie in the left orthogonal of the acyclic modules,
which for property (P) is Tag 09KM. The two routes prove the same lemma from the same
foundation; Tag 09KY is not needed on this one.

*Why two existence statements.* They are inequivalent and a consumer may need either; see the
implementation notes of `DerivedTensor.lean`. No bridge between them is claimed.

*Universes.* The differential graded algebras and their modules are taken at the library's
single-universe encoding `StacksDraft.Ch22.Sec4.Tag09JJ`, in which
`DifferentialGradedAlgebra : Type u → Type u` and a module over it again lies in `Type u`. The
Stacks source is universe-polymorphic in the base ring, each algebra and each module separately;
widening the encoding is an addition of universe parameters rather than a change of content, and
nothing below depends on the universes being equal.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS); the criterion it
  applies is [Tag 06XN](https://stacks.math.columbia.edu/tag/06XN), the resolutions are
  [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP), their orthogonality is
  [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), and the functor being derived is
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- Every differential graded `A`-module `M` receives a quasi-isomorphism from a differential
graded `A`-module whose class in `K(A, d)` is orthogonal on the left to the acyclic modules.

This is the hypothesis under which Tag 06XN produces left derived functors on `K(A, d)`, and it
is Tag 09KP — a resolution by a module with property (P) — followed by Tag 09KM — a module with
property (P) is left orthogonal to the acyclic modules. -/
theorem exists_quasiIso_leftOrthogonal_acyclic (A : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule.{u, u, u} A) :
    ∃ (P : DifferentialGradedModule.{u, u, u} A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  obtain ⟨P, f, hf, ⟨F⟩⟩ := exists_propertyP_resolution A M
  exact ⟨P, f, hf, leftOrthogonal_acyclic_of_propertyP F⟩

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **Stacks Tag 09LS**, in the source's own sense. Tensoring with the bimodule `N`, followed by
localization of the target, is left derivable with respect to the quasi-isomorphisms: its left
derived functor is defined at every object of `K(A, d)`, meaning that the pro-object
`Qis(A)/X ⥤ D(B, d)` is essentially constant (Tag 05SV). -/
@[stacks 09LS "existence in the pro-object sense"]
theorem tensorFunctorToDerivedCategory_isLeftDerivable (N : Bimodule A B) :
    (tensorFunctorToDerivedCategory N).IsLeftDerivable (quasiIsomorphisms' A) :=
  tensorFunctorToDerivedCategory_isLeftDerivable_of_resolutions N
    (exists_quasiIso_leftOrthogonal_acyclic A)

/-- **Stacks Tag 09LS**, in Mathlib's Kan extension sense. Tensoring with the bimodule `N`,
followed by localization of the target, has a total left derived functor: a right Kan extension
along the localization of `K(A, d)` at the quasi-isomorphisms. This is what names
`- ⊗_A^𝐋 N` as a functor on `D(A, d)`. -/
@[stacks 09LS "existence of the total left derived functor"]
theorem tensorFunctorToDerivedCategory_hasLeftDerivedFunctor (N : Bimodule A B) :
    (tensorFunctorToDerivedCategory N).HasLeftDerivedFunctor (quasiIsomorphisms' A) :=
  tensorFunctorToDerivedCategory_hasLeftDerivedFunctor_of_resolutions N
    (exists_quasiIso_leftOrthogonal_acyclic A)

/-- The derived tensor product `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of **Stacks Tag 09LS**: the total
left derived functor of tensoring with `N` followed by localization. -/
@[stacks 09LS "the derived tensor functor"]
def derivedTensorFunctor (N : Bimodule A B) : derivedCategory' A ⥤ derivedCategory' B := by
  letI := tensorFunctorToDerivedCategory_hasLeftDerivedFunctor N
  exact (tensorFunctorToDerivedCategory N).totalLeftDerived
    (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)

/-- The canonical comparison from the derived tensor product to ordinary tensoring: the counit of
the Kan extension defining `- ⊗_A^𝐋 N`. Its components are the maps
`P ⊗_A^𝐋 N → P ⊗_A N` in `D(B, d)`, which are isomorphisms exactly on the objects at which
ordinary tensoring already computes the derived functor. -/
@[stacks 0BZ2 "the canonical map from the derived to the plain tensor product"]
def derivedTensorFunctorCounit (N : Bimodule A B) :
    (quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N ⟶ tensorFunctorToDerivedCategory N := by
  letI := tensorFunctorToDerivedCategory_hasLeftDerivedFunctor N
  exact (tensorFunctorToDerivedCategory N).totalLeftDerivedCounit
    (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)

/-- The universal property of **Stacks Tag 09LS**: the comparison
`DifferentialGraded.Bimodule.derivedTensorFunctorCounit` exhibits `- ⊗_A^𝐋 N` as the left derived
functor of tensoring with `N` followed by localization, with respect to the
quasi-isomorphisms. -/
@[stacks 09LS "universal property"]
instance derivedTensorFunctor_isLeftDerivedFunctor (N : Bimodule A B) :
    (derivedTensorFunctor N).IsLeftDerivedFunctor
      (derivedTensorFunctorCounit N) (quasiIsomorphisms' A) := by
  let := tensorFunctorToDerivedCategory_hasLeftDerivedFunctor N
  change ((tensorFunctorToDerivedCategory N).totalLeftDerived
    (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)).IsLeftDerivedFunctor
    ((tensorFunctorToDerivedCategory N).totalLeftDerivedCounit
      (quasiIsomorphisms' A).Q (quasiIsomorphisms' A))
    (quasiIsomorphisms' A)
  infer_instance

end DifferentialGraded.Bimodule

end
