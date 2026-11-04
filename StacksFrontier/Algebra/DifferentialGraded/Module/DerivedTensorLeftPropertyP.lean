module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleToTensor
public import StacksFrontier.Algebra.DifferentialGraded.LeftModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP

/-! # Derived tensoring with a bimodule with property (P) on the left

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule which has property (P) as a *left* differential graded
`A`-module. Stacks Tag 0GZ2 asserts that `M ⊗_A^𝐋 N` is then computed by `M ⊗_A N` for every
differential graded `A`-module `M`: the comparison of Tag 09LS from the derived to the plain
tensor product is invertible.

## Main definitions

* `DifferentialGraded.Bimodule.LeftPropertyP`: the bimodule has property (P) as a left
  differential graded `A`-module, read on the right differential graded `A^{opp}`-module it is by
  Tag 0FQ0.
* `DifferentialGraded.Bimodule.TensorPreservesQuasiIso`: tensoring with `N` carries
  quasi-isomorphisms of differential graded `A`-modules to quasi-isomorphisms.
* `DifferentialGraded.Bimodule.LeftPropertyPPreservesQuasiIso`: every bimodule satisfying
  `LeftPropertyP` satisfies `TensorPreservesQuasiIso`.

## Main results

* `DifferentialGraded.Bimodule.tensorFunctorToDerivedCategory_isInvertedBy_of_preservesQuasiIso`:
  if `TensorPreservesQuasiIso N`, then tensoring with `N` followed by localization inverts the
  quasi-isomorphisms of `K(A, d)`.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_of_inverts`: if ordinary
  tensoring with `N` followed by localization inverts the quasi-isomorphisms, then the comparison
  of Tag 09LS from the derived to the plain tensor product is an isomorphism of functors.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_of_preservesQuasiIso` and
  `DifferentialGraded.Bimodule.derivedTensorIsoOfPreservesQuasiIso`: under
  `TensorPreservesQuasiIso N`, the comparison is invertible, giving an isomorphism
  `- ⊗_A^𝐋 N ≅ - ⊗_A N`.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftPropertyP`: under
  `LeftPropertyPPreservesQuasiIso A B`, for every bimodule `N` with `LeftPropertyP N` and every
  differential graded `A`-module `M`, the comparison `M ⊗_A^𝐋 N ⟶ M ⊗_A N` is invertible.

## Implementation notes

*"Is computed by" is the canonical comparison.* `DifferentialGraded.Bimodule.derivedTensorFunctor`
is the total left derived functor of ordinary tensoring followed by localization, and
`DifferentialGraded.Bimodule.derivedTensorFunctorCounit` is the counit of the Kan extension
exhibiting it as such. The conclusion of Tag 0GZ2 is that this one transformation is invertible;
an unspecified isomorphism between the two functors would be strictly weaker, since it need not
be compatible with the universal property.

*The hypothesis `LeftPropertyPPreservesQuasiIso`.* The statement that `f ⊗ id` is a
quasi-isomorphism whenever `f` is, for `N` with property (P) on the left, follows from the second
assertion of Tag 09S3 and the flip `M ⊗_A N = N ⊗_{A^{opp}} M`. In this file it is taken as the
hypothesis `LeftPropertyPPreservesQuasiIso`.

*Property (P) on the left.* Property (P) (Tag 09KK, `DifferentialGradedModule.PropertyPFiltration`)
is a property of *right* differential graded modules, while Tag 0GZ2 asks for it on the left.
`LeftPropertyP` passes to `A^{opp}`: `DifferentialGraded.Bimodule.toLeftModule` is the left
differential graded `A`-module underlying the bimodule and
`DifferentialGraded.leftRightEquivalence` (Tag 0FQ0) turns it into a right differential graded
module over `A^{opp}`, of which a property-(P) filtration is asked.

*Relation to invertibility at objects.*
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal` gives the
invertibility of the same comparison at the objects of `K(A, d)` orthogonal on the left to the
acyclic modules — a condition on the *object*, satisfied for instance by the modules with
property (P) by Tag 09KM. Tag 0GZ2 is the complementary statement: a condition on the *bimodule*
which makes the comparison invertible at every object.

*Universes.* The base ring, the two algebras and all their modules live in a single universe `u`,
as required by `DifferentialGraded.Bimodule.TensorDGFunctorData` and
`DifferentialGradedModule.PropertyPFiltration`. The base ring is commutative.

## References

* [Stacks Project, Tag 0GZ2](https://stacks.math.columbia.edu/tag/0GZ2); the construction it
  invokes is [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), the claim it needs is the
  second assertion of [Tag 09S3](https://stacks.math.columbia.edu/tag/09S3), property (P) is
  [Tag 09KK](https://stacks.math.columbia.edu/tag/09KK) and the identification of left modules
  with right modules over the opposite is [Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-! ### The hypothesis and the missing claim -/

/-- The differential graded `(A, B)`-bimodule `N` *has property (P) as a left differential graded
`A`-module*: the left differential graded `A`-module underlying it, read as a right differential
graded `A^{opp}`-module through the equivalence of Tag 0FQ0, carries a property-(P) filtration in
the sense of Tag 09KK. -/
@[stacks 0GZ2 "the hypothesis: property (P) as a left differential graded A-module"]
def LeftPropertyP (N : Bimodule A B) : Prop :=
  Nonempty (PropertyPFiltration
    ((DifferentialGraded.leftRightEquivalence R A).equivalence.functor.obj
      (toLeftModule A B N)))

/-- Tensoring with `N` carries every quasi-isomorphism `f : M ⟶ M'` of differential graded
`A`-modules to a quasi-isomorphism `f ⊗ id : M ⊗_A N ⟶ M' ⊗_A N` of differential graded
`B`-modules, where `f ⊗ id` is the image of `f` under the functor of Tag 09LM. -/
def TensorPreservesQuasiIso (N : Bimodule A B) : Prop :=
  ∀ {M M' : DifferentialGradedModule A} (f : M ⟶ M'),
    QuasiIso ((forgetToCochainComplex A).map f) →
      QuasiIso ((forgetToCochainComplex B).map ((tensorCompFunctor N).map f))

/-- Every differential graded `(A, B)`-bimodule `N` with property (P) as a left differential
graded `A`-module satisfies `TensorPreservesQuasiIso N`. -/
def LeftPropertyPPreservesQuasiIso (A B : DifferentialGradedAlgebra R) : Prop :=
  ∀ N : Bimodule A B, LeftPropertyP N → TensorPreservesQuasiIso N

/-! ### From the claim to the invertibility of the comparison -/

/-- If ordinary tensoring with `N` carries a homomorphism `g` of differential graded modules to a
quasi-isomorphism, then the localization of `K(B, d)` inverts the image of the homotopy class of
`g` under tensoring with `N`. -/
theorem isIso_q_map_tensorHomotopyFunctor_map (N : Bimodule A B)
    {M M' : DifferentialGradedModule A} (g : M ⟶ M')
    (hg : QuasiIso ((forgetToCochainComplex B).map ((tensorCompFunctor N).map g))) :
    IsIso ((quasiIsomorphisms' B).Q.map
      ((tensorHomotopyFunctor N).map ((toHomotopyCategory A).map g))) := by
  set Q := (quasiIsomorphisms' B).Q with hQ
  have h1 : quasiIsomorphisms' B ((toHomotopyCategory B).map ((tensorCompFunctor N).map g)) :=
    (quasiIsomorphisms_map_iff' B _).2 hg
  have h2 : IsIso (Q.map ((tensorCompFunctor N ⋙ toHomotopyCategory B).map g)) :=
    Localization.inverts Q (quasiIsomorphisms' B) _ h1
  have hq : ∀ X, IsIso (Q.map ((tensorCompFunctor_quotient N).hom.app X)) := fun X => by
    have : IsIso ((tensorCompFunctor_quotient N).hom.app X) := inferInstance
    infer_instance
  have := hq M
  have := hq M'
  have key : IsIso (Q.map ((tensorCompFunctor N ⋙ toHomotopyCategory B).map g ≫
      (tensorCompFunctor_quotient N).hom.app M')) := by
    rw [Functor.map_comp]
    infer_instance
  rw [(tensorCompFunctor_quotient N).hom.naturality g, Functor.map_comp] at key
  have hfinal : IsIso (Q.map ((toHomotopyCategory A ⋙ tensorHomotopyFunctor N).map g)) :=
    IsIso.of_isIso_comp_left (Q.map ((tensorCompFunctor_quotient N).hom.app M)) _
  exact hfinal

/-- If tensoring with `N` preserves quasi-isomorphisms, then tensoring with `N` followed by
localization inverts the quasi-isomorphisms of `K(A, d)`. -/
theorem tensorFunctorToDerivedCategory_isInvertedBy_of_preservesQuasiIso (N : Bimodule A B)
    (h : TensorPreservesQuasiIso N) :
    (quasiIsomorphisms' A).IsInvertedBy (tensorFunctorToDerivedCategory N) := by
  intro X Y f hf
  induction f using Quot.inductionOn with
  | _ g => exact isIso_q_map_tensorHomotopyFunctor_map N g (h g (hf g rfl))

/-- If ordinary tensoring with `N`, followed by localization, inverts the quasi-isomorphisms of
`K(A, d)`, then it *is* the derived tensor product: the comparison of Tag 09LS from `- ⊗_A^𝐋 N`
to `- ⊗_A N` is an isomorphism of functors. -/
theorem isIso_derivedTensorFunctorCounit_of_inverts (N : Bimodule A B)
    (h : (quasiIsomorphisms' A).IsInvertedBy (tensorFunctorToDerivedCategory N)) :
    IsIso (derivedTensorFunctorCounit N) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedTensorFunctor N)
    (derivedTensorFunctorCounit N) h

/-- If tensoring with `N` carries quasi-isomorphisms of differential graded `A`-modules to
quasi-isomorphisms, then `M ⊗_A^𝐋 N` is computed by `M ⊗_A N`: the comparison of Tag 09LS is an
isomorphism of functors. -/
theorem isIso_derivedTensorFunctorCounit_of_preservesQuasiIso (N : Bimodule A B)
    (h : TensorPreservesQuasiIso N) :
    IsIso (derivedTensorFunctorCounit N) :=
  isIso_derivedTensorFunctorCounit_of_inverts N
    (tensorFunctorToDerivedCategory_isInvertedBy_of_preservesQuasiIso N h)

/-- The isomorphism `- ⊗_A^𝐋 N ≅ - ⊗_A N` of functors `D(A, d) ⥤ D(B, d)` given by the
comparison of Tag 09LS, when tensoring with `N` preserves quasi-isomorphisms. -/
def derivedTensorIsoOfPreservesQuasiIso (N : Bimodule A B) (h : TensorPreservesQuasiIso N) :
    (quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N ≅ tensorFunctorToDerivedCategory N :=
  haveI := isIso_derivedTensorFunctorCounit_of_preservesQuasiIso N h
  asIso (derivedTensorFunctorCounit N)

/-! ### Tag 0GZ2 -/

/-- The statement of Stacks 0GZ2 under the assumption `LeftPropertyPPreservesQuasiIso`:

*"Let `R` be a ring. Let `(A, d)` and `(B, d)` be differential graded `R`-algebras. Let `N` be a
differential graded `(A, B)`-bimodule which has property (P) as a left differential graded
`A`-module. Then `M ⊗_A^𝐋 N` is computed by `M ⊗_A N` for all differential graded `A`-modules
`M`."*

"Is computed by" is the invertibility of the comparison of Tag 09LS at the image of `M`, so the
statement is that the canonical map `M ⊗_A^𝐋 N ⟶ M ⊗_A N` is an isomorphism in `D(B, d)` for
every differential graded `A`-module `M`. -/
theorem isIso_derivedTensorFunctorCounit_app_of_leftPropertyP
    (hclaim : LeftPropertyPPreservesQuasiIso A B) (N : Bimodule A B) (hP : LeftPropertyP N)
    (M : DifferentialGradedModule A) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M)) := by
  have := isIso_derivedTensorFunctorCounit_of_preservesQuasiIso N (hclaim N hP)
  infer_instance

/-- Under `LeftPropertyPPreservesQuasiIso A B`, for `N` with `LeftPropertyP N`, the comparison of
Tag 09LS is an isomorphism `- ⊗_A^𝐋 N ≅ - ⊗_A N` of functors. -/
def derivedTensorIsoOfLeftPropertyP (hclaim : LeftPropertyPPreservesQuasiIso A B)
    (N : Bimodule A B) (hP : LeftPropertyP N) :
    (quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N ≅ tensorFunctorToDerivedCategory N :=
  derivedTensorIsoOfPreservesQuasiIso N (hclaim N hP)

end DifferentialGraded.Bimodule

end
