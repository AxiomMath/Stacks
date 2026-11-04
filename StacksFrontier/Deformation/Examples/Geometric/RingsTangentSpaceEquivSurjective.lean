module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceEquivRealization
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceInjection

/-!
# Every class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` is the class of a deformation of `P`

Let `k` be a field, `P` a `k`-algebra and `V` a finite-dimensional `k`-vector space. A point of
the fibre of the deformation category of Stacks 0DY1 over the square-zero extension `k ⊕ V` of
Stacks 06IB has a class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)`,
`Deformation.Examples.squareZeroFiberExtClass`, and that class only depends on its isomorphism
class, so it descends to the value `V ↦ 𝓕(k[V])` of the tangent-space set functor as
`Deformation.Examples.tangentExtClass`.

This file builds the point of that fibre which realizes a given square-zero extension, which is
the geometric input for the half of the tangent-space clause of Stacks 0DY3 that goes from Ext
to deformations. Given a square-zero extension `E` of `P` by `P ⊗[k] V`,
`StacksFrontier/Deformation/Examples/Geometric/RingsTangentSpaceEquivRealization.lean` puts a flat
`k ⊕ V`-algebra structure on its middle ring and exhibits `P` as its base change along the
augmentation; those two facts are exactly the flat algebra and the cartesian square of an
object of the deformation category over `k ⊕ V`, so they assemble into a point of the fibre.
Since isomorphism classes of square-zero extensions of `P` by `P ⊗[k] V` exhaust
`Ext¹_P(NL_{P/k}, P ⊗[k] V)` by **Stacks 0GPT**, surjectivity of the family of classes follows
once the class of this point is identified with the class of `E`.

## Main definitions

* `Deformation.Examples.realizationFlatAlgebra`: the flat algebra over `k ⊕ V` of the
  deformation realizing a square-zero extension.
* `Deformation.Examples.realizationFiber`: that deformation as a point of the fibre of the
  deformation category over `k ⊕ V`.

## Main results

* `Deformation.Examples.realizationFiber_base`, `Deformation.Examples.realizationFiber_fiber`,
  `Deformation.Examples.realizationFiber_algebraMap`,
  `Deformation.Examples.realizationFiber_aug` and
  `Deformation.Examples.realizationFiber_red`: the realizing point of the fibre has the
  square-zero extension `k ⊕ V` of Stacks 06IB as its base, the middle ring of `E` as its flat
  algebra, `Deformation.Examples.realizationHom` as its structural map, the first projection as
  the augmentation of its base, and the reduction of `E` as its reduction. These pin the point
  down, so the class of the square-zero extension it determines is the class of `E` by
  `Deformation.Examples.extClass_firstOrderExtension_eq`.
* `Deformation.Examples.squareZeroFiberExtClass_realizationFiber`: **the class of the realizing
  point of the fibre is the class of `E`.**
* `Deformation.Examples.surjective_squareZeroFiberExtClass` and
  `Deformation.Examples.surjective_tangentExtClass`: **the family of extension classes is
  surjective**, on points of the fibre and on their isomorphism classes.
* `Deformation.Examples.bijective_tangentExtClass`: with
  `Deformation.Examples.tangentExtClass_injective`, the family is a bijection of the value
  `V ↦ 𝓕(k[V])` of the tangent-space set functor onto `Ext¹_P(NL_{P/k}, P ⊗[k] V)`.

## Implementation notes

Nothing here carries the tag of Stacks 0DY3; the tangent-space clause of that tag is
`Deformation.Examples.ringDeformationTangentSpaceLinearEquivExtOne` of
`StacksFrontier/Deformation/Examples/Geometric/RingsTangentSpaceEquivTangent.lean`, which turns
the bijection proved here into a `k`-linear equivalence. The infinitesimal-automorphism clause
of that tag is
`Deformation.Examples.exists_infinitesimalAutomorphismGroupMulEquivDerivation` of
`StacksFrontier/Deformation/Examples/Geometric/RingsInfinitesimalAutomorphisms.lean`.

`Deformation.Examples.squareZeroFiberExtClass_realizationFiber` installs the transported
algebra structures of `Deformation.Examples.algebraOfBaseEquiv` and
`Deformation.Examples.baseAlgebraOfBaseEquiv` as local instances before quoting
`Deformation.Examples.extClass_firstOrderExtension_eq`. That is not bookkeeping: the
`k`-algebra structure on `E.B'` which a point of the fibre presents is only propositionally the
one `E` carries, and without the local instances the elaborator attempts to identify the two
and unfolds the identification of the kernel of `E` without terminating.

The augmentation `k ⊕ V → k` is obtained as the unique morphism to the terminal object
`Deformation.Examples.residueFieldBase`, and
`Deformation.Examples.squareZeroAugHom_hom` identifies it with the first projection from the
compatibility of a morphism of `𝒞_Λ` with the chosen identifications of the residue fields.
Building it by hand would mean re-proving that the first projection is a local homomorphism.

## References

* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 06IB](https://stacks.math.columbia.edu/tag/06IB)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct TrivSqZeroExt Stacks.Deformation

universe u w

namespace Deformation.Examples

attribute [local instance] HasDerivedCategory.standard

section Realize

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P] {W : FGModuleCat.{w} k}

/-- The right `k`-action on `V` agreeing with the left one, needed to form `k ⊕ V`. -/
local instance moduleMulOppositeSurjective : Module kᵐᵒᵖ W.obj :=
  Module.oppositeOfCommSemiring k W.obj

/-- The two `k`-actions on `V` agree. -/
local instance isCentralScalarSurjective : IsCentralScalar k W.obj :=
  Module.isCentralScalar_oppositeOfCommSemiring k W.obj

/-- The augmentation of the square-zero extension `k ⊕ V` of Stacks 06IB, as a morphism of
`𝒞_Λ` to the residue field: the residue field is terminal. -/
public def squareZeroAugHom (W : FGModuleCat.{w} k) :
    (squareZeroExtensionArtinian Λ k).obj W ⟶ residueFieldBase Λ k :=
  (isTerminal_residueFieldBase (Λ := Λ) (k := k)).from _

/-- The augmentation is the first projection: a morphism of `𝒞_Λ` is compatible with the
chosen identifications of the residue fields, and both of those identifications are the first
projection here. -/
public lemma squareZeroAugHom_hom (W : FGModuleCat.{w} k)
    (a : (squareZeroExtensionArtinian Λ k).obj W) :
    (squareZeroAugHom (Λ := Λ) W).hom a = a.fst := by
  have h := (squareZeroAugHom (Λ := Λ) W).residue_comm a
  rw [residueFieldBase_residueEquiv_residue] at h
  exact h.trans (squareZeroExtensionArtinian_residue Λ k W a)

variable (E : (algebraExtensionProblem k P (P ⊗[k] W.obj)).CompatibleExtension.{w})

/-- **The flat algebra over `k ⊕ V` of the deformation realizing a square-zero extension of `P`
by `P ⊗[k] V`.** Its base is the square-zero extension `k ⊕ V` of Stacks 06IB, its algebra is
the middle ring of the extension with the structure of
`Deformation.Examples.realizationAlgebra`, and its flatness is
`Deformation.Examples.flat_realization`, that is Stacks 063Y. -/
@[implicit_reducible]
public def realizationFlatAlgebra : FlatAlgebraCategory.{u, w} Λ k where
  base := (squareZeroExtensionArtinian Λ k).obj W
  fiber := E.B'
  algebra := realizationAlgebra E
  flat := by
    let := realizationAlgebra E
    let := realizationIsScalarTower E
    exact flat_realization E fun _ ↦ rfl

/-- **The cartesian morphism from the realizing deformation to `(k, P)`.** Its base map is the
augmentation and its map of algebras is the reduction of the extension; the square is a pushout
by `Deformation.Examples.isPushout_realization`. -/
@[implicit_reducible]
public def realizationHomToResidue :
    realizationFlatAlgebra (Λ := Λ) E ⟶ residueFieldAlgebra (Λ := Λ) (k := k) P where
  base := squareZeroAugHom W
  map := CommRingCat.ofHom (toRed E).toRingHom
  cartesian := by
    let := realizationAlgebra E
    let := realizationIsScalarTower E
    exact isPushout_commRingCat_realization E (fun _ ↦ rfl)
      (squareZeroAugHom (Λ := Λ) W).hom.toRingHom (squareZeroAugHom_hom W)
      (toRed E).toRingHom fun _ ↦ rfl

/-- **The deformation realizing a square-zero extension, as a point of the fibre of the
deformation category over `k ⊕ V`.** -/
@[implicit_reducible]
public def realizationFiber :
    (ringDeformationProjection Λ k P).Fiber ((squareZeroExtensionArtinian Λ k).obj W) :=
  ⟨Over.mk (realizationHomToResidue (Λ := Λ) E), rfl⟩

/-- The base of the realizing point of the fibre is the square-zero extension `k ⊕ V` of
Stacks 06IB, on the nose. -/
public lemma realizationFiber_base :
    (realizationFiber (Λ := Λ) E).1.left.base = (squareZeroExtensionArtinian Λ k).obj W := rfl

/-- The flat algebra of the realizing point of the fibre is the middle ring of `E`. -/
public lemma realizationFiber_fiber :
    (realizationFiber (Λ := Λ) E).1.left.fiber = E.B' := rfl

/-- The structural map of the realizing point of the fibre is
`Deformation.Examples.realizationHom`. -/
public lemma realizationFiber_algebraMap (a : TrivSqZeroExt k W.obj) :
    algebraMap ((realizationFiber (Λ := Λ) E).1.left.base : Type w)
      (realizationFiber (Λ := Λ) E).1.left.fiber a = realizationHom E a := rfl

/-- The augmentation of the base of the realizing point of the fibre is the first
projection. -/
public lemma realizationFiber_aug (a : TrivSqZeroExt k W.obj) :
    (realizationFiber (Λ := Λ) E).1.hom.base.hom a = a.fst :=
  squareZeroAugHom_hom W a

/-- The reduction of the realizing point of the fibre is the reduction of `E`. -/
public lemma realizationFiber_red (z : E.B') :
    (realizationFiber (Λ := Λ) E).1.hom.map.hom z = toRed E z := rfl

/-- The canonical presentation of the base of the realizing point of the fibre is the identity:
that base *is* the square-zero extension `k ⊕ V` of Stacks 06IB, so the equality of objects the
point carries is `rfl`. -/
public lemma fiberSquareZeroEquiv_realizationFiber
    (r : ((squareZeroExtensionArtinian Λ k).obj W : Type w)) :
    fiberSquareZeroEquiv W (realizationFiber (Λ := Λ) E) r = r := rfl

/-! ### The class of the realizing point of the fibre -/

/-- **The class of the realizing point of the fibre is the class of `E`.** This is
`Deformation.Examples.extClass_firstOrderExtension_eq` read through the canonical presentation
of the base: the structural map of the realizing point is
`Deformation.Examples.realizationHom` by `Deformation.Examples.realizationFiber_algebraMap` and
its reduction is the reduction of `E` by `Deformation.Examples.realizationFiber_red`.

The three `let`s are not bookkeeping. A point of the fibre presents its flat algebra as a
`k`-algebra by *transporting* the structure from its base, so the `k`-algebra structure on
`E.B'` that `Deformation.Examples.squareZeroFiberExtClass` works with is
`Deformation.Examples.baseAlgebraOfBaseEquiv`, whose structural map is
`c ↦ algebraMap k E.B' c + kerIncl E (1 ⊗ₜ 0)`: equal to the structural map of `E` but not
definitionally so. Installing the transported structures as local instances is what makes the
elaborator compare the two by `Deformation.Examples.extClass_firstOrderExtension_eq`, which is
stated for an arbitrary `k`-algebra structure on `E.B'` compatible with `hstr`, instead of
trying to identify them. -/
public lemma squareZeroFiberExtClass_realizationFiber :
    squareZeroFiberExtClass W (realizationFiber (Λ := Λ) E) = extClass E := by
  let F := (realizationFiber (Λ := Λ) E).1.left.fiber
  let e := fiberSquareZeroEquiv W (realizationFiber (Λ := Λ) E)
  let : Algebra (TrivSqZeroExt k W.obj) E.B' := algebraOfBaseEquiv F e
  let : Algebra k E.B' := baseAlgebraOfBaseEquiv F e
  let : IsScalarTower k (TrivSqZeroExt k W.obj) E.B' := isScalarTower_baseAlgebraOfBaseEquiv F e
  have hstr : ∀ a : TrivSqZeroExt k W.obj,
      algebraMap (TrivSqZeroExt k W.obj) E.B' a = realizationHom E a := fun _ ↦ rfl
  unfold squareZeroFiberExtClass fiberExtClass extClassOfBaseEquiv
  exact extClass_firstOrderExtension_eq E hstr _ _ _ _ fun _ ↦ rfl

end Realize

/-! ### Surjectivity of the extension class -/

section Surjective

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P]

/-- **Every class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)` is the class of a point of the fibre of the
deformation category over `k ⊕ V`.** By **Stacks 0GPT** every class is the class of a
square-zero extension `E` of `P` by `P ⊗[k] V`, and
`Deformation.Examples.realizationFiber` turns that extension into a point of the fibre whose
class is the class of `E`. -/
public theorem surjective_squareZeroFiberExtClass (W : FGModuleCat.{w} k) :
    Function.Surjective (squareZeroFiberExtClass (Λ := Λ) (P := P) W) := by
  intro c
  obtain ⟨q, hq⟩ :=
    (squareZeroAlgebraExtensionClassesEquivExtOne k P (P ⊗[k] W.obj)).surjective c
  induction q using Quotient.inductionOn with
  | h E =>
      exact ⟨realizationFiber (Λ := Λ) E,
        (squareZeroFiberExtClass_realizationFiber E).trans hq⟩

/-- **The family of classes is surjective at every coefficient vector space.** Together with
`Deformation.Examples.tangentExtClass_injective` this makes the family of classes a bijection
from the value `V ↦ 𝓕(k[V])` of the tangent-space set functor onto
`Ext¹_P(NL_{P/k}, P ⊗[k] V)`. -/
public theorem surjective_tangentExtClass (W : FGModuleCat.{w} k) :
    Function.Surjective (tangentExtClass (Λ := Λ) (P := P) W) := by
  intro c
  obtain ⟨x, hx⟩ := surjective_squareZeroFiberExtClass (Λ := Λ) (P := P) W c
  exact ⟨classOf (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection x,
    (tangentExtClass_classOf W x).trans hx⟩

/-- **The family of classes is bijective at every coefficient vector space.** This is the
tangent-space clause of Stacks 0DY3 as a bijection of sets, before the canonical vector-space
structure of Stacks 06IH is matched against the `k`-module structure of the Ext group. -/
public theorem bijective_tangentExtClass (W : FGModuleCat.{w} k) :
    Function.Bijective (tangentExtClass (Λ := Λ) (P := P) W) :=
  ⟨tangentExtClass_injective W, surjective_tangentExtClass W⟩

end Surjective

end Deformation.Examples

end
