module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.TwoFibreProductSetoid

/-!
# A 2-fibre product of stacks represented by algebraic spaces is represented (Stacks 04SD)

Let `a : 𝒜 ⟶ 𝒞` and `b : ℬ ⟶ 𝒞` be 1-morphisms of algebraic stacks over `S` with `𝒜` and `ℬ`
represented by *algebraic space* presheaves `A` and `Bp` and `𝒞` represented by a presheaf `C`.
**Stacks 04SD** says that the presheaf of isomorphism classes of `𝒜 ×_𝒞 ℬ` is the fibre product
`A ×_C Bp` of the representing presheaves; `StacksDraft.AlgebraicGeometry.Stacks`'
`RepresentedTwoFibreProduct` and `...Pullback` carry that comparison, but only against a
presheaf which is *already known* to represent the 2-fibre product. This file supplies the
representation itself, and with it the two facts a base-change argument needs: that the apex is
an algebraic space, and that the square of representing maps of the canonical 2-fibre product
square is a pullback square of presheaves.

The input is the representability criterion of **Stacks 02ZX**
(`AlgebraicGeometry.exists_equivalenceOver_elements_of_setoids`): a category fibred in setoids
whose presheaf of isomorphism classes is identified with a small presheaf is equivalent over the
site to the category of elements of that presheaf. The identification is
`AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv` together with its naturality, and
the fibred-in-setoids hypothesis is **Stacks 05UJ**
(`CategoryTheory.Functor.isStackInSetoids_twoFibreProduct_of_isStackInSetoids`) applied to the
two factors, which are stacks in setoids because they are representable by algebraic spaces
(the implication (3) ⟹ (1) of **Stacks 04SZ**,
`AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace`),
and to the target, which is a stack because it is an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInSetoids_twoFibreProductStructureFunctor`: the structure
  functor of the 2-fibre product is fibred in setoids.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProduct_fibreProduct` and its
  algebraic-stacks form `...nonempty_equivalenceOver_twoFibreProductSquare_fibreProduct`: the
  2-fibre product is represented by `CategoryTheory.Presheaf.fibreProduct` of the two
  representing maps.
* `AlgebraicGeometry.Stack.exists_representation_isPullback_twoFibreProductSquare`: the same,
  packaged with the two consequences a consumer wants — the apex is an algebraic space
  (**Stacks 04T9**) and the four representing maps of the canonical square form a pullback
  square of presheaves (**Stacks 04SD**, through
  `AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare`).
* `AlgebraicGeometry.Stack.isStack_of_algebraicStacks`: the sieve-indexed stack clause of
  `AlgebraicGeometry.Stack.IsAlgebraicStack`, read off.

## Implementation notes

The bundled form is the useful one: a consumer that pastes two 2-fibre products needs the
representing presheaf of the first apex as *data* for the second application, so the existential
has to carry the `CategoryTheory.StacksRepresentableCFG.EquivalenceOver` and not only its
existence. The two projections it names are the `AlgebraicGeometry.Stack.representingMap`s of the
two projections of the canonical square, not the projections of
`CategoryTheory.Presheaf.fibreProduct`: those differ by an automorphism of the apex, and every
consumer only ever needs the pullback square, which the representing maps satisfy on the nose.

No `@[stacks]` attribute is claimed: **Stacks 04SD** is registered on
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting` and its pullback form, **Stacks 02ZX** on
`AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff`, **Stacks 05UJ** on
`CategoryTheory.Functor.isStackInSetoids_twoFibreProduct_of_isStackInSetoids` and **Stacks 04T9**
on `AlgebraicGeometry.isAlgebraicSpace_of_isPullback`.

## References

* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
* [Stacks Project, Tag 05UJ](https://stacks.math.columbia.edu/tag/05UJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FibredInGroupoids

variable (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver
    𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
  (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵)

include eF eG in
/-- The structure functor of the 2-fibre product of a cospan whose two sources are represented
by algebraic spaces and whose target is a stack is fibred in setoids. -/
theorem isFiberedInSetoids_twoFibreProductStructureFunctor
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (h𝒵 : Functor.IsStack 𝒵.val.p (BigFppfOver.topology B S hS)) :
    (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFiberedInSetoids := by
  have h𝒳 : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
    isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 ⟨F, hF, ⟨eF⟩⟩
  have h𝒴 : 𝒴.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
    isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒴 ⟨G, hG, ⟨eG⟩⟩
  have hstack := Functor.isStackInSetoids_twoFibreProduct_of_isStackInSetoids
    (BigFppfOver.topology B S hS) h𝒳 h𝒴 h𝒵
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒵.property
      (CatFiberedInGroupoids.homFunctor_comp_p f))
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒵.property
      (CatFiberedInGroupoids.homFunctor_comp_p g))
  exact ⟨(CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.property,
    hstack.fiber_isThin⟩

include eH in
/-- **A 2-fibre product of stacks represented by algebraic spaces is represented by the fibre
product of the representing presheaves.** -/
theorem nonempty_equivalenceOver_twoFibreProduct_fibreProduct
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (h𝒵 : Functor.IsStack 𝒵.val.p (BigFppfOver.topology B S hS)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
      (presheafOfCategories (Presheaf.fibreProduct
        (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g) ⋙ typeToCat)).p) := by
  let hset := isFiberedInSetoids_twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 F G eF eG f g
    hF hG h𝒵
  let : (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered :=
    hset.isFiberedInGroupoids.isFibered
  exact exists_equivalenceOver_elements_of_setoids
    (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g) _
    (fun U => twoFibreProductIsoClassSectionEquiv B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g U.unop)
    (fun {_ _} k x =>
      twoFibreProductIsoClassSectionEquiv_map B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g k.unop x)

end FibredInGroupoids

/-- The sieve-indexed stack condition of an algebraic stack. -/
theorem isStack_of_algebraicStacks (𝒜 : AlgebraicStacks.{u, w} B S hS) :
    Functor.IsStack 𝒜.val.val.p (BigFppfOver.topology B S hS) := by
  obtain ⟨-, hst, -⟩ := 𝒜.property
  exact hst.1

section Stacks

variable {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS}
  (A Bp C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eA : StacksRepresentableCFG.EquivalenceOver
    𝒜.val.val.p (presheafOfCategories (A ⋙ typeToCat)).p)
  (eB : StacksRepresentableCFG.EquivalenceOver
    ℬ.val.val.p (presheafOfCategories (Bp ⋙ typeToCat)).p)
  (eC : StacksRepresentableCFG.EquivalenceOver
    𝒞.val.val.p (presheafOfCategories (C ⋙ typeToCat)).p)

include eA eB eC in
/-- **The canonical 2-fibre product of algebraic stacks represented by algebraic spaces is
represented by the fibre product of the representing presheaves.** -/
theorem nonempty_equivalenceOver_twoFibreProductSquare_fibreProduct
    (hA : IsAlgebraicSpace B S hS A) (hB : IsAlgebraicSpace B S hS Bp)
    (a : 𝒜 ⟶ 𝒞) (b : ℬ ⟶ 𝒞) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProductSquare B S hS a b).pt.val.val.p
      (presheafOfCategories (Presheaf.fibreProduct
        (representingMap B S hS 𝒜.val 𝒞.val A C eA eC a.hom)
        (representingMap B S hS ℬ.val 𝒞.val Bp C eB eC b.hom) ⋙ typeToCat)).p) :=
  nonempty_equivalenceOver_twoFibreProduct_fibreProduct B S hS 𝒜.val ℬ.val 𝒞.val A Bp C
    eA eB eC a.hom b.hom hA hB (isStack_of_algebraicStacks B S hS 𝒞)


include eA eB eC in
/-- **The canonical 2-fibre product of algebraic stacks represented by algebraic spaces, with a
representing presheaf for which the square of representing maps is a pullback of presheaves and
the apex is an algebraic space.** -/
theorem exists_representation_isPullback_twoFibreProductSquare
    (hA : IsAlgebraicSpace B S hS A) (hB : IsAlgebraicSpace B S hS Bp)
    (hC : IsAlgebraicSpace B S hS C)
    (a : 𝒜 ⟶ 𝒞) (b : ℬ ⟶ 𝒞) :
    ∃ (Kp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (eK : StacksRepresentableCFG.EquivalenceOver
        (AlgebraicStacks.twoFibreProductSquare B S hS a b).pt.val.val.p
        (presheafOfCategories (Kp ⋙ typeToCat)).p),
      IsAlgebraicSpace B S hS Kp ∧
        IsPullback
          (representingMap B S hS
            (AlgebraicStacks.twoFibreProductSquare B S hS a b).pt.val 𝒜.val Kp A eK eA
            (AlgebraicStacks.twoFibreProductSquare B S hS a b).fst.hom)
          (representingMap B S hS
            (AlgebraicStacks.twoFibreProductSquare B S hS a b).pt.val ℬ.val Kp Bp eK eB
            (AlgebraicStacks.twoFibreProductSquare B S hS a b).snd.hom)
          (representingMap B S hS 𝒜.val 𝒞.val A C eA eC a.hom)
          (representingMap B S hS ℬ.val 𝒞.val Bp C eB eC b.hom) := by
  obtain ⟨eK⟩ := nonempty_equivalenceOver_twoFibreProductSquare_fibreProduct B S hS
    A Bp C eA eB eC hA hB a b
  let : (twoFibreProductStructureFunctor B S hS 𝒜.val ℬ.val 𝒞.val a.hom b.hom).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      a.hom b.hom).pt.property.isFibered
  have hpb := isPullback_representingMap_twoFibreProductSquare B S hS 𝒜.val ℬ.val 𝒞.val
    A Bp C eA eB eC a.hom b.hom _ eK
  exact ⟨_, eK, isAlgebraicSpace_of_isPullback hA hB hC.isSheaf hC.diagonal_representable hpb,
    hpb⟩

end Stacks

end AlgebraicGeometry.Stack

end
