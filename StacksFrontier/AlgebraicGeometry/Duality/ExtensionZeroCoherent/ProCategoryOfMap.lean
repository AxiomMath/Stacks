module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategory
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategory
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Morphisms of pro-objects induced by morphisms of inverse sequences

A morphism `α : M ⟶ N` of inverse sequences in `𝒟` induces a morphism
`CategoryTheory.ProSeq.of M ⟶ CategoryTheory.ProSeq.of N` of pro-objects. On functors of points,
`colim_n Mor(N_n, L) ⟶ colim_n Mor(M_n, L)`, it sends the class of `g : N_n ⟶ L` to the class of
`α_n ≫ g`.

## Main definitions

* `CategoryTheory.ProSeq.ofMap`: the morphism of pro-objects induced by a morphism of inverse
  sequences.

## Main results

* `CategoryTheory.ProSeq.ι_ofMap_unop_hom`: its value on the class of a morphism `N_n ⟶ L`.

## Implementation notes

The functors of points are colimits indexed by `CategoryTheory.Pro.liftedInverseSequence`, the
lift of an inverse sequence to the morphism universe of `𝒟`, so `ofMap α` is the `colimMap` of
`α` whiskered through that lift and the co-Yoneda embedding.

## References

* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace CategoryTheory

variable (𝒟 : Type u) [Category.{v} 𝒟]

variable {𝒟}

namespace ProSeq

/-- The morphism of pro-objects induced by a morphism `α : M ⟶ N` of inverse sequences. On
functors of points it sends the class of `g : N_n ⟶ L` to the class of `α_n ≫ g`. -/
public def ofMap {M N : ℕᵒᵖ ⥤ 𝒟} (α : M ⟶ N) : of M ⟶ of N :=
  (ObjectProperty.homMk (P := IsSequentialProObject 𝒟) (X := (of N).unop) (Y := (of M).unop)
    (colimMap (Functor.whiskerRight (NatTrans.op (Functor.whiskerLeft ULiftHom.down
      (Functor.whiskerLeft ULift.downFunctor α))) coyoneda))).op

/-- The morphism of pro-objects induced by a morphism `α` of inverse sequences sends the class of
`g : N_n ⟶ L` to the class of `α_n ≫ g`. -/
public lemma ι_ofMap_unop_hom {M N : ℕᵒᵖ ⥤ 𝒟} (α : M ⟶ N)
    (i : (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ) :
    colimit.ι ((Pro.liftedInverseSequence N).op ⋙ coyoneda) i ≫ (ofMap α).unop.hom =
      coyoneda.map (α.app (ULift.downFunctor.obj (ULiftHom.down.obj i.unop))).op ≫
        colimit.ι ((Pro.liftedInverseSequence M).op ⋙ coyoneda) i :=
  ι_colimMap _ _

end ProSeq

end CategoryTheory

end
