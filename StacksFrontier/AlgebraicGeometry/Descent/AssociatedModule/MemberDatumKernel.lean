module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberDatumPackaging

/-!
# The quasi-coherent descent datum of Stacks 03DX (1), as a term

This file assembles the two laws of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumPackaging.lean` into a term of
`CategoryTheory.Pseudofunctor.DescentData'` for the pullback pseudofunctor of sheaves of modules,
at the fibre products of the big fppf site read downstairs.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.memberDatum`: the descent datum of Stacks 03DX (1) for a family
  of objects of `(Sch/S)_fppf` whose structure morphisms are an fpqc covering family.

## Main results

* `AlgebraicGeometry.BigFppfOver.memberDatumSelfCondition`: the identity law of the datum, in the
  spelling in which the structure asks for it.
* `AlgebraicGeometry.BigFppfOver.memberDatumCompCondition`: the cocycle law of the datum, in the
  spelling in which the structure asks for it.

## Implementation notes

Provisional.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
  CategoryTheory.Pseudofunctor.DescentData'

universe u w

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {I : Type w} (G : SheafOfModules.{u} (structureSheaf B S hS))
  (X : I → BigFppfOver B S hS) (F : ∀ i, (objScheme B S hS (X i)).Modules)
  (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-- **The identity law of the descent datum, in the structure's own spelling.**  This is the
statement of the field `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_hom_self` at the chosen
pullbacks of the family, which differs from
`AlgebraicGeometry.BigFppfOver.memberHom_self_law` only in which proof of `𝟙 _ ≫ f = f` fills the
autoparameter of `CategoryTheory.Pseudofunctor.DescentData'.pullHom'`. -/
public theorem memberDatumSelfCondition (i : I) :
    pullHom' (sq := memberChosenPullback B S hS X) (memberHom B S hS G X F hF e)
      (objHom B S hS (X i)) (𝟙 (objScheme B S hS (X i))) (𝟙 (objScheme B S hS (X i)))
      (pullHom'_self'._proof_4 (f := fun i ↦ objHom B S hS (X i)) i)
      (pullHom'_self'._proof_4 (f := fun i ↦ objHom B S hS (X i)) i) = 𝟙 _ :=
  memberHom_self_law B S hS G X F hF e i

/-- **The cocycle law of the descent datum, in the structure's own spelling.**  This is the
statement of the field `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_hom_comp` at the chosen
pullbacks of the family: the three transports along the projections of the chosen threefold
product of `X i₁`, `X i₂` and `X i₃` compose.  It is
`AlgebraicGeometry.BigFppfOver.pullHom_memberHom_comp` read through the structure's own three
reduction lemmas, which carry the autoparameter proofs the field type was built with. -/
public theorem memberDatumCompCondition (i₁ i₂ i₃ : I) :
    pullHom' (sq := memberChosenPullback B S hS X) (memberHom B S hS G X F hF e)
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂
          (pullHom'₁₂_eq_pullHom_of_chosenPullback₃._proof_2
            (memberChosenPullback₃ B S hS X) i₁ i₂ i₃)
          (pullHom'₁₂_eq_pullHom_of_chosenPullback₃._proof_4
            (memberChosenPullback₃ B S hS X) i₁ i₂ i₃) ≫
        pullHom' (sq := memberChosenPullback B S hS X) (memberHom B S hS G X F hF e)
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₃
          (pullHom'₁₂_eq_pullHom_of_chosenPullback₃._proof_4
            (memberChosenPullback₃ B S hS X) i₁ i₂ i₃)
          (pullHom'₁₃_eq_pullHom_of_chosenPullback₃._proof_3
            (memberChosenPullback₃ B S hS X) i₁ i₂ i₃) =
      pullHom' (sq := memberChosenPullback B S hS X) (memberHom B S hS G X F hF e)
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₃
        (pullHom'₁₂_eq_pullHom_of_chosenPullback₃._proof_2
          (memberChosenPullback₃ B S hS X) i₁ i₂ i₃)
        (pullHom'₁₃_eq_pullHom_of_chosenPullback₃._proof_3
          (memberChosenPullback₃ B S hS X) i₁ i₂ i₃) :=
  Stacks.comp_eq_of_eq
    (pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (sq := memberChosenPullback B S hS X)
      (memberChosenPullback₃ B S hS X) (memberHom B S hS G X F hF e) i₁ i₂ i₃)
    (pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (sq := memberChosenPullback B S hS X)
      (memberChosenPullback₃ B S hS X) (memberHom B S hS G X F hF e) i₁ i₂ i₃)
    (pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (sq := memberChosenPullback B S hS X)
      (memberChosenPullback₃ B S hS X) (memberHom B S hS G X F hF e) i₁ i₂ i₃)
    (pullHom_memberHom_comp B S hS G X F hF e i₁ i₂ i₃)

end AlgebraicGeometry.BigFppfOver

end
