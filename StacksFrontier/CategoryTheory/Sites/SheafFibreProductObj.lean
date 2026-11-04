module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# A fibre product of sheaves of types, read as a presheaf

The forgetful functor from sheaves to presheaves creates limits, so a fibre product of sheaves
is computed as the fibre product of the underlying presheaves. This file records that
identification, `(A ×_X G).obj ≅ A.obj ×_{X.obj} G.obj`, together with its compatibility with the
two projections.

## Main results

* `CategoryTheory.Sheaf.pullbackObjIso`: the underlying presheaf of a fibre product of sheaves
  of types is the fibre product of the underlying presheaves.
* `CategoryTheory.Sheaf.pullbackObjIso_hom_fst` and
  `CategoryTheory.Sheaf.pullbackObjIso_hom_snd`: the identification commutes with the two
  projections.

## Implementation notes

The isomorphism is `CategoryTheory.Limits.PreservesPullback.iso` at
`CategoryTheory.sheafToPresheaf`, whose limit preservation comes from
`CategoryTheory.sheafToPresheaf` creating limits. What the restatement adds is the type:
`CategoryTheory.sheafToPresheaf` applied to an object is its underlying presheaf and applied to
a morphism is the underlying natural transformation, both by definition, but neither
syntactically, so the general comparison does not match a goal about `X.obj` and `f.hom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The underlying presheaf of a fibre product of sheaves of types is the fibre product of the
underlying presheaves: `(pullback t a).obj ≅ pullback t.hom a.hom`. -/
noncomputable def Sheaf.pullbackObjIso [HasPullbacks (Sheaf J (Type w))]
    {A X G : Sheaf J (Type w)} (t : A ⟶ X) (a : G ⟶ X) :
    (pullback t a).obj ≅ pullback t.hom a.hom :=
  PreservesPullback.iso (sheafToPresheaf J (Type w)) t a

/-- The identification `Sheaf.pullbackObjIso` followed by the first projection of the presheaf
fibre product is the underlying morphism of the first projection of the sheaf fibre product. -/
@[simp]
lemma Sheaf.pullbackObjIso_hom_fst [HasPullbacks (Sheaf J (Type w))]
    {A X G : Sheaf J (Type w)} (t : A ⟶ X) (a : G ⟶ X) :
    (Sheaf.pullbackObjIso t a).hom ≫ pullback.fst t.hom a.hom = (pullback.fst t a).hom :=
  PreservesPullback.iso_hom_fst (sheafToPresheaf J (Type w)) t a

/-- The identification `Sheaf.pullbackObjIso` followed by the second projection of the presheaf
fibre product is the underlying morphism of the second projection of the sheaf fibre product. -/
@[simp]
lemma Sheaf.pullbackObjIso_hom_snd [HasPullbacks (Sheaf J (Type w))]
    {A X G : Sheaf J (Type w)} (t : A ⟶ X) (a : G ⟶ X) :
    (Sheaf.pullbackObjIso t a).hom ≫ pullback.snd t.hom a.hom = (pullback.snd t a).hom :=
  PreservesPullback.iso_hom_snd (sheafToPresheaf J (Type w)) t a

end CategoryTheory

end
