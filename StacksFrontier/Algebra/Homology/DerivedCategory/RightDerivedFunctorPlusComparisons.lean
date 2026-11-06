module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow

/-!
# Two comparisons of right derived functors on the bounded below derived category

Let `𝒜`, `ℬ`, `𝒞` be abelian categories with derived categories, and `𝒜`, `ℬ` with enough
injectives. This file records the two isomorphisms between right derived functors on `D⁺` that
are needed to recognise a right derived functor one has built as the one a statement names.

The first says that right derivation only sees a functor up to isomorphism: an isomorphism
`F ≅ G` of additive functors `𝒜 ⥤ ℬ` induces an isomorphism `RF ≅ RG` of functors
`D⁺(𝒜) ⥤ D⁺(ℬ)`. The second is the isomorphism `R(G ∘ F) ≅ RF ⋙ RG` of [Stacks, Tag 015M]
under that tag's own hypothesis — `F(I)` right acyclic for `G` for every injective `I` of `𝒜` —
rather than under the stronger hypothesis that `F` preserve injective objects, which is what
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` assumes.

Both are obtained from existing material. The first is `Functor.rightDerivedNatIso`, the
uniqueness of right derived functors, applied to the isomorphism of functors
`K⁺(𝒜) ⥤ D⁺(ℬ)` induced by `F ≅ G`; that isomorphism is
`Functor.mapHomotopyCategoryPlusNatTrans` at the two directions of `F ≅ G`, assembled through
the fully faithful inclusion `K⁺(ℬ) ⥤ K(ℬ)` exactly as
`Functor.mapHomotopyCategoryPlusCompIso` is. The second is
`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` ([Stacks, Tag 015M]) applied to
the canonical transformation `CategoryTheory.Functor.rightDerivedFunctorPlusComp` and its
characterising factorization `rightDerivedFunctorPlusComp_fac`.

## Main definitions

* `CategoryTheory.Functor.mapHomotopyCategoryNatIso` and
  `CategoryTheory.Functor.mapHomotopyCategoryPlusNatIso`: the action of an isomorphism of
  additive functors on homotopy categories, and on bounded below homotopy categories.
* `CategoryTheory.Functor.rightDerivedFunctorPlusNatIso`: **the right derived functor on `D⁺`
  depends on the functor only up to isomorphism.**
* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`: **`R(G ∘ F) ≅ RF ⋙ RG`
  under the acyclicity hypothesis of [Stacks, Tag 015M].**

## Main results

* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusComp_of_rightAcyclic`: the canonical
  transformation `R(G ∘ F) ⟶ RF ⋙ RG` is invertible as soon as `F` carries injective objects to
  objects right acyclic for `G`.

## Implementation notes

Nothing here carries a Stacks tag. The acyclicity criterion is 015M and is tagged at
`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective`; this file only packages one
direction of it as data, which is what a consumer identifying an abutment needs.

## References

* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### An isomorphism of functors on homotopy categories -/

section HomotopyCategoryPlus

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B]

/-- The action on homotopy categories of an isomorphism of additive functors. -/
def mapHomotopyCategoryNatIso {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G)
    {ι : Type*} (c : ComplexShape ι) :
    F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- The action on bounded below homotopy categories of an isomorphism of additive functors.
It is the isomorphism on all of `K(ℬ)` read through the fully faithful inclusion of the
bounded below part, as `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso` is. -/
def mapHomotopyCategoryPlusNatIso {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategoryPlus ≅ G.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus B).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι A)
      (mapHomotopyCategoryNatIso e (ComplexShape.up ℤ)))

end HomotopyCategoryPlus

/-! ### Invariance of the right derived functor -/

section Invariance

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  [EnoughInjectives A]

/-- **The right derived functor on the bounded below derived category depends on the functor
only up to isomorphism**: an isomorphism `F ≅ G` of additive functors `𝒜 ⥤ ℬ` induces an
isomorphism `RF ≅ RG` of functors `D⁺(𝒜) ⥤ D⁺(ℬ)`.

This is the uniqueness of right derived functors, `Functor.rightDerivedNatIso`: the units of
`RF` and of `RG` exhibit both as right derived functors along `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)` of the two
isomorphic functors `K⁺(𝒜) ⥤ D⁺(ℬ)` induced by `F` and by `G`. -/
def rightDerivedFunctorPlusNatIso {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus :=
  rightDerivedNatIso _ _ F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
    (isoWhiskerRight (mapHomotopyCategoryPlusNatIso e) DerivedCategory.Plus.Qh)

end Invariance

/-! ### The composition isomorphism under the acyclicity hypothesis -/

section AcyclicComposition

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w''} C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [EnoughInjectives A] [EnoughInjectives B]

/-- The canonical transformation `R(G ∘ F) ⟶ RF ⋙ RG` of [Stacks, Tag 05T2] is invertible as
soon as `F` carries every injective object of `𝒜` to an object right acyclic for `G`. This is
the easy direction of [Stacks, Tag 015M], applied to the transformation
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`, whose characterising factorization is
`rightDerivedFunctorPlusComp_fac`. -/
theorem isIso_rightDerivedFunctorPlusComp_of_rightAcyclic
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) :
    IsIso (rightDerivedFunctorPlusComp F G) :=
  (isIso_iff_rightAcyclic_obj_injective F G (rightDerivedFunctorPlusComp F G)
    (rightDerivedFunctorPlusComp_fac F G)).2 hFG

/-- **`R(G ∘ F) ≅ RF ⋙ RG` under the acyclicity hypothesis of [Stacks, Tag 015M]**, with the
canonical transformation of [Stacks, Tag 05T2] as its `hom`. This is the form
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` takes when `F` is not assumed to
preserve injective objects, only to carry them to objects right acyclic for `G`. -/
def rightDerivedFunctorPlusCompIsoOfRightAcyclic
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  have := isIso_rightDerivedFunctorPlusComp_of_rightAcyclic F G hFG
  asIso (rightDerivedFunctorPlusComp F G)

end AcyclicComposition

end CategoryTheory.Functor

end
