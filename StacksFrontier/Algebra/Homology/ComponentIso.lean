module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# A single degree of an isomorphism of complexes of abelian groups

An isomorphism `e : A ≅ B` of homological complexes of abelian groups is in particular, in each
degree `n`, an isomorphism `A.X n ≅ B.X n` of abelian groups, namely the image of `e` under the
evaluation functor in degree `n`. This file names that isomorphism and records the two
round-trip identities on elements, stated for the degreewise components `e.hom.f n` and
`e.inv.f n`, and the injectivity of its forward map.

## Main definitions

* `Stacks.Homology.componentIso`: the degree-`n` component of an isomorphism of homological
  complexes of abelian groups, as an isomorphism of abelian groups.

## Main results

* `Stacks.Homology.componentIso_inv_hom_apply` and
  `Stacks.Homology.componentIso_hom_inv_apply`: the two round-trip identities on elements.
* `Stacks.Homology.componentIso_hom_injective`: in each degree the forward map of an
  isomorphism of complexes of abelian groups is injective on elements.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Homology

/-- A degree of an isomorphism of complexes of abelian groups, as an isomorphism of abelian
groups. -/
abbrev componentIso {c : ComplexShape ℤ} {A B : HomologicalComplex AddCommGrpCat.{u} c}
    (e : A ≅ B) (n : ℤ) : A.X n ≅ B.X n :=
  (HomologicalComplex.eval AddCommGrpCat c n).mapIso e

/-- In a fixed degree, the inverse of an isomorphism of complexes of abelian groups is a
section of its direct image on elements. -/
lemma componentIso_inv_hom_apply {c : ComplexShape ℤ}
    {A B : HomologicalComplex AddCommGrpCat.{u} c} (e : A ≅ B) (n : ℤ) (x : B.X n) :
    (e.hom.f n).hom ((e.inv.f n).hom x) = x :=
  (componentIso e n).inv_hom_id_apply x

/-- In a fixed degree, the inverse of an isomorphism of complexes of abelian groups is a
retraction of its direct image on elements. -/
lemma componentIso_hom_inv_apply {c : ComplexShape ℤ}
    {A B : HomologicalComplex AddCommGrpCat.{u} c} (e : A ≅ B) (n : ℤ) (x : A.X n) :
    (e.inv.f n).hom ((e.hom.f n).hom x) = x :=
  (componentIso e n).hom_inv_id_apply x

/-- In a fixed degree, an isomorphism of complexes of abelian groups is injective on
elements. -/
lemma componentIso_hom_injective {c : ComplexShape ℤ}
    {A B : HomologicalComplex AddCommGrpCat.{u} c} (e : A ≅ B) (n : ℤ) :
    Function.Injective (e.hom.f n).hom := by
  intro x y h
  simpa only [componentIso_hom_inv_apply] using congrArg (e.inv.f n).hom h

end Stacks.Homology
