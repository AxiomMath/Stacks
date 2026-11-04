module

public import Mathlib.Algebra.Category.Grp.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# A complex of abelian sheaves with acyclic sections is acyclic

A complex of abelian sheaves on a site whose complex of sections over every object of the site is
acyclic is acyclic. The converse fails — sheaf cohomology is not sectionwise — so this is one
implication only, and it is the useful one: it reduces exactness of a complex of sheaves to a
statement about complexes of abelian groups.

The reason is that sectionwise exactness is a statement about the underlying complex of
*presheaves*, where it is exactness, because evaluation at an object of a functor category is
exact; and sheafification is exact and returns a sheaf to itself.

## Main results

* `CategoryTheory.Presheaf.jointlyFaithful_evaluation`: the evaluation functors of a category of
  abelian presheaves are jointly faithful, hence jointly reflect isomorphisms by Mathlib's
  `CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms`.
* `CategoryTheory.Presheaf.exactAt_of_sectionwise`: a complex of abelian presheaves exact on
  sections over every object is exact.
* `CategoryTheory.Sheaf.acyclic_of_sectionwise`: **a complex of abelian sheaves whose complex of
  sections over every object is acyclic is acyclic.**

## Implementation notes

The joint reflection of isomorphisms is joint faithfulness of the evaluations — a morphism of
presheaves is its family of components — together with balancedness of the abelian category of
presheaves; `CategoryTheory.JointlyReflectIsomorphisms.exactAt_iff` then detects exactness,
evaluation preserving homology because it is exact.

The passage from presheaves to sheaves is the counit of the sheafification adjunction, which is
invertible because `CategoryTheory.sheafToPresheaf` is reflective, together with left exactness
of sheafification; both are available for abelian-group-valued sheaves on any site admitting
sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The evaluation functors of a category of abelian presheaves are jointly faithful: a morphism
of presheaves is its family of components. -/
lemma jointlyFaithful_evaluation :
    JointlyFaithful
      (fun U : Cᵒᵖ => (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U) where
  map_injective h := NatTrans.ext (funext h)

/-- **A complex of abelian presheaves exact on sections over every object is exact.** -/
theorem exactAt_of_sectionwise {ι : Type*} {c : ComplexShape ι}
    (P : HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) c) (n : ι)
    (h : ∀ U : Cᵒᵖ, ((((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U).mapHomologicalComplex
      c).obj P).ExactAt n) :
    P.ExactAt n :=
  (jointlyFaithful_evaluation.jointlyReflectsIsomorphisms.exactAt_iff P n).2 h

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- **A complex of abelian sheaves whose complex of sections over every object is acyclic is
acyclic.** -/
theorem acyclic_of_sectionwise (X : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (h : ∀ U : Cᵒᵖ, (((sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).Acyclic) :
    X.Acyclic := by
  have hP : (((sheafToPresheaf J AddCommGrpCat.{w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X).Acyclic := by
    intro n
    refine Presheaf.exactAt_of_sectionwise _ n fun U => ?_
    exact (h U n).of_iso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U)) (ComplexShape.up ℤ)).app X)
  have hiso : ((presheafToSheaf J AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((sheafToPresheaf J AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X) ≅ X :=
    (Functor.mapHomologicalComplexCompIso
        (asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit)
        (ComplexShape.up ℤ)).app X ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app X
  intro n
  exact (HomologicalComplex.Acyclic.map (presheafToSheaf J AddCommGrpCat.{w}) hP n).of_iso hiso

end CategoryTheory.Sheaf

end
