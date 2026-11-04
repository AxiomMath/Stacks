module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
import all StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusOpen

/-!
# A full subcategory cut out by an open locus on every scheme-valued point

Let `𝒴` be a category over the big fppf site of a scheme `S` and let `Q` be a property of its
objects, closed under isomorphism. Suppose that every scheme-valued point `y` of `𝒴` over an
object `U` of the site cuts out an open subscheme `V ⊆ U` through which an object `T` of the big
fppf site of `U` maps exactly when `y(T)` has `Q`. Then the inclusion of the full subcategory on
`Q` is representable by algebraic spaces, and it is an open immersion in the sense of
Stacks 04XB: every 2-fibre product of it with a scheme-valued point is represented by the open
subscheme `V`, and every algebraic space representing such a 2-fibre product is isomorphic to
`V`.

This is the argument the source gives for Stacks 06CL, and the one it gives, through
Stacks 06FJ, for the open substack attached to an open subset of the points of an algebraic
stack; it is stated here once, for an arbitrary property.

## Main results

* `AlgebraicGeometry.Stack.exists_isOpenImmersion_equivalenceOver_of_openLocus`: the 2-fibre
  product of the inclusion with a scheme-valued point is equivalent, over the big fppf site of
  the base, to the category of elements of the open subscheme cut out by the locus.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_openLocus`: the inclusion is
  representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isOpenImmersion_of_openLocus`: the inclusion is an open immersion in
  the sense of Stacks 04XB, written out.

## Implementation notes

Representability is the comparison of two categories over the big fppf site of the base: the
first projection of the 2-fibre product of the inclusion with a scheme-valued point, which is
fully faithful because the inclusion of a full subcategory is, and the category of elements of
the sheaf of points of the open subscheme `V`, whose projection is fully faithful because there
is at most one morphism to `V` over `U`. Two fully faithful categories over a base with the same
image on objects are equivalent over it, and the image of the first projection is exactly the
locus — this is where invariance under isomorphism enters. The same comparison identifies
*every* algebraic space representing the 2-fibre product with `V`, which is what the
open-immersion condition of Stacks 04XB quantifies over: both presheaves take subsingleton
values and have the same support, so they are isomorphic.

The comparison lemmas for two categories over a base used here (for example
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_of_image_eq` and
`AlgebraicGeometry.Stack.full_elementsProjection`) are the private ones of
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusOpen`, reached by `import all`
rather than restated.

The structural morphism the open-immersion condition tests is the one of Stacks 04SG, replaced
by `CategoryTheory.OverShriek.relocalizeToYoneda` through
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, which is the form in which the
identification of the representing presheaf with `V` can be used.

The inclusion is taken as a `CategoryTheory.BasedFunctor` whose underlying functor is the
inclusion of the full subcategory, rather than as a 1-morphism of the 2-category of categories
fibred in groupoids, because the fibred-in-groupoids structure of the full subcategory is
typically part of what the consumer is proving.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

/-! ### The open locus -/

section OpenLocus

universe v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒴 : BasedCategory.{v, w} (BigFppfOver B S hS)} (Q : ObjectProperty 𝒴.obj)

/-- An object `T` of the big fppf site of `U` is in the image of the first projection of the
2-fibre product of the inclusion of a full subcategory closed under isomorphism with a
scheme-valued point `y` exactly when `y(T)` lies in the full subcategory. -/
theorem image_twoFibreProductFst_of_isClosedUnderIsomorphisms [Q.IsClosedUnderIsomorphisms]
    (j : BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p) ⥤ᵇ 𝒴) (hj : j.toFunctor = Q.ι)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
        𝒴.p y j.toFunctor).obj a = T) ↔
      Q (y.obj T) := by
  obtain ⟨J, hJ⟩ := j
  obtain rfl : J = Q.ι := hj
  constructor
  · rintro ⟨a, rfl⟩
    exact Q.prop_of_iso a.iso.symm a.y.property
  · intro hT
    refine ⟨{ base := 𝒴.p.obj (y.obj T)
              x := T
              y := ⟨y.obj T, hT⟩
              hx := (congrArg (fun G => G.obj T) hy).symm
              hy := rfl
              iso := Iso.refl _
              vertical := IsHomLift.id rfl }, rfl⟩

variable (B S hS)

/-- The first projection of the 2-fibre product of the inclusion of a full subcategory with a
scheme-valued point is fully faithful. -/
private theorem full_faithful_twoFibreProductFst_of_eq_ι
    (j : BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p) ⥤ᵇ 𝒴) (hj : j.toFunctor = Q.ι)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) :
    (TwoFibreProductOver.fst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
      𝒴.p y j.toFunctor).Full ∧
    (TwoFibreProductOver.fst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
      𝒴.p y j.toFunctor).Faithful := by
  have : j.toFunctor.Full := by
    rw [hj]
    exact ObjectProperty.full_ι Q
  have : j.toFunctor.Faithful := by
    rw [hj]
    exact ObjectProperty.faithful_ι Q
  exact ⟨full_twoFibreProductFst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
    𝒴.p y j.toFunctor hy j.w, faithful_twoFibreProductFst (Over.map U.hom)
    (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p 𝒴.p y j.toFunctor⟩

/-- **The 2-fibre product with a scheme-valued point is the open subscheme cut out by the
locus.** The first projection of the 2-fibre product is fully faithful because the inclusion of a
full subcategory is, and the category of elements of the sheaf of points of an open subscheme has
fully faithful projection because there is at most one morphism to an open subscheme; the two
have the same image on objects, so they are equivalent over the big fppf site of the base. -/
theorem exists_isOpenImmersion_equivalenceOver_of_openLocus [Q.IsClosedUnderIsomorphisms]
    (j : BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p) ⥤ᵇ 𝒴) (hj : j.toFunctor = Q.ι)
    (hopen : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj),
      y ⋙ 𝒴.p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
          ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ Q (y.obj T))
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
            𝒴.p y j.toFunctor)
        (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) := by
  obtain ⟨V, hV, hVlocus⟩ := hopen U y hy
  obtain ⟨_, _⟩ := full_faithful_twoFibreProductFst_of_eq_ι B S hS Q j hj U y hy
  have _ := full_elementsProjection (yoneda.obj V)
    (fun T ↦ subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop)
  have _ := faithful_elementsProjection (yoneda.obj V)
  refine ⟨V, hV, nonempty_equivalenceOver_of_image_eq _ _ fun T ↦ ?_⟩
  rw [image_twoFibreProductFst_of_isClosedUnderIsomorphisms Q j hj U y hy T,
    image_elementsProjection]
  exact (hVlocus T).symm

/-- **The inclusion of a full subcategory cut out by an open locus is representable by algebraic
spaces**, the representing algebraic space of a base change being the open subscheme of the base
cut out by the locus. -/
theorem isRepresentableByAlgebraicSpaces_of_openLocus [Q.IsClosedUnderIsomorphisms]
    (j : BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p) ⥤ᵇ 𝒴) (hj : j.toFunctor = Q.ι)
    (hopen : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj),
      y ⋙ 𝒴.p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
          ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ Q (y.obj T)) :
    IsRepresentableByAlgebraicSpaces B S hS j := by
  intro U
  dsimp only
  intro y hy
  obtain ⟨V, _, he⟩ :=
    exists_isOpenImmersion_equivalenceOver_of_openLocus B S hS Q j hj hopen U y hy
  exact ⟨yoneda.obj V, isAlgebraicSpace_yoneda B U.left.1 U.left.2 V, he⟩

/-- Every algebraic space representing a base change of the inclusion of a full subcategory cut
out by an open locus is the open subscheme of the base cut out by the locus: both presheaves take
subsingleton values and have the same support. -/
theorem exists_iso_yoneda_of_equivalenceOver_of_openLocus [Q.IsClosedUnderIsomorphisms]
    (j : BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p) ⥤ᵇ 𝒴) (hj : j.toFunctor = Q.ι)
    (hopen : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj),
      y ⋙ 𝒴.p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
          ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ Q (y.obj T))
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (hy : y ⋙ 𝒴.p = Over.map U.hom)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
          𝒴.p y j.toFunctor)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
      Nonempty (P ≅ yoneda.obj V) := by
  obtain ⟨V, hV, hVlocus⟩ := hopen U y hy
  obtain ⟨_, _⟩ := full_faithful_twoFibreProductFst_of_eq_ι B S hS Q j hj U y hy
  have _ := full_of_equivalenceOver e
  refine ⟨V, hV, nonempty_iso_of_subsingleton P (yoneda.obj V)
    (subsingleton_of_full_elementsProjection P)
    (fun T ↦ subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop) fun T ↦ ?_⟩
  rw [← image_elementsProjection P T.unop, ← image_equivalenceOver e T.unop,
    image_twoFibreProductFst_of_isClosedUnderIsomorphisms Q j hj U y hy T.unop]
  exact (hVlocus T.unop).symm

/-- **The inclusion of a full subcategory cut out by an open locus is an open immersion**: every
algebraic space representing a base change of it along a scheme-valued point has open immersion
structural morphism, read as a morphism of algebraic spaces over `S`. This is the condition of
Stacks 04XB at `AlgebraicGeometry.Space.IsOpenImmersion`, written out. -/
theorem isOpenImmersion_of_openLocus [Q.IsClosedUnderIsomorphisms]
    (j : BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p) ⥤ᵇ 𝒴) (hj : j.toFunctor = Q.ι)
    (hopen : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj),
      y ⋙ 𝒴.p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
          ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ Q (y.obj T)) :
    ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj),
      y ⋙ 𝒴.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) (BasedCategory.ofFunctor (Q.ι ⋙ 𝒴.p)).p
              𝒴.p y j.toFunctor)
          (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsOpenImmersion B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  intro U y hy P hP he
  obtain ⟨V, hV, ⟨i⟩⟩ :=
    exists_iso_yoneda_of_equivalenceOver_of_openLocus B S hS Q j hj hopen U y hy P he.some
  exact isOpenImmersion_algebraicSpaceMap_of_iso_yoneda B S hS U P hP V i hV

end OpenLocus

end AlgebraicGeometry.Stack

end
