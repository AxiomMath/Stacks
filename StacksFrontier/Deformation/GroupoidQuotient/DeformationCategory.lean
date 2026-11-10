module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.GroupoidQuotient.RimSchlessinger
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Deformation categories as quotients of groupoids in functors

The quotient of a smooth groupoid in functors on the category of Artinian local algebras is a
deformation category as soon as its functors of objects and of arrows are deformation functors.

The quotient is the Grothendieck construction of the pointwise groupoids and its structure map
is the canonical projection to the base category. The predeformation half comes from the
deformation-functor conditions on objects and arrows: they make the fibre over the residue field
equivalent to the one-object, one-arrow category. The Rim–Schlessinger half is
`Deformation.quotient_satisfiesRS`.

## Main results

* `Deformation.quotient_isPredeformationCategory`: the quotient of a groupoid in deformation
  functors is a predeformation category.
* `Deformation.quotient_isDeformationCategory`: the quotient of a smooth groupoid in
  deformation functors is a deformation category.

## References

* [Stacks Project, Tag 06KU](https://stacks.math.columbia.edu/tag/06KU)
-/

@[expose] public section

namespace Deformation

/-! ### The quotient of a groupoid in deformation functors -/

section
open CategoryTheory

universe u v w t

/-- Fibre objects over the residue field are all of the form `⟨⟨A, x⟩, rfl⟩`. -/
private theorem quotientFiber_induction
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, _, t} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    {P : (Grothendieck.forget (evaluationFunctor G)).Fiber (residueFieldObject Λ k) → Prop}
    (h : ∀ x : G.objects.obj (residueFieldObject Λ k),
      P ⟨⟨residueFieldObject Λ k, x⟩, rfl⟩) (X) : P X := by
  rcases X with ⟨⟨B, x⟩, hX⟩
  change B = residueFieldObject Λ k at hX
  subst hX
  exact h x

private theorem quotientFiber_hom_subsingleton
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, _, t} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hR : Nonempty (Unique (G.arrows.obj (residueFieldObject Λ k)))) :
    ∀ (X Y : (Grothendieck.forget (evaluationFunctor G)).Fiber
      (residueFieldObject Λ k)) (f g : X ⟶ Y), f = g := by
  let A := residueFieldObject Λ k
  refine quotientFiber_induction G fun x => quotientFiber_induction G fun y => ?_
  intro f g
  apply Functor.Fiber.hom_ext
  change f.1 = g.1
  let _ : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 A) f.1 := f.2
  let _ : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 A) g.1 := g.2
  have hfbase := IsHomLift.fac' (Grothendieck.forget (evaluationFunctor G)) (𝟙 A) f.1
  have hgbase := IsHomLift.fac' (Grothendieck.forget (evaluationFunctor G)) (𝟙 A) g.1
  have hbase : f.1.base = g.1.base := hfbase.trans hgbase.symm
  refine Grothendieck.ext f.1 g.1 hbase ?_
  let _ : Unique (G.arrows.obj A) := hR.some
  let _ : Subsingleton
      (((evaluationFunctor G).map g.1.base).toFunctor.obj x ⟶ y) :=
    ⟨fun a b => (G.evaluationArrowEquiv A _ _).injective
      (Subtype.ext (Subsingleton.elim _ _))⟩
  exact Subsingleton.elim _ _

private theorem quotientFiber_nonempty_and_hom_unique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, _, t} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hU : Nonempty (Unique (G.objects.obj (residueFieldObject Λ k))))
    (hR : Nonempty (Unique (G.arrows.obj (residueFieldObject Λ k)))) :
    Nonempty ((Grothendieck.forget (evaluationFunctor G)).Fiber
      (residueFieldObject Λ k)) ∧
      ∀ X Y : (Grothendieck.forget (evaluationFunctor G)).Fiber
        (residueFieldObject Λ k), Nonempty (Unique (X ⟶ Y)) := by
  let A := residueFieldObject Λ k
  let _ : Unique (G.objects.obj A) := hU.some
  let _ : Unique (G.arrows.obj A) := hR.some
  let x : G.objects.obj A := default
  let X : (Grothendieck.forget (evaluationFunctor G)).Fiber A := ⟨⟨A, x⟩, rfl⟩
  refine ⟨⟨X⟩, ?_⟩
  refine quotientFiber_induction G fun x => quotientFiber_induction G fun y => ?_
  have hxy : x = y := Subsingleton.elim _ _
  let X' : (Grothendieck.forget (evaluationFunctor G)).Fiber A := ⟨⟨A, x⟩, rfl⟩
  let Y' : (Grothendieck.forget (evaluationFunctor G)).Fiber A := ⟨⟨A, y⟩, rfl⟩
  let q : (⟨A, x⟩ : Grothendieck (evaluationFunctor G)) ⟶ ⟨A, y⟩ :=
    { base := 𝟙 A
      fiber := eqToHom (by simp [evaluationFunctor]) ≫ eqToHom hxy }
  have hq : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 A) q :=
    IsHomLift.of_fac' (Grothendieck.forget (evaluationFunctor G)) (𝟙 A) q rfl rfl rfl
  let m : X' ⟶ Y' := ⟨q, hq⟩
  exact ⟨⟨⟨m⟩, fun f => quotientFiber_hom_subsingleton G hR X' Y' f m⟩⟩

/-- The quotient of a groupoid in deformation functors is a predeformation category. -/
public theorem quotient_isPredeformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, _, t} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hU : IsDeformationFunctor G.objects)
    (hR : IsDeformationFunctor G.arrows) :
    IsPredeformationCategory (Grothendieck.forget (evaluationFunctor G)) := by
  refine ⟨quotientProjection_cofibered G, ?_⟩
  exact (CategoryTheory.equiv_punit_iff_unique
    (C := (Grothendieck.forget (evaluationFunctor G)).Fiber
      (residueFieldObject Λ k))).2 (quotientFiber_nonempty_and_hom_unique G hU.1 hR.1)

/-- The quotient of a smooth groupoid of deformation functors is a deformation category. -/
@[stacks 06KU "quotient_deformation_category"]
public theorem quotient_isDeformationCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, _, t} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor G.objects)
    (hR : IsDeformationFunctor G.arrows) :
    IsDeformationCategory (Grothendieck.forget (evaluationFunctor G)) :=
  ⟨quotient_isPredeformationCategory G hU hR,
    quotient_satisfiesRS G hG hU.2 hR.2⟩

end

end Deformation
