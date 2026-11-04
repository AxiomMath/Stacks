module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.Properties.QuasicoherentAlgebra

/-!
# Approximating a quasi-coherent algebra by algebras of finite presentation

A quasi-coherent sheaf of algebras is *approximated* by algebras of finite presentation when it
is the colimit of a system, indexed by a directed partially ordered set, of quasi-coherent
algebras of finite presentation. This file defines that datum and its operations: descending a
map out of the algebra along the system, reindexing a filtered system over a directed order,
transport along an isomorphism, and the tautological approximation of an algebra that is already
of finite presentation.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.FinitePresentationApproximation` is the datum
  of a directed system of quasi-coherent algebras of finite presentation with colimit the given
  algebra.
* `Stacks.RelativeSpec.AlgebraSheaf.FinitePresentationApproximation.desc` descends
  a compatible family of maps out of the terms to a map out of the algebra, and
  `Stacks.RelativeSpec.AlgebraSheaf.FinitePresentationApproximation.coconePointIso`
  identifies the colimit of the system with the algebra.
* `Stacks.RelativeSpec.AlgebraSheaf.IsDirectedColimitOfFinitePresentation` is the
  existence of such an approximation.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.IsDirectedColimitOfFinitePresentation.of_isFiltered` builds
  an approximation out of a colimit over an arbitrary filtered category.
* `Stacks.RelativeSpec.AlgebraSheaf.FinitePresentationApproximation.self` shows an
  algebra that is itself quasi-coherent of finite presentation is approximated by itself.
* `Stacks.RelativeSpec.AlgebraSheaf.IsDirectedColimitOfFinitePresentation.exists_directedSystem`
  unfolds an approximation into the existential form of the statement.
* `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation.of_iso` shows finite
  presentation of an algebra depends only on its isomorphism class.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-- Finite presentation of a sheaf of `O_X`-algebras only depends on its isomorphism class. -/
public lemma IsFinitePresentation.of_iso {A B : AlgebraSheaf X} (e : A ≅ B)
    (h : IsFinitePresentation A) : IsFinitePresentation B := by
  intro U hU
  have hcomp : B.hom.hom.app (.op U) = A.hom.hom.app (.op U) ≫ e.hom.right.hom.app (.op U) := by
    rw [← Under.w e.hom]; rfl
  rw [hcomp, CommRingCat.hom_comp]
  exact RingHom.finitePresentation_respectsIso.1 _
    ((((sheafToPresheaf _ CommRingCat).mapIso ((Under.forget X.sheaf).mapIso e)).app
      (.op U)).commRingCatIsoToRingEquiv) (h U hU)

/-- A presentation of a sheaf of `O_X`-algebras `A` as a directed colimit of quasi-coherent
`O_X`-algebras of finite presentation: a directed partially ordered set, a system of algebras
over it, maps from the terms of the system to `A` making the resulting cocone colimiting, and
quasi-coherence and finite presentation for each term. -/
public structure FinitePresentationApproximation (A : AlgebraSheaf X) where
  /-- The indexing set of the system. -/
  index : Type w
  /-- The partial order on the indexing set. -/
  [partialOrder : PartialOrder index]
  /-- The indexing set is nonempty. -/
  [nonempty : Nonempty index]
  /-- The indexing set is directed. -/
  [isDirected : IsDirected index (· ≤ ·)]
  /-- The system of algebras. -/
  diagram : index ⥤ AlgebraSheaf X
  /-- The maps from the terms of the system to `A`. -/
  toTarget : diagram ⟶ (Functor.const index).obj A
  /-- Each term of the system is quasi-coherent. -/
  isQuasicoherent (i : index) : IsQuasicoherent (diagram.obj i)
  /-- Each term of the system is of finite presentation. -/
  isFinitePresentation (i : index) : IsFinitePresentation (diagram.obj i)
  /-- The maps to `A` exhibit `A` as the colimit of the system. -/
  isColimit : IsColimit (Cocone.mk A toTarget)

namespace FinitePresentationApproximation

attribute [instance] partialOrder nonempty isDirected

variable {A B : AlgebraSheaf X}

/-- The colimiting cocone of an approximation. -/
public abbrev cocone (a : FinitePresentationApproximation.{w} A) : Cocone a.diagram :=
  Cocone.mk A a.toTarget

/-- The map to `A` from the term of the system at an index. -/
public abbrev hom (a : FinitePresentationApproximation.{w} A) (i : a.index) :
    a.diagram.obj i ⟶ A :=
  a.toTarget.app i

/-- The maps to `A` from the terms of the system are compatible with its transition maps. -/
@[reassoc (attr := simp)]
public lemma map_hom (a : FinitePresentationApproximation.{w} A) {i j : a.index} (f : i ⟶ j) :
    a.diagram.map f ≫ a.hom j = a.hom i := by
  simp

/-- Any two indices of an approximation are dominated by a third. -/
public lemma exists_ge_ge (a : FinitePresentationApproximation.{w} A) (i j : a.index) :
    ∃ k, i ≤ k ∧ j ≤ k :=
  directed_of (· ≤ ·) i j

/-- A compatible family of maps out of the terms of the system descends to a map out of `A`. -/
public noncomputable def desc (a : FinitePresentationApproximation.{w} A)
    {T : AlgebraSheaf X} (s : ∀ i, a.diagram.obj i ⟶ T)
    (hs : ∀ ⦃i j : a.index⦄ (f : i ⟶ j), a.diagram.map f ≫ s j = s i) : A ⟶ T :=
  a.isColimit.desc (Cocone.mk T { app := s, naturality := fun _ _ f ↦ by simpa using hs f })

/-- The map descended from a compatible family restricts to that family on each term of the
system. -/
@[reassoc (attr := simp)]
public lemma hom_desc (a : FinitePresentationApproximation.{w} A)
    {T : AlgebraSheaf X} (s : ∀ i, a.diagram.obj i ⟶ T)
    (hs : ∀ ⦃i j : a.index⦄ (f : i ⟶ j), a.diagram.map f ≫ s j = s i) (i : a.index) :
    a.hom i ≫ a.desc s hs = s i :=
  a.isColimit.fac _ i

/-- Two maps out of `A` agree as soon as they agree on every term of the system. -/
public lemma hom_ext (a : FinitePresentationApproximation.{w} A)
    {T : AlgebraSheaf X} {f g : A ⟶ T} (h : ∀ i, a.hom i ≫ f = a.hom i ≫ g) : f = g :=
  a.isColimit.hom_ext h

/-- The colimit of the system of an approximation is identified with `A`. -/
public noncomputable def coconePointIso (a : FinitePresentationApproximation.{w} A)
    [HasColimit a.diagram] : colimit a.diagram ≅ A :=
  (colimit.isColimit a.diagram).coconePointUniqueUpToIso a.isColimit

/-- The identification of the colimit with `A` carries each colimit inclusion to the map to `A`
from the corresponding term of the system. -/
@[reassoc (attr := simp)]
public lemma ι_coconePointIso_hom (a : FinitePresentationApproximation.{w} A)
    [HasColimit a.diagram] (i : a.index) :
    colimit.ι a.diagram i ≫ a.coconePointIso.hom = a.hom i :=
  (colimit.isColimit a.diagram).comp_coconePointUniqueUpToIso_hom a.isColimit i

/-- An approximation of `A` is an approximation of any algebra isomorphic to `A`. -/
public noncomputable def ofIso (a : FinitePresentationApproximation.{w} A) (e : A ≅ B) :
    FinitePresentationApproximation.{w} B where
  index := a.index
  diagram := a.diagram
  toTarget := a.toTarget ≫ (Functor.const a.index).map e.hom
  isQuasicoherent := a.isQuasicoherent
  isFinitePresentation := a.isFinitePresentation
  isColimit := a.isColimit.ofIsoColimit (Cocone.ext e (by simp))

/-- A quasi-coherent algebra of finite presentation is approximated by itself. -/
public noncomputable def self (A : AlgebraSheaf X) (hq : IsQuasicoherent A)
    (hfp : IsFinitePresentation A) : FinitePresentationApproximation.{w} A where
  index := PUnit.{w + 1}
  diagram := (Functor.const _).obj A
  toTarget := 𝟙 _
  isQuasicoherent _ := hq
  isFinitePresentation _ := hfp
  isColimit :=
    { desc s := s.ι.app ⟨⟩
      fac s := fun ⟨⟩ ↦ by simp
      uniq s m hm := by simpa using hm ⟨⟩ }

end FinitePresentationApproximation

/-- A sheaf of `O_X`-algebras is a directed colimit of quasi-coherent algebras of finite
presentation when it admits an approximation by such algebras. -/
public def IsDirectedColimitOfFinitePresentation (A : AlgebraSheaf X) : Prop :=
  Nonempty (FinitePresentationApproximation.{w} A)

namespace IsDirectedColimitOfFinitePresentation

variable {A : AlgebraSheaf X}

/-- The existential form of the statement: a directed set, a system over it of quasi-coherent
algebras of finite presentation, and maps to `A` inducing an isomorphism from the colimit. -/
public lemma exists_directedSystem (h : IsDirectedColimitOfFinitePresentation.{w} A) :
    ∃ (I : Type w) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ AlgebraSheaf X) (φ : F ⟶ (Functor.const I).obj A),
      (∀ i, IsQuasicoherent (F.obj i) ∧ IsFinitePresentation (F.obj i)) ∧
        Nonempty (IsColimit (Cocone.mk A φ)) :=
  let a := h.some
  ⟨a.index, a.partialOrder, a.nonempty, a.isDirected, a.diagram, a.toTarget,
    fun i ↦ ⟨a.isQuasicoherent i, a.isFinitePresentation i⟩, ⟨a.isColimit⟩⟩

/-- A system over an arbitrary filtered category whose colimit is `A` exhibits `A` as a directed
colimit of quasi-coherent algebras of finite presentation. -/
public lemma of_isFiltered {J : Type w} [SmallCategory J] [IsFiltered J]
    {G : J ⥤ AlgebraSheaf X} (ψ : G ⟶ (Functor.const J).obj A)
    (hq : ∀ j, IsQuasicoherent (G.obj j)) (hfp : ∀ j, IsFinitePresentation (G.obj j))
    (hc : IsColimit (Cocone.mk A ψ)) : IsDirectedColimitOfFinitePresentation.{w} A := by
  obtain ⟨α, _, _, _, e, _⟩ := IsFiltered.exists_directed J
  exact ⟨{ index := α
           diagram := e ⋙ G
           toTarget := Functor.whiskerLeft e ψ
           isQuasicoherent := fun _ ↦ hq _
           isFinitePresentation := fun _ ↦ hfp _
           isColimit := (Functor.Final.isColimitWhiskerEquiv e _).symm hc }⟩

/-- An algebra that is quasi-coherent and of finite presentation is a directed colimit of
quasi-coherent algebras of finite presentation. -/
public lemma of_isFinitePresentation (hq : IsQuasicoherent A)
    (hfp : IsFinitePresentation A) : IsDirectedColimitOfFinitePresentation.{w} A :=
  ⟨.self A hq hfp⟩

end IsDirectedColimitOfFinitePresentation

end Stacks.RelativeSpec.AlgebraSheaf

end
