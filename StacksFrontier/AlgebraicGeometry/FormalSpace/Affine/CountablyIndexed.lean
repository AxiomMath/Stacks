module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Countably indexed affine formal algebraic spaces

An affine formal algebraic space is *countably indexed* when it admits a presentation by a
sequence `X_0 ⊆ X_1 ⊆ ⋯` of affine schemes and thickenings. This is one of several equivalent
conditions: a presentation indexed by an arbitrary countable directed preorder can always be
replaced by a sequential one, because a countable directed preorder admits a monotone cofinal
sequence and a cofinal reindexing does not change a colimit.

## Main definitions

* `AlgebraicGeometry.IsCountablyIndexed`: existence of a sequential affine presentation by
  thickenings.

## Main results

* `AlgebraicGeometry.exists_sequential_presentation_iff_exists_countable_presentation`: a
  sequential affine presentation by thickenings exists exactly when a presentation indexed by
  a countable nonempty directed preorder does.

## Implementation notes

Both presentations use the affine objects of the chosen big fppf site of `S` and the sheaves
they represent, and each identifies the given sheaf with the colimit only up to isomorphism.
The predicate is stated for an arbitrary sheaf rather than only for an affine formal
algebraic space, since the existence of a sequential presentation makes sense without the
set-theoretic condition; applications combine it with
`AlgebraicGeometry.IsAffineFormalAlgebraicSpace`.

## References

* [Stacks Project, Tag 0AII](https://stacks.math.columbia.edu/tag/0AII)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0AIJ.** A sheaf on the big fppf site of `S` is *countably indexed* when it is
the colimit of a sequence of sheaves represented by affine schemes whose transition
morphisms are thickenings. -/
@[stacks 0AIJ]
abbrev IsCountablyIndexed (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) : Prop :=
  ∃ D : ℕ ⥤ BigAffineFppf B S hS,
    (∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
      Nonempty (X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

/-- Restricting a colimit presentation along a final functor does not change the colimit. -/
private theorem nonempty_iso_colimit_comp_final {C J I : Type*} [Category C] [Category J]
    [Category I] {Y : C} (e : J ⥤ I) [e.Final] (F : I ⥤ C) [HasColimit F]
    (h : Nonempty (Y ≅ colimit F)) : Nonempty (Y ≅ colimit (e ⋙ F)) :=
  h.map fun h => h ≪≫ (Functor.Final.colimitIso e F).symm

/-- **Stacks 0AII.** A sequential affine presentation by thickenings exists exactly when a
countably indexed directed affine presentation by thickenings exists. -/
@[stacks 0AII]
theorem exists_sequential_presentation_iff_exists_countable_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :
    (∃ D : ℕ ⥤ BigAffineFppf B S hS,
      (∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
        Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
        Nonempty (X ≅ colimit
          (D ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)))) ↔
    (∃ (I : Type (u + 1)) (pre : Preorder I),
      letI : Preorder I := pre
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧ Countable I ∧
        ∃ D : I ⥤ BigAffineFppf B S hS,
          (∀ ⦃i j : I⦄ (f : i ⟶ j),
            Stacks.Thickenings.IsThickening
              ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
            Nonempty (X ≅ colimit
              (D ⋙ BigAffineFppf.inclusion B S hS ⋙
                Sheaf.sheafifiedYoneda
                  (BigFppfOver.topology B S hS)))) := by
  classical
  constructor
  · rintro ⟨D, hthick, hcolim⟩
    refine ⟨ULift.{u + 1, 0} ℕ, inferInstance, ?_⟩
    have hc : Monotone (ULift.down : ULift.{u + 1, 0} ℕ → ℕ) := fun _ _ h => h
    let e := hc.functor
    have : Functor.Final e := hc.final_functor_iff.mpr fun n => ⟨ULift.up n, le_rfl⟩
    exact ⟨⟨ULift.up 0⟩, inferInstance, inferInstance, e ⋙ D, fun ⦃_ _⦄ f => hthick (e.map f),
      nonempty_iso_colimit_comp_final e _ hcolim⟩
  · rintro ⟨I, pre, hI, hdir, hcnt, D, hthick, hcolim⟩
    obtain ⟨c, hc, hcof⟩ := exists_monotone_cofinal_nat (I := I)
    let e := hc.functor
    have : Functor.Final e := hc.final_functor_iff.mpr hcof
    exact ⟨e ⋙ D, fun ⦃_ _⦄ f => hthick (e.map f), nonempty_iso_colimit_comp_final e _ hcolim⟩

end AlgebraicGeometry
