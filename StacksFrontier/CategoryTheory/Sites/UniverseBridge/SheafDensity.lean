module

/-
Copyright (c) 2026 the Stacks in Lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.CategoryTheory.Sites.UniverseBridge.ShrunkGeneratedColimit
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Finite diagrams of large-valued sheaves are filtered colimits of small-valued ones

This module discharges the presentation hypothesis of
`preservesFiniteLimits_sheafPullback_of_small_presentations`, along the route the density theorem
of `ShrunkGeneratedColimit` was built for:

* a finite diagram `G : T ⥤ Sheaf J (Type (max u v))` is uncurried into a single functor
  `(T × Cᵒᵖ) ⥤ Type (max u v)` on the `u`-small category `T × Cᵒᵖ`;
* `ShrunkGeneratedColimit` presents that functor as a filtered colimit of the lifts of functors
  landing in `Type u`;
* currying is an equivalence and sheafification is a left adjoint, so both carry that colimit;
* `sheafComposeNatIso` for `uliftFunctor` moves the lift across sheafification — this is the step
  that needs `J.PreservesSheafification uliftFunctor`, which Mathlib supplies for `Type`-valued
  sheaves on a small site.

The whole comparison is assembled at the level of functors, by whiskering isomorphisms that are
already natural, so no naturality square is proved by hand here.

## Main results

* `exists_small_presentation`: the presentation hypothesis, discharged.

## References

* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Sites.UniverseBridge

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (T : Type) [SmallCategory T] [FinCategory T]

/-- The underlying presheaves of a finite diagram of sheaves, uncurried into a single functor on
the `u`-small category `T × Cᵒᵖ`. This is the functor the density theorem applies to. -/
public abbrev uncurriedDiagram (G : T ⥤ Sheaf J (Type (max u v))) :
    (T × Cᵒᵖ) ⥤ Type (max u v) :=
  Functor.uncurry.obj (G ⋙ sheafToPresheaf J (Type (max u v)))

/-- Lifting a `T`-diagram of presheaves to the larger universe, objectwise. -/
public abbrev uliftDiagramPresheaves :
    (T ⥤ Cᵒᵖ ⥤ Type u) ⥤ (T ⥤ Cᵒᵖ ⥤ Type (max u v)) :=
  (Functor.whiskeringRight T _ _).obj
    ((Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max u v))).obj uliftFunctor.{v, u})

/-- Lifting a functor on `T × Cᵒᵖ` to the larger universe. -/
public abbrev liftDiagram :
    ((T × Cᵒᵖ) ⥤ Type u) ⥤ ((T × Cᵒᵖ) ⥤ Type (max u v)) :=
  (Functor.whiskeringRight (T × Cᵒᵖ) (Type u) (Type (max u v))).obj uliftFunctor.{v, u}

/-- Sheafifying a `T`-diagram of small-valued presheaves. -/
public abbrev sheafifyDiagramSmall : (T ⥤ Cᵒᵖ ⥤ Type u) ⥤ (T ⥤ Sheaf J (Type u)) :=
  (Functor.whiskeringRight T _ _).obj (presheafToSheaf J (Type u))

/-- Sheafifying a `T`-diagram of large-valued presheaves. -/
public abbrev sheafifyDiagramLarge :
    (T ⥤ Cᵒᵖ ⥤ Type (max u v)) ⥤ (T ⥤ Sheaf J (Type (max u v))) :=
  (Functor.whiskeringRight T _ _).obj (presheafToSheaf J (Type (max u v)))

/-- Lifting a `T`-diagram of small-valued sheaves, objectwise. -/
public abbrev composeUliftDiagram :
    (T ⥤ Sheaf J (Type u)) ⥤ (T ⥤ Sheaf J (Type (max u v))) :=
  (Functor.whiskeringRight T _ _).obj (sheafCompose J uliftFunctor.{v, u})

/-- Currying a functor on `T × Cᵒᵖ` and sheafifying the result. -/
public abbrev curryThenSheafify :
    ((T × Cᵒᵖ) ⥤ Type (max u v)) ⥤ (T ⥤ Sheaf J (Type (max u v))) :=
  Functor.curry ⋙ sheafifyDiagramLarge J T

/-- **Sheafification commutes with the universe lift.** This is Mathlib's `sheafComposeNatIso` for
`uliftFunctor`, which applies because `uliftFunctor` preserves the sheafification. -/
public def sheafifyUliftIso :
    (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max u v))).obj uliftFunctor.{v, u} ⋙
        presheafToSheaf J (Type (max u v)) ≅
      presheafToSheaf J (Type u) ⋙ sheafCompose J uliftFunctor.{v, u} :=
  sheafComposeNatIso J uliftFunctor.{v, u} (sheafificationAdjunction J (Type u))
    (sheafificationAdjunction J (Type (max u v)))

/-- The same comparison, for `T`-diagrams. -/
public def sheafifyUliftDiagramIso :
    sheafifyDiagramSmall J T ⋙ composeUliftDiagram J T ≅
      uliftDiagramPresheaves T ⋙ sheafifyDiagramLarge J T :=
  (Functor.whiskeringRight T _ _).mapIso (sheafifyUliftIso J).symm

/-- Currying commutes with the objectwise universe lift, on the nose. -/
public def curryUliftIso :
    Functor.curry ⋙ uliftDiagramPresheaves T (C := C) ≅
      liftDiagram T ⋙ Functor.curry :=
  Iso.refl _

/-- The comparison carrying a small-valued curried diagram, sheafified and then lifted, to its
lift, curried and then sheafified. -/
public def densityComparison :
    Functor.curry ⋙ sheafifyDiagramSmall J T ⋙ composeUliftDiagram J T ≅
      liftDiagram T ⋙ curryThenSheafify J T :=
  Functor.isoWhiskerLeft Functor.curry (sheafifyUliftDiagramIso J T) ≪≫
    Functor.isoWhiskerRight (curryUliftIso T) (sheafifyDiagramLarge J T)

omit [FinCategory T] in
/-- **Every finite diagram of large-valued sheaves is a filtered colimit of the lifts of
small-valued ones.** This is the presentation hypothesis of
`preservesFiniteLimits_sheafPullback_of_small_presentations`. -/
public theorem exists_small_presentation (G : T ⥤ Sheaf J (Type (max u v))) :
    ∃ (I : Type (max u v)) (_ : SmallCategory I) (_ : IsFiltered I)
      (E : I ⥤ (T ⥤ Sheaf J (Type u)))
      (c : Cocone (E ⋙ (Functor.whiskeringRight T _ _).obj
        (sheafCompose J uliftFunctor.{v, u}))),
      Nonempty (c.pt ≅ G) ∧ Nonempty (IsColimit c) := by
  classical
  let P : (T × Cᵒᵖ) ⥤ Type (max u v) := uncurriedDiagram J T G
  -- Currying is the inverse of an equivalence, so it carries the colimit; instance search does
  -- not see that through the name `Functor.curry`, so the witness is supplied here.
  let : (Functor.curry (C := T) (D := Cᵒᵖ) (E := Type (max u v))).IsEquivalence :=
    Functor.currying.isEquivalence_inverse
  refine ⟨Finset (Σ a, P.obj a), inferInstance, isFiltered_finsetGens P,
    generatedShrunkDiagram P ⋙ Functor.curry ⋙ sheafifyDiagramSmall J T, ?_⟩
  refine ⟨(Cocone.precompose (Functor.isoWhiskerLeft (generatedShrunkDiagram P)
    (densityComparison J T)).hom).obj
      ((curryThenSheafify J T).mapCocone (generatedShrunkCocone P)), ⟨?_⟩, ⟨?_⟩⟩
  · exact (sheafifyDiagramLarge J T).mapIso
        ((Functor.currying.unitIso.app (G ⋙ sheafToPresheaf J (Type (max u v)))).symm) ≪≫
      Functor.isoWhiskerLeft G
        (asIso (sheafificationAdjunction J (Type (max u v))).counit) ≪≫
      G.rightUnitor
  · exact (IsColimit.precomposeHomEquiv _ _).symm
      (isColimitOfPreserves (curryThenSheafify J T) (isColimitGeneratedShrunkCocone P))

end Stacks.Sites.UniverseBridge

end
