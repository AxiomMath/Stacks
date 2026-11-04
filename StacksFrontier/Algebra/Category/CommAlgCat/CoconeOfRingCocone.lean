module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Filtered colimits of commutative algebras are computed on the underlying rings

A cocone of commutative rings under a diagram of `A`-algebras over a filtered index category
carries an `A`-algebra structure on its vertex, transported along the leg at any chosen index,
and the legs are then algebra maps. Consequently a colimit cocone of a filtered diagram of
`A`-algebras stays a colimit cocone after the algebra structure is forgotten, and the forgetful
functor to commutative rings preserves filtered colimits.

## Main definitions

* `Stacks.CommAlgCat.algebraOfRingCocone`: the transported algebra structure on the vertex.
* `Stacks.CommAlgCat.commAlgCoconeOfRingCocone`: the cocone of algebras.

## Main results

* `Stacks.CommAlgCat.isColimit_forgetToCommRing` and
  `Stacks.CommAlgCat.forget₂CommRingCat_preservesFilteredColimits`: the forgetful functor to
  commutative rings carries a colimit cocone of a filtered diagram of `A`-algebras to a colimit
  cocone, with no size relation between the index category and the algebras.
* `Stacks.CommAlgCat.forget_preservesFilteredColimitsOfSize`: the forgetful functor to types
  preserves the filtered colimits of `A`-algebras indexed by a category no larger than the
  algebras.

## Implementation notes

The two steps of the forgetful functor to types behave differently in the universes. Forgetting
only the algebra structure is a formal manipulation of cocones, so it preserves filtered colimits
indexed by a category of any size. Forgetting down to types does not: Mathlib proves that the
forgetful functor of commutative rings preserves filtered colimits whose index category has the
size of the rings (`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`), and the size
condition is carried here as `UnivLE` hypotheses rather than dropped. A directed system in the
sense of the Stacks project is indexed by a set, so it satisfies them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w a

namespace Stacks.CommAlgCat

/-- The algebra structure on the vertex of a cocone of rings under a diagram of algebras,
transported along the leg at a chosen index. -/
public abbrev algebraOfRingCocone {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A}
    (c : Cocone (F ⋙ forget₂ (CommAlgCat.{a} A) CommRingCat.{a})) (j : J) :
    Algebra A c.pt :=
  (c.ι.app j).hom.comp (algebraMap A (F.obj j)) |>.toAlgebra

/-- A cocone of commutative rings under a diagram of algebras over a filtered index category is
a cocone of algebras, for the algebra structure transported along the leg at a chosen index. -/
public def commAlgCoconeOfRingCocone {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A}
    (c : Cocone (F ⋙ forget₂ (CommAlgCat.{a} A) CommRingCat.{a})) (j : J) : Cocone F where
  pt :=
    letI : Algebra A c.pt := algebraOfRingCocone c j
    CommAlgCat.of A c.pt
  ι.app k := by
    letI : Algebra A c.pt := algebraOfRingCocone c j
    refine CommAlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact c.ι.naturality_apply f _

/-- Forgetting the algebra structure of a colimit cocone of algebras over a filtered index
category gives a colimit cocone of commutative rings. -/
public noncomputable def isColimit_forgetToCommRing {A : Type u} [CommRing A]
    {J : Type v} [Category.{w} J] [IsFiltered J]
    {F : J ⥤ CommAlgCat.{a} A} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).mapCocone c) where
  desc s := (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map
    (hc.desc (commAlgCoconeOfRingCocone s IsFiltered.nonempty.some))
  fac s k := by
    change (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map
      (c.ι.app k ≫ hc.desc (commAlgCoconeOfRingCocone s IsFiltered.nonempty.some)) = _
    rw [hc.fac]
    rfl
  uniq s m hm := by
    let : Algebra A s.pt := algebraOfRingCocone s IsFiltered.nonempty.some
    let m' : c.pt ⟶ (commAlgCoconeOfRingCocone s IsFiltered.nonempty.some).pt :=
      CommAlgCat.ofHom
      { __ := m.hom
        commutes' r := by
          change m.hom (algebraMap A c.pt r) =
            s.ι.app IsFiltered.nonempty.some
              (algebraMap A (F.obj IsFiltered.nonempty.some) r)
          have hh := ConcreteCategory.congr_hom (hm IsFiltered.nonempty.some)
            (algebraMap A (F.obj IsFiltered.nonempty.some) r)
          calc
            m.hom (algebraMap A c.pt r) =
                m.hom ((c.ι.app IsFiltered.nonempty.some).hom
                  (algebraMap A (F.obj IsFiltered.nonempty.some) r)) :=
              congrArg m.hom ((c.ι.app IsFiltered.nonempty.some).hom.commutes r).symm
            _ = s.ι.app IsFiltered.nonempty.some
                  (algebraMap A (F.obj IsFiltered.nonempty.some) r) := by simpa using hh }
    have heq : m' = hc.desc (commAlgCoconeOfRingCocone s IsFiltered.nonempty.some) :=
      hc.uniq _ m' fun k ↦ (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map_injective (hm k)
    have hm' : (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}).map m' = m := by ext x; rfl
    exact hm'.symm.trans (congrArg _ heq)

/-- **The forgetful functor from commutative `A`-algebras to commutative rings preserves
filtered colimits**, with no size relation between the index category and the algebras. -/
public instance forget₂CommRingCat_preservesFilteredColimits {A : Type u} [CommRing A] :
    PreservesFilteredColimitsOfSize.{w, v} (forget₂ (CommAlgCat.{a} A) CommRingCat.{a}) where
  preserves_filtered_colimits _ _ _ := ⟨fun {_} ↦ ⟨fun hc ↦ ⟨isColimit_forgetToCommRing hc⟩⟩⟩

/-- **The forgetful functor from commutative `A`-algebras to types preserves the filtered
colimits indexed by a category no larger than the algebras**. -/
public instance forget_preservesFilteredColimitsOfSize {A : Type u} [CommRing A]
    [UnivLE.{v, a}] [UnivLE.{w, a}] :
    PreservesFilteredColimitsOfSize.{w, v} (forget (CommAlgCat.{a} A)) := by
  have h : PreservesFilteredColimitsOfSize.{a, a} (forget (CommAlgCat.{a} A)) := by
    rw [← HasForget₂.forget_comp (C := CommAlgCat.{a} A) (D := CommRingCat.{a})]
    infer_instance
  exact preservesFilteredColimitsOfSize_of_univLE.{a, a, w, v} (forget (CommAlgCat.{a} A))

end Stacks.CommAlgCat

end
