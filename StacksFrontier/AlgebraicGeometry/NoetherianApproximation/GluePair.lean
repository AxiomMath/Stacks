module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Glueing two schemes along a common open subscheme

Given open immersions `f : W ⟶ X` and `g : W ⟶ Y`, the scheme `gluePair f g` is obtained by
glueing `X` and `Y` along `W`. It is the colimit of the two-legged wide span diagram `W ⟶ X`,
`W ⟶ Y`; this diagram is locally directed, so the colimit exists and is covered by the images of
its legs.

## Main definitions

* `AlgebraicGeometry.Scheme.gluePair`: the glued scheme.
* `AlgebraicGeometry.Scheme.gluePairInl`, `AlgebraicGeometry.Scheme.gluePairInr`: the two open
  immersions into it.
* `AlgebraicGeometry.Scheme.gluePairDesc`: the morphism out of the glueing determined by a
  pair of morphisms agreeing on `W`.

## Main results

* `AlgebraicGeometry.Scheme.gluePair_opensRange_sup`: the two legs cover the glueing.
* `AlgebraicGeometry.Scheme.gluePair_hom_ext`: morphisms out of the glueing are determined by
  their restrictions to the two legs.
* `AlgebraicGeometry.Scheme.compactSpace_gluePair` and
  `AlgebraicGeometry.Scheme.locallyOfFiniteType_terminal_from_gluePair`: the glueing of two
  quasi-compact schemes of finite type over the terminal scheme is again such.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)

/-- The wide span diagram of a pair of morphisms out of a common scheme.  Its colimit glues
the two targets along the common source. -/
@[reducible] noncomputable def gluePairDiagram : WidePushoutShape WalkingPair ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan W (fun b ↦ b.casesOn X Y) (fun b ↦ b.casesOn f g)

variable [IsOpenImmersion f] [IsOpenImmersion g]

/-- Every morphism of the wide span diagram of two open immersions is an open immersion. -/
instance isOpenImmersion_gluePairDiagram_map {i j : WidePushoutShape WalkingPair} (h : i ⟶ j) :
    IsOpenImmersion ((gluePairDiagram f g).map h) := by
  cases h with
  | id a => simp only [WidePushoutShape.hom_id]; infer_instance
  | init b => cases b <;> assumption

/-- Two schemes glued along a common open subscheme, presented as a colimit. -/
@[reducible] noncomputable def gluePair : Scheme.{u} := colimit (gluePairDiagram f g)

/-- The leg of the glueing coming from the first scheme. -/
@[reducible] noncomputable def gluePairInl : X ⟶ gluePair f g :=
  colimit.ι (gluePairDiagram f g) (some .left)

/-- The leg of the glueing coming from the second scheme. -/
@[reducible] noncomputable def gluePairInr : Y ⟶ gluePair f g :=
  colimit.ι (gluePairDiagram f g) (some .right)

/-- The first leg of the glueing is an open immersion. -/
instance : IsOpenImmersion (gluePairInl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (gluePairDiagram f g) (some .left)))

/-- The second leg of the glueing is an open immersion. -/
instance : IsOpenImmersion (gluePairInr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (gluePairDiagram f g) (some .right)))

/-- The colimit leg at the common scheme factors through the first leg. -/
private lemma gluePair_ι_none :
    colimit.ι (gluePairDiagram f g) none = f ≫ gluePairInl f g :=
  (colimit.w (gluePairDiagram f g) (WidePushoutShape.Hom.init WalkingPair.left)).symm

/-- The two legs of the glueing agree on the common open subscheme. -/
lemma gluePair_condition : f ≫ gluePairInl f g = g ≫ gluePairInr f g :=
  (gluePair_ι_none f g).symm.trans
    (colimit.w (gluePairDiagram f g) (WidePushoutShape.Hom.init WalkingPair.right)).symm

/-- The cocone on the wide span diagram given by a pair of morphisms agreeing on the common
open subscheme. -/
@[reducible] noncomputable def gluePairCocone {Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z)
    (hab : f ≫ a = g ≫ b) : Cocone (gluePairDiagram f g) :=
  WidePushoutShape.mkCocone (f ≫ a) (fun c ↦ c.casesOn a b)
    (fun c ↦ by cases c with | left => rfl | right => exact hab.symm)

/-- The morphism out of a glueing determined by a pair of morphisms agreeing on the common
open subscheme. -/
noncomputable def gluePairDesc {Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z)
    (hab : f ≫ a = g ≫ b) : gluePair f g ⟶ Z :=
  colimit.desc (gluePairDiagram f g) (gluePairCocone f g a b hab)

/-- The morphism `gluePairDesc f g a b hab` restricts to `a` along the first leg. -/
@[simp]
lemma gluePairInl_desc {Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (hab : f ≫ a = g ≫ b) :
    gluePairInl f g ≫ gluePairDesc f g a b hab = a :=
  colimit.ι_desc (gluePairCocone f g a b hab) (some WalkingPair.left)

/-- The morphism `gluePairDesc f g a b hab` restricts to `b` along the second leg. -/
@[simp]
lemma gluePairInr_desc {Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (hab : f ≫ a = g ≫ b) :
    gluePairInr f g ≫ gluePairDesc f g a b hab = b :=
  colimit.ι_desc (gluePairCocone f g a b hab) (some WalkingPair.right)

/-- Two morphisms out of the glueing that agree after composing with both legs are equal. -/
lemma gluePair_hom_ext {Z : Scheme.{u}} {u v : gluePair f g ⟶ Z}
    (hl : gluePairInl f g ≫ u = gluePairInl f g ≫ v)
    (hr : gluePairInr f g ≫ u = gluePairInr f g ≫ v) : u = v := by
  refine colimit.hom_ext fun i ↦ ?_
  obtain _ | b := i
  · rw [gluePair_ι_none, Category.assoc, Category.assoc]
    exact congrArg _ hl
  · cases b
    · exact hl
    · exact hr

/-- Every point of the glueing lies in the image of one of the two legs. -/
lemma gluePair_jointly_surjective (x : gluePair f g) :
    (∃ y, (gluePairInl f g) y = x) ∨ ∃ y, (gluePairInr f g) y = x := by
  obtain ⟨i, xi, hxi⟩ := IsLocallyDirected.ι_jointly_surjective (gluePairDiagram f g) x
  obtain _ | b := i
  · exact Or.inl ⟨f xi, by rw [← hxi, gluePair_ι_none, Scheme.Hom.comp_apply]⟩
  · cases b
    · exact Or.inl ⟨xi, hxi⟩
    · exact Or.inr ⟨xi, hxi⟩

/-- The images of the two legs cover the glueing. -/
lemma gluePair_range_union :
    Set.range (gluePairInl f g) ∪ Set.range (gluePairInr f g) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ gluePair_jointly_surjective f g x

/-- The open subschemes given by the ranges of the two legs cover the glueing. -/
lemma gluePair_opensRange_sup :
    (gluePairInl f g).opensRange ⊔ (gluePairInr f g).opensRange = ⊤ :=
  TopologicalSpace.Opens.ext (by simpa using gluePair_range_union f g)

/-- The glueing of two quasi-compact schemes is quasi-compact. -/
lemma compactSpace_gluePair [CompactSpace X] [CompactSpace Y] :
    CompactSpace (gluePair f g) := by
  rw [← isCompact_univ_iff, ← gluePair_range_union f g]
  exact (isCompact_range (gluePairInl f g).continuous).union
    (isCompact_range (gluePairInr f g).continuous)

private lemma isZariskiLocalAtSource_of_hasRingHomProperty (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance

/-- The glueing of two schemes locally of finite type over the terminal scheme is locally of
finite type over the terminal scheme. -/
lemma locallyOfFiniteType_terminal_from_gluePair
    [LocallyOfFiniteType (terminal.from X)] [LocallyOfFiniteType (terminal.from Y)] :
    LocallyOfFiniteType (terminal.from (gluePair f g)) := by
  have hobj : ∀ i, LocallyOfFiniteType (terminal.from ((gluePairDiagram f g).obj i)) := by
    rintro (_ | b)
    · have h : terminal.from ((gluePairDiagram f g).obj none) = f ≫ terminal.from X :=
        terminal.hom_ext _ _
      rw [h]; infer_instance
    · cases b <;> assumption
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    isZariskiLocalAtSource_of_hasRingHomProperty @LocallyOfFiniteType
      (Q := @RingHom.FiniteType)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType)
    (fun i ↦ (colimit.ι (gluePairDiagram f g) i).opensRange) ?_ fun i ↦ ?_
  · refine top_unique fun x _ ↦ ?_
    obtain ⟨i, xi, hxi⟩ := IsLocallyDirected.ι_jointly_surjective (gluePairDiagram f g) x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, xi, hxi⟩
  · have h : ((colimit.ι (gluePairDiagram f g) i).opensRange).ι ≫
        terminal.from (gluePair f g) =
        (Scheme.Hom.isoOpensRange (colimit.ι (gluePairDiagram f g) i)).inv ≫
          terminal.from ((gluePairDiagram f g).obj i) := terminal.hom_ext _ _
    rw [h]
    have := hobj i
    infer_instance

end AlgebraicGeometry.Scheme
