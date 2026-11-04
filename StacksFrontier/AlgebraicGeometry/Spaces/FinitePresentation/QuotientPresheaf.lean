module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Limit preservation for the quotient presheaf of a pre-relation

The quotient presheaf of a pre-relation is limit preserving as soon as the functors of points
of the two schemes carrying the relation are. The quotient presheaf is their objectwise
coequalizer, and a coequalizer of presheaves of sets sends a cone to a colimit cocone as soon
as its two constituents do.

## Main results

* `Stacks.Groupoids.limitPreserving_of_isColimit_cofork`: a presheaf which is objectwise a
  coequalizer of two limit-preserving presheaves is limit preserving.
* `Stacks.Groupoids.limitPreserving_quotientPresheaf`: the quotient presheaf of a pre-relation
  inherits limit preservation from the functors of points of its two constituents.

## Implementation notes

The argument is the universal property of a coequalizer of presheaves of sets, which is
computed objectwise; neither filteredness nor affineness of the tested system is used, only
the two colimit descriptions supplied by the hypotheses.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v' w w'

namespace Stacks.Groupoids

/-- A presheaf of sets which is objectwise a coequalizer of two presheaves sends the opposite of
a cone to a colimit cocone as soon as both of those presheaves do. -/
private theorem nonempty_isColimit_mapCocone_of_isColimit_cofork
    {C : Type v} [Category.{v'} C] {A B P : Cᵒᵖ ⥤ Type u}
    (s t : A ⟶ B) (p : B ⟶ P)
    (hw : ∀ X : Cᵒᵖ, s.app X ≫ p.app X = t.app X ≫ p.app X)
    (hp : ∀ X : Cᵒᵖ, Nonempty (IsColimit (Cofork.ofπ (p.app X) (hw X))))
    {I : Type w} [Category.{w'} I] (D : I ⥤ C) (c : Cone D)
    (hA : IsColimit (A.mapCocone c.op)) (hB : IsColimit (B.mapCocone c.op)) :
    Nonempty (IsColimit (P.mapCocone c.op)) := by
  refine ⟨IsColimit.ofExistsUnique fun E => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : B.obj c.op.pt ⟶ E.pt,
      ∀ i, B.map (c.op.ι.app i) ≫ k = p.app (D.op.obj i) ≫ E.ι.app i :=
    ⟨hB.desc ((Cocone.precompose (D.op.whiskerLeft p)).obj E),
      fun i => hB.fac ((Cocone.precompose (D.op.whiskerLeft p)).obj E) i⟩
  have hst : s.app c.op.pt ≫ k = t.app c.op.pt ≫ k := by
    refine hA.hom_ext fun i => ?_
    have key : ∀ α : A ⟶ B, (A.mapCocone c.op).ι.app i ≫ α.app c.op.pt ≫ k =
        (α.app (D.op.obj i) ≫ p.app (D.op.obj i)) ≫ E.ι.app i := by
      intro α
      dsimp only [Functor.mapCocone_ι_app]
      rw [← Category.assoc, α.naturality, Category.assoc, hk i, ← Category.assoc]
    rw [key s, key t, hw]
  have hl : p.app c.op.pt ≫ Cofork.IsColimit.desc (hp c.op.pt).some k hst = k :=
    Cofork.IsColimit.π_desc' _ k hst
  refine ⟨Cofork.IsColimit.desc (hp c.op.pt).some k hst, fun i => ?_, fun m hm => ?_⟩
  · refine Cofork.IsColimit.hom_ext (hp (D.op.obj i)).some ?_
    dsimp only [Cofork.π_ofπ, Functor.mapCocone_ι_app]
    rw [← Category.assoc, ← p.naturality, Category.assoc, hl, hk i]
  · have hm' : ∀ i, P.map (c.op.ι.app i) ≫ m = E.ι.app i := hm
    refine Cofork.IsColimit.hom_ext (hp c.op.pt).some ?_
    dsimp only [Cofork.π_ofπ]
    rw [hl]
    refine hB.hom_ext fun i => ?_
    dsimp only [Functor.mapCocone_ι_app]
    rw [← Category.assoc, p.naturality, Category.assoc, hm' i, hk i]

/-- A presheaf of sets which is objectwise a coequalizer of two limit-preserving presheaves is
itself limit preserving. -/
theorem limitPreserving_of_isColimit_cofork {C : Type v} [Category.{v'} C] (T : C ⥤ Scheme.{u})
    {A A' P : Cᵒᵖ ⥤ Type u} (s t : A ⟶ A') (p : A' ⟶ P)
    (hw : ∀ X : Cᵒᵖ, s.app X ≫ p.app X = t.app X ≫ p.app X)
    (hp : ∀ X : Cᵒᵖ, Nonempty (IsColimit (Cofork.ofπ (p.app X) (hw X))))
    (hA : LimitPreserving.{u, u, w, w', v} T A)
    (hA' : LimitPreserving.{u, u, w, w', v} T A') :
    LimitPreserving.{u, u, w, w', v} T P := fun I _ _ D c hc hD hC =>
  nonempty_isColimit_mapCocone_of_isColimit_cofork s t p hw hp D c
    (hA I D c hc hD hC).some (hA' I D c hc hD hC).some

/-- The quotient presheaf of a pre-relation sends cofiltered inverse limits of affine schemes to
filtered colimits of sets as soon as the functors of points of its two constituents do. -/
theorem limitPreserving_quotientPresheaf {S : Scheme.{u}} {C : Type v} [Category.{v'} C]
    (T : C ⥤ Scheme.{u}) (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)
    (hR : LimitPreserving.{u, u, w, w', v} T (points F R))
    (hU : LimitPreserving.{u, u, w, w', v} T (points F U)) :
    LimitPreserving.{u, u, w, w', v} T (quotientPresheaf F j) :=
  limitPreserving_of_isColimit_cofork T (sourceMap F j) (targetMap F j) (toQuotientPresheaf F j)
    (fun X => NatTrans.congr_app (coequalizer.condition (sourceMap F j) (targetMap F j)) X)
    (fun X => ⟨isColimitOfHasCoequalizerOfPreservesColimit
      ((evaluation Cᵒᵖ (Type u)).obj X) (sourceMap F j) (targetMap F j)⟩)
    hR hU

end Stacks.Groupoids

end
