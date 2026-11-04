module

public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered colimits of sheaves of sets are universal

A colimit is *universal* (`CategoryTheory.Limits.IsUniversalColimit`) when it stays a colimit
after base change along any morphism out of its vertex. Filtered colimits of sheaves of sets
are universal.

## Main results

* `CategoryTheory.Limits.type_filteredColimit_isUniversalColimit`: a filtered colimit of types
  is universal.
* `CategoryTheory.Limits.presheaf_filteredColimit_isUniversalColimit`: a filtered colimit of
  presheaves of types is universal.
* `CategoryTheory.Limits.sheaf_filteredColimit_isUniversalColimit`: a filtered colimit of
  sheaves of types is universal.

## Implementation notes

The three statements are the three rungs of one ladder, and only the first carries analytic
content. For types, a filtered colimit is the quotient of the disjoint union of the stages by
the transition maps, so two elements of the colimit agree exactly when they agree at some later
stage (`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`) and every element comes
from some stage (`CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`). Base changing
along `f` replaces each stage by its fibre product with the vertex, and the two facts above
transfer to the pulled-back cocone because the pullback squares are pullbacks of types: joint
surjectivity gives a stage and an element for every point of the new vertex, and the
"agree later" criterion plus monomorphy of the pullback gives that the induced map to any
other cocone is well defined. The second rung is the first applied objectwise, since colimits
and pullbacks of presheaves are computed pointwise and `evaluation` jointly reflects colimits.
The third rung transports the second along the reflective, left-exact sheafification adjunction
by `CategoryTheory.Limits.IsUniversalColimit.map_reflective`, the counit of a reflective
adjunction being invertible.

The index category is any filtered `I` small relative to the universe of the values; for
presheaves and sheaves the colimit is the one of `CategoryTheory.Limits.colimit.cocone`, which
determines the vertex, so the statements are about a specific cocone rather than an arbitrary
colimit cocone — any other is isomorphic to it and
`CategoryTheory.Limits.IsUniversalColimit.of_iso` transports the conclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u x

namespace CategoryTheory.Limits

/-- A filtered colimit of types is a universal colimit: it remains a colimit after base change
along any map out of its vertex. -/
@[sga "4 I 2.6" "special case"]
theorem type_filteredColimit_isUniversalColimit
    {I : Type x} [SmallCategory I] [Small.{w} I] [IsFiltered I]
    (F : I ⥤ Type w) (c : Cocone F) (hc : IsColimit c) :
    IsUniversalColimit c := by
  intro F' c' α f h hα hpb
  have hnat (i : I) (y : F'.obj i) : f (c'.ι.app i y) = c.ι.app i (α.app i y) :=
    (ConcreteCategory.congr_hom (congr_app h i) y).symm
  have huniq : ∀ (i j : I) (y : F'.obj i) (z : F'.obj j),
      c'.ι.app i y = c'.ι.app j z →
      ∀ s : Cocone F', s.ι.app i y = s.ι.app j z := by
    intro i j y z heq s
    have hbase : c.ι.app i (α.app i y) = c.ι.app j (α.app j z) := by
      rw [← hnat i y, ← hnat j z, heq]
    obtain ⟨k, uu, vv, hu⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff F hc).1 hbase
    have hc' : c'.ι.app k (F'.map uu y) = c'.ι.app k (F'.map vv z) := by
      calc
        c'.ι.app k (F'.map uu y) = c'.ι.app i y := ConcreteCategory.congr_hom (c'.w uu) y
        _ = c'.ι.app j z := heq
        _ = c'.ι.app k (F'.map vv z) := (ConcreteCategory.congr_hom (c'.w vv) z).symm
    have hα' : α.app k (F'.map uu y) = α.app k (F'.map vv z) := by
      calc
        α.app k (F'.map uu y) = F.map uu (α.app i y) :=
          ConcreteCategory.congr_hom (α.naturality uu) y
        _ = F.map vv (α.app j z) := hu
        _ = α.app k (F'.map vv z) := (ConcreteCategory.congr_hom (α.naturality vv) z).symm
    have hyz' := ((Types.isPullback_iff _ _ _ _).1 (hpb k)).2.1
      (F'.map uu y) (F'.map vv z) ⟨hc', hα'⟩
    calc
      s.ι.app i y = s.ι.app k (F'.map uu y) := (ConcreteCategory.congr_hom (s.w uu) y).symm
      _ = s.ι.app k (F'.map vv z) := congrArg (s.ι.app k) hyz'
      _ = s.ι.app j z := ConcreteCategory.congr_hom (s.w vv) z
  have hex : ∀ t : c'.pt, ∃ (i : I) (y : F'.obj i), c'.ι.app i y = t := by
    intro t
    obtain ⟨i, z, hz⟩ := Types.jointly_surjective_of_isColimit hc (f t)
    obtain ⟨y, hy₁, -⟩ := ((Types.isPullback_iff _ _ _ _).1 (hpb i)).2.2 t z
      (by simpa [hnat] using hz.symm)
    exact ⟨i, y, hy₁⟩
  let pickI (t : c'.pt) : I := Classical.choose (hex t)
  let pickX (t : c'.pt) : F'.obj (pickI t) :=
    Classical.choose (Classical.choose_spec (hex t))
  have pick_spec (t : c'.pt) : c'.ι.app (pickI t) (pickX t) = t :=
    Classical.choose_spec (Classical.choose_spec (hex t))
  let desc (s : Cocone F') : c'.pt ⟶ s.pt :=
    TypeCat.ofHom (fun t => s.ι.app (pickI t) (pickX t))
  refine ⟨{ desc := desc, fac := ?_, uniq := ?_ }⟩
  · intro s i
    ext y
    exact huniq (pickI (c'.ι.app i y)) i (pickX (c'.ι.app i y)) y
      (pick_spec (c'.ι.app i y)) s
  · intro s m hm
    ext t
    calc
      m t = m (c'.ι.app (pickI t) (pickX t)) := congrArg m (pick_spec t).symm
      _ = s.ι.app (pickI t) (pickX t) := ConcreteCategory.congr_hom (hm (pickI t)) (pickX t)

/-- A filtered colimit of presheaves of types is a universal colimit: colimits and pullbacks of
presheaves are computed pointwise, so this is the statement for types at every object. -/
@[sga "4 I 3.3" "special case", sga "4 II 4.3" "special case"]
theorem presheaf_filteredColimit_isUniversalColimit
    {C : Type v} [Category.{u} C] {I : Type x} [SmallCategory I]
    [Small.{w} I] [IsFiltered I] (F : I ⥤ (Cᵒᵖ ⥤ Type w)) :
    IsUniversalColimit (colimit.cocone F) := by
  intro F' c' α f h hα hpb
  refine ⟨evaluationJointlyReflectsColimits c' (fun U => ?_)⟩
  let ev := (evaluation Cᵒᵖ (Type w)).obj U
  have hu := type_filteredColimit_isUniversalColimit (F ⋙ ev) (ev.mapCocone (colimit.cocone F))
    (isColimitOfPreserves ev (colimit.isColimit F))
  refine (hu (ev.mapCocone c') (Functor.whiskerRight α ev) (ev.map f) ?_
    (hα.whiskerRight ev) fun i => (hpb i).map ev).some
  ext i y
  exact ConcreteCategory.congr_hom (congrArg ev.map (congr_app h i)) y

/-- A filtered colimit of sheaves of types is a universal colimit, transported from the presheaf
statement along the reflective, left-exact sheafification adjunction. -/
@[sga "4 I 3.3" "special case"]
theorem sheaf_filteredColimit_isUniversalColimit
    {C : Type v} [Category.{u} C] (J : GrothendieckTopology C)
    {I : Type x} [SmallCategory I] [Small.{w} I] [IsFiltered I]
    (F : I ⥤ Sheaf J (Type w)) [HasSheafify J (Type w)] :
    IsUniversalColimit (colimit.cocone F) := by
  let Gl := presheafToSheaf J (Type w)
  let Gr := sheafToPresheaf J (Type w)
  let adj : Gl ⊣ Gr := sheafificationAdjunction J (Type w)
  let e : (F ⋙ Gr) ⋙ Gl ≅ F :=
    Functor.associator F Gr Gl ≪≫ Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  have hu := (presheaf_filteredColimit_isUniversalColimit (F ⋙ Gr)).map_reflective adj
    |>.precompose_isIso e.inv
  exact hu.of_iso (hu.isColimit.uniqueUpToIso (colimit.isColimit F))

end CategoryTheory.Limits

end
