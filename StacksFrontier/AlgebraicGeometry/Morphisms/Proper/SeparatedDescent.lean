module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.UniversallyClosedPullback

/-!
# Descent of separatedness along universally closed surjections

A scheme which is the universally closed surjective image of a scheme separated over a base is
itself separated over that base, and the same holds for separatedness of the scheme itself.
These are the separatedness parts of Tag 09MQ; the quasi-separatedness parts are in
`StacksFrontier.AlgebraicGeometry.Morphisms.Proper.QuasiSeparated`.

## Main results

* `AlgebraicGeometry.isSeparated_of_surjective_universallyClosed` descends separatedness over a
  base along a surjective universally closed morphism.
* `AlgebraicGeometry.Scheme.isSeparated_of_surjective_universallyClosed` is the absolute form,
  for separatedness of a scheme.

## Implementation notes

Schemes over `S` are represented by objects of `Over S`, and the morphism between them by a
morphism in that category, exactly as in the quasi-separated case. The geometric hypotheses on
the latter are imposed on its underlying scheme morphism `f.left`.

Writing `p` and `q` for the two structure morphisms and `g` for the induced morphism
`X ×_S X ⟶ Y ×_S Y`, the diagonal of `p` composed with `g` equals `f.left` composed with the
diagonal of `q`, so these two morphisms have the same set-theoretic range because `f.left` is
surjective. The left-hand composite is universally closed, being a closed immersion followed by
`AlgebraicGeometry.universallyClosed_map_self_pullback`, so that range is closed; and a
preimmersion with closed range is a closed immersion.

## References

* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The diagonal of `p = f ≫ q` followed by the induced morphism of self-fibre products is `f`
followed by the diagonal of `q`. -/
private lemma diagonal_comp_map_self_pullback {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (h : p = f ≫ q) :
    pullback.diagonal p ≫ pullback.map p p q q f f (𝟙 S)
      ((Category.comp_id p).trans h) ((Category.comp_id p).trans h) =
      f ≫ pullback.diagonal q := by
  apply pullback.hom_ext <;> simp only [pullback.map, Category.assoc,
    pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd]
    <;> simp

/-- For `f` surjective, the diagonal of `q` has the same range as the diagonal of `p = f ≫ q`
followed by the induced morphism of self-fibre products. -/
private lemma range_diagonal_eq_range_diagonal_comp_map_self_pullback
    {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (h : p = f ≫ q) [Surjective f] :
    Set.range (pullback.diagonal q) =
      Set.range (pullback.diagonal p ≫ pullback.map p p q q f f (𝟙 S)
        ((Category.comp_id p).trans h) ((Category.comp_id p).trans h)) := by
  have heq := congrArg (fun k : X ⟶ pullback q q => Set.range (fun x : X => k x))
    (diagonal_comp_map_self_pullback p q f h)
  rw [heq]
  apply Set.Subset.antisymm
  · rintro z ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := Scheme.Hom.surjective f y
    exact ⟨x, by simp⟩
  · rintro z ⟨x, rfl⟩
    exact ⟨f x, by simp⟩

/-- **Stacks Project, Tag 09MQ (separated over the base).** Separatedness over a base descends
along a surjective universally closed morphism of schemes. -/
@[stacks 09MQ "separated_over_s", sga "3 V 7.4"]
theorem isSeparated_of_surjective_universallyClosed {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [Surjective f.left] [UniversallyClosed f.left] [IsSeparated X.hom] :
    IsSeparated Y.hom := by
  have hg : UniversallyClosed
      (pullback.map X.hom X.hom Y.hom Y.hom f.left f.left (𝟙 S)
        ((Category.comp_id X.hom).trans f.w.symm)
        ((Category.comp_id X.hom).trans f.w.symm)) :=
    universallyClosed_map_self_pullback X.hom Y.hom f.left f.w.symm
  have hclosed : IsClosed (Set.range (pullback.diagonal Y.hom)) := by
    rw [range_diagonal_eq_range_diagonal_comp_map_self_pullback X.hom Y.hom f.left f.w.symm]
    simpa using
      (Scheme.Hom.isClosedMap (pullback.diagonal X.hom ≫ _)) Set.univ isClosed_univ
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

/-- **Stacks Project, Tag 09MQ (separated scheme).** A scheme receiving a surjective
universally closed morphism from a separated scheme is itself separated.

This is the absolute form of `AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`,
obtained by taking the base to be the terminal scheme. -/
@[stacks 09MQ "separated_scheme", sga "3 V 7.4" "special case"]
theorem Scheme.isSeparated_of_surjective_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [UniversallyClosed f] [X.IsSeparated] : Y.IsSeparated := by
  let g : (Over.mk (terminal.from X) : Over (⊤_ Scheme)) ⟶ Over.mk (terminal.from Y) :=
    Over.homMk f (terminal.comp_from f)
  have : Surjective g.left := show Surjective f from inferInstance
  have : UniversallyClosed g.left := show UniversallyClosed f from inferInstance
  have : IsSeparated (Over.mk (terminal.from X) : Over (⊤_ Scheme)).hom :=
    show IsSeparated (terminal.from X) from inferInstance
  exact ⟨_root_.AlgebraicGeometry.isSeparated_of_surjective_universallyClosed g⟩

end AlgebraicGeometry

end
