module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.UniversallyClosedPullback

/-!
# Descent of quasi-separatedness along universally closed surjections

A scheme which is the universally closed surjective image of a scheme quasi-separated over a
base is itself quasi-separated over that base, and the same holds for quasi-separatedness of
the underlying space.

## Main results

* `AlgebraicGeometry.quasiSeparated_of_surjective_universallyClosed` descends
  quasi-separatedness over a base along a surjective universally closed morphism.
* `AlgebraicGeometry.quasiSeparatedSpace_of_surjective_universallyClosed` descends
  quasi-separatedness of the underlying space along such a morphism.

## Implementation notes

Schemes over `S` are represented by objects of `Over S`, and the morphism between them by a
morphism in that category. The geometric hypotheses on the latter are imposed on its
underlying scheme morphism `f.left`. In the absolute statement the base scheme is omitted:
the assertion concerns only the underlying morphism, and any morphism of schemes is
canonically a morphism over the terminal scheme.

## References

* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 09MQ (quasi-separated over the base).**
Quasi-separatedness over a base descends along a surjective universally
closed morphism of schemes. -/
@[stacks 09MQ "quasi_separated_over_s"]
theorem quasiSeparated_of_surjective_universallyClosed {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [Surjective f.left] [UniversallyClosed f.left] [QuasiSeparated X.hom] :
    QuasiSeparated Y.hom := by
  let c := pullback.map X.hom X.hom Y.hom Y.hom f.left f.left (𝟙 S)
      ((Category.comp_id X.hom).trans f.w.symm)
      ((Category.comp_id X.hom).trans f.w.symm)
  have : QuasiCompact c := quasiCompact_map_self_pullback X.hom Y.hom f.left f.w.symm
  refine ⟨⟨fun V hVopen hVcompact => ?_⟩⟩
  have hdiag : IsCompact ((pullback.diagonal X.hom).base ⁻¹' (c.base ⁻¹' V)) :=
    QuasiCompact.isCompact_preimage (f := pullback.diagonal X.hom)
      (c.base ⁻¹' V) (c.continuous.isOpen_preimage V hVopen)
      (QuasiCompact.isCompact_preimage (f := c) V hVopen hVcompact)
  have hnat : pullback.diagonal X.hom ≫ c = f.left ≫ pullback.diagonal Y.hom := by
    apply pullback.hom_ext <;>
      simp only [c, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd] <;>
      simp [← Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  have himage :
      f.left.base '' ((pullback.diagonal X.hom).base ⁻¹' (c.base ⁻¹' V)) =
        (pullback.diagonal Y.hom).base ⁻¹' V := by
    rw [← Set.image_preimage_eq ((pullback.diagonal Y.hom).base ⁻¹' V)
      f.left.surjective]
    congr 1
    ext x
    simp only [Set.mem_preimage]
    rw [show c (pullback.diagonal X.hom x) = pullback.diagonal Y.hom (f.left x) by
      simpa only [Scheme.Hom.comp_apply] using
        (congrArg (fun g : X.left ⟶ pullback Y.hom Y.hom => g x) hnat)]
  rw [← himage]
  exact hdiag.image f.left.continuous

/-- **Stacks Project, Tag 09MQ (scheme part).** The target of a surjective
universally closed morphism from a quasi-separated scheme is
quasi-separated. -/
@[stacks 09MQ "quasi_separated_scheme"]
lemma quasiSeparatedSpace_of_surjective_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [UniversallyClosed f]
    [QuasiSeparatedSpace X] : QuasiSeparatedSpace Y := by
  let g : (Over.mk (terminal.from X) : Over (⊤_ Scheme)) ⟶
      Over.mk (terminal.from Y) := Over.homMk f (by subsingleton)
  have : Surjective g.left := inferInstanceAs (Surjective f)
  have : UniversallyClosed g.left := inferInstanceAs (UniversallyClosed f)
  have : QuasiSeparated (Over.mk (terminal.from X) : Over (⊤_ Scheme)).hom :=
    (quasiSeparatedSpace_iff_quasiSeparated X).mp inferInstance
  exact (quasiSeparatedSpace_iff_quasiSeparated Y).mpr
    (quasiSeparated_of_surjective_universallyClosed g)

end AlgebraicGeometry

end
