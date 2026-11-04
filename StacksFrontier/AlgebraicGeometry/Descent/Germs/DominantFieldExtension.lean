module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.BaseChange

/-!
# Dominance after a field extension

A morphism of schemes over a field is dominant if and only if its base change along a field
extension is dominant.

## Main results

* `AlgebraicGeometry.isDominant_iff_baseChange_fieldExtension` characterises dominance of a
  morphism of schemes over a field by dominance of its base change to a field extension.

## Implementation notes

The scheme structures over the ground field are the morphisms `pX` and `pY`, and `h` says that
`f` is a morphism over that field. The base-changed morphism is the canonical map between the
chosen categorical pullbacks along the morphism of spectra induced by the field extension. That
morphism of spectra is surjective and universally open, so one direction is base change of
dominance along an open morphism, read through the comparison of iterated pullbacks, and the
other is cancellation of dominance in a composition.

## References

* [Stacks Project, Tag 0H8I](https://stacks.math.columbia.edu/tag/0H8I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0H8I.** A morphism of schemes over a field is dominant exactly
when its base change along a field extension is dominant. -/
@[stacks 0H8I]
theorem isDominant_iff_baseChange_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (h : f ≫ pY = pX) :
    let g : Spec (.of K) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    let fK : pullback pX g ⟶ pullback pY g :=
      pullback.map pX g pY g f (𝟙 _) (𝟙 _) (by simpa using h.symm) (by simp)
    IsDominant f ↔ IsDominant fK := by
  cases h
  intro g fK
  have : Surjective g := by
    rw [surjective_iff]
    exact fun _ ↦ ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩
  have hmapfst : fK ≫ pullback.fst pY g = pullback.fst (f ≫ pY) g ≫ f := by
    dsimp [fK, pullback.map]
    rw [pullback.lift_fst]
  have hmapsnd : fK ≫ pullback.snd pY g = pullback.snd (f ≫ pY) g := by
    dsimp [fK, pullback.map]
    rw [pullback.lift_snd]
    simp
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have heq : (pullbackRightPullbackFstIso pY g f).hom ≫ fK =
        pullback.snd f (pullback.fst pY g) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hmapfst, ← Category.assoc, pullbackRightPullbackFstIso_hom_fst,
          pullback.condition]
      · rw [Category.assoc, hmapsnd, pullbackRightPullbackFstIso_hom_snd]
    have := isDominant_pullback_snd_of_isOpenMap f _ (pullback.fst pY g).isOpenMap
    rw [← heq] at this
    exact IsDominant.of_comp (pullbackRightPullbackFstIso pY g f).hom fK
  · have : IsDominant (pullback.fst (f ≫ pY) g ≫ f) := by
      rw [← hmapfst]
      infer_instance
    exact IsDominant.of_comp (pullback.fst (f ≫ pY) g) f

end AlgebraicGeometry
