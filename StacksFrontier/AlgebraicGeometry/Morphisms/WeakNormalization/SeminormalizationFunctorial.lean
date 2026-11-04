module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Functoriality of seminormalization

Every morphism of schemes lifts uniquely to a morphism between their seminormalizations,
compatibly with the canonical morphisms to the original schemes.

## Main results

* `AlgebraicGeometry.existsUnique_seminormalization_lift` gives the unique compatible lift.

## Implementation notes

The seminormalizations and their structure morphisms are the chosen initial objects of the
seminormalization categories, so they are available exactly when those initial objects are,
which is why the existence of the initial object appears as an instance hypothesis.
Compatibility is expressed by a commutative square of scheme morphisms. The key input is that
the base change of a universal homeomorphism inducing isomorphisms on residue fields again
induces isomorphisms on residue fields, which is read off from the residue field of a point of
a fibre product.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EUS.** A morphism of schemes has a unique compatible
lift to their seminormalizations. -/
@[stacks 0EUS "seminormalization_functorial"]
theorem existsUnique_seminormalization_lift {X' X : Scheme.{u}}
    [HasInitial (SeminormalizationCategory X')]
    [HasInitial (SeminormalizationCategory X)]
    (h : X' ⟶ X) :
    ∃! hsn : X'.seminormalization ⟶ X.seminormalization,
      hsn ≫ X.seminormalizationHom =
        X'.seminormalizationHom ≫ h := by
  let f := X.seminormalizationHom
  let f' := X'.seminormalizationHom
  have hf := (initial (SeminormalizationCategory X)).property
  let target : SeminormalizationCategory X' :=
    ⟨Over.mk (pullback.snd f h),
      ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f h) hf.1.universally_isHomeomorph⟩,
      fun z => pullback_snd_residueFieldMap_isIso f h z (hf.2 (pullback.fst f h z))⟩
  let m := initial.to target
  refine ⟨m.hom.left ≫ pullback.fst f h, ?_, ?_⟩
  · calc
      (m.hom.left ≫ pullback.fst f h) ≫ f =
          (m.hom.left ≫ pullback.snd f h) ≫ h := by
            simp [pullback.condition]
      _ = f' ≫ h := by simpa [target] using congrArg (fun q => q ≫ h) m.hom.w
  · intro g hg
    let lift := pullback.lift g f' (by simpa [Category.assoc] using hg)
    let n : initial (SeminormalizationCategory X') ⟶ target :=
      ObjectProperty.homMk (Over.homMk lift (by
        show lift ≫ pullback.snd f h = f'
        rw [pullback.lift_snd]))
    have hn := congrArg
      (fun q : initial (SeminormalizationCategory X') ⟶
        target => q.hom.left ≫ pullback.fst f h) (initial.hom_ext m n)
    calc
      g = lift ≫ pullback.fst f h := by rw [pullback.lift_fst]
      _ = m.hom.left ≫ pullback.fst f h := by simpa [n] using hn.symm

end AlgebraicGeometry

end
