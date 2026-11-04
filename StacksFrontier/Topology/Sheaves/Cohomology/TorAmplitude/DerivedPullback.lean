module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatPullback

/-!
# Derived pullback preserves Tor amplitude

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces. If an object `E` of `D(O_Y)` has
Tor amplitude in `[a, b]`, then `Lf^*E` has Tor amplitude in `[a, b]`.

## Main results

* `Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback`: **Tag 09U8.**

## Implementation notes

`E` is replaced by a bounded flat representative `K` using Tag 08CI. Such a `K` is K-flat by
Tag 06YQ, so the comparison `Lf^*K ⟶ f^*K` is invertible on it, by Tag 06YJ; and the degreewise
pullback `f^*K` is again flat in each degree, by Tag 0H97, and still vanishes outside `[a, b]`,
pullback being additive. Tag 08CI read in the other direction then gives the conclusion.

For a degenerate interval `b < a` the hypothesis is vacuously about every degree, so it implies
Tor amplitude in a one-point interval placed above whichever degree is being examined, and the
ordered case applies there.

Both derived categories are the standard ones, which is what Tag 06YJ's derived pullback is
stated at; the hom universe is not left free here, unlike in the Tor-amplitude vocabulary
itself.

## References

* [Stacks Project, Tag 09U8](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0H97](https://stacks.math.columbia.edu/tag/0H97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude.Pullback

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Tag 09U8 for an ordered interval.** Derived pullback along a morphism of ringed spaces
preserves Tor amplitude in `[a, b]` when `a ≤ b`. -/
theorem hasTorAmplitude_derivedPullback_of_le (E : DerivedCategory (OXMod.{u} Y)) (a b : ℤ)
    (hab : a ≤ b) (hE : HasTorAmplitude Y E a b) :
    HasTorAmplitude X
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E) a b := by
  classical
  obtain ⟨K, hKflat, hKzero, ⟨e⟩⟩ :=
    (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative (X := Y)
      E a b hab).mp hE
  have hKLE : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hKzero i (by simp only [Set.mem_Icc]; omega)
  have hKkflat := kFlat_of_boundedAbove_of_flat Y K ⟨b, hKLE⟩ hKflat
  let K' : CochainComplex (Modules X) ℤ :=
    ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hK'flat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.sheaf) (K'.X i) := fun i =>
    Stacks.SheafOfModules.modulePullback_isFlat f (K.X i) (hKflat i)
  have hK'zero : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K'.X i) := fun i hi =>
    Functor.map_isZero (modulePullback f) (hKzero i hi)
  refine (BoundedFlatRepresentative.hasTorAmplitude_iff_exists_flat_representative (X := X)
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E)
    a b hab).2 ⟨K', hK'flat, hK'zero, ⟨?_⟩⟩
  refine ?_ ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso (OXMod.{u} Y)).app K ≪≫ e)
  refine (DerivedCategory.Qh.mapIso
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso (OXMod.{u} X)).app K').symm ≪≫ ?_
  exact (@asIso _ _ _ _
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (OXMod.{u} Y) (ComplexShape.up ℤ)).obj K))
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      f K hKkflat)).symm

/-- **Tag 09U8.** Derived pullback along a morphism of ringed spaces preserves Tor amplitude in
a fixed interval.

A degenerate interval is replaced by a one-point interval above the degree under
consideration, which is weaker, and `hasTorAmplitude_derivedPullback_of_le` applies. -/
@[stacks 09U8]
theorem hasTorAmplitude_derivedPullback (E : DerivedCategory (OXMod.{u} Y)) (a b : ℤ)
    (hE : HasTorAmplitude Y E a b) :
    HasTorAmplitude X
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E) a b := by
  by_cases hab : a ≤ b
  · exact hasTorAmplitude_derivedPullback_of_le f E a b hab hE
  · intro F i _
    have hE' : HasTorAmplitude Y E (i + 1) (i + 1) :=
      fun G j hj => hE G j (by simp only [Set.mem_Icc]; omega)
    exact hasTorAmplitude_derivedPullback_of_le f E (i + 1) (i + 1) le_rfl hE' F i
      (by simp only [Set.mem_Icc]; omega)

end Stacks.Cohomology.TorAmplitude.Pullback

end
