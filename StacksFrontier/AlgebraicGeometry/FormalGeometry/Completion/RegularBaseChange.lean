module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Regularity after completion of the base

Let `A` be a Noetherian local ring and let `X` be a scheme over `Spec A`. This file compares
regularity of `X` with regularity of its base change `X ×_{Spec A} Spec A^` along the completion
of `A`.

Regularity of a local ring of the base change always descends to the local ring at the image
point. Over the closed fibre the two are equivalent, because the two local rings have isomorphic
completions; and for a proper `X` every point of the base change in the relevant position lies
over the closed point, so regularity of `X` and of its completed base change agree.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_of_completion` — regularity descends pointwise from
  the completed base change.
* `AlgebraicGeometry.isRegularLocalRing_stalk_pullback_completion_iff` — at a point of the closed
  fibre, regularity of the local ring is invariant under the completed base change.
* `AlgebraicGeometry.isRegular_pullback_completion_iff` — a proper scheme over a Noetherian local
  ring is regular if and only if its completed base change is.

## Implementation notes

The completion is `AdicCompletion (IsLocalRing.maximalIdeal A) A` and the completed base change
is the categorical pullback of schemes. Membership in the closed fibre is expressed by asking
that the image of the point in the spectrum of the completion be its maximal ideal.

Mathlib's `IsProper` extends `LocallyOfFiniteType`, so the source's local finite-type assumption
is already part of the properness hypothesis in the last statement.

## References

* [Stacks Project, Tag 0BG6](https://stacks.math.columbia.edu/tag/0BG6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Regularity of a local ring of a scheme descends pointwise from its base change to the
completion of a Noetherian local base ring. -/
@[stacks 0BG6 "pointwise_descent", ega "0 17.1.5" "Â regular ⇒ A regular"]
theorem isRegularLocalRing_stalk_of_completion
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R))
    (x : X)
    (y : (pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) : Scheme.{u}))
    (hy : (pullback.fst f
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))))).base y = x)
    (hregular : IsRegularLocalRing
      ((pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) :
          Scheme.{u}).presheaf.stalk y)) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  have : Module.FaithfullyFlat R
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by
        rw [← Ideal.jacobson_bot]
        exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  let g := pullback.fst f (Spec.map (CommRingCat.ofHom
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))))
  have : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) := by
    rw [Flat.SpecMap_iff]
    change (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  rw [← hy]
  algebraize [(g.stalkMap y).hom]
  let S := ((pullback f (Spec.map (CommRingCat.ofHom
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) : Scheme.{u}).presheaf.stalk y)
  have : IsRegularRing S := (IsLocalRing.isRegularRing_tfae.out 1 3).mp hregular
  have : Module.FaithfullyFlat (X.presheaf.stalk (g.base y)) S :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g y) (g.toLRSHom.prop y)
  have : IsRegularRing (X.presheaf.stalk (g.base y)) := IsRegularRing.of_faithfullyFlat S
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing (X.presheaf.stalk (g.base y))

/-- At a point of the closed fibre, regularity of the local ring is invariant under base change
from a Noetherian local ring to its completion. -/
@[stacks 0BG6 "closed_fibre_equivalence", ega "0 17.1.5"]
theorem isRegularLocalRing_stalk_pullback_completion_iff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) : Scheme.{u}))
    (hx : (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).base y = x)
    (hy : (pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).base y =
      (⟨IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A), inferInstance⟩ :
        PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    IsRegularLocalRing
        ((pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) :
          Scheme.{u}).presheaf.stalk y) ↔
      IsRegularLocalRing (X.presheaf.stalk x) := by
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
  let Y : Scheme.{u} := pullback f g
  let π : Y ⟶ X := pullback.fst f g
  let ρ : Y ⟶ Spec (.of Ahat) := pullback.snd f g
  subst x
  have hclosed : f.base (π.base y) =
      (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) := by
    have hcomm : f.base (π.base y) = g.base (ρ.base y) := by
      simpa [π, ρ] using congrArg (fun k : Y ⟶ Spec (.of A) => k.base y)
        (show pullback.fst f g ≫ f = pullback.snd f g ≫ g from pullback.condition)
    rw [hcomm, hy]
    exact PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap (algebraMap A Ahat))
  obtain ⟨e, _he⟩ :=
    stalkMap_adicCompletion_isomorphism A
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing X f y hclosed
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Ahat := inferInstance
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  conv_lhs => rw [isRegularLocalRing_iff_adicCompletion_maximalIdeal]
  conv_rhs => rw [isRegularLocalRing_iff_adicCompletion_maximalIdeal]
  exact ⟨fun _ ↦ .of_ringEquiv e.symm, fun _ ↦ .of_ringEquiv e⟩

/-- A point of a universally closed scheme over a local ring which is closed in its own space
maps to the closed point of the base. -/
private lemma image_eq_maximalIdeal_of_mem_closedPoints
    (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [UniversallyClosed f]
    (x : X) (hx : x ∈ closedPoints X) :
    f.base x = (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) :=
  PrimeSpectrum.ext <| IsLocalRing.eq_maximalIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (mem_closedPoints_iff.mp (show f.base x ∈ closedPoints (Spec (.of A)) by
        rw [mem_closedPoints_iff, ← Set.image_singleton]
        exact f.isClosedMap {x} (mem_closedPoints_iff.mp hx))))

/-- A proper scheme locally of finite type over a Noetherian local ring is regular if and only
if its base change to the completion of the base ring is regular. -/
@[stacks 0BG6 "proper_equivalence"]
theorem isRegular_pullback_completion_iff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f] :
    IsRegular X ↔
      IsRegular
        (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) : Scheme.{u}) := by
  let A' := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let g : Spec (.of A') ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let Y : Scheme.{u} := pullback f g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  change IsRegular X ↔ IsRegular Y
  refine ⟨fun hX ↦ ?_, fun hY ↦ ?_⟩
  · apply ((isRegular_tfae Y).out 1 3).mpr
    refine ⟨inferInstance, fun y hy ↦ ?_⟩
    have hX' := ((isRegular_tfae X).out 1 2).mp hX
    let x : X := (pullback.fst f g).base y
    have hy' : (pullback.snd f g).base y =
        (⟨IsLocalRing.maximalIdeal A', inferInstance⟩ : PrimeSpectrum A') :=
      image_eq_maximalIdeal_of_mem_closedPoints A' (pullback.snd f g) y hy
    exact (isRegularLocalRing_stalk_pullback_completion_iff A X f x y rfl hy').2 (hX'.2 x)
  · apply ((isRegular_tfae X).out 1 3).mpr
    refine ⟨inferInstance, fun x hx ↦ ?_⟩
    have hY' := ((isRegular_tfae Y).out 1 2).mp hY
    let y' : Spec (.of A') := ⟨IsLocalRing.maximalIdeal A', inferInstance⟩
    have hx' : f.base x = g.base y' := by
      rw [image_eq_maximalIdeal_of_mem_closedPoints A f x hx]
      exact PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap (algebraMap A A')).symm
    obtain ⟨y, hyx, hyy'⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y' hx'
    exact (isRegularLocalRing_stalk_pullback_completion_iff A X f x y hyx hyy').1 (hY'.2 y)

end AlgebraicGeometry

end
