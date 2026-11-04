module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetSingleMorphism

/-!
# Descending an open subset along the spectrum of a faithfully flat ring map

Let `R → A` be a faithfully flat ring map, let `C₀` be an `R`-algebra and let `C` be the base
change `A ⊗[R] C₀`, presented as a `C₀`-algebra satisfying `Algebra.IsPushout R A C₀ C`.  Then
`Spec C → Spec C₀` is surjective, flat and quasi-compact, so an open subset of `Spec C` whose
two preimages in `Spec C ×_{Spec C₀} Spec C` agree descends uniquely to an open subset of
`Spec C₀`.

This is the last step of the proof of Stacks 0APK over an affine base: there `C₀` is the ring
called `R'`, `C = R' ⊗_R A` is the ring of functions on the set-theoretically invariant subset
`E`, and the open being descended is the image of the invariant open `W` under the canonical
embedding of Stacks 0API.

## Main results

* `Module.FaithfullyFlat.of_isPushout'` : faithful flatness of `R → A` passes to the base change
  `C₀ → C`.
* `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_faithfullyFlat` : Stacks 03N0 for the
  spectrum of a faithfully flat ring map.
* `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout` : the same for the base change
  of a faithfully flat ring map along an arbitrary ring map out of its source.

## Implementation notes

No new tag is claimed.  Stacks 03N0 is already carried, for a covering by a single surjective
flat quasi-compact morphism, by
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective`; the
statements here are that statement read at a morphism of affine schemes, which is a proof step of
Stacks 0APK and not a separate part of 03N0.  The repository refuses tags on proof steps in the
same way at `StacksFrontier/AlgebraicGeometry/Descent/AffineFlatChartCandidate.lean`.

Faithful flatness of the base change is not obtained from
`RingHom.FaithfullyFlat.isStableUnderBaseChange`, which would require exhibiting the square as a
`MorphismProperty` base change.  It is read off the Mathlib instance
`Module.FaithfullyFlat C₀ (C₀ ⊗[R] A)` through the comparison `Algebra.IsPushout.equiv` of the
pushout hypothesis, taken in the form `Algebra.IsPushout R C₀ A C` so that the comparison is
`C₀`-linear.

The compatibility hypothesis is stated on underlying sets of the fibre product of schemes, as
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective` states
it, and not on `Spec (C ⊗[C₀] C)`: the comparison of the two is not needed for the descent and
would be an extra identification for the consumer to discharge.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct

universe u

/-- **Faithful flatness passes to a base change.**  If `R → A` is faithfully flat and `C` is the
base change of `A` along a ring map `R → C₀`, in the sense that `Algebra.IsPushout R A C₀ C`,
then `C₀ → C` is faithfully flat.

This is the form with the four rings taken explicitly in one universe;
`Module.FaithfullyFlat.of_isPushout` is the same statement with them implicit and in
independent universes. -/
@[ega "0 6.6.3" "special case", ega "IV 2.2.11" "(i), special case"]
theorem Module.FaithfullyFlat.of_isPushout' (R A C₀ C : Type u) [CommRing R] [CommRing A]
    [CommRing C₀] [CommRing C] [Algebra R A] [Algebra R C₀] [Algebra R C] [Algebra A C]
    [Algebra C₀ C] [IsScalarTower R A C] [IsScalarTower R C₀ C]
    [Algebra.IsPushout R A C₀ C] [Module.FaithfullyFlat R A] :
    Module.FaithfullyFlat C₀ C :=
  have h : Algebra.IsPushout R C₀ A C := Algebra.IsPushout.symm inferInstance
  Module.FaithfullyFlat.of_linearEquiv _ _ h.equiv.symm.toLinearEquiv

namespace AlgebraicGeometry

/-- **Stacks 03N0 for the spectrum of a faithfully flat ring map.**  Let `f : R' ⟶ B` be a
faithfully flat map of commutative rings and let `W' ⊆ Spec B` be an open subscheme whose two
preimages in `Spec B ×_{Spec R'} Spec B` agree.  Then `W'` is the preimage of a unique open
subscheme of `Spec R'`.

This is the shape in which the last step of the proof of Stacks 0APK consumes Stacks 03N0: the
covering morphism there is the base change `Spec (R' ⊗_R A) → Spec R'` of a faithfully flat ring
map, which is affine, hence quasi-compact, and surjective and flat because the ring map is
faithfully flat. -/
theorem existsUnique_opens_preimage_eq_of_faithfullyFlat {R' B : CommRingCat.{u}} (f : R' ⟶ B)
    (hf : f.hom.FaithfullyFlat) (W' : (Spec B).Opens)
    (hcompat : (pullback.fst (Spec.map f) (Spec.map f)).base ⁻¹' (W' : Set (Spec B)) =
      (pullback.snd (Spec.map f) (Spec.map f)).base ⁻¹' (W' : Set (Spec B))) :
    ∃! W : (Spec R').Opens, Spec.map f ⁻¹ᵁ W = W' := by
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff f).mpr hf
  have := hflat
  have := hsurj
  exact existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective
    (Spec.map f) W' hcompat

/-- **Stacks 03N0 along the base change of a faithfully flat ring map.**  Let `R → A` be
faithfully flat, let `C₀` be an `R`-algebra and let `C` be the base change `A ⊗[R] C₀`, in the
sense that `Algebra.IsPushout R A C₀ C`.  An open subscheme of `Spec C` whose two preimages in
`Spec C ×_{Spec C₀} Spec C` agree is the preimage of a unique open subscheme of `Spec C₀`.

This is the step of the proof of Stacks 0APK which produces the open `W₀ ⊆ Spec R'` whose base
change to `Spec A` is the image `j(W)` of the invariant open `W`. -/
@[sga "3 V 7.3" "special case"]
theorem existsUnique_opens_preimage_eq_of_isPushout (R A C₀ C : Type u) [CommRing R] [CommRing A]
    [CommRing C₀] [CommRing C] [Algebra R A] [Algebra R C₀] [Algebra R C] [Algebra A C]
    [Algebra C₀ C] [IsScalarTower R A C] [IsScalarTower R C₀ C]
    [Algebra.IsPushout R A C₀ C] [Module.FaithfullyFlat R A]
    (W' : (Spec (CommRingCat.of C)).Opens)
    (hcompat :
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))
            (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))).base ⁻¹'
          (W' : Set (Spec (CommRingCat.of C))) =
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))
            (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))).base ⁻¹'
          (W' : Set (Spec (CommRingCat.of C)))) :
    ∃! W : (Spec (CommRingCat.of C₀)).Opens,
      Spec.map (CommRingCat.ofHom (algebraMap C₀ C)) ⁻¹ᵁ W = W' := by
  have : Module.FaithfullyFlat C₀ C := Module.FaithfullyFlat.of_isPushout' R A C₀ C
  refine existsUnique_opens_preimage_eq_of_faithfullyFlat
    (CommRingCat.ofHom (algebraMap C₀ C)) ?_ W' hcompat
  rw [CommRingCat.hom_ofHom]
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

end AlgebraicGeometry

end
