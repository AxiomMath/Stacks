module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Homology.TorAmplitude.ChangeOfRings
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of relative Tor amplitude across a square of rings

Let

```
P ---β---> P'
^          ^
φ          φ'
|          |
A ---α---> A'
```

be a commutative square of commutative rings with `α` flat and `β` faithfully flat, and let `K`
be a complex of `P`-modules.  If the base change `K ⊗_P P'`, read over `A'`, has Tor amplitude
in `[a, b]`, then `K`, read over `A`, has Tor amplitude in `[a, b]`.

This is the ring-level content of the descent half of Stacks 0DL2: at a geometric point of the
upper-left corner of a cartesian square of algebraic spaces whose lower edge is a member of an
fpqc covering, `A → A'` is the homomorphism of stalks of the base, flat because the covering
member is, and `P → P'` the homomorphism of stalks of the source, flat and local hence
faithfully flat.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_of_flatSquare`: the
  descent statement above.

## Implementation notes

The argument is the composite of two results already in the library.  Restriction along the
flat `α` keeps the bound (Stacks 066J), so `K ⊗_P P'` read over `A` has Tor amplitude in
`[a, b]`; the square identifies that restriction with the restriction along `A → P → P'`.
Stacks 0DJF then descends the bound along the faithfully flat `β`, for a complex read over a
third ring: this is exactly the shape of `K ⊗_P P'` over `A`.  Stacks 0DJF is stated for the
projective-resolution Tor amplitude, which agrees with the canonical one on every complex by
`AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF`.

The source's own argument instead identifies `K ⊗^𝐋_P P'` with `K ⊗^𝐋_A A'` by Stacks 0661 and
applies Stacks 068S over `A → A'`; that identification holds only after a further flat base
change (the upper-left corner `P'` is flat over `P ⊗_A A'`, not equal to it), and the route above
avoids it.

## References

* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 066J](https://stacks.math.columbia.edu/tag/066J)
* [Stacks Project, Tag 0DJF](https://stacks.math.columbia.edu/tag/0DJF)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-- **Relative Tor amplitude descends across a flat, faithfully flat square of rings.**  Let
`φ' ∘ α = β ∘ φ` be a commutative square of commutative rings with `α : A → A'` flat and
`β : P → P'` faithfully flat, and let `K` be a complex of `P`-modules.  If `K ⊗_P P'`, read over
`A'` through `φ'`, has Tor amplitude in `[a, b]`, then `K`, read over `A` through `φ`, has Tor
amplitude in `[a, b]`.

The base change is termwise; `β` being flat, it represents the derived base change. -/
@[ega "IV 2.5.1" "special case", sga "6 I 5.7" "Exercise 5.7 a)"]
theorem hasTorAmplitudeCanonical_restrictScalars_of_flatSquare
    {A A' P P' : Type u} [CommRing A] [CommRing A'] [CommRing P] [CommRing P']
    (φ : A →+* P) (φ' : A' →+* P') (α : A →+* A') (β : P →+* P')
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{u} P) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonical A' (DerivedCategory.Q.obj
      ((CochainComplex.restrictScalars φ').obj ((CochainComplex.extendScalars β).obj K))) a b) :
    HasTorAmplitudeCanonical A
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars φ).obj K)) a b := by
  let : Algebra A A' := α.toAlgebra
  have : Module.Flat A A' := RingHom.flat_algebraMap_iff.mp hα
  set L := (CochainComplex.restrictScalars φ').obj ((CochainComplex.extendScalars β).obj K)
  have h₁ : HasTorAmplitudeCanonical A
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars α).obj L)) a b := by
    rw [hasTorAmplitudeCanonical_iff_hasFlatRepresentative] at h ⊢
    exact hasTorAmplitudeIn_restrictScalars A A' L a b h
  have h₂ : HasTorAmplitudeCanonical A (DerivedCategory.Q.obj
      ((CochainComplex.restrictScalars (β.comp φ)).obj
        ((CochainComplex.extendScalars β).obj K))) a b := by
    refine AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (DerivedCategory.Q.mapIso ?_) a b h₁
    exact ((NatIso.mapHomologicalComplex
      (ModuleCat.restrictScalarsComp'.{u} α φ' (β.comp φ) hsq.symm) (ComplexShape.up ℤ)).app
        ((CochainComplex.extendScalars β).obj K)).symm
  let : Algebra A P := φ.toAlgebra
  let : Algebra P P' := β.toAlgebra
  let : Algebra A P' := (β.comp φ).toAlgebra
  have : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat P P' := RingHom.faithfullyFlat_algebraMap_iff.mp hβ
  have h₃ :=
    (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
      _ a b).mp h₂
  exact
    (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
      _ a b).mpr ((FaithfullyFlat.hasTorAmplitudeIn_iff_extendScalars A P P' K a b).mpr h₃)

end StacksDraft.TorAmplitude

end
