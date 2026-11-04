module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosedPointRationalPoint
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# Residue fields of a scheme over an affine base, at a point with maximal prime

Let `f : X ⟶ Spec R` and let `x` be a point of `X`. This file produces the two inputs that make
the residue field extension `κ(x)/κ(f x)` **purely inseparable**:

* **separable closedness of `κ(f x)`**, when `R` is local with separably closed residue field and
  `x` lies over the closed point: the residue field of `Spec R` at a point whose prime is the
  maximal ideal is the residue field of the local ring `R` itself;
* **algebraicity of `κ(x)` over `κ(f x)`**, when the ring map `R ⟶ κ(x)` adjoint to
  `X.fromSpecResidueField x ≫ f` is integral.

For an affine `X` the integrality input is in turn supplied by integrality of `Γ(X, ⊤)` over `R`
together with maximality of the prime of `Γ(X, ⊤)` cut out by `x` — which holds, by going up,
precisely because `x` lies over the closed point. Going through the adjoint ring map rather than
through primes of `Γ(X, ⊤)` is what makes this cheap: the adjoint map is the structure map
`R ⟶ Γ(X, ⊤)` followed by a map which is *surjective*, because the residue field at a maximal
ideal is a quotient, so integrality transports along it with no further bookkeeping.

## Main results

* `AlgebraicGeometry.isSepClosed_residueField_spec_of_asIdeal_eq_maximalIdeal`: the residue field
  of `Spec R` at the closed point of a local ring `R` is separably closed when that of `R` is.
* `AlgebraicGeometry.surjective_preimage_fromSpecResidueField_comp_toSpecΓ`: on an affine scheme
  the global functions surject onto the residue field at a point whose prime is maximal.
* `AlgebraicGeometry.isIntegral_preimage_fromSpecResidueField_comp_toSpecΓ_comp`: integrality of
  the adjoint ring map at such a point.
* `AlgebraicGeometry.isPurelyInseparable_residueField_of_isIntegral`: **the residue field
  extension at a point is purely inseparable** when the residue field of the image point is
  separably closed and the adjoint ring map is integral.

## Implementation notes

The algebra structure on `κ(x)` over `κ(f x)` is an instance argument pinned to
`AlgebraicGeometry.Scheme.Hom.residueFieldMap` by an equation, rather than installed by a `let`
inside the statement: a `let`-bound instance is not the instance the caller has, and the caller
is who consumes the pure inseparability. This is the same shape as
`AlgebraicGeometry.eq_of_comp_eq_of_isPurelyInseparable`, which is the consumer.

Separable closedness is a hypothesis on the *scheme* residue field `κ(f x)` rather than on
`Ideal.ResidueField`, and the point over which the fibre is taken is a variable constrained by an
equation of ideals rather than the closed point itself. Both choices are forced by instance
resolution: `Field ↥((Spec R).residueField p)` is found for a `p` of type `↥(Spec R)` but not for
`IsLocalRing.closedPoint R` coerced into that type, and rewriting an ideal underneath
`Ideal.ResidueField` is not a type-correct motive, because the primality instance depends on it.

Pure inseparability is produced by Mathlib's instance
`Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`, so the proof only installs the inputs
it wants: separable closedness of the base, the scalar tower `R / κ(f x) / κ(x)`, and integrality
over `R`. Algebraicity over `κ(f x)` is then `Algebra.IsIntegral.tower_top`.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The residue field of `Spec R` at a point whose prime is the maximal ideal of a local ring
`R` is separably closed as soon as the residue field of `R` is.** The two fields are identified
through the residue field of the prime: the quotient of `R` by a maximal ideal already is its own
residue field. -/
theorem isSepClosed_residueField_spec_of_asIdeal_eq_maximalIdeal (R : CommRingCat.{u})
    [IsLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)] (x : Spec R)
    (hx : x.asIdeal = IsLocalRing.maximalIdeal R) :
    IsSepClosed ((Spec R).residueField x) := by
  have : x.asIdeal.IsMaximal := by rw [hx]; infer_instance
  have e : (Spec R).residueField x ≃+* IsLocalRing.ResidueField R :=
    (Scheme.Spec.residueFieldIso R x).commRingCatIsoToRingEquiv.trans
      ((RingEquiv.ofBijective _
        (Ideal.bijective_algebraMap_quotient_residueField x.asIdeal)).symm.trans
          (Ideal.quotEquivOfEq hx))
  exact IsSepClosed.of_ringEquiv e

/-- **On an affine scheme the global functions surject onto the residue field at a point whose
prime is maximal.** The adjoint ring map of `X.fromSpecResidueField x ≫ X.toSpecΓ` is the map from
`Γ(X, ⊤)` to the residue field of that prime, which is surjective because the prime is maximal,
followed by two isomorphisms. -/
theorem surjective_preimage_fromSpecResidueField_comp_toSpecΓ {X : Scheme.{u}} [IsAffine X]
    (x : X) (hx : (X.toSpecΓ.base x).asIdeal.IsMaximal) :
    Function.Surjective (Spec.preimage (X.fromSpecResidueField x ≫ X.toSpecΓ)).hom := by
  have surj_of_iso : ∀ {A B : CommRingCat.{u}} (e : A ⟶ B) [IsIso e], Function.Surjective e.hom :=
    fun _ _ => ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective
  have := hx
  rw [Spec.preimage_fromSpecResidueField_comp X.toSpecΓ x]
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp] using
    ((surj_of_iso _).comp (surj_of_iso _)).comp (Ideal.algebraMap_residueField_surjective _)

/-- **Integrality of the ring map from the base to the residue field at a point of an affine
scheme over `Spec R` whose prime is maximal.** The adjoint ring map is the structure map
`R ⟶ Γ(X, ⊤)` followed by a surjection onto the residue field, so it is integral as soon as the
structure map is. -/
theorem isIntegral_preimage_fromSpecResidueField_comp_toSpecΓ_comp {X : Scheme.{u}} [IsAffine X]
    {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) (x : X) (hφ : RingHom.IsIntegral φ.hom)
    (hx : (X.toSpecΓ.base x).asIdeal.IsMaximal) :
    RingHom.IsIntegral
      (Spec.preimage (X.fromSpecResidueField x ≫ X.toSpecΓ ≫ Spec.map φ)).hom := by
  rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp]
  exact RingHom.IsIntegral.trans φ.hom _ hφ
    (RingHom.isIntegral_of_surjective _
      (surjective_preimage_fromSpecResidueField_comp_toSpecΓ x hx))

/-- **The residue field extension at a point is purely inseparable** when the residue field of
the image point is separably closed and the ring map from the base to the residue field of the
point is integral.

`κ(x)` is integral, hence algebraic, over `κ(f x)`, because it is integral over `R` and `R` maps
into `κ(x)` through `κ(f x)`; an algebraic extension of a separably closed field is purely
inseparable. -/
theorem isPurelyInseparable_residueField_of_isIntegral {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (x : X) [IsSepClosed ((Spec R).residueField (f.base x))]
    (hint : RingHom.IsIntegral (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom)
    [Algebra ((Spec R).residueField (f.base x)) (X.residueField x)]
    (hcompat : algebraMap ((Spec R).residueField (f.base x)) (X.residueField x) =
      (f.residueFieldMap x).hom) :
    IsPurelyInseparable ((Spec R).residueField (f.base x)) (X.residueField x) := by
  let _ : Algebra R (X.residueField x) :=
    (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
  have : Algebra.IsIntegral R (X.residueField x) := ⟨hint⟩
  have : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  let _ : Algebra R ((Spec R).residueField (f.base x)) :=
    (CommRingCat.ofHom (algebraMap R (f.base x).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (f.base x)).inv).hom.toAlgebra
  have : IsScalarTower R ((Spec R).residueField (f.base x)) (X.residueField x) := by
    have h := Spec.preimage_fromSpecResidueField_comp f x
    refine IsScalarTower.of_algebraMap_eq fun z => ?_
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, hcompat, h]
    rfl
  have : Algebra.IsIntegral ((Spec R).residueField (f.base x)) (X.residueField x) :=
    Algebra.IsIntegral.tower_top R
  infer_instance

end AlgebraicGeometry

end

end
