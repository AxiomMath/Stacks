module

public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElement
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology

/-!
# Lift classes at the field's own dual numbers

Let `A` be a `Λ`-algebra and `k` an `A`-algebra which is a field, and let `x` be an object of
a category fibred in groupoids over the big fppf site of `S`, lying over `Spec A`. The
isomorphism classes of lifts of `x` to the trivial square-zero extension `A[k]`, where `k`
carries its `A`-module structure, are identified by the Rim–Schlessinger input
`Deformation.Artin.baseChangeLiftClassesEquiv` with the isomorphism classes of lifts, over
the trivial square-zero extension `k[k]` of `k` by itself, of the restriction of `x` to the
point `Spec k` determined by the `A`-algebra structure. The comparison of module structures
used is the identity on the underlying field, since the two `A`-module and `k`-module
structures that the `A`-algebra `k` puts on itself agree through `Algebra.smul_def`.

This is part of the second piece of the comparison, for Stacks tag 07YM, between the lifting
property defining `Deformation.Artin.IsVersalAt` and the tangent-space description of
versality: it moves the tangent-space naturality fact of
`Deformation.Artin.isCanonicalLiftTransition_canonicalTangentMap`, stated over `A[k]`, down
to lift classes over `k[k]`, the extension that a witness of the lifting property at the
residue field `k` actually lives over.

## Main definitions

* `Deformation.Artin.coeffCompare` — the comparison of the `A`-module and `k`-module
  structures that the `A`-algebra `k` carries on itself, as the identity on the underlying
  field.

## Main results

* `Deformation.Artin.canonicalFieldBaseChangeEquiv` — the identification of lift classes over
  `A[k]` with lift classes, over `k[k]`, of the restriction of `x` to `Spec k`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

variable (A k : Type u) [CommRing A] [Field k] [Algebra A k]

/-- The comparison of the `A`-module and `k`-module structures that the `A`-algebra `k`
carries on itself, as the identity on the underlying field. -/
public def coeffCompare : (ModuleCat.of A k : Type u) →+ (ModuleCat.of k k : Type u) :=
  AddMonoidHom.id k

/-- The comparison `Deformation.Artin.coeffCompare` is semilinear over the structure map
`A ⟶ k`: the `A`-action on `k` agrees with scaling by the image of the structure map, by
`Algebra.smul_def`. -/
public theorem coeffCompare_smul (a : A) (m : (ModuleCat.of A k : Type u)) :
    coeffCompare A k (a • m) = algebraMap A k a • coeffCompare A k m := by
  change a • m = algebraMap A k a • m
  rw [Algebra.smul_def, smul_eq_mul]

/-- The comparison `Deformation.Artin.coeffCompare` is bijective, being the identity. -/
public theorem coeffCompare_bijective : Function.Bijective (coeffCompare A k) :=
  Function.bijective_id

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hAk : B.Contains (Spec (.of k)))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))

/-- **Stacks 07YM.** The isomorphism classes of lifts of `x` over the dual numbers `A[k]`,
`k` carrying its `A`-module structure, are the isomorphism classes of lifts, over the dual
numbers `k[k]` of `k` by itself, of the restriction of `x` to `Spec k` along the point
determined by the `A`-algebra structure on `k`. This is
`Deformation.Artin.baseChangeLiftClassesEquiv` specialized at the identity comparison
`Deformation.Artin.coeffCompare` of the two module structures that the `A`-algebra `k`
carries on itself. -/
public noncomputable def canonicalFieldBaseChangeEquiv :
    letI : p.IsFibered := hp.isFibered
    squareZeroLiftClasses A B S hS toS hA p x hx (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) ≃
      squareZeroLiftClasses k B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk p
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).1
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) :=
  baseChangeLiftClassesEquiv (algebraMap A k) B S hS toS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
    (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
    (coeffCompare A k) (coeffCompare_smul A k) p hp hRS (coeffCompare_bijective A k) x hx

end Deformation.Artin
