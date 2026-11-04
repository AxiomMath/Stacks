module

public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.TensorProduct.ReducedFractionRingIntegralClosure

/-!
# The integral closure of the compositum, read over the unlocalized base

Let `R` be a domain with fraction field `K`, let `A'` be an `R`-algebra with the same fraction
field — in the reduced fibre theorem `R` is the new base ring and `A'` its localization at the
prime under a point — let `O` be an `R`-algebra which is also an `A'`-algebra, with fraction
field `F`, and let `K₁ / K` be a finite extension.  Write

```
S  = integralClosure R  K₁        A₁ = integralClosure A' K₁
T  = integralClosure O  ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))
```

so that `T` is at the same time the ring named `B₁` by
`IsDiscreteValuationRing.canonicalBaseChange A' O K F K₁` and the ring in which
`Scheme.exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`
presents the local rings of a normalized base change.  **The two `S`-algebra structures that `T`
inherits from those two readings agree**: the one factoring through `O ⊗[R] S`, which is the one
the stalk identification speaks, and the one factoring through `A₁`, which is the one the
solution property of Tag 09EN(2) speaks.

This is the last join of the proof of the reduced fibre theorem.  The smoothness criterion
`AlgebraicGeometry.smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ` reads the stalk map
of `Y ⟶ Spec S` through the first structure, while
`RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl` carries the solution
property down from `A₁` to `S` through the second; the agreement below is exactly the scalar
tower `S → A₁ → T` that the second asks for.

Both structure maps send `b : S` to the class of `1 ⊗ₜ (b : K₁)` in the reduction of `F ⊗[K] K₁`:
through `O ⊗[R] S` because `1 ⊗ₜ b` goes to `1 ⊗ₜ (b : K₁)` under
`tensorProductFractionRingAlgebra`, and through `A₁` because
`IsDiscreteValuationRing.integralClosureCompositumMap` is the restriction of
`algebraMap K₁ ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))`, whose value at `(b : K₁)` is that class
by `Algebra.TensorProduct.rightAlgebra`.

## Main definitions

* `algebraIntegralClosureOfLocalizedBase`: the `S`-algebra structure on `A₁`, an element of `K₁`
  integral over `R` being integral over `A'`.
* `algebraIntegralClosureCompositumOfBase`: the `S`-algebra structure on `T` obtained from the
  `(O ⊗[R] S)`-algebra structure of `integralClosureTensorProductAlgebra`.

## Main results

* `coe_algebraMap_integralClosureCompositumOfBase`: the structure map `S → T` is the class of
  `1 ⊗ₜ (b : K₁)`.
* `algebraMap_integralClosureCompositumOfBase_eq`: the two structure maps `S → T` agree.
* `isScalarTower_integralClosureCompositumOfBase`: hence `S → A₁ → T` is a scalar tower.

## Implementation notes

`IsDiscreteValuationRing.algebraIntegralClosure`, the `A₁`-algebra structure on `T`, is a `local
instance` of
`StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction`, as is
`Algebra.TensorProduct.rightAlgebra`; both are switched on here for the same reason, so that
nothing leaks to consumers.  A consumer wanting the scalar tower switches them on too, which is
what `IsDiscreteValuationRing.canonicalBaseChange` already forces it to do.

No hypothesis relates `A'` to `R` beyond the two towers into `K₁` and into `O`: the agreement is
an identity between two descriptions of the same subring of the reduced compositum, and the
localization enters only later, through
`RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl`.

## References

* [Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  IsDiscreteValuationRing.isScalarTower_tensor_of_base
  IsDiscreteValuationRing.algebraIntegralClosure

/-! ### The integral closure over a localized base -/

section LocalizedBase

variable (R A' K₁ : Type u) [CommRing R] [CommRing A'] [Field K₁] [Algebra R A'] [Algebra R K₁]
  [Algebra A' K₁] [IsScalarTower R A' K₁]

/-- **An element of `K₁` integral over `R` is integral over any `R`-algebra `A'` inside `K₁`.**
This is the `integralClosure R K₁`-algebra structure on `integralClosure A' K₁`, given by the
inclusion of the two subrings of `K₁`. -/
@[instance_reducible]
def algebraIntegralClosureOfLocalizedBase :
    Algebra ↥(integralClosure R K₁) ↥(integralClosure A' K₁) :=
  (RingHom.codRestrict (algebraMap ↥(integralClosure R K₁) K₁) (integralClosure A' K₁)
    fun x ↦ IsIntegral.tower_top x.2).toAlgebra

/-- The inclusion `integralClosure R K₁ → integralClosure A' K₁` is the identity on
underlying elements of `K₁`. -/
@[simp]
theorem coe_algebraMap_integralClosureOfLocalizedBase (b : ↥(integralClosure R K₁)) :
    letI := algebraIntegralClosureOfLocalizedBase R A' K₁
    ((algebraMap ↥(integralClosure R K₁) ↥(integralClosure A' K₁) b : ↥(integralClosure A' K₁))
      : K₁) = (b : K₁) := rfl

/-- The inclusion of the two integral closures is compatible with their embeddings in `K₁`. -/
theorem isScalarTower_integralClosureOfLocalizedBase_right :
    letI := algebraIntegralClosureOfLocalizedBase R A' K₁
    IsScalarTower ↥(integralClosure R K₁) ↥(integralClosure A' K₁) K₁ :=
  let := algebraIntegralClosureOfLocalizedBase R A' K₁
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The inclusion of the two integral closures is compatible with the structure maps of `R`. -/
theorem isScalarTower_integralClosureOfLocalizedBase_left :
    letI := algebraIntegralClosureOfLocalizedBase R A' K₁
    IsScalarTower R ↥(integralClosure R K₁) ↥(integralClosure A' K₁) :=
  let := algebraIntegralClosureOfLocalizedBase R A' K₁
  IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext <| by
    rw [coe_algebraMap_integralClosureOfLocalizedBase]
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply R A' K₁]

end LocalizedBase

/-! ### The two structure maps of the integral closure of the compositum -/

section Compositum

variable (R A' O K F K₁ : Type u) [CommRing R] [CommRing A'] [CommRing O] [Field K] [Field F]
  [Field K₁] [Algebra R A'] [Algebra R O] [Algebra R K] [Algebra R F] [Algebra R K₁]
  [Algebra A' O] [Algebra A' K] [Algebra A' F] [Algebra A' K₁] [Algebra K F] [Algebra K K₁]
  [Algebra O F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower R K K₁]
  [IsScalarTower R A' K₁] [IsScalarTower A' O F] [IsScalarTower A' K F] [IsScalarTower A' K K₁]
  [Module.Finite R ↥(integralClosure R K₁)]

/-- **The `integralClosure R K₁`-algebra structure on the integral closure of the compositum, as
the stalk identification produces it.**  It is the structure map of `O ⊗[R] integralClosure R K₁`
restricted along the inclusion of the right factor. -/
@[instance_reducible]
def algebraIntegralClosureCompositumOfBase :
    Algebra ↥(integralClosure R K₁)
      ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))) :=
  letI := tensorProductFractionRingAlgebra R O K F ↥(integralClosure R K₁) K₁
  letI := integralClosureTensorProductAlgebra R O K F ↥(integralClosure R K₁) K₁
  ((algebraMap (O ⊗[R] ↥(integralClosure R K₁))
      ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁)))).comp
    (Algebra.TensorProduct.includeRight :
      ↥(integralClosure R K₁) →ₐ[R] O ⊗[R] ↥(integralClosure R K₁)).toRingHom).toAlgebra

/-- The structure map of `algebraIntegralClosureCompositumOfBase` is the one the stalk
identification writes down: the image of `1 ⊗ₜ b` under the structure map of
`O ⊗[R] integralClosure R K₁`. -/
theorem algebraMap_integralClosureCompositumOfBase (b : ↥(integralClosure R K₁)) :
    letI := tensorProductFractionRingAlgebra R O K F ↥(integralClosure R K₁) K₁
    letI := integralClosureTensorProductAlgebra R O K F ↥(integralClosure R K₁) K₁
    letI := algebraIntegralClosureCompositumOfBase R O K F K₁
    algebraMap ↥(integralClosure R K₁)
        ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))) b =
      algebraMap (O ⊗[R] ↥(integralClosure R K₁))
        ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁)))
        ((Algebra.TensorProduct.includeRight :
          ↥(integralClosure R K₁) →ₐ[R] O ⊗[R] ↥(integralClosure R K₁)) b) := rfl

/-- **The structure map `integralClosure R K₁ → T` is the class of `1 ⊗ₜ b`.** -/
theorem coe_algebraMap_integralClosureCompositumOfBase (b : ↥(integralClosure R K₁)) :
    letI := algebraIntegralClosureCompositumOfBase R O K F K₁
    ((algebraMap ↥(integralClosure R K₁)
          ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))) b :
        ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))))
        : (F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁)) =
      Ideal.Quotient.mk _ (1 ⊗ₜ[K] (b : K₁)) := by
  let := tensorProductFractionRingAlgebra R O K F ↥(integralClosure R K₁) K₁
  let := integralClosureTensorProductAlgebra R O K F ↥(integralClosure R K₁) K₁
  let := algebraIntegralClosureCompositumOfBase R O K F K₁
  show Ideal.Quotient.mk _ (algebraMap (O ⊗[R] ↥(integralClosure R K₁)) (F ⊗[K] K₁)
    ((Algebra.TensorProduct.includeRight :
      ↥(integralClosure R K₁) →ₐ[R] O ⊗[R] ↥(integralClosure R K₁)) b)) = _
  congr 1
  show (Algebra.TensorProduct.lift _ _ _).toRingHom (1 ⊗ₜ[R] b) = _
  simp [Algebra.TensorProduct.lift_tmul]

/-- **The two `integralClosure R K₁`-algebra structures on the integral closure of the compositum
agree.**  The one through `O ⊗[R] integralClosure R K₁` is the one the identification of the
local rings of a normalized base change speaks; the one through `integralClosure A' K₁` is the
one the solution property of Tag 09EN(2) speaks.  Both send `b` to the class of
`1 ⊗ₜ (b : K₁)`. -/
theorem algebraMap_integralClosureCompositumOfBase_eq (b : ↥(integralClosure R K₁)) :
    letI := algebraIntegralClosureCompositumOfBase R O K F K₁
    letI := algebraIntegralClosureOfLocalizedBase R A' K₁
    algebraMap ↥(integralClosure R K₁)
        ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))) b =
      IsDiscreteValuationRing.integralClosureCompositumMap A' O K F K₁
        (algebraMap ↥(integralClosure R K₁) ↥(integralClosure A' K₁) b) := by
  let := algebraIntegralClosureCompositumOfBase R O K F K₁
  let := algebraIntegralClosureOfLocalizedBase R A' K₁
  refine Subtype.ext ?_
  rw [coe_algebraMap_integralClosureCompositumOfBase,
    IsDiscreteValuationRing.coe_integralClosureCompositumMap,
    coe_algebraMap_integralClosureOfLocalizedBase]
  rfl

/-- **The scalar tower `integralClosure R K₁ → integralClosure A' K₁ → T`.**  This is the
compatibility that `RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl` asks
for, in the shape the stalk identification supplies. -/
theorem isScalarTower_integralClosureCompositumOfBase :
    letI := algebraIntegralClosureCompositumOfBase R O K F K₁
    letI := algebraIntegralClosureOfLocalizedBase R A' K₁
    IsScalarTower ↥(integralClosure R K₁) ↥(integralClosure A' K₁)
      ↥(integralClosure O ((F ⊗[K] K₁) ⧸ nilradical (F ⊗[K] K₁))) :=
  let := algebraIntegralClosureCompositumOfBase R O K F K₁
  let := algebraIntegralClosureOfLocalizedBase R A' K₁
  IsScalarTower.of_algebraMap_eq fun b ↦
    algebraMap_integralClosureCompositumOfBase_eq R A' O K F K₁ b

end Compositum

end
