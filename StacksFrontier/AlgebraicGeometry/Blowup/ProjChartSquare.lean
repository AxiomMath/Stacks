module

public import StacksFrontier.AlgebraicGeometry.Blowup.AwayBaseChange

/-!
# The base-change square of a standard affine chart of `Proj`, over the degree-zero part

Let `A` be a graded `R`-algebra with grading `𝒜 : ℕ → Submodule R A`, let `S` be an `R`-algebra
and let `a : A` be homogeneous of degree `d`. `StacksFrontier/AlgebraicGeometry/Blowup/
AwayBaseChange.lean` shows that the standard affine chart of `Proj (S ⊗[R] A)` attached to
`1 ⊗ₜ a` is the base change of the chart of `Proj A` attached to `a` along `R → S`. This file
turns that into the statement needed for a relative `Proj`: the square

```
Spec (Away (S ⊗[R] 𝒜) (1 ⊗ₜ a)) ⟶ Spec (Away 𝒜 a)
          |                              |
          v                              v
   Spec (S ⊗[R] 𝒜) 0            ⟶   Spec (𝒜 0)
```

is cartesian, that is, the chart of `Proj (S ⊗[R] A)` is the fibre product of the chart of
`Proj A` with `Spec` of the degree-zero part of the base change over `Spec (𝒜 0)`. This is the
chart-level form of Stacks tag 01NO.

The passage from one square to the other is a cancellation: both charts and both degree-zero
parts are base changes along `R → S`, and a square whose composite with a cartesian square
below it is cartesian is itself cartesian (`CategoryTheory.IsPullback.of_bot`).

## Main definitions

* `Stacks.ProjBaseChange.zeroBaseChange` is the comparison homomorphism
  `S ⊗[R] 𝒜 0 →+* (S ⊗[R] 𝒜) 0` on degree-zero parts.
* `Stacks.ProjBaseChange.zeroBaseChangeEquiv` is the same map as a ring isomorphism.

## Main results

* `Stacks.ProjBaseChange.isPushout_gradedZeroRingHom`: the degree-zero parts form a pushout
  square of rings.
* `Stacks.ProjBaseChange.isPullback_Spec_gradedZeroRingHom`: the same square of affine schemes
  is cartesian.
* `Stacks.ProjBaseChange.isPullback_Spec_awayMap_toZero`: **the chart-level form of tag 01NO**,
  the square above.

## Implementation notes

The degree-zero comparison map is bijective for the same reason as the chart-level one, but much
more directly: on degree-zero parts it is literally `Submodule.toBaseChange`, which is bijective
by `DirectSum.toBaseChange_bijective` because the grading decomposes `A` into `R`-module
summands. The only work is to see that the ring homomorphism built from the universal property of
the tensor product has that underlying function, which is checked on the generators.

As in `AwayBaseChange.lean`, the `R`-algebra structures on the two base-changed objects are
`local instance`s and no statement mentions them.

No `@[stacks]` attribute is attached: tag 01NO is the cartesianness of the base-change square for
the whole of `Proj`, of which this is the statement on one standard affine chart.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct HomogeneousLocalization CommRingCat

universe u

namespace Stacks.ProjBaseChange

/-! ### The structure map of a chart factors through the degree-zero part -/

section Factor

variable {R₀ A₀ : Type u} [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
  (𝒜₀ : ℕ → Submodule R₀ A₀) [GradedRing 𝒜₀] (x : Submonoid A₀)

/-- The structure map of a chart over the base ring factors through the degree-zero part. This is
how the vertical composites of the three-row diagram below are recognised. -/
theorem Spec_map_fromZeroRingHom_comp :
    Spec.map (ofHom (fromZeroRingHom 𝒜₀ x)) ≫ Spec.map (ofHom (algebraMap R₀ ↥(𝒜₀ 0))) =
      Spec.map (ofHom (algebraMap R₀ (HomogeneousLocalization 𝒜₀ x))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end Factor

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]

/-! ### The degree-zero part of the base change -/

section Zero

/-- The `R`-algebra structure on the degree-zero part of the base-changed grading obtained from
its `S`-algebra structure along `R → S`. It is a `local instance` and no statement of this file
mentions it. -/
@[instance_reducible]
def zeroAlgebraBase : Algebra R ↥(grading 𝒜 S 0) :=
  ((algebraMap S ↥(grading 𝒜 S 0)).comp (algebraMap R S)).toAlgebra

attribute [local instance] zeroAlgebraBase

/-- The degree-zero component of `Stacks.ProjBaseChange.includeRight` is a homomorphism of
`R`-algebras: it sends the image of a scalar `r` to `1 ⊗ₜ r`, which is the image of `r` under the
structure map of the base change. -/
def includeZeroₐ : ↥(𝒜 0) →ₐ[R] ↥(grading 𝒜 S 0) where
  __ := (includeRight 𝒜 S).gradedZeroRingHom
  commutes' r := by
    refine Subtype.ext ?_
    change (1 : S) ⊗ₜ[R] algebraMap R A r = algebraMap S (S ⊗[R] A) (algebraMap R S r)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      Algebra.algebraMap_eq_smul_one (R := R) (A := S), Algebra.algebraMap_eq_smul_one (R := R),
      TensorProduct.smul_tmul]

/-- The structure map of the degree-zero part of the base change over `S`, read as a homomorphism
of `R`-algebras. -/
def toZeroₐ : S →ₐ[R] ↥(grading 𝒜 S 0) where
  __ := algebraMap S ↥(grading 𝒜 S 0)
  commutes' _ := rfl

/-- **The comparison homomorphism on degree-zero parts.** -/
def zeroBaseChange : S ⊗[R] ↥(𝒜 0) →+* ↥(grading 𝒜 S 0) :=
  (Algebra.TensorProduct.productMap (toZeroₐ 𝒜 S) (includeZeroₐ 𝒜 S)).toRingHom

/-- The comparison homomorphism on degree-zero parts is `Submodule.toBaseChange`, which is where
its bijectivity comes from. -/
theorem zeroBaseChange_eq_toBaseChange (u : S ⊗[R] ↥(𝒜 0)) :
    zeroBaseChange 𝒜 S u = (𝒜 0).toBaseChange S u := by
  induction u with
  | tmul s y =>
      refine Subtype.ext ?_
      rw [Submodule.coe_toBaseChange_tmul]
      show ((s ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] (y : A)) : S ⊗[R] A) = s ⊗ₜ[R] (y : A)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- **The degree-zero part of the base change is the base change of the degree-zero part.** -/
theorem zeroBaseChange_bijective : Function.Bijective (zeroBaseChange 𝒜 S) := by
  have h : (zeroBaseChange 𝒜 S : S ⊗[R] ↥(𝒜 0) → ↥(grading 𝒜 S 0)) = (𝒜 0).toBaseChange S :=
    funext (zeroBaseChange_eq_toBaseChange 𝒜 S)
  rw [h]
  exact DirectSum.toBaseChange_bijective 𝒜 0

/-- **The degree-zero part of the base change is the base change of the degree-zero part,** as a
ring isomorphism. -/
def zeroBaseChangeEquiv : S ⊗[R] ↥(𝒜 0) ≃+* ↥(grading 𝒜 S 0) :=
  RingEquiv.ofBijective (zeroBaseChange 𝒜 S) (zeroBaseChange_bijective 𝒜 S)

/-- **The degree-zero parts form a pushout square of rings.** -/
theorem isPushout_gradedZeroRingHom :
    IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R ↥(𝒜 0)))
      (ofHom (algebraMap S ↥(grading 𝒜 S 0)))
      (ofHom (includeRight 𝒜 S).gradedZeroRingHom) := by
  refine (CommRingCat.isPushout_tensorProduct R S ↥(𝒜 0)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (zeroBaseChangeEquiv 𝒜 S).toCommRingCatIso (by simp) (by simp) ?_ ?_
  all_goals
    rw [Iso.refl_hom, Category.id_comp]
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  · change zeroBaseChange 𝒜 S (x ⊗ₜ[R] 1) = _
    simp [zeroBaseChange, toZeroₐ]
  · change zeroBaseChange 𝒜 S (1 ⊗ₜ[R] x) = _
    simp [zeroBaseChange, includeZeroₐ]

/-- **The degree-zero base-change square of affine schemes is cartesian.** -/
theorem isPullback_Spec_gradedZeroRingHom :
    IsPullback (Spec.map (ofHom (includeRight 𝒜 S).gradedZeroRingHom))
      (Spec.map (ofHom (algebraMap S ↥(grading 𝒜 S 0))))
      (Spec.map (ofHom (algebraMap R ↥(𝒜 0)))) (Spec.map (ofHom (algebraMap R S))) :=
  (AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_gradedZeroRingHom 𝒜 S)).flip

end Zero

/-! ### The chart square over the degree-zero part -/

section Chart

variable {d : ℕ} {a : A}

attribute [local instance] chartAlgebraBase zeroAlgebraBase

/-- **The chart-level form of Stacks tag 01NO.** The standard affine chart of
`Proj (S ⊗[R] A)` attached to `1 ⊗ₜ a` is the fibre product of the standard affine chart of
`Proj A` attached to `a` with `Spec` of the degree-zero part of the base-changed grading, over
`Spec (𝒜 0)`. -/
theorem isPullback_Spec_awayMap_toZero (ha : a ∈ 𝒜 d) :
    IsPullback (Spec.map (ofHom (awayMap 𝒜 S a)))
      (Spec.map (ofHom (fromZeroRingHom (grading 𝒜 S)
        (Submonoid.powers ((1 : S) ⊗ₜ[R] a)))))
      (Spec.map (ofHom (fromZeroRingHom 𝒜 (Submonoid.powers a))))
      (Spec.map (ofHom (includeRight 𝒜 S).gradedZeroRingHom)) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_Spec_gradedZeroRingHom 𝒜 S)
  · rw [Spec_map_fromZeroRingHom_comp (grading 𝒜 S) (Submonoid.powers ((1 : S) ⊗ₜ[R] a)),
      Spec_map_fromZeroRingHom_comp 𝒜 (Submonoid.powers a)]
    exact (isPullback_Spec_awayMap 𝒜 S ha).flip
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f ↦ Spec.map (ofHom f))
      (AlgebraicGeometry.Proj.awayMap_comp_fromZeroRingHom (includeRight 𝒜 S) a)

end Chart

end Stacks.ProjBaseChange

end
