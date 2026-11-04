module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.MonogenicPresentation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksCore.Tactic.StacksAttribute

/-!
# A deformation of the multiplicative group: coordinate rings and points

For an element `π` of a commutative ring `A` the affine scheme `Spec A[x, 1/(πx + 1)]` carries
the group law `x + y = πxy + x + y`, with neutral element the origin. It is the additive group
for `π = 0` and is isomorphic to the multiplicative group whenever `π` is a unit, the
isomorphism being `x ↦ πx + 1`. Write `G^{(π)}` for this group scheme over `Spec A`.

Now let `ζ` be an `ℓ`-th root of unity in `A` for which `X ^ ℓ - 1` splits as the product of
the `X - ζ ^ i`, and put `π = ζ - 1`. There is a monic polynomial `Φ` of degree `ℓ` with
`(π X + 1) ^ ℓ = π ^ ℓ Φ + 1`, namely the product of the `X - σ_i` over the points
`σ_i = 1 + ζ + ⋯ + ζ ^ (i - 1)`, and substituting `Φ` for the variable defines a morphism of
group schemes `f : G^{(π)} → G^{(π ^ ℓ)}`.

This file sets up the algebra: the coordinate rings, the comultiplication, the polynomial `Φ`,
the map of coordinate rings dual to `f`, and the groups of points.

## Main definitions

* `AlgebraicGeometry.MultiplicativeDeformation.coordinateRing` is the Hopf algebra
  `A[x, 1/(πx + 1)]`, `AlgebraicGeometry.MultiplicativeDeformation.coordinateGenerator` its
  generator and `AlgebraicGeometry.MultiplicativeDeformation.comultiplication` the
  comultiplication `x ↦ πx ⊗ x + x ⊗ 1 + 1 ⊗ x`.
* `AlgebraicGeometry.MultiplicativeDeformation.DeformedPoint` is the group of `R`-points of
  `G^{(π)}` and `AlgebraicGeometry.MultiplicativeDeformation.pointOfAlgHom` its comparison with
  `A`-algebra maps out of the coordinate ring.
* `AlgebraicGeometry.MultiplicativeDeformation.sigmaPoint` is `σ_i` and
  `AlgebraicGeometry.MultiplicativeDeformation.constantPoint` is `σ_i` regarded as an
  `A`-point of `G^{(π)}`.
* `AlgebraicGeometry.MultiplicativeDeformation.isogenyPolynomial` is `Φ`,
  `AlgebraicGeometry.MultiplicativeDeformation.isogeny` the map of coordinate rings dual to
  `f`, and `AlgebraicGeometry.MultiplicativeDeformation.isogenyOnPoints` the map `f` induces
  on points.
* `AlgebraicGeometry.MultiplicativeDeformation.kernelCoordinateRing` is the coordinate ring of
  the kernel of `f`, that is of the closed subscheme `Φ(s) = 0` of `G^{(π)}`.
* `AlgebraicGeometry.MultiplicativeDeformation.constantComponentOver` is the section of the
  constant group scheme of `ℤ/ℓℤ` over `Spec A` indexed by a group element.

## Main results

* `AlgebraicGeometry.MultiplicativeDeformation.pointOfAlgHom_bijective` and
  `AlgebraicGeometry.MultiplicativeDeformation.pointOfAlgHom_comp_comultiplication` identify the
  group of points with the functor of points of the coordinate ring, so that the group law
  `x + y = πxy + x + y` is the one defined by the comultiplication.

## Implementation notes

An affine group scheme is given here by its coordinate ring together with its comultiplication,
and the group law it induces on points. `DeformedPoint π R` is the set of `R`-points of
`Spec A[x, 1/(πx + 1)]`, which is the set of `x : R` with `πx + 1` invertible, and is given the
group structure `x + y = πxy + x + y` with neutral element `0`, as in the source's
`σ_i +_G σ_j = σ_{i + j}`. That this group structure is the one defined by the comultiplication
is `pointOfAlgHom_comp_comultiplication`, and `pointOfAlgHom_bijective` identifies it with the
functor of points of the coordinate ring; both are proved, so no group law is postulated. The
unit and the inverse of the group scheme are recorded by the group structure itself.

## References

* [Stacks Project, Tag 0GY4](https://stacks.math.columbia.edu/tag/0GY4)
-/

@[expose] public section

open Polynomial TensorProduct CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v

namespace AlgebraicGeometry.MultiplicativeDeformation

variable {A : Type u} [CommRing A]

/-! ### The cyclotomic points `σ_i` and the polynomial `Φ` -/

/-- The point `σ_i = (ζ ^ i - 1)/(ζ - 1) = ζ ^ (i - 1) + ⋯ + ζ + 1`. -/
noncomputable def sigmaPoint (ℓ : ℕ) (ζ : A) (i : ZMod ℓ) : A :=
  ∑ j ∈ Finset.range i.val, ζ ^ j

/-- The defining property of `σ_i`: it is the quotient of `ζ ^ i - 1` by `π = ζ - 1`. -/
lemma mul_sigmaPoint (ℓ : ℕ) (ζ : A) (i : ZMod ℓ) :
    (ζ - 1) * sigmaPoint ℓ ζ i = ζ ^ i.val - 1 := by
  rw [sigmaPoint, mul_comm, geom_sum_mul]

/-- The polynomial `Φ = ((πX + 1) ^ ℓ - 1)/π ^ ℓ`, as the product of the linear factors
`X - σ_i`. -/
noncomputable def isogenyPolynomial (ℓ : ℕ) [NeZero ℓ] (ζ : A) : A[X] :=
  ∏ i : ZMod ℓ, (X - C (sigmaPoint ℓ ζ i))

/-- `Φ` is monic. -/
lemma isogenyPolynomial_monic (ℓ : ℕ) [NeZero ℓ] (ζ : A) :
    (isogenyPolynomial ℓ ζ).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- `Φ` satisfies the identity `(πX + 1) ^ ℓ = π ^ ℓ Φ + 1`. -/
lemma one_add_mul_pow_eq_isogenyPolynomial (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    (C (ζ - 1) * X + 1) ^ ℓ = C ((ζ - 1) ^ ℓ) * isogenyPolynomial ℓ ζ + 1 := by
  set u : A[X] := C (ζ - 1) * X + 1 with hu
  have h := congrArg (fun p : A[X] => aeval u p) hsplit
  simp only [map_prod, map_sub, aeval_X, aeval_C, map_pow, map_one, algebraMap_eq] at h
  have hfac : ∀ i : ZMod ℓ, u - C ζ ^ i.val = C (ζ - 1) * (X - C (sigmaPoint ℓ ζ i)) := by
    intro i
    have hm : C (ζ - 1) * C (sigmaPoint ℓ ζ i) = C (ζ ^ i.val) - 1 := by
      rw [← C_mul, mul_sigmaPoint, map_sub, map_one]
    rw [← C_pow, hu]
    linear_combination hm
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ZMod.card] at h
  simp only [isogenyPolynomial, C_pow]
  linear_combination -h

/-! ### The group schemes and the morphism between them -/

/-- The Hopf algebra `A[x, 1/(πx + 1)]` of `G^{(π)}`. -/
abbrev coordinateRing (π : A) : Type u := Localization.Away (C π * X + 1)

/-- The generator `x` of the coordinate ring of `G^{(π)}`. -/
noncomputable abbrev coordinateGenerator (π : A) : coordinateRing π :=
  algebraMap A[X] (coordinateRing π) X

/-- Constants in the coordinate ring come from the base ring. -/
lemma algebraMap_C (π : A) (a : A) :
    algebraMap A[X] (coordinateRing π) (C a) = algebraMap A (coordinateRing π) a := by
  simpa only [C_eq_algebraMap] using
    (IsScalarTower.algebraMap_apply A A[X] (coordinateRing π) a).symm

/-- The element `πx + 1` inverted in the coordinate ring is a unit. -/
lemma isUnit_coordinateGenerator (π : A) :
    IsUnit (algebraMap A (coordinateRing π) π * coordinateGenerator π + 1) := by
  have h : algebraMap A (coordinateRing π) π * coordinateGenerator π + 1
      = algebraMap A[X] (coordinateRing π) (C π * X + 1) := by
    simp only [map_add, map_mul, map_one, algebraMap_C]
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit (C π * X + 1)

/-- The comultiplication `x ↦ π x ⊗ x + x ⊗ 1 + 1 ⊗ x` of `G^{(π)}`. -/
@[sga "3 VIIA 3.3" "partial"]
noncomputable def comultiplication (π : A) :
    coordinateRing π →ₐ[A] (coordinateRing π) ⊗[A] (coordinateRing π) :=
  IsLocalization.Away.liftAlgHom (C π * X + 1)
    (f := Polynomial.aeval (R := A)
      (algebraMap A ((coordinateRing π) ⊗[A] (coordinateRing π)) π *
          Algebra.TensorProduct.includeLeft (S := A) (coordinateGenerator π) *
          Algebra.TensorProduct.includeRight (coordinateGenerator π) +
        Algebra.TensorProduct.includeLeft (S := A) (coordinateGenerator π) +
        Algebra.TensorProduct.includeRight (coordinateGenerator π)))
    (by
      have h : (Polynomial.aeval (R := A)
          (algebraMap A ((coordinateRing π) ⊗[A] (coordinateRing π)) π *
              Algebra.TensorProduct.includeLeft (S := A) (coordinateGenerator π) *
              Algebra.TensorProduct.includeRight (coordinateGenerator π) +
            Algebra.TensorProduct.includeLeft (S := A) (coordinateGenerator π) +
            Algebra.TensorProduct.includeRight (coordinateGenerator π))) (C π * X + 1) =
          Algebra.TensorProduct.includeLeft (S := A)
              (algebraMap A (coordinateRing π) π * coordinateGenerator π + 1) *
            Algebra.TensorProduct.includeRight
              (algebraMap A (coordinateRing π) π * coordinateGenerator π + 1) := by
        simp only [map_add, map_mul, map_one, aeval_C, aeval_X, AlgHom.commutes]
        ring
      rw [h]
      exact ((isUnit_coordinateGenerator π).map _).mul ((isUnit_coordinateGenerator π).map _))

/-- The comultiplication on the generator, in terms of the two inclusions. -/
@[sga "3 VIIA 3.3" "partial"]
lemma comultiplication_coordinateGenerator (π : A) :
    comultiplication π (coordinateGenerator π) =
      algebraMap A ((coordinateRing π) ⊗[A] (coordinateRing π)) π *
          Algebra.TensorProduct.includeLeft (S := A) (coordinateGenerator π) *
          Algebra.TensorProduct.includeRight (coordinateGenerator π) +
        Algebra.TensorProduct.includeLeft (S := A) (coordinateGenerator π) +
        Algebra.TensorProduct.includeRight (coordinateGenerator π) := by
  simp [comultiplication, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift]

/-- The comultiplication is the map `x ↦ π x ⊗ x + x ⊗ 1 + 1 ⊗ x`. -/
@[sga "3 VIIA 3.3" "partial"]
lemma comultiplication_coordinateGenerator_tmul (π : A) :
    comultiplication π (coordinateGenerator π) =
      algebraMap A ((coordinateRing π) ⊗[A] (coordinateRing π)) π *
          (coordinateGenerator π ⊗ₜ[A] coordinateGenerator π) +
        coordinateGenerator π ⊗ₜ[A] 1 + 1 ⊗ₜ[A] coordinateGenerator π := by
  rw [comultiplication_coordinateGenerator]
  simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The map of coordinate rings `t ↦ Φ(s)` dual to the morphism of group schemes
`f : G^{(ζ - 1)} → G^{((ζ - 1) ^ ℓ)}`. -/
noncomputable def isogeny (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    coordinateRing ((ζ - 1) ^ ℓ) →ₐ[A] coordinateRing (ζ - 1) :=
  localizationMap A (ζ - 1) ℓ (isogenyPolynomial ℓ ζ)
    (one_add_mul_pow_eq_isogenyPolynomial ℓ ζ hsplit)

/-! ### Points -/

/-- An `R`-point of `Spec A[x, 1/(πx + 1)]`: an element of `R` at which `πx + 1` is
invertible. -/
@[ext] structure DeformedPoint (π : A) (R : Type v) [CommRing R] [Algebra A R] where
  /-- The coordinate `x` of the point. -/
  coord : R
  /-- The element inverted in the coordinate ring is invertible at the point. -/
  isUnit_one_add : IsUnit (algebraMap A R π * coord + 1)

namespace DeformedPoint

variable {π : A} {R : Type v} [CommRing R] [Algebra A R]

/-- The sum of points `x` and `y` is the point `πxy + x + y`. -/
instance : Add (DeformedPoint π R) where
  add x y := ⟨algebraMap A R π * x.coord * y.coord + x.coord + y.coord, by
    have h : algebraMap A R π * (algebraMap A R π * x.coord * y.coord + x.coord + y.coord) + 1 =
        (algebraMap A R π * x.coord + 1) * (algebraMap A R π * y.coord + 1) := by ring
    rw [h]
    exact x.isUnit_one_add.mul y.isUnit_one_add⟩

/-- The zero point is the origin `x = 0`. -/
instance : Zero (DeformedPoint π R) where
  zero := ⟨0, by simp⟩

/-- The inverse of the point `x` is the point `-x/(πx + 1)`. -/
noncomputable instance : Neg (DeformedPoint π R) where
  neg x := ⟨-(x.coord * Ring.inverse (algebraMap A R π * x.coord + 1)), by
    have hu := Ring.mul_inverse_cancel _ x.isUnit_one_add
    have h : algebraMap A R π * -(x.coord * Ring.inverse (algebraMap A R π * x.coord + 1)) + 1 =
        Ring.inverse (algebraMap A R π * x.coord + 1) := by linear_combination -hu
    rw [h]
    exact isUnit_ringInverse.mpr x.isUnit_one_add⟩

/-- The group law `x + y = πxy + x + y`. -/
@[simp] lemma coord_add (x y : DeformedPoint π R) :
    (x + y).coord = algebraMap A R π * x.coord * y.coord + x.coord + y.coord := rfl

/-- The neutral element is the origin. -/
@[simp] lemma coord_zero : (0 : DeformedPoint π R).coord = 0 := rfl

/-- The inverse of a point. -/
@[simp] lemma coord_neg (x : DeformedPoint π R) :
    (-x).coord = -(x.coord * Ring.inverse (algebraMap A R π * x.coord + 1)) := rfl

/-- The `R`-points form an abelian group under the law `x + y = πxy + x + y`. -/
noncomputable instance : AddCommGroup (DeformedPoint π R) :=
  { AddGroup.ofLeftAxioms
      (fun a b c => by ext; simp only [coord_add]; ring)
      (fun a => by ext; simp)
      (fun a => by
        ext
        have hu := Ring.mul_inverse_cancel _ a.isUnit_one_add
        simp only [coord_add, coord_neg, coord_zero]
        linear_combination (-a.coord) * hu) with
    add_comm := fun a b => by ext; simp only [coord_add]; ring }

end DeformedPoint

/-- The point of `Spec A[x, 1/(πx + 1)]` attached to an `A`-algebra map out of the
coordinate ring. -/
noncomputable def pointOfAlgHom (π : A) {R : Type v} [CommRing R] [Algebra A R]
    (g : coordinateRing π →ₐ[A] R) : DeformedPoint π R :=
  ⟨g (coordinateGenerator π), by
    have h : algebraMap A R π * g (coordinateGenerator π) + 1
        = g (algebraMap A (coordinateRing π) π * coordinateGenerator π + 1) := by
      simp only [map_add, map_mul, map_one, AlgHom.commutes]
    rw [h]
    exact (isUnit_coordinateGenerator π).map g⟩

/-- The coordinate of the point attached to an `A`-algebra map is the image of the
generator. -/
@[simp] lemma coord_pointOfAlgHom (π : A) {R : Type v} [CommRing R] [Algebra A R]
    (g : coordinateRing π →ₐ[A] R) :
    (pointOfAlgHom π g).coord = g (coordinateGenerator π) := rfl

/-- The points of `Spec A[x, 1/(πx + 1)]` are exactly the `A`-algebra maps out of its
coordinate ring. -/
lemma pointOfAlgHom_bijective (π : A) (R : Type v) [CommRing R] [Algebra A R] :
    Function.Bijective (pointOfAlgHom π (R := R)) := by
  refine ⟨fun g g' h => IsLocalization.algHom_ext (Submonoid.powers (C π * X + 1))
    (Polynomial.algHom_ext (congrArg DeformedPoint.coord h)), fun x => ?_⟩
  have hu : IsUnit ((Polynomial.aeval (R := A) x.coord) (C π * X + 1)) := by
    simpa using x.isUnit_one_add
  refine ⟨IsLocalization.Away.liftAlgHom (C π * X + 1) hu, ?_⟩
  ext
  simp [IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift]

/-- The group law on points is the one defined by the comultiplication. -/
lemma pointOfAlgHom_comp_comultiplication (π : A) {R : Type v} [CommRing R]
    [Algebra A R] (g h : coordinateRing π →ₐ[A] R) :
    pointOfAlgHom π
        ((Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _)).comp (comultiplication π))
      = pointOfAlgHom π g + pointOfAlgHom π h := by
  ext
  simp only [coord_pointOfAlgHom, DeformedPoint.coord_add, AlgHom.comp_apply,
    comultiplication_coordinateGenerator, map_add, map_mul, AlgHom.commutes]
  simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

/-- The map on points induced by `f`, namely `s ↦ Φ(s)`. -/
noncomputable def isogenyOnPoints (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type v} [CommRing R] [Algebra A R] (x : DeformedPoint (ζ - 1) R) :
    DeformedPoint ((ζ - 1) ^ ℓ) R :=
  ⟨aeval x.coord (isogenyPolynomial ℓ ζ), by
    have h := congrArg (fun p : A[X] => aeval x.coord p)
      (one_add_mul_pow_eq_isogenyPolynomial ℓ ζ hsplit)
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, map_one] at h
    rw [map_pow, ← h]
    exact x.isUnit_one_add.pow ℓ⟩

/-- The coordinate of the image of a point under `f` is `Φ` evaluated at its coordinate. -/
@[simp] lemma coord_isogenyOnPoints (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type v} [CommRing R] [Algebra A R] (x : DeformedPoint (ζ - 1) R) :
    (isogenyOnPoints ℓ ζ hsplit x).coord = aeval x.coord (isogenyPolynomial ℓ ζ) := rfl

/-- On points, the morphism `f` of coordinate rings is `s ↦ Φ(s)`. -/
lemma pointOfAlgHom_comp_isogeny (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {R : Type v} [CommRing R] [Algebra A R] (g : coordinateRing (ζ - 1) →ₐ[A] R) :
    pointOfAlgHom ((ζ - 1) ^ ℓ) (g.comp (isogeny ℓ ζ hsplit))
      = isogenyOnPoints ℓ ζ hsplit (pointOfAlgHom (ζ - 1) g) := by
  ext
  simp only [coord_pointOfAlgHom, AlgHom.comp_apply, isogeny, coord_isogenyOnPoints,
    localizationMap_X]
  exact (Polynomial.aeval_algHom_apply g _ _).symm

/-- The `A`-point `σ_i` of `G^{(ζ - 1)}`. -/
noncomputable def constantPoint (ℓ : ℕ) [NeZero ℓ] (ζ : A) (hζ : ζ ^ ℓ = 1)
    (i : ZMod ℓ) : DeformedPoint (ζ - 1) A :=
  ⟨sigmaPoint ℓ ζ i, by
    have h : algebraMap A A (ζ - 1) * sigmaPoint ℓ ζ i + 1 = ζ ^ i.val := by
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      linear_combination mul_sigmaPoint ℓ ζ i
    rw [h]
    exact (IsUnit.of_pow_eq_one hζ (NeZero.ne ℓ)).pow i.val⟩

/-- The coordinate of the `A`-point `σ_i` is `σ_i`. -/
@[simp] lemma coord_constantPoint (ℓ : ℕ) [NeZero ℓ] (ζ : A) (hζ : ζ ^ ℓ = 1)
    (i : ZMod ℓ) : (constantPoint ℓ ζ hζ i).coord = sigmaPoint ℓ ζ i := rfl

/-- The coordinate ring of the kernel of `f`: the fibre of `f` over the origin of
`G^{((ζ - 1) ^ ℓ)}`, that is the closed subscheme `Φ(s) = 0` of `G^{(ζ - 1)}`. -/
noncomputable abbrev kernelCoordinateRing (ℓ : ℕ) [NeZero ℓ] (ζ : A)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) : Type u :=
  coordinateRing (ζ - 1) ⧸
    Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}

/-- The section of the constant group scheme over `Spec A` indexed by `j`. -/
noncomputable abbrev constantComponentOver (ℓ : ℕ) (j : Multiplicative (ZMod ℓ)) :
    (𝟙_ (Over (Spec (.of A)))) ⟶
      (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X :=
  ((Over.mapPullbackAdj (terminal.from (Spec (.of A)))).homEquiv _
    (constantSchemeOverIntegersObj.{u, 0} (Multiplicative (ZMod ℓ))))
    (toUnit ((Over.map (terminal.from (Spec (.of A)))).obj
        (𝟙_ (Over (Spec (.of A))))) ≫
      constantComponent.{u, 0} (Multiplicative (ZMod ℓ)) j)

end AlgebraicGeometry.MultiplicativeDeformation

end
