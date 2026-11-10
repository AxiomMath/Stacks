module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.PairGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.RingTheory.Cech.FunctorialCechFamilyObstruction

/-!
# A groupoid scheme on a field whose arrows and stabilizer have different dimensions

The dimension of the arrow scheme of a groupoid scheme whose object scheme is the spectrum of a
field agrees with the dimension of its stabilizer group scheme *provided the source and target
morphisms are locally of finite type*. Without that hypothesis the two dimensions differ, and
the groupoid scheme built here is a witness.

The witness is the one the source describes. Start from the multiplicative action
`𝐆_{m,𝐐} ×_𝐐 𝐀¹_𝐐 → 𝐀¹_𝐐` and restrict the associated groupoid scheme to the generic point of
`𝐀¹_𝐐`, i.e. along `Spec 𝐐(x) → Spec 𝐐[x]`. The restriction has object scheme `Spec 𝐐(x)` and
arrow scheme `Spec (𝐐(x)[y][1/P(xy)])`, with `P` ranging over the nonzero elements of `𝐐[T]`;
its source is `x ↦ x` and its target is `x ↦ xy`. Because `x` is a unit of `𝐐(x)`, the
coordinate `y = (xy)/x` is recovered from `Y := xy`, so that arrow ring is
`𝐐(x)[Y][1/P(Y)]` — the localization of `𝐐(x)[Y]` at the image of `𝐐[Y] ∖ {0}` — on which the
source is the structure map and the target sends `x` to `Y`. That pair of maps exhibits the
arrow ring as the tensor square `𝐐(x) ⊗_𝐐 𝐐(x)`, and therefore exhibits the restricted
groupoid as the pair groupoid of `Spec 𝐐(x) → Spec 𝐐`, which is how it is built below.

## Main definitions

* `AlgebraicGeometry.RationalFunctionPairGroupoid.arrowSubmonoid` is the multiplicative set of
  the source: the nonzero polynomials with rational coefficients, viewed inside `𝐐(x)[Y]`.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.arrowRing` is the arrow ring
  `𝐐(x)[Y][1/P(Y)]`.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.baseMap` is `Spec 𝐐(x) → Spec 𝐐`.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.groupoid` is the groupoid scheme itself: the
  pair groupoid of `baseMap`, with object scheme `Spec 𝐐(x)` and arrow scheme
  `Spec 𝐐(x) ×_{Spec 𝐐} Spec 𝐐(x)`.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.toArrowRing` is the map from the tensor
  square `𝐐(x) ⊗_𝐐 𝐐(x)` to the arrow ring given by the source and the target.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.arrowRingEquiv` is the isomorphism of the
  tensor square with the arrow ring that this map turns out to be.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.powerDenominators` is the subring of the
  elements of the arrow ring that can be written with a denominator a power of a fixed
  polynomial.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.evalAtMulX` sends a polynomial `P` with
  rational coefficients to `P(xy)`, and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.sourceArrowSubmonoid` is the multiplicative
  set of the nonzero such `P(xy)`; its localization
  `AlgebraicGeometry.RationalFunctionPairGroupoid.sourceArrowRing` is the arrow ring exactly as
  the source writes it, `𝐐(x)[y][1/P(xy)]`.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.coordChange` is the substitution `Y = xy`,
  the dilation of `𝐐(x)[y]` by `x⁻¹`.

## Main results

* `AlgebraicGeometry.RationalFunctionPairGroupoid.ringKrullDim_arrowRing`: the arrow ring has
  Krull dimension one.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.toArrowRing_surjective` and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.toArrowRing_injective`: the tensor square maps
  bijectively onto the arrow ring.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.topologicalKrullDim_stabilizer`: the
  stabilizer group scheme has dimension zero.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.topologicalKrullDim_arrows_eq_one`: the arrow
  scheme has dimension one.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.topologicalKrullDim_arrows_ne_stabilizer`:
  the two dimensions differ.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.not_finiteType_sourceHom`: the arrow ring is
  not a finitely generated algebra over `𝐐(x)` along the source, and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.not_finiteType_includeLeftRingHom` and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.not_finiteType_includeRight`: the tensor
  square is not of finite type over either factor.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.not_locallyOfFiniteType_source` and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.not_locallyOfFiniteType_target`: neither
  structure morphism is locally of finite type.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.mem_sourceArrowSubmonoid_iff` and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.sourceArrowRingEquiv`: the multiplicative set
  of the source is the set of the nonzero `P(xy)`, and the substitution `Y = xy` identifies its
  localization with the arrow ring; hence
  `AlgebraicGeometry.RationalFunctionPairGroupoid.arrowsIsoSpecSourceArrowRing`, the arrow
  scheme is `Spec (𝐐(x)[y][1/P(xy)])`.
* `AlgebraicGeometry.RationalFunctionPairGroupoid.exists_dim_arrows_eq_one_dim_stabilizer_eq_zero`
  is the example of the warning in full, and
  `AlgebraicGeometry.RationalFunctionPairGroupoid.not_forall_dim_arrows_eq_dim_stabilizer`
  is the warning itself: the conclusion of Tag 04MQ fails for a groupoid scheme on a field
  whose source and target are not locally of finite type.

## Implementation notes

The source-target morphism of a pair groupoid is the identity of `X ×_S X` once both the arrow
scheme and the square of the object scheme are unfolded to that fibre product, so it is an
isomorphism; the stabilizer is therefore carried isomorphically onto the object scheme by the
second projection of its defining square, and its dimension is the Krull dimension of `𝐐(x)`.

That the source and the target are not locally of finite type is the statement that
`𝐐(x) ⊗_𝐐 𝐐(x)` is not a finitely generated `𝐐(x)`-algebra, which is proved on the arrow ring
`𝐐(x)[Y][1/P(Y)]`: finitely many generators have a common denominator `m`, so every element
would be a quotient `p/mⁿ`, whereas `1/(Y - a)` lies in the arrow ring for every rational
number `a`, and a rational number `a` with `m(a) ≠ 0` exists because `m` comes from a nonzero
polynomial with rational coefficients, which has finitely many roots.  Since the two factors
of the tensor square are exchanged by `Algebra.TensorProduct.comm`, one computation settles
both morphisms.

The upper bound for the arrow ring uses that `𝐐(x)[Y]` is a principal ideal domain and that the
spectrum of a localization is inducing in the spectrum; the lower bound uses the prime
`(Y - x)`, which meets no nonzero polynomial with rational coefficients because `x` is
transcendental over `𝐐`. The tensor square is identified with the arrow ring by writing down
the inverse of the source-target map: sending `Y` to `1 ⊗ x` carries the nonzero rational
polynomials to units of the tensor square, hence factors through the localization, and the two
composites are the identity because they are so on the generators.

The substitution `Y = xy` that passes between the source's presentation `𝐐(x)[y][1/P(xy)]` of
the arrow ring and the presentation `𝐐(x)[Y][1/P(Y)]` used here is the dilation of `𝐐(x)[y]` by
`x⁻¹`, `Stacks.FunctorialCechFamily.dilate`; the multiplicative set the source inverts is the
image of the one inverted here under the dilation by `x`, so the two dilations identify the two
localizations.

## References

* [Stacks Project, Tag 04MQ](https://stacks.math.columbia.edu/tag/04MQ)
* [Stacks Project, Tag 04MR](https://stacks.math.columbia.edu/tag/04MR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open Stacks.Groupoids

namespace AlgebraicGeometry.RationalFunctionPairGroupoid

/-! ### The arrow ring -/

/-- The nonzero polynomials with rational coefficients, viewed inside `𝐐(x)[Y]`.  In the
coordinates of the source, `Y` is `xy` and this is the set of the `P(xy)`. -/
noncomputable def arrowSubmonoid : Submonoid (Polynomial (RatFunc ℚ)) :=
  Submonoid.map
    (Polynomial.mapRingHom (algebraMap ℚ (RatFunc ℚ))).toMonoidHom
    (nonZeroDivisors (Polynomial ℚ))

theorem arrowSubmonoid_le_nonZeroDivisors :
    arrowSubmonoid ≤ nonZeroDivisors (Polynomial (RatFunc ℚ)) := by
  rintro m ⟨P, hP, rfl⟩
  have hPne : P ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hP
  refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
  change Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P ≠ 0
  simpa [Polynomial.map_eq_zero_iff (algebraMap ℚ (RatFunc ℚ)).injective] using hPne

/-- The arrow ring `𝐐(x)[Y][1/P(Y)]` of the groupoid scheme of the warning. -/
noncomputable abbrev arrowRing := Localization arrowSubmonoid

noncomputable instance : IsDomain arrowRing :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := arrowSubmonoid) arrowRing
    arrowSubmonoid_le_nonZeroDivisors

theorem ringKrullDim_arrowRing_le_one : ringKrullDim arrowRing ≤ 1 :=
  calc ringKrullDim arrowRing
      = topologicalKrullDim (PrimeSpectrum arrowRing) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim arrowRing).symm
    _ ≤ topologicalKrullDim (PrimeSpectrum (Polynomial (RatFunc ℚ))) :=
        (PrimeSpectrum.localization_comap_isInducing arrowRing
          arrowSubmonoid).topologicalKrullDim_le
    _ = ringKrullDim (Polynomial (RatFunc ℚ)) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField _)

/-- Evaluating a polynomial with rational coefficients at `x` is the inclusion of `𝐐[x]` in
`𝐐(x)`. -/
theorem aeval_ratFuncX (P : Polynomial ℚ) :
    Polynomial.aeval (RatFunc.X : RatFunc ℚ) P = algebraMap (Polynomial ℚ) (RatFunc ℚ) P := by
  have h : (Polynomial.aeval (RatFunc.X : RatFunc ℚ) : Polynomial ℚ →ₐ[ℚ] RatFunc ℚ)
      = IsScalarTower.toAlgHom ℚ (Polynomial ℚ) (RatFunc ℚ) := by
    apply Polynomial.algHom_ext
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun f : Polynomial ℚ →ₐ[ℚ] RatFunc ℚ => f P) h

/-- The prime `(Y - x)` of `𝐐(x)[Y]`, as the kernel of evaluation at `x`. -/
noncomputable def diagonalPrime : Ideal (Polynomial (RatFunc ℚ)) :=
  RingHom.ker (Polynomial.evalRingHom (RatFunc.X : RatFunc ℚ))

instance : diagonalPrime.IsPrime := RingHom.ker_isPrime _

theorem disjoint_arrowSubmonoid_diagonalPrime :
    Disjoint (arrowSubmonoid : Set (Polynomial (RatFunc ℚ))) (diagonalPrime : Set _) := by
  rw [Set.disjoint_left]
  rintro m ⟨P, hP, rfl⟩ hm
  have hPne : P ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hP
  have h0 : Polynomial.eval (RatFunc.X : RatFunc ℚ)
      (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P) = 0 := hm
  rw [Polynomial.eval_map, ← Polynomial.aeval_def, aeval_ratFuncX] at h0
  exact hPne ((map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h0)

theorem one_le_ringKrullDim_arrowRing : 1 ≤ ringKrullDim arrowRing := by
  have hinj : Function.Injective (algebraMap (Polynomial (RatFunc ℚ)) arrowRing) :=
    IsLocalization.injective arrowRing arrowSubmonoid_le_nonZeroDivisors
  have hq : (Ideal.map (algebraMap (Polynomial (RatFunc ℚ)) arrowRing) diagonalPrime).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint arrowSubmonoid arrowRing diagonalPrime
      inferInstance disjoint_arrowSubmonoid_diagonalPrime
  have hu : (Polynomial.X - Polynomial.C (RatFunc.X : RatFunc ℚ)) ∈ diagonalPrime := by
    simp [diagonalPrime, RingHom.mem_ker]
  have hune : algebraMap (Polynomial (RatFunc ℚ)) arrowRing
      (Polynomial.X - Polynomial.C (RatFunc.X : RatFunc ℚ)) ≠ 0 := by
    intro h
    have h2 := hinj (h.trans (map_zero _).symm)
    simp only [sub_eq_zero] at h2
    exact Polynomial.X_ne_C _ h2
  have hne : Ideal.map (algebraMap (Polynomial (RatFunc ℚ)) arrowRing) diagonalPrime ≠ ⊥ := by
    intro h
    exact hune (Ideal.mem_bot.mp (h ▸ Ideal.mem_map_of_mem _ hu))
  change 1 ≤ Order.krullDim (PrimeSpectrum arrowRing)
  rw [Order.one_le_krullDim_iff]
  refine ⟨⟨⊥, inferInstance⟩, ⟨_, hq⟩, lt_of_le_of_ne ?_ ?_⟩
  · rw [← PrimeSpectrum.asIdeal_le_asIdeal]; exact bot_le
  · intro h
    exact hne (congrArg PrimeSpectrum.asIdeal h).symm

theorem ringKrullDim_arrowRing : ringKrullDim arrowRing = 1 :=
  le_antisymm ringKrullDim_arrowRing_le_one one_le_ringKrullDim_arrowRing

/-! ### The source and the target of the arrow ring -/

/-- The composite `𝐐[Y] → 𝐐(x)[Y] → 𝐐(x)[Y][1/P(Y)]`, which lands in the units on nonzero
polynomials. -/
noncomputable def toArrowRingPolynomial : Polynomial ℚ →+* arrowRing :=
  (algebraMap (Polynomial (RatFunc ℚ)) arrowRing).comp
    (Polynomial.mapRingHom (algebraMap ℚ (RatFunc ℚ)))

theorem isUnit_toArrowRingPolynomial (y : nonZeroDivisors (Polynomial ℚ)) :
    IsUnit (toArrowRingPolynomial y) :=
  IsLocalization.map_units arrowRing (⟨_, ⟨y, y.2, rfl⟩⟩ : arrowSubmonoid)

/-- The target of the groupoid scheme on the arrow ring: it sends `x` to `Y`. -/
noncomputable def targetHom : RatFunc ℚ →ₐ[ℚ] arrowRing where
  toRingHom := IsLocalization.lift isUnit_toArrowRingPolynomial
  commutes' := by
    intro r
    change IsLocalization.lift isUnit_toArrowRingPolynomial (algebraMap ℚ (RatFunc ℚ) r)
      = algebraMap ℚ arrowRing r
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) r, IsLocalization.lift_eq,
      IsScalarTower.algebraMap_apply ℚ (Polynomial (RatFunc ℚ)) arrowRing r]
    simp [toArrowRingPolynomial,
      IsScalarTower.algebraMap_apply ℚ (RatFunc ℚ) (Polynomial (RatFunc ℚ)) r]

/-- The source of the groupoid scheme on the arrow ring: the structure map of `𝐐(x)[Y]`. -/
noncomputable def sourceHom : RatFunc ℚ →ₐ[ℚ] arrowRing where
  toRingHom := (algebraMap (Polynomial (RatFunc ℚ)) arrowRing).comp Polynomial.C
  commutes' := by
    intro r
    change algebraMap (Polynomial (RatFunc ℚ)) arrowRing
        (Polynomial.C (algebraMap ℚ (RatFunc ℚ) r)) = algebraMap ℚ arrowRing r
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial (RatFunc ℚ)) arrowRing r]
    congr 1

/-- The map from the tensor square of `𝐐(x)` to the arrow ring given by the source on the first
factor and the target on the second. -/
noncomputable def toArrowRing :
    TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) →ₐ[ℚ] arrowRing :=
  Algebra.TensorProduct.lift sourceHom targetHom (fun _ _ => Commute.all _ _)

theorem sourceHom_mem_range (a : RatFunc ℚ) : sourceHom a ∈ toArrowRing.range :=
  ⟨a ⊗ₜ[ℚ] 1, by simp [toArrowRing, Algebra.TensorProduct.lift_tmul]⟩

theorem targetHom_mem_range (a : RatFunc ℚ) : targetHom a ∈ toArrowRing.range :=
  ⟨1 ⊗ₜ[ℚ] a, by simp [toArrowRing, Algebra.TensorProduct.lift_tmul]⟩

/-- The target sends a polynomial with rational coefficients, seen in `𝐐(x)`, to the same
polynomial in `Y`. -/
private theorem targetHom_algebraMap (P : Polynomial ℚ) :
    targetHom (algebraMap (Polynomial ℚ) (RatFunc ℚ) P)
      = algebraMap (Polynomial (RatFunc ℚ)) arrowRing
        (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P) :=
  IsLocalization.lift_eq _ P

/-- A nonzero polynomial with rational coefficients is nonzero in `𝐐(x)`. -/
private theorem algebraMap_ratFunc_ne_zero {P : Polynomial ℚ}
    (hP : P ∈ nonZeroDivisors (Polynomial ℚ)) : algebraMap (Polynomial ℚ) (RatFunc ℚ) P ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hP)

theorem targetHom_ratFuncX : targetHom (RatFunc.X : RatFunc ℚ)
    = algebraMap (Polynomial (RatFunc ℚ)) arrowRing Polynomial.X := by
  rw [← RatFunc.algebraMap_X, targetHom_algebraMap]
  simp

theorem algebraMap_mem_range (p : Polynomial (RatFunc ℚ)) :
    algebraMap (Polynomial (RatFunc ℚ)) arrowRing p ∈ toArrowRing.range := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [map_add] using add_mem hp hq
  | monomial n a =>
      have h : algebraMap (Polynomial (RatFunc ℚ)) arrowRing (Polynomial.monomial n a)
          = sourceHom a * (targetHom (RatFunc.X : RatFunc ℚ)) ^ n := by
        rw [targetHom_ratFuncX, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        rfl
      rw [h]
      exact mul_mem (sourceHom_mem_range a) (pow_mem (targetHom_mem_range _) n)

theorem inv_mem_range (m : arrowSubmonoid) :
    IsLocalization.mk' arrowRing 1 m ∈ toArrowRing.range := by
  obtain ⟨P, hP, hPm⟩ := m.2
  have hbne := algebraMap_ratFunc_ne_zero hP
  have htb : targetHom (algebraMap (Polynomial ℚ) (RatFunc ℚ) P)
      = algebraMap (Polynomial (RatFunc ℚ)) arrowRing (m : Polynomial (RatFunc ℚ)) := by
    rw [targetHom_algebraMap, ← hPm]
    rfl
  have hmk : IsLocalization.mk' arrowRing 1 m
      = targetHom (algebraMap (Polynomial ℚ) (RatFunc ℚ) P)⁻¹ := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, map_one, ← htb, ← map_mul, inv_mul_cancel₀ hbne,
      map_one]
  rw [hmk]
  exact targetHom_mem_range _

theorem toArrowRing_surjective : Function.Surjective toArrowRing := by
  intro z
  obtain ⟨⟨p, m⟩, rfl⟩ := IsLocalization.mk'_surjective arrowSubmonoid z
  have h : IsLocalization.mk' arrowRing p m ∈ toArrowRing.range := by
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact mul_mem (algebraMap_mem_range p) (inv_mem_range m)
  exact h

/-! ### The tensor square is the arrow ring -/

/-- The map `𝐐(x)[Y] → 𝐐(x) ⊗_𝐐 𝐐(x)` of `𝐐(x)`-algebras sending `Y` to `1 ⊗ x`.  It is the
candidate inverse of `toArrowRing`. -/
noncomputable def ofPolynomial :
    Polynomial (RatFunc ℚ) →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) :=
  (Polynomial.aeval (1 ⊗ₜ[ℚ] (RatFunc.X : RatFunc ℚ)) :
    Polynomial (RatFunc ℚ) →ₐ[RatFunc ℚ] TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).toRingHom

theorem ofPolynomial_C (a : RatFunc ℚ) : ofPolynomial (Polynomial.C a) = a ⊗ₜ[ℚ] 1 := by
  change Polynomial.aeval _ (Polynomial.C a) = _
  rw [Polynomial.aeval_C]
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem ofPolynomial_X : ofPolynomial Polynomial.X = 1 ⊗ₜ[ℚ] (RatFunc.X : RatFunc ℚ) := by
  change Polynomial.aeval _ Polynomial.X = _
  rw [Polynomial.aeval_X]

/-- On the polynomials with rational coefficients, `ofPolynomial` is the second inclusion of the
tensor square: it sends `P(Y)` to `1 ⊗ P(x)`. -/
theorem ofPolynomial_comp_mapRingHom :
    ofPolynomial.comp (Polynomial.mapRingHom (algebraMap ℚ (RatFunc ℚ)))
      = (Algebra.TensorProduct.includeRight :
            RatFunc ℚ →ₐ[ℚ] TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).toRingHom.comp
          (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · change ofPolynomial (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) (Polynomial.C a))
      = 1 ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C a)
    rw [Polynomial.map_C, ofPolynomial_C, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ) a]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul a
  · change ofPolynomial (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) Polynomial.X)
      = 1 ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X
    rw [Polynomial.map_X, ofPolynomial_X, RatFunc.algebraMap_X]

theorem ofPolynomial_map (P : Polynomial ℚ) :
    ofPolynomial (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P)
      = 1 ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) (RatFunc ℚ) P :=
  congrArg (fun f : Polynomial ℚ →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) => f P)
    ofPolynomial_comp_mapRingHom

/-- `ofPolynomial` sends the nonzero polynomials with rational coefficients to units, because
`1 ⊗ P(x)` is inverted by `1 ⊗ P(x)⁻¹`. -/
theorem isUnit_ofPolynomial (m : arrowSubmonoid) :
    IsUnit (ofPolynomial (m : Polynomial (RatFunc ℚ))) := by
  obtain ⟨P, hP, hPm⟩ := m.2
  have hbne := algebraMap_ratFunc_ne_zero hP
  have hm : ofPolynomial (m : Polynomial (RatFunc ℚ))
      = 1 ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) (RatFunc ℚ) P := by
    rw [← hPm]
    exact ofPolynomial_map P
  have hmul : (1 ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) (RatFunc ℚ) P)
      * (1 ⊗ₜ[ℚ] (algebraMap (Polynomial ℚ) (RatFunc ℚ) P)⁻¹)
      = (1 : TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hbne,
      Algebra.TensorProduct.one_def]
  rw [hm]
  exact IsUnit.of_mul_eq_one _ hmul

/-- The map from the arrow ring back to the tensor square: `ofPolynomial` inverts the nonzero
rational polynomials, so it factors through the localization. -/
noncomputable def fromArrowRing :
    arrowRing →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) :=
  IsLocalization.lift (M := arrowSubmonoid) isUnit_ofPolynomial

theorem fromArrowRing_algebraMap (p : Polynomial (RatFunc ℚ)) :
    fromArrowRing (algebraMap (Polynomial (RatFunc ℚ)) arrowRing p) = ofPolynomial p :=
  IsLocalization.lift_eq _ p

theorem fromArrowRing_sourceHom (a : RatFunc ℚ) : fromArrowRing (sourceHom a) = a ⊗ₜ[ℚ] 1 := by
  change fromArrowRing (algebraMap (Polynomial (RatFunc ℚ)) arrowRing (Polynomial.C a)) = _
  rw [fromArrowRing_algebraMap, ofPolynomial_C]

theorem fromArrowRing_comp_targetHom :
    fromArrowRing.comp (targetHom : RatFunc ℚ →ₐ[ℚ] arrowRing).toRingHom
      = (Algebra.TensorProduct.includeRight :
          RatFunc ℚ →ₐ[ℚ] TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).toRingHom := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ)) (RingHom.ext fun P => ?_)
  change fromArrowRing (targetHom (algebraMap (Polynomial ℚ) (RatFunc ℚ) P))
    = 1 ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) (RatFunc ℚ) P
  rw [targetHom_algebraMap, fromArrowRing_algebraMap, ofPolynomial_map]

theorem fromArrowRing_targetHom (b : RatFunc ℚ) : fromArrowRing (targetHom b) = 1 ⊗ₜ[ℚ] b :=
  congrArg (fun f : RatFunc ℚ →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) => f b)
    fromArrowRing_comp_targetHom

theorem fromArrowRing_toArrowRing (z : TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)) :
    fromArrowRing (toArrowRing z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      have h : toArrowRing (a ⊗ₜ[ℚ] b) = sourceHom a * targetHom b := by
        simp [toArrowRing, Algebra.TensorProduct.lift_tmul]
      rw [h, map_mul, fromArrowRing_sourceHom, fromArrowRing_targetHom,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem toArrowRing_injective : Function.Injective toArrowRing :=
  Function.LeftInverse.injective fromArrowRing_toArrowRing

/-- **The arrow ring is the tensor square.**  The source and the target exhibit
`𝐐(x) ⊗_𝐐 𝐐(x)` as `𝐐(x)[Y][1/P(Y)]`. -/
noncomputable def arrowRingEquiv :
    TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) ≃+* arrowRing :=
  RingEquiv.ofBijective (toArrowRing : _ →+* arrowRing)
    ⟨toArrowRing_injective, toArrowRing_surjective⟩

theorem ringKrullDim_tensorSquare :
    ringKrullDim (TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)) = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv arrowRingEquiv, ringKrullDim_arrowRing]

/-! ### The arrow ring in the coordinates of the source -/

/-- Substituting `xy` for the variable: the map `𝐐[T] → 𝐐(x)[y]` sending `P` to `P(xy)`. -/
noncomputable def evalAtMulX : Polynomial ℚ →ₐ[ℚ] Polynomial (RatFunc ℚ) :=
  Polynomial.aeval (Polynomial.C (RatFunc.X : RatFunc ℚ) * Polynomial.X)

/-- The multiplicative set the source inverts, inside `𝐐(x)[y]`: the elements `P(xy)` for `P` a
nonzero polynomial with rational coefficients.  It is the image of `arrowSubmonoid` under the
dilation `y ↦ xy`, which is the substitution `Y = xy` read backwards. -/
noncomputable def sourceArrowSubmonoid : Submonoid (Polynomial (RatFunc ℚ)) :=
  Submonoid.map (Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ)).toMonoidHom
    arrowSubmonoid

/-- The arrow ring exactly as the source writes it: `𝐐(x)[y][1/P(xy)]`. -/
noncomputable abbrev sourceArrowRing := Localization sourceArrowSubmonoid

/-- Dilating the image of a polynomial with rational coefficients by `x` evaluates it at `xy`. -/
theorem dilate_map_eq_evalAtMulX (P : Polynomial ℚ) :
    Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ)
        (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P)
      = evalAtMulX P := by
  have hC : (algebraMap ℚ (Polynomial (RatFunc ℚ)))
      = (Polynomial.C : RatFunc ℚ →+* Polynomial (RatFunc ℚ)).comp
        (algebraMap ℚ (RatFunc ℚ)) :=
    RingHom.ext fun a => Polynomial.algebraMap_apply a
  rw [Stacks.FunctorialCechFamily.dilate_apply, evalAtMulX, Polynomial.aeval_def, hC]
  exact Polynomial.eval₂_map _ _ _

/-- The multiplicative set the source inverts consists exactly of the `P(xy)` for `P` a nonzero
polynomial with rational coefficients. -/
theorem mem_sourceArrowSubmonoid_iff (q : Polynomial (RatFunc ℚ)) :
    q ∈ sourceArrowSubmonoid ↔ ∃ P : Polynomial ℚ, P ≠ 0 ∧ q = evalAtMulX P := by
  constructor
  · rintro ⟨m, ⟨P, hP, rfl⟩, rfl⟩
    refine ⟨P, mem_nonZeroDivisors_iff_ne_zero.mp hP, ?_⟩
    simpa using dilate_map_eq_evalAtMulX P
  · rintro ⟨P, hP, rfl⟩
    refine ⟨Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P,
      ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP, rfl⟩, ?_⟩
    exact dilate_map_eq_evalAtMulX P

/-- Dilating twice multiplies the two factors. -/
private theorem dilate_dilate (c d : RatFunc ℚ) (p : Polynomial (RatFunc ℚ)) :
    Stacks.FunctorialCechFamily.dilate c (Stacks.FunctorialCechFamily.dilate d p)
      = Stacks.FunctorialCechFamily.dilate (d * c) p := by
  simp only [Stacks.FunctorialCechFamily.dilate_apply]
  rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    ← mul_assoc, ← Polynomial.C_mul]

/-- Dilating by one does nothing. -/
private theorem dilate_one (p : Polynomial (RatFunc ℚ)) :
    Stacks.FunctorialCechFamily.dilate (1 : RatFunc ℚ) p = p := by
  rw [Stacks.FunctorialCechFamily.dilate_apply, Polynomial.C_1, one_mul, Polynomial.comp_X]

/-- The substitution `Y = xy` of the source, as an automorphism of `𝐐(x)[y]`: the dilation by
`x⁻¹`, which carries `P(xy)` to `P(Y)`. -/
noncomputable def coordChange : Polynomial (RatFunc ℚ) ≃+* Polynomial (RatFunc ℚ) where
  toFun := Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ)⁻¹
  invFun := Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ)
  left_inv p := by rw [dilate_dilate, inv_mul_cancel₀ RatFunc.X_ne_zero, dilate_one]
  right_inv p := by rw [dilate_dilate, mul_inv_cancel₀ RatFunc.X_ne_zero, dilate_one]
  map_mul' p q := map_mul _ p q
  map_add' p q := map_add _ p q

theorem coordChange_apply (p : Polynomial (RatFunc ℚ)) :
    coordChange p = Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ)⁻¹ p := rfl

/-- The substitution undoes the dilation by `x`, so it sends `P(xy)` to `P(Y)`. -/
theorem coordChange_dilate (p : Polynomial (RatFunc ℚ)) :
    coordChange (Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ) p) = p := by
  rw [coordChange_apply, dilate_dilate, mul_inv_cancel₀ RatFunc.X_ne_zero, dilate_one]

/-- The substitution `Y = xy` carries the multiplicative set the source inverts onto the one
inverted above. -/
theorem map_coordChange_sourceArrowSubmonoid :
    Submonoid.map coordChange.toMonoidHom sourceArrowSubmonoid = arrowSubmonoid := by
  have h : coordChange.toMonoidHom.comp
      (Stacks.FunctorialCechFamily.dilate (RatFunc.X : RatFunc ℚ)).toMonoidHom
      = MonoidHom.id (Polynomial (RatFunc ℚ)) :=
    MonoidHom.ext fun p => coordChange_dilate p
  rw [sourceArrowSubmonoid, Submonoid.map_map, h, Submonoid.map_id]

/-- **The arrow ring is the one the source displays.**  Under the substitution `Y = xy` the
localization `𝐐(x)[y][1/P(xy)]` of the source is the localization `𝐐(x)[Y][1/P(Y)]` used
above. -/
noncomputable def sourceArrowRingEquiv : sourceArrowRing ≃+* arrowRing :=
  IsLocalization.ringEquivOfRingEquiv (M := sourceArrowSubmonoid) (T := arrowSubmonoid)
    sourceArrowRing arrowRing coordChange map_coordChange_sourceArrowSubmonoid

theorem ringKrullDim_sourceArrowRing : ringKrullDim sourceArrowRing = 1 := by
  rw [ringKrullDim_eq_of_ringEquiv sourceArrowRingEquiv, ringKrullDim_arrowRing]

/-! ### The tensor square is not of finite type over either factor -/

/-- The elements of the arrow ring that can be written with a denominator a power of a fixed
polynomial `m`, i.e. the image of `𝐐(x)[Y][1/m]` in `𝐐(x)[Y][1/P(Y)]`. -/
noncomputable def powerDenominators (m : Polynomial (RatFunc ℚ)) : Subring arrowRing where
  carrier := {z | ∃ (n : ℕ) (p : Polynomial (RatFunc ℚ)),
    z * algebraMap (Polynomial (RatFunc ℚ)) arrowRing m ^ n
      = algebraMap (Polynomial (RatFunc ℚ)) arrowRing p}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro z w ⟨n, p, hp⟩ ⟨k, q, hq⟩
    refine ⟨n + k, p * m ^ k + q * m ^ n, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, pow_add, add_mul, ← hp, ← hq]
    ring
  neg_mem' := by
    rintro z ⟨n, p, hp⟩
    exact ⟨n, -p, by rw [map_neg, ← hp, neg_mul]⟩
  mul_mem' := by
    rintro z w ⟨n, p, hp⟩ ⟨k, q, hq⟩
    refine ⟨n + k, p * q, ?_⟩
    rw [map_mul, pow_add, ← hp, ← hq]
    ring

theorem algebraMap_mem_powerDenominators (m p : Polynomial (RatFunc ℚ)) :
    algebraMap (Polynomial (RatFunc ℚ)) arrowRing p ∈ powerDenominators m :=
  ⟨0, p, by simp⟩

theorem sourceHom_apply (a : RatFunc ℚ) :
    sourceHom a = algebraMap (Polynomial (RatFunc ℚ)) arrowRing (Polynomial.C a) := rfl

/-- **The arrow ring is not of finite type over its source.**  Finitely many generators have a
common denominator `m`, so every element of the arrow ring would be a quotient `p/mⁿ`; but
`1/(Y - a)` lies in the arrow ring for every rational number `a`, and `a` may be chosen so that
`m(a) ≠ 0`, which forbids `Y - a` from dividing a power of `m`. -/
theorem not_finiteType_sourceHom :
    ¬ (sourceHom : RatFunc ℚ →ₐ[ℚ] arrowRing).toRingHom.FiniteType := by
  classical
  intro h
  let : Algebra (RatFunc ℚ) arrowRing :=
    (sourceHom : RatFunc ℚ →ₐ[ℚ] arrowRing).toRingHom.toAlgebra
  have hft : Algebra.FiniteType (RatFunc ℚ) arrowRing := h
  obtain ⟨s, hs⟩ := hft.out
  -- Every element of the arrow ring has a denominator in the multiplicative set.
  have hden : ∀ g : arrowRing, ∃ (d : arrowSubmonoid) (p : Polynomial (RatFunc ℚ)),
      g * algebraMap (Polynomial (RatFunc ℚ)) arrowRing (d : Polynomial (RatFunc ℚ))
        = algebraMap (Polynomial (RatFunc ℚ)) arrowRing p := by
    intro g
    obtain ⟨⟨p, d⟩, rfl⟩ := IsLocalization.mk'_surjective arrowSubmonoid g
    exact ⟨d, p, IsLocalization.mk'_spec arrowRing p d⟩
  choose den num hnum using hden
  -- The product of the denominators of the generators is a common denominator.
  set M : arrowSubmonoid := ∏ g ∈ s, den g with hMdef
  have hall : ∀ z : arrowRing, z ∈ powerDenominators (M : Polynomial (RatFunc ℚ)) := by
    intro z
    have hz : z ∈ Algebra.adjoin (RatFunc ℚ) (s : Set arrowRing) := hs ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem g hg =>
        refine ⟨1, num g * ∏ k ∈ s.erase g, (den k : Polynomial (RatFunc ℚ)), ?_⟩
        have hMg : (M : Polynomial (RatFunc ℚ))
            = (den g : Polynomial (RatFunc ℚ))
              * ∏ k ∈ s.erase g, (den k : Polynomial (RatFunc ℚ)) := by
          rw [hMdef]
          push_cast
          exact (Finset.mul_prod_erase s _ hg).symm
        rw [pow_one, hMg, map_mul, ← mul_assoc, hnum g, ← map_mul]
    | algebraMap r =>
        refine ⟨0, Polynomial.C r, ?_⟩
        rw [pow_zero, mul_one, RingHom.algebraMap_toAlgebra]
        exact sourceHom_apply r
    | add x y _ _ ihx ihy => exact add_mem ihx ihy
    | mul x y _ _ ihx ihy => exact mul_mem ihx ihy
  -- The common denominator comes from a nonzero polynomial with rational coefficients.
  obtain ⟨P, hP, hPM⟩ := M.2
  have hPne : P ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hP
  obtain ⟨a, ha⟩ : ∃ a : ℚ, P.eval a ≠ 0 := by
    by_contra hcon
    exact hPne (Polynomial.funext fun r => by simpa using not_exists.mp hcon r)
  -- The inverse of `Y - a` lies in the arrow ring.
  have hDne : (Polynomial.X - Polynomial.C a : Polynomial ℚ) ≠ 0 := Polynomial.X_sub_C_ne_zero a
  have hDmem : Polynomial.map (algebraMap ℚ (RatFunc ℚ)) (Polynomial.X - Polynomial.C a)
      ∈ arrowSubmonoid :=
    ⟨Polynomial.X - Polynomial.C a, mem_nonZeroDivisors_iff_ne_zero.mpr hDne, rfl⟩
  set d : arrowSubmonoid := ⟨_, hDmem⟩ with hd
  obtain ⟨n, q, hq⟩ := hall (IsLocalization.mk' arrowRing 1 d)
  have hspec : IsLocalization.mk' arrowRing 1 d
      * algebraMap (Polynomial (RatFunc ℚ)) arrowRing (d : Polynomial (RatFunc ℚ)) = 1 := by
    simp
  -- Hence `q * (Y - a) = mⁿ` in `𝐐(x)[Y]`.
  have key : algebraMap (Polynomial (RatFunc ℚ)) arrowRing
        (q * (d : Polynomial (RatFunc ℚ)))
      = algebraMap (Polynomial (RatFunc ℚ)) arrowRing ((M : Polynomial (RatFunc ℚ)) ^ n) := by
    rw [map_mul, map_pow, ← hq]
    calc IsLocalization.mk' arrowRing 1 d
          * algebraMap (Polynomial (RatFunc ℚ)) arrowRing (M : Polynomial (RatFunc ℚ)) ^ n
          * algebraMap (Polynomial (RatFunc ℚ)) arrowRing (d : Polynomial (RatFunc ℚ))
        = IsLocalization.mk' arrowRing 1 d
            * algebraMap (Polynomial (RatFunc ℚ)) arrowRing (d : Polynomial (RatFunc ℚ))
          * algebraMap (Polynomial (RatFunc ℚ)) arrowRing (M : Polynomial (RatFunc ℚ)) ^ n := by
          ring
      _ = algebraMap (Polynomial (RatFunc ℚ)) arrowRing (M : Polynomial (RatFunc ℚ)) ^ n := by
          rw [hspec, one_mul]
  have key2 : q * (d : Polynomial (RatFunc ℚ)) = (M : Polynomial (RatFunc ℚ)) ^ n :=
    IsLocalization.injective arrowRing arrowSubmonoid_le_nonZeroDivisors key
  -- Evaluating at `a` gives `0 = P(a)ⁿ ≠ 0`.
  have heval := congrArg (Polynomial.eval (algebraMap ℚ (RatFunc ℚ) a)) key2
  have hdeval : Polynomial.eval (algebraMap ℚ (RatFunc ℚ) a) (d : Polynomial (RatFunc ℚ)) = 0 := by
    rw [hd]
    simp
  have hMeval : Polynomial.eval (algebraMap ℚ (RatFunc ℚ) a) (M : Polynomial (RatFunc ℚ))
      = algebraMap ℚ (RatFunc ℚ) (P.eval a) := by
    rw [← hPM]
    change Polynomial.eval (algebraMap ℚ (RatFunc ℚ) a)
      (Polynomial.map (algebraMap ℚ (RatFunc ℚ)) P) = _
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [Polynomial.eval_mul, hdeval, mul_zero, Polynomial.eval_pow, hMeval] at heval
  have hPa : algebraMap ℚ (RatFunc ℚ) (P.eval a) ≠ 0 := by simpa using ha
  exact pow_ne_zero n hPa heval.symm

theorem toArrowRing_comp_includeLeftRingHom :
    (toArrowRing : TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) →ₐ[ℚ] arrowRing).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          RatFunc ℚ →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ))
      = (sourceHom : RatFunc ℚ →ₐ[ℚ] arrowRing).toRingHom := by
  ext a
  change toArrowRing (a ⊗ₜ[ℚ] 1) = sourceHom a
  simp [toArrowRing, Algebra.TensorProduct.lift_tmul]

/-- **The tensor square is not of finite type over its left factor.**  This is the source of the
groupoid scheme of the warning: `𝐐(x) ⊗_𝐐 𝐐(x)` is not a finitely generated `𝐐(x)`-algebra. -/
theorem not_finiteType_includeLeftRingHom :
    ¬ (Algebra.TensorProduct.includeLeftRingHom :
        RatFunc ℚ →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).FiniteType := by
  intro h
  refine not_finiteType_sourceHom ?_
  rw [← toArrowRing_comp_includeLeftRingHom]
  exact RingHom.FiniteType.comp
    (RingHom.FiniteType.of_surjective _ (by simpa using toArrowRing_surjective)) h

/-- **The tensor square is not of finite type over its right factor** either: the exchange of
the two factors carries one inclusion to the other. -/
theorem not_finiteType_includeRight :
    ¬ (Algebra.TensorProduct.includeRight :
        RatFunc ℚ →ₐ[ℚ] TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).toRingHom.FiniteType := by
  intro h
  refine not_finiteType_includeLeftRingHom ?_
  have hcomm : (Algebra.TensorProduct.includeLeftRingHom :
        RatFunc ℚ →+* TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ))
      = ((Algebra.TensorProduct.comm ℚ (RatFunc ℚ) (RatFunc ℚ)).symm :
            TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ) →ₐ[ℚ]
              TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            RatFunc ℚ →ₐ[ℚ] TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)).toRingHom := by
    ext a
    change a ⊗ₜ[ℚ] (1 : RatFunc ℚ)
      = (Algebra.TensorProduct.comm ℚ (RatFunc ℚ) (RatFunc ℚ)).symm (1 ⊗ₜ[ℚ] a)
    rw [Algebra.TensorProduct.comm_symm_tmul]
  rw [hcomm]
  exact RingHom.FiniteType.comp
    (RingHom.FiniteType.of_surjective _
      (Algebra.TensorProduct.comm ℚ (RatFunc ℚ) (RatFunc ℚ)).symm.surjective) h

/-! ### The groupoid scheme -/

/-- The morphism `Spec 𝐐(x) → Spec 𝐐`. -/
noncomputable def baseMap :
    Spec (CommRingCat.of (RatFunc ℚ)) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ)))

/-- **The groupoid scheme of the warning.**  The restriction of the groupoid scheme of the
multiplicative action of `𝐆_{m,𝐐}` on `𝐀¹_𝐐` to the generic point of `𝐀¹_𝐐`, presented as the
pair groupoid of `Spec 𝐐(x) → Spec 𝐐`: its object scheme is `Spec 𝐐(x)`, the spectrum of a
field, and its arrow scheme is `Spec 𝐐(x) ×_{Spec 𝐐} Spec 𝐐(x)`, whose ring of functions is
the arrow ring `𝐐(x)[Y][1/P(Y)]` of the source. -/
@[stacks 04MR "the groupoid scheme of the warning, as the pair groupoid of Spec Q(x) over Q"]
noncomputable def groupoid : GroupoidScheme (Spec (CommRingCat.of ℚ)) := pairGroupoid baseMap

/-- The object scheme is the spectrum of the field `𝐐(x)`. -/
theorem objects_left : groupoid.objects.left = Spec (CommRingCat.of (RatFunc ℚ)) := rfl

/-- The arrow scheme is the fibre square of `Spec 𝐐(x)` over `Spec 𝐐`. -/
theorem arrows_left : groupoid.arrows.left = Limits.pullback baseMap baseMap := rfl

theorem sourceTarget_left :
    (sourceTarget groupoid).left = 𝟙 (Limits.pullback baseMap baseMap) := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [sourceTarget, groupoid, pairTarget, pairSource]

theorem isIso_sourceTarget : IsIso (sourceTarget groupoid) := by
  have h : IsIso ((Over.forget (Spec (CommRingCat.of ℚ))).map (sourceTarget groupoid)) := by
    have he : (Over.forget (Spec (CommRingCat.of ℚ))).map (sourceTarget groupoid)
        = 𝟙 (Limits.pullback baseMap baseMap) := sourceTarget_left
    rw [he]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (Over.forget _)

theorem isIso_stabilizer_proj :
    IsIso (pullback.snd (sourceTarget groupoid) (diagonal groupoid)).left := by
  have := isIso_sourceTarget
  have : IsIso (pullback.snd (sourceTarget groupoid) (diagonal groupoid)) :=
    pullback_snd_iso_of_left_iso _ _
  have h : IsIso ((Over.forget (Spec (CommRingCat.of ℚ))).map
    (pullback.snd (sourceTarget groupoid) (diagonal groupoid))) := inferInstance
  exact h

/-- The stabilizer group scheme has dimension zero: the second projection of its defining
square carries it isomorphically onto `Spec 𝐐(x)`. -/
@[stacks 04MR "dim G = 0"]
theorem topologicalKrullDim_stabilizer :
    topologicalKrullDim (stabilizer groupoid).left = 0 := by
  have := isIso_stabilizer_proj
  calc topologicalKrullDim (stabilizer groupoid).left
      = topologicalKrullDim (Spec (CommRingCat.of (RatFunc ℚ))) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (Scheme.Hom.homeomorph
            (pullback.snd (sourceTarget groupoid) (diagonal groupoid)).left).isHomeomorph
    _ = ringKrullDim (RatFunc ℚ) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (RatFunc ℚ)
    _ = 0 := ringKrullDim_eq_zero_of_field (RatFunc ℚ)

/-- The dimension of the arrow scheme is the Krull dimension of the tensor square. -/
theorem topologicalKrullDim_arrows :
    topologicalKrullDim groupoid.arrows.left
      = ringKrullDim (TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)) := by
  have h : topologicalKrullDim (Limits.pullback (C := Scheme.{0})
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ)))))
      = ringKrullDim (TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (pullbackSpecIso ℚ (RatFunc ℚ) (RatFunc ℚ)).hom.homeomorph.isHomeomorph]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  exact h

/-- The arrow scheme has dimension one. -/
@[stacks 04MR "dim R = 1"]
theorem topologicalKrullDim_arrows_eq_one :
    topologicalKrullDim groupoid.arrows.left = 1 := by
  rw [topologicalKrullDim_arrows, ringKrullDim_tensorSquare]

/-- **The conclusion of Tag 04MQ fails for this groupoid scheme.**  Its object scheme is the
spectrum of a field, yet the dimension of its arrow scheme is not the dimension of its
stabilizer group scheme: the stabilizer has dimension zero and the arrows have dimension one.
The source and target morphisms are not locally of finite type, which is the hypothesis of
Tag 04MQ that this example drops. -/
@[stacks 04MR "dim R = 1 ≠ 0 = dim G there, so the conclusion of Tag 04MQ fails for this \
groupoid scheme; that its source and target are not locally of finite type, which is the \
hypothesis of Tag 04MQ the example drops, is proved below"]
theorem topologicalKrullDim_arrows_ne_stabilizer :
    topologicalKrullDim groupoid.arrows.left
      ≠ topologicalKrullDim (stabilizer groupoid).left := by
  rw [topologicalKrullDim_arrows_eq_one, topologicalKrullDim_stabilizer]
  decide

/-! ### The source and the target are not locally of finite type -/

/-- The source of the groupoid scheme is the second projection of the fibre square. -/
theorem source_left : groupoid.source.left = Limits.pullback.snd baseMap baseMap := rfl

/-- The target of the groupoid scheme is the first projection of the fibre square. -/
theorem target_left : groupoid.target.left = Limits.pullback.fst baseMap baseMap := rfl

/-- **The source of the groupoid scheme is not locally of finite type.**  On rings it is the
inclusion of `𝐐(x)` into `𝐐(x) ⊗_𝐐 𝐐(x)` as the right factor, which is not of finite type. -/
@[stacks 04MR "s is not locally of finite type"]
theorem not_locallyOfFiniteType_source : ¬ LocallyOfFiniteType groupoid.source.left := by
  intro hsrc
  have : LocallyOfFiniteType (Limits.pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ))))) := hsrc
  have h : LocallyOfFiniteType ((pullbackSpecIso ℚ (RatFunc ℚ) (RatFunc ℚ)).inv ≫
      Limits.pullback.snd _ _) := inferInstance
  rw [pullbackSpecIso_inv_snd] at h
  exact not_finiteType_includeRight (HasRingHomProperty.Spec_iff.mp h)

/-- **The target of the groupoid scheme is not locally of finite type.**  On rings it is the
inclusion of `𝐐(x)` into `𝐐(x) ⊗_𝐐 𝐐(x)` as the left factor, which is not of finite type. -/
@[stacks 04MR "t is not locally of finite type"]
theorem not_locallyOfFiniteType_target : ¬ LocallyOfFiniteType groupoid.target.left := by
  intro htgt
  have : LocallyOfFiniteType (Limits.pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (RatFunc ℚ))))) := htgt
  have h : LocallyOfFiniteType ((pullbackSpecIso ℚ (RatFunc ℚ) (RatFunc ℚ)).inv ≫
      Limits.pullback.fst _ _) := inferInstance
  rw [pullbackSpecIso_inv_fst] at h
  exact not_finiteType_includeLeftRingHom (HasRingHomProperty.Spec_iff.mp h)

/-! ### The warning -/

/-- **The arrow scheme is the spectrum the source displays**, namely
`Spec (𝐐(x)[y][1/P(xy)])`: the arrow scheme is the fibre square of `Spec 𝐐(x)` over `Spec 𝐐`,
whose ring of functions is the tensor square, and the tensor square is that localization. -/
noncomputable def arrowsIsoSpecSourceArrowRing :
    groupoid.arrows.left ≅ Spec (CommRingCat.of sourceArrowRing) := by
  refine (?_ : groupoid.arrows.left
      ≅ Spec (CommRingCat.of (TensorProduct ℚ (RatFunc ℚ) (RatFunc ℚ)))).trans
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (sourceArrowRingEquiv.trans arrowRingEquiv.symm)).op)
  exact pullbackSpecIso ℚ (RatFunc ℚ) (RatFunc ℚ)

/-- **The example of Tag 04MR, in full.**  There is a groupoid scheme whose object scheme is
the spectrum of a field — here `𝐐(x)` — whose arrow scheme is `Spec (𝐐(x)[y][1/P(xy)])`, whose
source and target morphisms are not locally of finite type, and for which the dimension of the
arrow scheme is one while the dimension of the stabilizer group scheme is zero. -/
@[stacks 04MR "the example in full: U = Spec Q(x) with Q(x) a field, R = Spec (Q(x)[y][1/P(xy)]), \
s and t are not locally of finite type, dim R = 1 and dim G = 0"]
theorem exists_dim_arrows_eq_one_dim_stabilizer_eq_zero :
    ∃ (k : Type) (_ : Field k) (G : GroupoidScheme (Spec (CommRingCat.of ℚ))),
      G.objects.left = Spec (CommRingCat.of k) ∧
        Nonempty (G.arrows.left ≅ Spec (CommRingCat.of sourceArrowRing)) ∧
        ¬ LocallyOfFiniteType G.source.left ∧
        ¬ LocallyOfFiniteType G.target.left ∧
        topologicalKrullDim G.arrows.left = 1 ∧
        topologicalKrullDim (stabilizer G).left = 0 :=
  ⟨RatFunc ℚ, inferInstance, groupoid, objects_left, ⟨arrowsIsoSpecSourceArrowRing⟩,
    not_locallyOfFiniteType_source, not_locallyOfFiniteType_target,
    topologicalKrullDim_arrows_eq_one, topologicalKrullDim_stabilizer⟩

/-- **The warning of Tag 04MR.**  Tag 04MQ is wrong without the condition that `s` and `t` are
locally of finite type: for a groupoid scheme whose object scheme is the spectrum of a field,
the dimension of the arrow scheme need not be the dimension of the stabilizer group scheme. -/
@[stacks 04MR "Tag 04MQ is wrong without the condition that s and t are locally of finite type"]
theorem not_forall_dim_arrows_eq_dim_stabilizer :
    ¬ ∀ (S : Scheme.{0}) (G : GroupoidScheme S) (k : Type) (_ : Field k),
        G.objects.left = Spec (CommRingCat.of k) →
          topologicalKrullDim G.arrows.left = topologicalKrullDim (stabilizer G).left :=
  fun h => topologicalKrullDim_arrows_ne_stabilizer
    (h (Spec (CommRingCat.of ℚ)) groupoid (RatFunc ℚ) inferInstance objects_left)

end AlgebraicGeometry.RationalFunctionPairGroupoid

end
