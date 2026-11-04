module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureStalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.MilnorBoundary
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Height-one primes of a local ring and the intermediate points of a specialization

Let `W` be an integral scheme with generic point `x = genericPoint W`, let `x''` be a point of
`W`, and let `A = 𝒪_{W, x''}` be the local ring there. The canonical morphism
`AlgebraicGeometry.Scheme.fromSpecStalk` identifies the primes of `A` with the points of `W`
that specialize to `x''`, and under that identification the height of a prime is the coheight of
the point. When `dim A = 2`, the height-one primes of `A` are therefore exactly the points `x'`
with

`x ⇝ x' ⇝ x''`,

each step an immediate specialization, and the orders of the Milnor `K₂` tame-symbol boundaries,
summed over these points `x'`, give zero.

## Main results

* `Stacks.Chow.coheight_fromSpecStalk_eq_height` — the height of a prime of `𝒪_{W, x}` is the
  coheight, in the specialization order, of the point of `W` it corresponds to.
* `Stacks.Chow.coheight_eq_one_iff_isImmediateSpecialization_genericPoint` — on an integral
  scheme a point has coheight one exactly when the generic point specializes to it immediately.
* `Stacks.Chow.isImmediateSpecialization_of_coheight_eq_one_of_coheight_eq_two` — a coheight-one
  generization of a coheight-two point is an immediate generization of it.
* `Stacks.Chow.height_eq_one_iff_isImmediateSpecialization_genericPoint` — the height-one primes
  of `𝒪_{W, x''}` correspond to the immediate specializations of the generic point.
* `Stacks.Chow.heightOnePrimeEquivIntermediatePoint` — for `dim 𝒪_{W, x''} = 2`, an equivalence
  between the height-one primes of `𝒪_{W, x''}` and the points `x'` with `x ⇝ x' ⇝ x''`, both
  steps immediate.
* `Stacks.Chow.isLocalization_stalk_heightOnePrime` — the local ring at such an `x'` is the
  localization of `𝒪_{W, x''}` at the corresponding height-one prime.
* `Stacks.Chow.ringKrullDim_stalk_intermediatePoint_eq_one` — that local ring is
  one-dimensional.
* `Stacks.Chow.sum_intermediatePointMilnorBoundaryOrder_eq_zero` — the orders of the Milnor `K₂`
  tame-symbol boundaries, summed over the intermediate points, give zero.
* `Stacks.Chow.coheight_eq_one_iff_isImmediateSpecialization_pointClosure` — the coheight-one
  criterion on the reduced closure `closure {x}` of a point, with `x` as its generic point.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

variable {W : Scheme.{u}}

/-! ### The specialization preorder on the points of a scheme -/

/-- The specialization preorder on the points of a scheme is antisymmetric. -/
theorem scheme_eq_of_le_of_le {a b : W} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  (Specializes.antisymm (Scheme.le_iff_specializes.mp hba)
    (Scheme.le_iff_specializes.mp hab)).eq

/-- In the specialization preorder, `a ≤ b` and `a ≠ b` give `a < b`. -/
private theorem scheme_lt_of_le_of_ne {a b : W} (hab : a ≤ b) (hne : a ≠ b) : a < b :=
  lt_iff_le_not_ge.mpr ⟨hab, fun h => hne (scheme_eq_of_le_of_le hab h)⟩

/-- On an integral scheme the top element of the specialization preorder is the generic point. -/
theorem genericPoint_eq_top [IsIntegral W] : genericPoint W = (⊤ : W) := rfl

/-! ### Primes of a local ring and the generizations of the point -/

/-- Every generization of `x` comes from a prime of `𝒪_{W, x}`. -/
theorem exists_fromSpecStalk_eq {x z : W} (h : z ⤳ x) :
    ∃ p : Spec (W.presheaf.stalk x), W.fromSpecStalk x p = z := by
  show z ∈ Set.range ⇑(W.fromSpecStalk x)
  rw [W.range_fromSpecStalk]
  exact h

/-- The order on the primes of `𝒪_{W, x}` is the specialization order on the corresponding
points of `W`. -/
@[ega "I 2.4.2" "partial"]
theorem fromSpecStalk_le_iff (x : W) {p q : Spec (W.presheaf.stalk x)} :
    W.fromSpecStalk x p ≤ W.fromSpecStalk x q ↔ p ≤ q := by
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact (W.fromSpecStalk x).isEmbedding.isInducing.specializes_iff

/-- The height of a prime of `𝒪_{W, x}` is the coheight, in the specialization order, of the
corresponding point of `W`. -/
theorem coheight_fromSpecStalk_eq_height (x : W) (p : Spec (W.presheaf.stalk x)) :
    Order.coheight (W.fromSpecStalk x p) = p.asIdeal.height := by
  have hlt {p q : Spec (W.presheaf.stalk x)} :
      W.fromSpecStalk x p < W.fromSpecStalk x q ↔ p < q := by
    simp only [lt_iff_le_not_ge, fromSpecStalk_le_iff]
  have hco := Order.coheight_eq_of_strictMono ⇑(W.fromSpecStalk x) (fun _ _ => hlt.mpr)
    (fun p y hpy => by
    obtain ⟨q, rfl⟩ := exists_fromSpecStalk_eq
      ((Scheme.le_iff_specializes.mp hpy.le).trans (specializes_fromSpecStalk x p))
    exact ⟨q, hlt.mp hpy, rfl⟩) p
  exact hco.symm.trans (idealHeight_eq_coheight (W.presheaf.stalk x) p).symm

/-! ### Coheight one and immediate specialization from the generic point -/

/-- A point of an integral scheme has coheight one exactly when the generic point specializes
to it immediately. -/
theorem coheight_eq_one_iff_isImmediateSpecialization_genericPoint [IsIntegral W] (z : W) :
    Order.coheight z = 1 ↔ IsImmediateSpecialization (genericPoint W) z := by
  constructor
  · intro h
    have hle : Order.coheight z ≤ ((1 : ℕ) : ℕ∞) := by rw [h]; simp
    refine ⟨genericPoint_specializes z, fun hz => ?_, fun y _ hyz => ?_⟩
    · rw [← hz, genericPoint_eq_top, Order.coheight_top] at h
      exact zero_ne_one h
    by_cases hyz' : y = z
    · exact Or.inr hyz'
    have hzy : z ≤ y := Scheme.le_iff_specializes.mpr hyz
    have hy0 : Order.coheight y = 0 := Order.lt_one_iff.mp (by
      simpa using Order.coheight_le_coe_iff.mp hle y
        (scheme_lt_of_le_of_ne hzy (Ne.symm hyz')))
    exact Or.inl (scheme_eq_of_le_of_le le_top (Order.coheight_eq_zero.mp hy0 le_top))
  · intro himm
    have hle : Order.coheight z ≤ ((1 : ℕ) : ℕ∞) := by
      refine Order.coheight_le_coe_iff.mpr fun y hzy => ?_
      obtain hy | hy := himm.2.2 y (genericPoint_specializes y)
        (Scheme.le_iff_specializes.mp hzy.le)
      · rw [hy, genericPoint_eq_top, Order.coheight_top]
        exact Nat.cast_pos.mpr Nat.one_pos
      · exact absurd hy hzy.ne'
    refine le_antisymm (by simpa using hle) (Order.one_le_iff_ne_zero.mpr
      (Order.coheight_ne_zero.mpr fun hmax => himm.2.1 ?_))
    exact (scheme_eq_of_le_of_le le_top (hmax le_top)).symm

/-- A coheight-one generization of a coheight-two point is an immediate generization of it. -/
theorem isImmediateSpecialization_of_coheight_eq_one_of_coheight_eq_two {x' x'' : W}
    (h'' : Order.coheight x'' = 2) (h' : Order.coheight x' = 1) (hle : x'' ≤ x') :
    IsImmediateSpecialization x' x'' := by
  refine ⟨Scheme.le_iff_specializes.mp hle, ?_, ?_⟩
  · intro hx
    rw [hx, h''] at h'
    exact absurd h' (by decide)
  · intro z hx'z hzx''
    by_cases hz' : z = x'
    · exact Or.inl hz'
    by_cases hz'' : z = x''
    · exact Or.inr hz''
    have hzle : z ≤ x' := Scheme.le_iff_specializes.mpr hx'z
    have hlez : x'' ≤ z := Scheme.le_iff_specializes.mpr hzx''
    have h₁ := Order.coheight_add_one_le
      (scheme_lt_of_le_of_ne hlez (Ne.symm hz''))
    have h₂ := Order.coheight_add_one_le
      (scheme_lt_of_le_of_ne hzle hz')
    rw [h''] at h₁
    rw [h'] at h₂
    exact absurd ((add_le_add h₂ le_rfl).trans h₁) (by norm_num)

/-! ### The correspondence -/

/-- A prime of `𝒪_{W, x''}` has height one exactly when the generic point of the integral scheme
`W` specializes immediately to the corresponding point. -/
theorem height_eq_one_iff_isImmediateSpecialization_genericPoint [IsIntegral W] (x'' : W)
    (p : Spec (W.presheaf.stalk x'')) :
    p.asIdeal.height = 1 ↔
      IsImmediateSpecialization (genericPoint W) (W.fromSpecStalk x'' p) := by
  rw [← coheight_fromSpecStalk_eq_height x'' p,
    coheight_eq_one_iff_isImmediateSpecialization_genericPoint]

/-- The point of the integral scheme `W` attached to a height-one prime of `𝒪_{W, x''}`. -/
def intermediatePointOfHeightOnePrime (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) : W :=
  W.fromSpecStalk x'' ⟨q.1, q.2.1⟩

/-- Distinct height-one primes of `𝒪_{W, x''}` cut out distinct points of `W`. -/
theorem injective_intermediatePointOfHeightOnePrime (x'' : W) :
    Function.Injective (intermediatePointOfHeightOnePrime x'') := by
  intro q q' h
  have hp : (⟨q.1, q.2.1⟩ : Spec (W.presheaf.stalk x'')) = ⟨q'.1, q'.2.1⟩ :=
    (W.fromSpecStalk x'').isEmbedding.injective h
  exact Subtype.ext (congrArg PrimeSpectrum.asIdeal hp)

/-- The generic point of `W` specializes immediately to the point attached to a height-one prime
of `𝒪_{W, x''}`. -/
theorem isImmediateSpecialization_genericPoint_intermediatePointOfHeightOnePrime
    [IsIntegral W] (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    IsImmediateSpecialization (genericPoint W) (intermediatePointOfHeightOnePrime x'' q) :=
  (height_eq_one_iff_isImmediateSpecialization_genericPoint x'' ⟨q.1, q.2.1⟩).mp q.2.2

/-- The point attached to a prime of `𝒪_{W, x''}` specializes to `x''`. -/
theorem specializes_intermediatePointOfHeightOnePrime (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    intermediatePointOfHeightOnePrime x'' q ⤳ x'' :=
  specializes_fromSpecStalk x'' ⟨q.1, q.2.1⟩

/-- When `𝒪_{W, x''}` is two-dimensional, the point attached to a height-one prime specializes
*immediately* to `x''`. -/
theorem isImmediateSpecialization_intermediatePointOfHeightOnePrime [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    IsImmediateSpecialization (intermediatePointOfHeightOnePrime x'' q) x'' := by
  have h'' : Order.coheight x'' = 2 := by
    have h : ((Order.coheight x'' : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x'', hdim]
      norm_num
    exact WithBot.coe_inj.mp h
  have h' : Order.coheight (intermediatePointOfHeightOnePrime x'' q) = 1 :=
    (coheight_eq_one_iff_isImmediateSpecialization_genericPoint _).mpr
      (isImmediateSpecialization_genericPoint_intermediatePointOfHeightOnePrime x'' q)
  exact isImmediateSpecialization_of_coheight_eq_one_of_coheight_eq_two h'' h'
    (Scheme.le_iff_specializes.mpr (specializes_intermediatePointOfHeightOnePrime x'' q))

/-- The map underlying the correspondence: a height-one prime of `𝒪_{W, x''}` goes to the
intermediate point of `W` it cuts out. -/
def heightOnePrimeToIntermediatePoint [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    {x' : W // IsImmediateSpecialization (genericPoint W) x' ∧
      IsImmediateSpecialization x' x''} :=
  ⟨intermediatePointOfHeightOnePrime x'' q,
    isImmediateSpecialization_genericPoint_intermediatePointOfHeightOnePrime x'' q,
    isImmediateSpecialization_intermediatePointOfHeightOnePrime hdim q⟩

/-- The map from height-one primes of `𝒪_{W, x''}` to intermediate points is bijective. -/
theorem bijective_heightOnePrimeToIntermediatePoint [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2) :
    Function.Bijective (heightOnePrimeToIntermediatePoint hdim) := by
  refine ⟨fun q q' hqq' => injective_intermediatePointOfHeightOnePrime x'' <|
    (congrArg Subtype.val hqq' :), fun x' => ?_⟩
  obtain ⟨p, hp⟩ := exists_fromSpecStalk_eq x'.2.2.1
  exact ⟨⟨p.asIdeal, p.2,
    (height_eq_one_iff_isImmediateSpecialization_genericPoint x'' p).mpr (hp ▸ x'.2.1)⟩,
    Subtype.ext hp⟩

/-- Let `W` be an integral scheme with generic point `x`, and let `x''` be a point of `W` whose
local ring is two-dimensional. Then the height-one primes `𝔮` of `𝒪_{W, x''}` correspond
bijectively to the points `x'` of `W` with `x ⇝ x' ⇝ x''`, both steps immediate
specializations; the point attached to `𝔮` is the one `𝔮` cuts out under
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
def heightOnePrimeEquivIntermediatePoint [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2) :
    {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1} ≃
      {x' : W // IsImmediateSpecialization (genericPoint W) x' ∧
        IsImmediateSpecialization x' x''} :=
  Equiv.ofBijective _ (bijective_heightOnePrimeToIntermediatePoint hdim)

/-- The point attached to a height-one prime by `Stacks.Chow.heightOnePrimeEquivIntermediatePoint`
is `Stacks.Chow.intermediatePointOfHeightOnePrime` of it. -/
@[simp] theorem heightOnePrimeEquivIntermediatePoint_apply [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    (heightOnePrimeEquivIntermediatePoint hdim q : W) =
      intermediatePointOfHeightOnePrime x'' q := rfl

/-! ### The local ring at an intermediate point -/

/-- If `𝔮` is a height-one prime of `A = 𝒪_{W, x''}` and `x'` is the point it cuts out, then
`TopCat.Presheaf.stalkSpecializes` makes `𝒪_{W, x'}` the localization `A_𝔮`. -/
theorem isLocalization_stalk_heightOnePrime (x'' : W)
    (q : {q : Ideal (W.presheaf.stalk x'') // q.IsPrime ∧ q.height = 1}) :
    letI : q.1.IsPrime := q.2.1
    letI : Algebra (W.presheaf.stalk x'')
        (W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q)) :=
      (W.presheaf.stalkSpecializes
        (specializes_intermediatePointOfHeightOnePrime x'' q)).hom.toAlgebra
    IsLocalization.AtPrime
      (W.presheaf.stalk (intermediatePointOfHeightOnePrime x'' q)) q.1 :=
  isLocalization_stalk_of_specializes (specializes_intermediatePointOfHeightOnePrime x'' q)
    ⟨q.1, q.2.1⟩ rfl

/-- The local ring of an integral scheme at a point to which the generic point specializes
immediately is one-dimensional. -/
theorem ringKrullDim_stalk_intermediatePoint_eq_one [IsIntegral W] {x' : W}
    (himm : IsImmediateSpecialization (genericPoint W) x') :
    ringKrullDim (W.presheaf.stalk x') = 1 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x',
    (coheight_eq_one_iff_isImmediateSpecialization_genericPoint x').mpr himm]
  rfl

/-! ### The geometric vanishing of the composite -/

variable [IsLocallyNoetherian W]

/-- The order, along the quotient of `A = 𝒪_{W, x''}` by the height-one prime corresponding to
the intermediate point `x'`, of the Milnor `K₂` tame-symbol boundary of `α` there. -/
def intermediatePointMilnorBoundaryOrder [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (α : MilnorKTheory (FractionRing (W.presheaf.stalk x'')) 2)
    (x' : {x' : W // IsImmediateSpecialization (genericPoint W) x' ∧
      IsImmediateSpecialization x' x''}) : ℤ :=
  localMilnorBoundaryOrder hdim ((heightOnePrimeEquivIntermediatePoint hdim).symm x') α

/-- Let `W` be an integral locally Noetherian scheme with generic point `x`, let `x''` be a
point of `W` whose local ring is two-dimensional, and let `α` be a class in the degree-two
Milnor K-group of the fraction field of that local ring. Then the orders of the tame-symbol
boundaries of `α`, summed over the points `x'` with `x ⇝ x' ⇝ x''` and both steps immediate,
give zero. -/
theorem sum_intermediatePointMilnorBoundaryOrder_eq_zero [IsIntegral W] {x'' : W}
    (hdim : ringKrullDim (W.presheaf.stalk x'') = 2)
    (α : MilnorKTheory (FractionRing (W.presheaf.stalk x'')) 2) :
    (∑ᶠ x' : {x' : W // IsImmediateSpecialization (genericPoint W) x' ∧
      IsImmediateSpecialization x' x''},
        intermediatePointMilnorBoundaryOrder hdim α x') = 0 :=
  (finsum_comp_equiv (heightOnePrimeEquivIntermediatePoint hdim).symm
    (f := fun q => localMilnorBoundaryOrder hdim q α)).trans
    (sum_localMilnorBoundaryOrder_eq_zero hdim α)

/-! ### Reading the correspondence at the reduced closure of a point -/

/-- On the reduced closed subscheme `W = closure {x}` of a scheme `X`, a point has coheight one
exactly when `x` specializes to it immediately. -/
theorem coheight_eq_one_iff_isImmediateSpecialization_pointClosure {X : Scheme.{u}} (x : X)
    (z : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme) :
    Order.coheight z = 1 ↔ IsImmediateSpecialization
      (⟨x, subset_closure (Set.mem_singleton x)⟩ :
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subscheme) z := by
  let : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  rw [coheight_eq_one_iff_isImmediateSpecialization_genericPoint,
    genericPoint_subscheme_vanishingIdeal_closure_singleton x]
  rfl

end Stacks.Chow

end
