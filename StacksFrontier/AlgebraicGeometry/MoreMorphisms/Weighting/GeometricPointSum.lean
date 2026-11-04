module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.WeightedFibreSum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The weighted fibre sum as a plain sum over geometric points

Let `π : U ⟶ V` be locally quasi-finite, let `ω : U → ℤ` and let `v` be a point of `V`. The
separable-degree weighted fibre sum `AlgebraicGeometry.separableDegreeWeightedFiberSum π ω v`
weights the value `ω x` at a point `x` of the fibre by the separable degree of the residue-field
extension `κ(v) ⊆ κ(x)`. Choosing an algebraically closed field `K` and an embedding
`ψ : κ(v) ⟶ K`, the weighted sum is the *plain* sum of `ω` over the `K`-points of `U` lying above
the `K`-point `Spec ψ` of `V`, whenever `ω` has finite support on the fibre over `v`. This is the
second description of the weighted fibre sum in Stacks 0F39.

## Main results

* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_specPoints` — **the weighted
  fibre sum is the plain sum of `ω` over the `K`-points above `Spec ψ`**, whenever `ω` has finite
  support on the fibre over `v`.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_finite_fiber` and
  `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_isFinite` — the same
  for a morphism with finite fibres, where no hypothesis on `ω` is needed.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_eq` and
  `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_hom` — the same
  indexed by an arbitrary `K`-point `q₀` of `V`, which is what a geometric point of `V` gives,
  rather than by an embedding of the residue field at `v`.

## References

* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The weighted fibre sum is a plain sum over geometric points.** For `K` algebraically closed
and `ψ` an embedding of the residue field at `v` into `K`, the separable-degree weighted fibre
sum of `ω` over `v` is the plain sum of `ω` over the `K`-points of `U` lying above the `K`-point
`Spec ψ` of `V`.

Only `ω` is assumed to have finite support on the fibre; the fibre itself may be infinite. -/
@[ega "I 6.4.7" "partial", sga "1 IX 5.4" "more general"]
public theorem separableDegreeWeightedFiberSum_eq_finsum_specPoints
    {U V : Scheme.{u}} (π : U ⟶ V) [LocallyQuasiFinite π] (ω : U → ℤ) (v : V)
    {K : Type u} [Field K] [IsAlgClosed K] (ψ : V.residueField v ⟶ CommRingCat.of K)
    (hfin : {x : U | π.base x = v ∧ ω x ≠ 0}.Finite) :
    separableDegreeWeightedFiberSum π ω v =
      ∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U //
                q ≫ π = Spec.map ψ ≫ V.fromSpecResidueField v},
        ω (q.1.base (IsLocalRing.closedPoint K)) := by
  classical
  let Fib := {x : U // π x = v}
  let L : Fib → Type u := fun x =>
    {φ : U.residueField x.1 ⟶ CommRingCat.of K //
      π.residueFieldMap x.1 ≫ φ = (V.residueFieldCongr x.2).hom ≫ ψ}
  have : ∀ x : Fib, Finite (L x) := fun x =>
    finite_residueField_extension_lifts π x.1 ((V.residueFieldCongr x.2).hom ≫ ψ)
  let : ∀ x : Fib, Fintype (L x) := fun x => Fintype.ofFinite (L x)
  have hcard : ∀ x : Fib, (let := (π.residueFieldMap x.1).hom.toAlgebra
      Field.finSepDegree (V.residueField (π x.1)) (U.residueField x.1)) = Fintype.card (L x) := by
    intro x
    let := (π.residueFieldMap x.1).hom.toAlgebra
    simpa [L, Nat.card_eq_fintype_card] using
      residueField_extension_lifts_card π x.1 ((V.residueFieldCongr x.2).hom ≫ ψ)
  have hsupp : {x : Fib | ω x.1 ≠ 0}.Finite :=
    (hfin.preimage Subtype.val_injective.injOn).subset fun x hx => ⟨x.2, hx⟩
  have hlhs : separableDegreeWeightedFiberSum π ω v =
      ∑ x ∈ hsupp.toFinset, ω x.1 * (Fintype.card (L x) : ℤ) := by
    calc separableDegreeWeightedFiberSum π ω v
        = ∑ᶠ x : Fib, let := (π.residueFieldMap x.1).hom.toAlgebra
            ω x.1 * (Field.finSepDegree (V.residueField (π x.1)) (U.residueField x.1) : ℤ) :=
          separableDegreeWeightedFiberSum_eq_finsum_fiber π ω v
      _ = ∑ᶠ x : Fib, ω x.1 * (Fintype.card (L x) : ℤ) :=
          finsum_congr fun x => congrArg (fun n : ℕ => ω x.1 * (n : ℤ)) (hcard x)
      _ = ∑ x ∈ hsupp.toFinset, ω x.1 * (Fintype.card (L x) : ℤ) := by
          refine finsum_eq_sum_of_support_subset _ fun x hx => hsupp.mem_toFinset.mpr fun h0 => ?_
          simp [h0] at hx
  have hrhs : (∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U //
        q ≫ π = Spec.map ψ ≫ V.fromSpecResidueField v},
          ω (q.1.base (IsLocalRing.closedPoint K))) =
      ∑ x ∈ hsupp.toFinset, ω x.1 * (Fintype.card (L x) : ℤ) := by
    have he : (∑ᶠ d : Σ x : Fib, L x, ω d.1.1) =
        ∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U //
            q ≫ π = Spec.map ψ ≫ V.fromSpecResidueField v},
          ω (q.1.base (IsLocalRing.closedPoint K)) :=
      (finsum_comp_equiv (specPointFiberFieldSigmaEquiv π v ψ)
        (f := fun d : Σ x : Fib, L x => ω d.1.1)).symm.trans
        (finsum_congr fun q => by congr 1)
    rw [← he]
    calc (∑ᶠ d : Σ x : Fib, L x, ω d.1.1)
        = ∑ d ∈ hsupp.toFinset.sigma fun x : Fib => (Finset.univ : Finset (L x)), ω d.1.1 :=
          finsum_eq_sum_of_support_subset _ fun d hd =>
            Finset.mem_sigma.mpr ⟨hsupp.mem_toFinset.mpr hd, Finset.mem_univ _⟩
      _ = ∑ x ∈ hsupp.toFinset, ∑ _φ ∈ (Finset.univ : Finset (L x)), ω x.1 :=
          Finset.sum_sigma _ _ _
      _ = ∑ x ∈ hsupp.toFinset, ω x.1 * (Fintype.card (L x) : ℤ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  exact hlhs.trans hrhs.symm

/-- The weighted fibre sum over a point with finite fibre is the plain sum of `ω` over the
`K`-points above `Spec ψ`, for `K` algebraically closed. No hypothesis on `ω` is needed. -/
public theorem separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_finite_fiber
    {U V : Scheme.{u}} (π : U ⟶ V) [LocallyQuasiFinite π] (ω : U → ℤ) (v : V)
    {K : Type u} [Field K] [IsAlgClosed K] (ψ : V.residueField v ⟶ CommRingCat.of K)
    (hfibre : (π.base ⁻¹' {v}).Finite) :
    separableDegreeWeightedFiberSum π ω v =
      ∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U //
                q ≫ π = Spec.map ψ ≫ V.fromSpecResidueField v},
        ω (q.1.base (IsLocalRing.closedPoint K)) :=
  separableDegreeWeightedFiberSum_eq_finsum_specPoints π ω v ψ
    (hfibre.subset fun _ hx => hx.1)

/-- The weighted fibre sum along a finite morphism is the plain sum of `ω` over the `K`-points
above `Spec ψ`, for `K` algebraically closed. -/
public theorem separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_isFinite
    {U V : Scheme.{u}} (π : U ⟶ V) [IsFinite π] (ω : U → ℤ) (v : V)
    {K : Type u} [Field K] [IsAlgClosed K] (ψ : V.residueField v ⟶ CommRingCat.of K) :
    separableDegreeWeightedFiberSum π ω v =
      ∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U //
                q ≫ π = Spec.map ψ ≫ V.fromSpecResidueField v},
        ω (q.1.base (IsLocalRing.closedPoint K)) :=
  separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_finite_fiber π ω v ψ
    (π.finite_preimage_singleton v)

/-- The weighted fibre sum as a plain sum over the `K`-points above a `K`-point `q₀` of `V`,
given a factorisation of `q₀` through the residue field at its image. -/
public theorem separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_eq
    {U V : Scheme.{u}} (π : U ⟶ V) [LocallyQuasiFinite π] (ω : U → ℤ) (v : V)
    {K : Type u} [Field K] [IsAlgClosed K] (ψ : V.residueField v ⟶ CommRingCat.of K)
    (q₀ : Spec (CommRingCat.of K) ⟶ V)
    (hq₀ : Spec.map ψ ≫ V.fromSpecResidueField v = q₀)
    (hfin : {x : U | π.base x = v ∧ ω x ≠ 0}.Finite) :
    separableDegreeWeightedFiberSum π ω v =
      ∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U // q ≫ π = q₀},
        ω (q.1.base (IsLocalRing.closedPoint K)) := by
  subst hq₀
  exact separableDegreeWeightedFiberSum_eq_finsum_specPoints π ω v ψ hfin

/-- **The weighted fibre sum at a geometric point.** For an arbitrary `K`-point `q₀` of `V` with
`K` algebraically closed, the weighted fibre sum of `ω` over the image of `q₀` is the plain sum
of `ω` over the `K`-points of `U` above `q₀`, provided `ω` has finite support on that fibre. -/
public theorem separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_hom
    {U V : Scheme.{u}} (π : U ⟶ V) [LocallyQuasiFinite π] (ω : U → ℤ)
    {K : Type u} [Field K] [IsAlgClosed K] (q₀ : Spec (CommRingCat.of K) ⟶ V)
    (hfin : {x : U | π.base x = q₀.base (IsLocalRing.closedPoint K) ∧ ω x ≠ 0}.Finite) :
    separableDegreeWeightedFiberSum π ω (q₀.base (IsLocalRing.closedPoint K)) =
      ∑ᶠ q : {q : Spec (CommRingCat.of K) ⟶ U // q ≫ π = q₀},
        ω (q.1.base (IsLocalRing.closedPoint K)) :=
  separableDegreeWeightedFiberSum_eq_finsum_specPoints_of_eq π ω
    (q₀.base (IsLocalRing.closedPoint K)) (Scheme.SpecToEquivOfField K V q₀).2 q₀
    ((Scheme.SpecToEquivOfField K V).symm_apply_apply q₀) hfin

end AlgebraicGeometry
