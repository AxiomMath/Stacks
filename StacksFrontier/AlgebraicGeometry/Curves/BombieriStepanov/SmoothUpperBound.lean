module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.PointCount
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.PrescribedResidueFieldPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Bombieri–Stepanov upper bound for a smooth curve, without a rational point

Let `X` be a smooth proper geometrically integral curve over a finite field `k` with `q`
elements, and let `N m = #X(k_m)` be its number of points over the extension of degree `m`.
Then there are `C`, `m₀` and `d ≠ 0` with

`N m ≤ q ^ m + C · √q ^ m` for every `m ≥ m₀` divisible by `d`.

The bound `Stacks.BombieriStepanov.exists_upper_bound_even` needs a closed point of residue field
`k`. In general `X` has none, and the hypothesis is removed by extending the ground field: a
closed point `x` of `X` has a finite residue field `κ(x)` of some degree `d` over `k`, the base
change `X' = X ×_k κ(x)` is again a smooth proper geometrically integral curve, now over
`κ(x)`, and it has a `κ(x)`-rational point above `x`
(`AlgebraicGeometry.exists_baseChange_point_of_residueFieldHom`). Every extension `K` of `κ(x)`
has `X'(K) = X(K)` by the universal property of the fibre product, so the bound for `X'` over
`κ(x)` — whose field has `q ^ d` elements — is the bound for `X` along the multiples of `2d`.

## Main results

* `Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one`: the local rings
  of a smooth curve at its places are discrete valuation rings.
* `Stacks.BombieriStepanov.natCard_fieldValuedPoints_baseChange`: `X_{k'}(K) = X(K)` for a tower
  `k ⊆ k' ⊆ K`.
* `Stacks.BombieriStepanov.exists_upper_bound_of_smooth`: the upper bound above.
* `Stacks.BombieriStepanov.norm_eq_sqrt_of_lower_bound_of_smooth`: the Riemann hypothesis for such
  a curve from a lower bound of the same shape, the point count formula and the pairing.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Order

universe u

namespace Stacks.BombieriStepanov

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **The local ring of a smooth curve at a place is a discrete valuation ring.** A point of
coheight one is not the generic point, and the local ring of a smooth curve at any other point is
a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_coheight_eq_one [IsCurve k p] [Smooth p] (x : X)
    (hx : coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  refine IsCurve.isDiscreteValuationRing_stalk k p fun hxg => ?_
  rw [hxg, Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y] at hx
  exact zero_ne_one hx

/-- **Points of a base change with values in an extension.** For a tower of fields
`k ⊆ k' ⊆ K`, the `K`-valued points of `X_{k'} = X ×_k k'` over `k'` are the `K`-valued points of
`X` over `k`: compose with the first projection, and lift through the fibre product. -/
@[ega "I 3.4.5" "base-change step"]
def fieldValuedPointsBaseChangeEquiv (k' : Type u) [Field k'] [Algebra k k'] (K : Type u)
    [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K] :
    Stacks.EtaleCohomology.fieldValuedPoints
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k k')))) K ≃
      Stacks.EtaleCohomology.fieldValuedPoints p K where
  toFun g := ⟨g.1 ≫ pullback.fst _ _, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, g.2, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]⟩
  invFun g := ⟨pullback.lift g.1 (Spec.map (CommRingCat.ofHom (algebraMap k' K))) (by
    rw [g.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]),
    pullback.lift_snd _ _ _⟩
  left_inv g := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans g.2.symm))
  right_inv g := Subtype.ext (pullback.lift_fst _ _ _)

/-- `#X_{k'}(K) = #X(K)` for a tower of fields `k ⊆ k' ⊆ K`. -/
theorem natCard_fieldValuedPoints_baseChange (k' : Type u) [Field k'] [Algebra k k'] (K : Type u)
    [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K] :
    Nat.card (Stacks.EtaleCohomology.fieldValuedPoints
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k k')))) K) =
      Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) :=
  Nat.card_congr (fieldValuedPointsBaseChangeEquiv p k' K)

/-- `√(q ^ d) ^ m = √q ^ (d m)`. -/
theorem sqrt_pow_pow (q : ℝ) (hq : 0 ≤ q) (d m : ℕ) :
    Real.sqrt (q ^ d) ^ m = Real.sqrt q ^ (d * m) := by
  have h : q ^ d = (Real.sqrt q ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq]
  rw [h, Real.sqrt_sq (by positivity), ← pow_mul]

/-- **A point of residue degree one is closed.** If `p' : X' ⟶ Spec K` is of locally finite type
and the residue field of `y` is `K` itself, the structure map makes `κ(y)` a finite `K`-module,
so `{y}` is closed. -/
private theorem isClosed_singleton_of_residueDegree_eq_one {K : Type u} [Field K]
    {X' : Scheme.{u}} (p' : X' ⟶ Spec (.of K)) [LocallyOfFiniteType p'] (y : X')
    (hfin : Stacks.EtaleCohomology.residueDegree p' y = 1) : IsClosed ({y} : Set X') := by
  refine isClosed_singleton_of_module_finite_residueField p' y ?_
  have hbridge : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p'.appTop ≫ X'.Γevaluation y =
      fieldToResidue p' y := by
    simp only [fieldToResidue, fieldToStalk, Scheme.Γevaluation, Scheme.evaluation,
      Category.assoc]
  rw [hbridge]
  let : Algebra K (X'.residueField y) := (fieldToResidue p' y).hom.toAlgebra
  exact Module.finite_of_finrank_eq_succ hfin

/-- **The point counts of a base change, reindexed.** Let `K` be a finite extension of `k` of
degree `d`. An extension `L` of `K` of degree `m` has degree `d * m` over `k`, and the `L`-valued
points of `X_K` over `K` are the `L`-valued points of `X` over `k`; so the counting function of
`X_K` is `m ↦ N (d * m)`. -/
private theorem natCard_fieldValuedPoints_baseChange_eq (K : Type u) [Field K] [Algebra k K]
    [Module.Finite k K] (N : ℕ → ℕ)
    (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K' : Type u) [Field K'] [Algebra k K'] [Finite K'],
      Module.finrank k K' = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K') = N m)
    (d : ℕ) (hd : Module.finrank k K = d) (hdpos' : 0 < d) :
    ∀ m : ℕ, m ≠ 0 → ∀ (L : Type u) [Field L] [Algebra K L] [Finite L],
      Module.finrank K L = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L) = N (d * m) := by
  intro m hm L _ _ _ hL
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [natCard_fieldValuedPoints_baseChange p K L]
  have : Module.Finite K L := Module.Finite.of_finite
  exact hNcard (d * m) (Nat.mul_ne_zero hdpos'.ne' hm) L
    (by rw [← Module.finrank_mul_finrank k K L, hL, hd])

/-- **The Bombieri–Stepanov upper bound for a smooth curve.** Let `X` be a smooth proper
geometrically integral curve over the finite field `k` with `q` elements, and let `N m` be the
number of points of `X` over the extensions of degree `m` of `k`. There are `C`, `m₀` and
`d ≠ 0` with `N m ≤ q^m + C · √q^m` for every `m ≥ m₀` divisible by `d`. No rational point is
assumed: the bound is proved for the base change to the residue field of a closed point, which
has one. -/
theorem exists_upper_bound_of_smooth [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    [IsProper p] [Smooth p] [GeometricallyIntegral p] [IsCurve k p]
    (N : ℕ → ℕ) (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m) :
    ∃ (C : ℝ) (m₀ d : ℕ), d ≠ 0 ∧ ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      (N m : ℝ) ≤ (Fintype.card k : ℝ) ^ m + C * Real.sqrt (Fintype.card k) ^ m := by
  classical
  -- a closed point and its residue field
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  set K := X.residueField x
  let : Algebra k K := (fieldToResidue p x).hom.toAlgebra
  set d := Module.finrank k K with hd
  have hdpos' : 0 < d := Stacks.EtaleCohomology.residueDegree_pos p x hx
  have : Module.Finite k K := Module.finite_of_finrank_pos hdpos'
  have : Finite K := Module.finite_of_finite k
  let : Fintype K := Fintype.ofFinite K
  have : CharP K pr := charP_of_injective_algebraMap (algebraMap k K).injective pr
  have hcardK : Fintype.card K = Fintype.card k ^ d := Module.card_eq_pow_finrank
  -- the base change to `κ(x)`
  set X' : Scheme.{u} := pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  set p' : X' ⟶ Spec (.of K) := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_subsingleton p'
  have : IsCurve K p' :=
    { topologicalKrullDim_eq_one := by
        rw [topologicalKrullDim_baseChange k K (pullback.fst _ _) p'
          p (IsPullback.of_hasPullback _ _)]
        exact IsCurve.topologicalKrullDim_eq_one p }
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian p'
  -- the rational point above `x`
  obtain ⟨y, -, hbij, -⟩ := exists_baseChange_point_of_residueFieldHom p x
    (CommRingCat.ofHom (RingHom.id K)) rfl
  have hfin : Stacks.EtaleCohomology.residueDegree p' y = 1 := by
    let : Algebra K (X'.residueField y) := (fieldToResidue p' y).hom.toAlgebra
    show Module.finrank K (X'.residueField y) = 1
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K (X'.residueField y)) hbij).finrank_eq,
      Module.finrank_self]
  have hcl : IsClosed ({y} : Set X') := isClosed_singleton_of_residueDegree_eq_one p' y hfin
  let P₀ : CurvePlace X' := ⟨y, coheight_eq_one_of_isCurve K p' hcl⟩
  have hP₀ : curveDeg K p' P₀ = 1 := by
    rwa [curveDeg, ← residueDegree_eq_residueDegree]
  have hsurj : Function.Surjective fun c : K =>
      IsLocalRing.residue (X'.presheaf.stalk P₀.1) ((fieldToStalk p' P₀.1).hom c) :=
    hbij.2
  -- the counts of `X'` are those of `X` along the multiples of `d`
  obtain ⟨C, m₀, hup⟩ := exists_upper_bound_even p'
    (isDiscreteValuationRing_stalk_of_coheight_eq_one p') pr P₀ hcl hP₀ hsurj
    (fun m => N (d * m)) (natCard_fieldValuedPoints_baseChange_eq p K N hNcard d hd.symm hdpos')
  refine ⟨C, d * m₀, 2 * d, by omega, fun m hm hdm => ?_⟩
  obtain ⟨t, rfl⟩ := hdm
  have h := hup (2 * t) (by nlinarith) (dvd_mul_right 2 t)
  rw [show 2 * d * t = d * (2 * t) by ring]
  rwa [hcardK, Nat.cast_pow, sqrt_pow_pow _ (Nat.cast_nonneg _), ← pow_mul] at h

/-- **The Riemann hypothesis for a smooth curve, from a lower bound and the pairing.** Let `X` be
a smooth proper geometrically integral curve over `𝔽_q` and `N m = #X(k_m) = 1 - ∑_i α_i^m + q^m`
(Tag 03V8, part (3)). Assume a lower bound `q^m ≤ N m + C · √q^m` for large `m` in an arithmetic
progression `d ℕ`, and the pairing `α_i α_j = q`. Then `‖α_i‖ = √q`. The upper bound is
`Stacks.BombieriStepanov.exists_upper_bound_of_smooth`; no rational point is assumed. -/
theorem norm_eq_sqrt_of_lower_bound_of_smooth [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    [IsProper p] [Smooth p] [GeometricallyIntegral p] [IsCurve k p]
    (N : ℕ → ℕ) (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m)
    {ι : Type*} [Fintype ι] (α : ι → ℂ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (Fintype.card k : ℂ) ^ m)
    (C : ℝ) (m₀ d : ℕ) (hd : d ≠ 0)
    (hlower : ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      (Fintype.card k : ℝ) ^ m ≤ N m + C * Real.sqrt (Fintype.card k) ^ m)
    (hpair : ∀ i, ∃ j, α i * α j = Fintype.card k) (i : ι) :
    ‖α i‖ = Real.sqrt (Fintype.card k) := by
  obtain ⟨C', m₁, d', hd', hup⟩ := exists_upper_bound_of_smooth p pr N hNcard
  have hs : ∀ m : ℕ, 0 ≤ Real.sqrt (Fintype.card k) ^ m := fun m => by positivity
  refine Stacks.TraceFormula.norm_eq_sqrt_of_upper_lower α Fintype.card_pos N hN
    (C := max C C') (d := d * d') (Nat.mul_ne_zero hd hd') (max m₀ m₁) (fun m hm hdm => ?_)
    (fun m hm hdm => ?_) hpair i
  · have := hup m (le_of_max_le_right hm) (dvd_trans (dvd_mul_left d' d) hdm)
    nlinarith [hs m, le_max_right C C']
  · have := hlower m (le_of_max_le_left hm) (dvd_trans (dvd_mul_right d d') hdm)
    nlinarith [hs m, le_max_left C C']

end Stacks.BombieriStepanov

end
