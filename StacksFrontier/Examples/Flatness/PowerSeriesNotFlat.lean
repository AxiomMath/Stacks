module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Flatness.CountableCoherent

/-!
# A power series ring that is flat over neither the coefficients nor the polynomials

There is a commutative ring `R` whose ring of formal power series in one variable is not a flat
`R`-module, and hence is not flat over `R[x]` either.

The witness is the trivial square-zero extension of `ZMod 2` by the countably infinite
`ZMod 2`-vector space `ℕ →₀ ZMod 2`. In that ring the element `x` coming from the first basis
vector of the module satisfies `x * (0 ⋉ v) = 0` for every `v`, so the annihilator of `x` is the
whole module summand, which is not finitely generated; a coherent ring would make that
annihilator finitely generated, so the ring is not coherent. The ring is countable, so by the
criterion for coherence of a countable ring the countable product `ℕ → R` is not flat, and
`PowerSeries R` is `R`-linearly isomorphic to `ℕ → R` by taking coefficients. Flatness over
`R[x]` would give flatness over `R` by transitivity, so it fails as well.

## Main results

* `Stacks.Examples.exists_powerSeries_not_flat`: there is a commutative ring whose power series
  ring is flat neither over the ring nor over its polynomial ring.

## Implementation notes

The `(x)`-adic completion of `R[x]` in the source is `PowerSeries R`; its module structures over
`R` and over `Polynomial R` are the canonical ones induced by the constant-series and
polynomial-to-power-series maps. One ring witnesses both failures of flatness.

## References

* [Stacks Project, Tag 0ALC](https://stacks.math.columbia.edu/tag/0ALC)
-/

@[expose] public section

namespace Stacks.Examples

universe u

private abbrev NotFlatCoeff : Type := ZMod 2

private noncomputable abbrev NotFlatModule : Type u := ULift.{u} (ℕ →₀ NotFlatCoeff)

/-- A countable commutative ring whose power series ring is not flat over it: the trivial
square-zero extension of `ZMod 2` by a countably infinite `ZMod 2`-vector space. -/
private noncomputable abbrev NotFlatRing : Type u :=
  TrivSqZeroExt.{0, u} NotFlatCoeff NotFlatModule

private theorem notFlatRing_not_isCoherentRing : ¬ IsCoherentRing (NotFlatRing) := by
  classical
  let K := NotFlatCoeff
  let V := NotFlatModule
  let R := NotFlatRing
  let : CommRing R := inferInstance
  let : SMulCommClass R R R :=
    ⟨fun a b c => by simpa only [smul_eq_mul] using mul_left_comm a b c⟩
  let x : R := TrivSqZeroExt.inr (ULift.up (Finsupp.single 0 (1 : K)))
  let φ : R →ₗ[R] R := LinearMap.mulRight R x
  intro hR
  let : Module.IsCoherent R R := hR.isCoherent
  have hfp : Module.FinitePresentation R φ.range :=
    Module.IsCoherent.fg_submodule_finitePresentation φ.range (Submodule.fg_range φ)
  have hkerfg : φ.ker.FG := by
    simpa [LinearMap.ker_rangeRestrict] using
      Module.FinitePresentation.fg_ker φ.rangeRestrict (LinearMap.surjective_rangeRestrict φ)
  have hkerfin : Module.Finite R φ.ker := Module.Finite.of_fg hkerfg
  let σ : R →+* K := (TrivSqZeroExt.fstHom K K V).toRingHom
  let g : φ.ker →ₛₗ[σ] V :=
    { toFun := fun y => y.1.snd
      map_add' _ _ := rfl
      map_smul' := by
        intro r y
        have hy : y.1.fst = 0 := by
          have h := congrArg TrivSqZeroExt.snd y.2
          change (y.1 * x).snd = 0 at h
          rw [TrivSqZeroExt.snd_mul] at h
          simp only [x, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr] at h
          have h0 := congrArg (fun f : V => f.down 0) h
          simpa [Finsupp.smul_single] using h0
        change (r * y.1).snd = σ r • y.1.snd
        rw [TrivSqZeroExt.snd_mul, hy]
        simp only [MulOpposite.op_zero, zero_smul, add_zero]
        rfl }
  have hgsurj : Function.Surjective g := by
    intro v
    refine ⟨⟨TrivSqZeroExt.inr v, ?_⟩, rfl⟩
    change TrivSqZeroExt.inr v * x = 0
    rw [TrivSqZeroExt.inr_mul_inr]
  let : Module.Finite K V := Module.Finite.of_surjective g hgsurj
  let e : (ℕ →₀ K) ≃ₗ[K] V :=
    (ULift.moduleEquiv (R := K) (M := ℕ →₀ K)).symm
  have hind : LinearIndependent K (fun n : ℕ => ULift.up (Finsupp.single n (1 : K))) := by
    change LinearIndependent K (fun n : ℕ => e (Finsupp.single n (1 : K)))
    exact (Finsupp.linearIndependent_single_one K ℕ).map' e.toLinearMap e.ker
  exact not_finite_iff_infinite.mpr inferInstance hind.finite

/-- Formal power series over a semiring, as the module of their coefficient sequences. -/
private noncomputable def powerSeriesCoeffLinearEquiv (R : Type*) [Semiring R] :
    PowerSeries R ≃ₗ[R] (ℕ → R) where
  toFun f n := PowerSeries.coeff n f
  invFun f := PowerSeries.mk f
  left_inv f := PowerSeries.ext fun n => by simp
  right_inv f := funext fun n => by simp
  map_add' f g := funext fun n => map_add (PowerSeries.coeff n) f g
  map_smul' r f := funext fun n => map_smul (PowerSeries.coeff n) r f

/-- For some commutative ring, its formal power series ring is flat over neither the
coefficient ring nor the polynomial ring. -/
@[stacks 0ALC]
theorem exists_powerSeries_not_flat :
    ∃ (R : Type u) (hR : CommRing R),
      letI : CommRing R := hR
      (¬ Module.Flat R (PowerSeries R)) ∧
        (¬ Module.Flat (Polynomial R) (PowerSeries R)) := by
  refine ⟨NotFlatRing, inferInstance, ?_⟩
  let : Countable NotFlatRing := inferInstanceAs (Countable (NotFlatCoeff × NotFlatModule))
  have hnotFlat : ¬ Module.Flat NotFlatRing (PowerSeries NotFlatRing) := fun hflat =>
    notFlatRing_not_isCoherentRing ((isCoherentRing_iff_flat_pi_nat NotFlatRing).mpr
      ((Module.Flat.equiv_iff (powerSeriesCoeffLinearEquiv NotFlatRing)).mp hflat))
  exact ⟨hnotFlat, fun _ => hnotFlat
    (Module.Flat.trans NotFlatRing (Polynomial NotFlatRing) (PowerSeries NotFlatRing))⟩

end Stacks.Examples

end
