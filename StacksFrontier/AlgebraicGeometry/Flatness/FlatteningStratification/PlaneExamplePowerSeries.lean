module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.PlaneExample

/-!
# The flattening example of the affine plane has no value over the formal plane

Let `k` be a field, `R = k[x, y]` and let `𝓕` be the quasi-coherent module on `Spec R`
associated to `k[x, x⁻¹, y]/(y) = (R/(y))[1/x]`, viewed over `Spec R` through the identity
morphism, as in
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.PlaneExample`. Over the formal
plane `A = k[[x, y]]` the base change of `𝓕` is `(A/yA)[1/x] = k[[x]][1/x]`, a nonzero module
annihilated by `y`. Since `y` is a nonzerodivisor of `A`, that module is not flat, so the
flatness functor of `𝓕` takes the empty value on `Spec k[[x, y]]`.

Together with the singleton values on the infinitesimal quotients `R/(x, y)^n` proved in
`PlaneExample`, this is the computation behind the Stacks Project's example of a quasi-coherent
module with no universal flattening.

## Main definitions

* `AlgebraicGeometry.PlaneFlatteningExample.formalPlane` is the power series ring `k[[x, y]]`,
  an algebra over `k[x, y]`.

## Main results

* `Module.not_flat_of_forall_smul_eq_zero`: a nontrivial module annihilated by a nonzerodivisor
  of the base is not flat.
* `MvPowerSeries.X_not_dvd_X_pow`: no power of one formal variable is divisible by another.
* `LocalizedModule.not_flat_quotient_span_singleton`: if `b` is a nonzerodivisor and no power of
  `a` is divisible by `b`, then `(A/bA)[1/a]` is not a flat `A`-module.
* `AlgebraicGeometry.isFlatOver_id_tilde_iff`: the sheaf associated to a module on the spectrum
  of a ring is flat over that spectrum exactly when the module is flat.
* `AlgebraicGeometry.PlaneFlatteningExample.isFlatAfterBaseChange_iff`: the base change of the
  example module to `Spec A` is flat over `Spec A` exactly when `(A/yA)[1/x]` is flat over `A`.
* `AlgebraicGeometry.PlaneFlatteningExample.flatValue_formalPlane_isEmpty`: the flatness functor
  of the example has no value over `k[[x, y]]`.

## Implementation notes

The obstruction to flatness is Mathlib's `Module.Flat.isSMulRegular_of_nonZeroDivisors`:
multiplication by a nonzerodivisor of the base is injective on a flat module, while it is zero
on `(A/bA)[1/a]`, which is nontrivial because no power of `a` lies in `(b)`. For `A = k[[x, y]]`
with `a = x` and `b = y` the two inputs are `MvPowerSeries.X_mem_nonzeroDivisors` and a
coefficient computation through `MvPowerSeries.X_pow_dvd_iff`.

Flatness over the base is transported from the fibre product `Spec R ×_{Spec R} Spec A` to
`Spec A` along the isomorphism coming from `IsPullback.of_id_snd`, since the morphism of the
situation is the identity; the module there is identified by the already available
`AlgebraicGeometry.PlaneFlatteningExample.affineBaseChangeModuleIso`, and flatness of an
associated sheaf over its own base is read off its module of sections through
`AlgebraicGeometry.isFlatOver_specMap_iff` and the unit of the tilde-Gamma adjunction.

## References

* [Stacks Project, Tag 0FJ1](https://stacks.math.columbia.edu/tag/0FJ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

/-- A nontrivial module annihilated by a nonzerodivisor of the base is not flat. -/
public theorem Module.not_flat_of_forall_smul_eq_zero {A N : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [Nontrivial N] {r : A} (hr : r ∈ nonZeroDivisors A)
    (hrN : ∀ z : N, r • z = 0) : ¬ Module.Flat A N := by
  intro h
  obtain ⟨z, hz⟩ := exists_ne (0 : N)
  exact hz (Module.Flat.isSMulRegular_of_nonZeroDivisors hr
    (show r • z = r • (0 : N) by rw [hrN z, hrN 0]))

namespace MvPowerSeries

/-- A power of one variable is not divisible by another variable. -/
public theorem X_not_dvd_X_pow {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R]
    {i j : σ} (hij : i ≠ j) (n : ℕ) :
    ¬ (X j : MvPowerSeries σ R) ∣ (X i : MvPowerSeries σ R) ^ n := by
  classical
  intro h
  rw [← pow_one (X j : MvPowerSeries σ R), X_pow_dvd_iff] at h
  have hz := h (Finsupp.single i n)
    (by rw [Finsupp.single_eq_of_ne hij.symm]; exact Nat.zero_lt_one)
  rw [coeff_X_pow, ite_eq_left rfl] at hz
  exact one_ne_zero hz

end MvPowerSeries

/-- The structure map from the polynomial ring to the power series ring sends a variable to the
corresponding formal variable. -/
public theorem MvPolynomial.algebraMap_mvPowerSeries_X {σ R : Type*} [CommSemiring R] (s : σ) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ R) (MvPolynomial.X s) =
      MvPowerSeries.X s := by
  rw [RingHom.algebraMap_toAlgebra]
  simp [MvPolynomial.coeToMvPowerSeries.algHom_apply]

/-- The class of the generator of a principal ideal vanishes in the quotient, so the quotient is
annihilated by that generator. -/
public theorem Ideal.smul_quotient_span_singleton_self {A : Type*} [CommRing A] (b : A)
    (m : A ⧸ Ideal.span {b}) : b • m = 0 := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self b), zero_mul]

/-- Localizing the quotient by a principal ideal at the powers of an element is annihilated by
the generator of that ideal. -/
public theorem LocalizedModule.smul_quotient_span_singleton_self {A : Type*} [CommRing A]
    (a b : A) (z : LocalizedModule (Submonoid.powers a) (A ⧸ Ideal.span {b})) : b • z = 0 := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    rw [LocalizedModule.smul'_mk, Ideal.smul_quotient_span_singleton_self b m,
      LocalizedModule.zero_mk]

/-- If no power of `a` is divisible by `b`, then localizing `A ⧸ (b)` at the powers of `a` gives
a nontrivial module. -/
public theorem LocalizedModule.nontrivial_quotient_span_singleton {A : Type*} [CommRing A]
    {a b : A} (hab : ∀ n : ℕ, ¬ b ∣ a ^ n) :
    Nontrivial (LocalizedModule (Submonoid.powers a) (A ⧸ Ideal.span {b})) := by
  refine ⟨⟨LocalizedModule.mk 1 1, 0, ?_⟩⟩
  intro hcon
  rw [← LocalizedModule.mkLinearMap_apply (Submonoid.powers a)] at hcon
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) (A ⧸ Ideal.span {b}))).mp hcon
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) a).mp s.2
  rw [Submonoid.smul_def, ← hn, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hs
  exact hab n hs

/-- **A nonzerodivisor annihilating a nontrivial module obstructs flatness.** If `b` is a
nonzerodivisor of `A` and no power of `a` is divisible by `b`, then the localization of
`A ⧸ (b)` at the powers of `a` is not a flat `A`-module. -/
public theorem LocalizedModule.not_flat_quotient_span_singleton {A : Type*} [CommRing A]
    {a b : A} (hb : b ∈ nonZeroDivisors A) (hab : ∀ n : ℕ, ¬ b ∣ a ^ n) :
    ¬ Module.Flat A (LocalizedModule (Submonoid.powers a) (A ⧸ Ideal.span {b})) := by
  have := LocalizedModule.nontrivial_quotient_span_singleton hab
  exact Module.not_flat_of_forall_smul_eq_zero hb
    (LocalizedModule.smul_quotient_span_singleton_self a b)

namespace AlgebraicGeometry

/-- **Flatness of an associated sheaf over its own base.** The sheaf associated to a module on
the spectrum of a ring is flat over that spectrum exactly when the module is flat. -/
public theorem isFlatOver_id_tilde_iff {A : CommRingCat.{u}} (N : ModuleCat.{u} A) :
    IsFlatOver (𝟙 (Spec A) : Spec A ⟶ Spec A).toLRSHom.toShHom (tilde N) ↔ Module.Flat A N := by
  rw [← Spec.map_id]
  refine (isFlatOver_specMap_iff (𝟙 A) (tilde N)).trans ?_
  exact Module.Flat.equiv_iff (ModuleCat.restrictScalarsId'App ((𝟙 A : A ⟶ A).hom)
    CommRingCat.hom_id (moduleSpecΓFunctor.obj ((tilde.functor A).obj N)) ≪≫
      (tilde.toTildeΓNatIso.app N).symm).toLinearEquiv

namespace PlaneFlatteningExample

/-- **The flatness functor of the example, read on an affine base.** The base change of the
example module to `Spec A` is flat over `Spec A` exactly when `(A/yA)[1/x]` is a flat
`A`-module. -/
public theorem isFlatAfterBaseChange_iff (E : PlaneFlatteningExample.{u}) (A : Type u)
    [CommRing A] [Algebra E.R A] :
    E.flatnessSituation.IsFlatAfterBaseChange
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E.R A)))) ↔
      Module.Flat A (LocalizedModule (Submonoid.powers (algebraMap E.R A E.x))
        (A ⧸ Ideal.span {algebraMap E.R A E.y})) := by
  let t : Spec (CommRingCat.of A) ⟶ E.X :=
    Spec.map (CommRingCat.ofHom (algebraMap E.R A))
  have hpb : IsPullback t (𝟙 (Spec (CommRingCat.of A))) (𝟙 E.X) t := IsPullback.of_id_snd
  have h1 := isFlatOver_pullback_iff_of_iso (pullback.snd (𝟙 E.X) t)
    (pullback.fst (𝟙 E.X) t) hpb.isoPullback E.F
  rw [hpb.isoPullback_hom_snd, hpb.isoPullback_hom_fst] at h1
  exact h1.trans <| (isFlatOver_iff_of_moduleIso _ (affineBaseChangeModuleIso E A)).trans
    (isFlatOver_id_tilde_iff _)

/-- The formal plane `k[[x, y]]`, an algebra over `k[x, y]` through the inclusion of
polynomials into power series. -/
public abbrev formalPlane (E : PlaneFlatteningExample.{u}) : Type u :=
  MvPowerSeries (Fin 2) E.k

/-- Over the formal plane the base change of the example module is `k[[x]][1/x]`, which is a
nontrivial module annihilated by the nonzerodivisor `y`, hence not flat. -/
public theorem not_flat_formalPlane_baseChange (E : PlaneFlatteningExample.{u}) :
    ¬ Module.Flat E.formalPlane
      (LocalizedModule (Submonoid.powers (algebraMap E.R E.formalPlane E.x))
        (E.formalPlane ⧸ Ideal.span {algebraMap E.R E.formalPlane E.y})) := by
  rw [show algebraMap E.R E.formalPlane E.x = MvPowerSeries.X 0 from
      MvPolynomial.algebraMap_mvPowerSeries_X 0,
    show algebraMap E.R E.formalPlane E.y = MvPowerSeries.X 1 from
      MvPolynomial.algebraMap_mvPowerSeries_X 1]
  exact LocalizedModule.not_flat_quotient_span_singleton MvPowerSeries.X_mem_nonzeroDivisors
    (MvPowerSeries.X_not_dvd_X_pow (by decide))

/-- The flatness functor of the flattening example on the affine plane has no value over the
formal plane `k[[x, y]]` (the second claim of **Stacks 0FJ1**, stated in full by
`AlgebraicGeometry.PlaneFlatteningExample.flatFunctor_unique_isEmpty_not_representable`). -/
public theorem flatValue_formalPlane_isEmpty (E : PlaneFlatteningExample.{u}) :
    IsEmpty (E.flatValue E.formalPlane) := by
  refine not_nonempty_iff.mp ?_
  rw [FlatnessSituation.flatFunctor_obj_nonempty_iff, isFlatAfterBaseChange_iff]
  exact E.not_flat_formalPlane_baseChange

end PlaneFlatteningExample

end AlgebraicGeometry
