module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction maps between standard opens of a prime spectrum

An inclusion `D(g) ≤ D(f)` of standard opens in the prime spectrum of a commutative ring `R`
induces canonical restriction maps on the associated localizations: the `R`-algebra map
`R_f → R_g` on functions, and, for an `R`-module `M`, the compatible map `M_f → M_g` on
sections.

Both maps are characterized by their compatibility with the localization maps out of `R` and
out of `M`, and each is the unique map with that compatibility.

## Main definitions

* `PrimeSpectrum.ringRestrictionMap`: the canonical `R`-algebra map `R_f → R_g` attached to
  `D(g) ≤ D(f)`.
* `PrimeSpectrum.moduleRestrictionMap`: the canonical `R_f`-linear map `M_f → M_g` attached to
  the same inclusion.

## Main results

* `PrimeSpectrum.ringRestrictionMap_unique`: the ring restriction map is the unique `R`-algebra
  homomorphism between the two localizations.
* `PrimeSpectrum.moduleRestrictionMap_mk`: the module restriction map agrees with the
  localization maps on elements of `M`.
* `PrimeSpectrum.moduleRestrictionMap_unique`: that property determines it.

## Implementation notes

The rings `R_f` and modules `M_f` are represented by `Localization.Away f` and
`LocalizedModule.Away f M`. The ring map is an `R`-algebra homomorphism, so its compatibility
with the structure maps from `R` is part of the homomorphism structure; the module map is linear
over `Localization.Away f`, the target being regarded as an `R_f`-module by restriction of
scalars along `PrimeSpectrum.ringRestrictionMap`.

## References

* [Stacks Project, Tag 01HS](https://stacks.math.columbia.edu/tag/01HS)
-/

@[expose] public section

namespace PrimeSpectrum

universe u v

/-- The canonical `R`-algebra map `R_f → R_g` attached to an inclusion `D(g) ⊆ D(f)`. -/
@[stacks 01HS "ring_restriction_map"]
noncomputable def ringRestrictionMap {R : Type u} [CommRing R] (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    Localization.Away f →ₐ[R] Localization.Away g :=
  IsLocalization.Away.liftAlgHom (S := Localization.Away f) (P := Localization.Away g)
    (A := R) (f := Algebra.ofId R (Localization.Away g)) f
    ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := Localization.Away g)).mp hfg)

/-- The restriction map is canonical: it is the unique `R`-algebra
homomorphism from `R_f` to `R_g`. -/
@[stacks 01HS "ring_restriction_map"]
theorem ringRestrictionMap_unique {R : Type u} [CommRing R] (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (φ : Localization.Away f →ₐ[R] Localization.Away g) :
    φ = ringRestrictionMap f g hfg := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext

/-- The canonical `R_f`-linear restriction map `M_f → M_g` associated to an inclusion
`D(g) ⊆ D(f)`. -/
@[stacks 01HS "module_restriction_map"]
noncomputable def moduleRestrictionMap {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    let φ := ringRestrictionMap f g hfg
    letI := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
      (LocalizedModule.Away (R := R) g M) φ.toRingHom
    LocalizedModule.Away (R := R) f M →ₗ[Localization.Away f]
      LocalizedModule.Away (R := R) g M := by
  let φ := ringRestrictionMap f g hfg
  letI := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
    (LocalizedModule.Away (R := R) g M) φ.toRingHom
  letI : IsScalarTower R (Localization.Away f)
      (LocalizedModule.Away (R := R) g M) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change φ (algebraMap R (Localization.Away f) r) • m = r • m
      rw [φ.commutes]
      exact IsScalarTower.algebraMap_smul (Localization.Away g) r m
  let hunit : ∀ x : Submonoid.powers f,
      IsUnit (algebraMap R
        (Module.End R (LocalizedModule.Away (R := R) g M)) x) := by
    intro x
    rw [Module.End.isUnit_iff]
    change Function.Bijective
      (fun m : LocalizedModule.Away (R := R) g M => (x : R) • m)
    rw [show (fun m : LocalizedModule.Away (R := R) g M => (x : R) • m) =
        fun m => algebraMap R (Localization.Away g) x • m by
      funext m
      exact (IsScalarTower.algebraMap_smul
        (Localization.Away g) (x : R) m).symm]
    obtain ⟨n, hn⟩ := x.property
    rw [← hn, map_pow]
    exact ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := Localization.Away g)).mp hfg).pow n
      |>.smul_bijective
  exact LinearMap.extendScalarsOfIsLocalization
    (Submonoid.powers f) (Localization.Away f)
    (LocalizedModule.lift (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) hunit)

/-- The module restriction map agrees with the canonical localization maps on
elements of `M`. -/
@[simp, stacks 01HS "module_restriction_map"]
theorem moduleRestrictionMap_mk {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (m : M) :
    moduleRestrictionMap f g hfg
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m := by
  simp only [moduleRestrictionMap, LinearMap.extendScalarsOfIsLocalization_apply',
    LocalizedModule.mkLinearMap_apply, LocalizedModule.lift_mk_one]

/-- An `R_f`-linear map `M_f → M_g` which agrees with the localization maps
from `M` is the canonical module restriction map. -/
@[stacks 01HS "module_restriction_map"]
theorem moduleRestrictionMap_unique {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (F :
      let φ := ringRestrictionMap f g hfg
      letI := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
        (LocalizedModule.Away (R := R) g M) φ.toRingHom
      LocalizedModule.Away (R := R) f M →ₗ[Localization.Away f]
        LocalizedModule.Away (R := R) g M)
    (hF : ∀ m : M,
      F (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers g) M m) :
    F = moduleRestrictionMap f g hfg := by
  let := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
    (LocalizedModule.Away (R := R) g M)
    (ringRestrictionMap f g hfg).toRingHom
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    have hx : LocalizedModule.mk m s =
        (Localization.mk 1 s : Localization.Away f) •
          LocalizedModule.mkLinearMap (Submonoid.powers f) M m := by
      rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [hx, map_smul, map_smul, hF, moduleRestrictionMap_mk]

end PrimeSpectrum

end
