module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Flatness of a module and of its associated sheaf

For a module over a commutative ring, flatness is equivalent to flatness of the associated
quasi-coherent sheaf on the prime spectrum.

## Main results

* `AlgebraicGeometry.isFlat_tilde_iff_flat`: the sheaf associated to a module on an affine
  scheme is flat if and only if the module is flat.

## Implementation notes

The associated sheaf is Mathlib's `AlgebraicGeometry.tilde`. Flatness of a sheaf of modules is
`AlgebraicGeometry.SheafOfModules.IsFlat`, which on a ringed space is detected on stalks by
`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`; flatness of a module is
`Module.Flat`.

The stalk of the structure sheaf of `Spec R` at a prime `p` is a localization of `R` at `p`,
and the stalk of `M̃` is the corresponding localized module. The bridge between the two
flatness notions is therefore the local-to-global criterion `flat_iff_forall_flat_atPrime`, which
  compares
flatness of `M` with flatness of all of its localizations at primes, together with the
invariance of flatness under a localization of the base ring.

## References

* [Stacks Project, Tag 05P0](https://stacks.math.columbia.edu/tag/05P0)
-/

public section

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The stalk of `M̃` at a point of `Spec R`, as a module over the stalk of the structure
sheaf, is flat exactly when the localization of `M` at the corresponding prime is flat over
the localization of `R`. -/
private lemma flat_tildeStalk_iff_flat_localized {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (x : Spec.topObj R) :
    letI : x.asIdeal.IsPrime := (x : PrimeSpectrum (↑R)).isPrime
    letI : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := Spec.topObj R)
      (Spec.structureSheaf (↑R)).obj x) ((tilde M).presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (id (tilde M).val : PresheafOfModules.{u}
          ((Spec.structureSheaf (↑R)).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) x
    Module.Flat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := Spec.topObj R)
      (Spec.structureSheaf (↑R)).obj x) ((tilde M).presheaf.stalk x) ↔
      Module.Flat (Localization.AtPrime x.asIdeal)
        (LocalizedModule.AtPrime x.asIdeal (↑M)) := by
  let p : PrimeSpectrum (↑R) := x
  let : x.asIdeal.IsPrime := p.isPrime
  let A := TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := Spec.topObj R)
    (Spec.structureSheaf (↑R)).obj x
  let N := (tilde M).presheaf.stalk x
  let : Algebra (↑R) (↑A) := StructureSheaf.stalkAlgebra (↑R) x
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (id (tilde M).val : PresheafOfModules.{u}
        ((Spec.structureSheaf (↑R)).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) x
  let : Module (↑R) (↑N) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M x
  let f := AlgebraicGeometry.tilde.toStalk M x
  let : IsLocalizedModule x.asIdeal.primeCompl f.hom :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      M x
  let : IsScalarTower (↑R) (↑A) (↑N) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalization.AtPrime A x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (↑R) x
  show Module.Flat A N ↔ Module.Flat (Localization.AtPrime x.asIdeal)
    (LocalizedModule.AtPrime x.asIdeal (↑M))
  calc
    Module.Flat A N ↔ Module.Flat (↑R) N :=
      Module.flat_iff_of_isLocalization A x.asIdeal.primeCompl N
    _ ↔ Module.Flat (↑R) (LocalizedModule x.asIdeal.primeCompl (↑M)) :=
      (Module.Flat.equiv_iff (IsLocalizedModule.iso x.asIdeal.primeCompl f.hom)).symm
    _ ↔ Module.Flat (Localization.AtPrime x.asIdeal)
        (LocalizedModule.AtPrime x.asIdeal (↑M)) :=
      (Module.flat_iff_of_isLocalization (Localization.AtPrime x.asIdeal)
        x.asIdeal.primeCompl (LocalizedModule.AtPrime x.asIdeal (↑M))).symm

/-- **Stacks Project, Tag 05P0.** The sheaf associated to a module on an affine
scheme is flat if and only if the module is flat. -/
@[stacks 05P0, ega "III 1.4.15.5" "case A = B, φ = id", ega "IV 2.1.2" "A = B, φ = id"]
theorem isFlat_tilde_iff_flat {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    AlgebraicGeometry.SheafOfModules.IsFlat (tilde M) ↔ Module.Flat R M := by
  have hiff := AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat
    (X := Spec.topObj R) (Spec.structureSheaf (↑R)) (tilde M)
  exact ⟨fun h ↦ (flat_iff_forall_flat_atPrime (M := (↑M))).2 fun P hP ↦
      (flat_tildeStalk_iff_flat_localized M ⟨P, hP⟩).mp (hiff.mp h ⟨P, hP⟩),
    fun h ↦ hiff.mpr fun x ↦ (flat_tildeStalk_iff_flat_localized M x).mpr
      ((flat_iff_forall_flat_atPrime (M := (↑M))).1 h x.asIdeal
        (x : PrimeSpectrum (↑R)).isPrime)⟩

end AlgebraicGeometry
