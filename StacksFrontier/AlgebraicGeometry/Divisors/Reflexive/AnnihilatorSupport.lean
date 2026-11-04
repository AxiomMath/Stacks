module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The scheme-theoretic support of a finite-type quasi-coherent module

The annihilators of the modules of sections over the affine opens of a scheme form a
quasi-coherent sheaf of ideals, because annihilators of finite modules commute with
localization.  The closed subscheme it cuts out is the scheme-theoretic support of the module,
and its underlying closed set is the support.

## Main definitions

* `AlgebraicGeometry.annihilatorIdeal'`: the ideal sheaf whose sections over an affine open are
  the annihilator of the sections of the module there.

## Main results

* `AlgebraicGeometry.annihilatorIdeal_ideal`: the ideal of `annihilatorIdeal' F` over an affine
  open is the module annihilator.
* `AlgebraicGeometry.supp_eq_annihilatorIdeal_support`: the support of the module is the
  support of its annihilator ideal sheaf.

## References

* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The ideal sheaf cutting out the scheme-theoretic support of a module: over an affine open
it is the annihilator of the module of sections there.

Saturated with `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`, so that it is defined for an
arbitrary module on an arbitrary scheme; its ideals are the annihilators as soon as the module
is quasi-coherent of finite type (`AlgebraicGeometry.annihilatorIdeal_ideal`). Those are the
weaker hypotheses: `AlgebraicGeometry.annihilatorIdeal` builds the same ideal sheaf directly,
and so asks for a coherent module on a locally Noetherian scheme. -/
@[sga "4 XVII 6.3.4"]
noncomputable def annihilatorIdeal' (F : X.Modules) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U => Module.annihilator Γ(X, U.1) Γ(F, U.1)

/-- Annihilators of finite modules commute with localization: the extension of the annihilator
of `M` along a localization `R → A` is the annihilator of the localized module. -/
private theorem annihilator_map_of_isLocalizedModule (R A M N : Type*) [CommRing R]
    [CommRing A] {S : Submonoid R} [Algebra R A] [IsLocalization S A] [Module.Flat R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module A N]
    [Module R N] [IsScalarTower R A N] {f : M →ₗ[R] N} [IsLocalizedModule S f] :
    Ideal.map (algebraMap R A) (Module.annihilator R M) = Module.annihilator A N := by
  rw [ann_extension_eq_ann_baseChange_module]
  exact (IsLocalizedModule.isBaseChange S A f).equiv.annihilator_eq

/-- The annihilators of the sections over the affine opens of a scheme are compatible with
passage to a basic open, so they assemble into an ideal sheaf. -/
private noncomputable def annihilatorIdealData (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U.1) Γ(F, U.1)
  map_ideal_basicOpen U f := by
    let R := Γ(X, U.1)
    let A := Γ(X, X.basicOpen f)
    let M := Γ(F, U.1)
    let N := Γ(F, X.basicOpen f)
    let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    let : Module.Finite R M := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F U.2
    let : IsLocalization (Submonoid.powers f) A :=
      AlgebraicGeometry.isLocalization_basicOpen_of_qcqs U.2.isCompact U.2.isQuasiSeparated f
    let : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
    let : Algebra R A := ρ.toAlgebra
    let : Module R N := Module.compHom (R := A) (S := R) N ρ
    let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hloc := AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F
      U.2.isCompact U.2.isQuasiSeparated f
    let : IsLocalizedModule (Submonoid.powers f)
        (AlgebraicGeometry.Scheme.Modules.restrictionLinearMap F
          (homOfLE (X.basicOpen_le f))) := hloc
    have halg : algebraMap R A = ρ := rfl
    change Ideal.map ρ (Module.annihilator R M) = Module.annihilator A N
    rw [← halg]
    exact annihilator_map_of_isLocalizedModule (S := Submonoid.powers f) R A M N
      (f := AlgebraicGeometry.Scheme.Modules.restrictionLinearMap F
        (homOfLE (X.basicOpen_le f)))

/-- **The ideal of the scheme-theoretic support over an affine open is the annihilator of the
sections.** -/
theorem annihilatorIdeal_ideal (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : X.affineOpens) :
    (annihilatorIdeal' F).ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  have h : annihilatorIdeal' F = annihilatorIdealData F := by
    simpa [annihilatorIdeal', annihilatorIdealData] using
      (Scheme.IdealSheafData.ofIdeals_ideal (annihilatorIdealData F))
  rw [h]
  rfl

/-- On an affine open, a point lies in the zero locus of the annihilator exactly when the
corresponding prime lies in the support of the module of sections. -/
private lemma zeroLocus_annihilator_iff_moduleSupport (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (U : X.affineOpens) {x : X} (hxU : x ∈ U.1) :
    x ∈ X.zeroLocus (U := U.1) (Module.annihilator Γ(X, U.1) Γ(F, U.1)) ↔
      U.2.primeIdealOf ⟨x, hxU⟩ ∈ Module.support Γ(X, U.1) Γ(F, U.1) := by
  classical
  let : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F U.2
  set p := U.2.primeIdealOf ⟨x, hxU⟩ with hp
  have hpoint : U.2.fromSpec p = x := U.2.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hbasic (s : Γ(X, U.1)) : x ∈ X.basicOpen s ↔ p ∈ PrimeSpectrum.basicOpen s := by
    rw [← hpoint, ← U.2.fromSpec_preimage_basicOpen s]
    rfl
  rw [Scheme.mem_zeroLocus_iff, Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  simp only [SetLike.mem_coe, Set.subset_def]
  constructor
  · intro h s hs
    by_contra hsp
    exact h s hs ((hbasic s).2 ((PrimeSpectrum.mem_basicOpen s p).2 hsp))
  · intro h s hs hx
    exact (PrimeSpectrum.mem_basicOpen s p).1 ((hbasic s).1 hx) (h s hs)

/-- **The support of a finite-type quasi-coherent module is the support of its annihilator
ideal sheaf**, so the closed subscheme cut out by the annihilator is the scheme-theoretic
support of the module. -/
theorem supp_eq_annihilatorIdeal_support (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    SheafOfModules.supp F = (annihilatorIdeal' F).support := by
  classical
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hSupp : (SheafOfModules.moduleSheafOfModules F).supp = SheafOfModules.supp F :=
    SheafOfModules.supp_eq_moduleSheaf_supp F
  have hsec : U'.2.primeIdealOf ⟨x, hxU⟩ ∈ Module.support Γ(X, U'.1) Γ(F, U'.1) ↔
      x ∈ SheafOfModules.supp F :=
    (Scheme.Modules.mem_support_sections_iff_mem_supp F U' x hxU).trans (hSupp ▸ Iff.rfl)
  show (x ∈ SheafOfModules.supp F) ↔ x ∈ (annihilatorIdeal' F).support
  rw [(annihilatorIdeal' F).mem_support_iff_of_mem (U := U') hxU, annihilatorIdeal_ideal F U']
  exact hsec.symm.trans (zeroLocus_annihilator_iff_moduleSupport F U' hxU).symm

end AlgebraicGeometry

end
