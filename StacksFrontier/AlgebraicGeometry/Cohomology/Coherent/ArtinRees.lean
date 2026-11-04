module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Filtration
public import StacksCore.RingTheory.Localization.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# Artin-Rees for coherent sheaves on a Noetherian scheme

If `G` is a quasi-coherent subsheaf of a coherent sheaf `F` on a Noetherian scheme and `I` is a
quasi-coherent ideal sheaf, then one Artin-Rees constant `c` works uniformly over the whole
scheme: for every `n ≥ c` and every affine open `U`, the sections over `U` satisfy
`I ^ (n - c) • (I ^ c • F ⊓ G) = I ^ n • F ⊓ G`.

## Main results

* `AlgebraicGeometry.exists_local_shift` is Artin-Rees on a single affine open, which needs only
  local Noetherianness.
* `AlgebraicGeometry.exists_ideal_pow_smul_inf_eq` is the sheaf-theoretic Artin-Rees equality,
  tested on every affine open with a single exponent.
* `AlgebraicGeometry.moduleFinite_sections`: the sections of a coherent sheaf over an affine open
  of a locally Noetherian scheme are a finite module.

## Implementation notes

On an affine open the products and intersections of quasi-coherent subsheaves appearing in the
formula are computed on modules of sections, and equality on all affine opens is equality of the
corresponding subsheaves. The affine ingredient is the module-level Artin-Rees lemma
`Ideal.exists_pow_inf_eq_pow_smul`, applicable because the sections of a coherent sheaf over an
affine open of a locally Noetherian scheme form a finite module over a Noetherian ring. A finite
affine cover turns the chartwise constants into a single one, after enlarging each of them, which
is what `artinRees_enlarge_exponent` permits.

Passing from the finite cover to *every* affine open is `of_affine_open_cover`, whose two
hypotheses are that the submodule families in question are compatible with passing to a basic
open and local on a spanning family of basic opens. Both reduce to the fact that the sections of
a quasi-coherent module over a basic open of an affine open are a localization of its sections
over that affine open, which is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`.

## References

* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry

/-! ### Sections of a quasi-coherent module over an affine open -/

/-- For a quasi-coherent submodule `H` of a quasi-coherent module `M`, an affine open `U` and
`f : Γ(X, U)`, the localization at the powers of `f` of the sections of `H` over `U`, taken inside
the sections of `M` over `X.basicOpen f`, is the submodule of sections of `H` over
`X.basicOpen f`. -/
theorem submodule_sections_localized {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (H : M.Submodule)
    [H.toSheafOfModules.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    letI := moduleOfLE M (X.basicOpen_le f)
    letI := isScalarTowerOfLE M (X.basicOpen_le f)
    letI : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
    letI : IsLocalizedModule (Submonoid.powers f) (restrictₗ M (X.basicOpen_le f)) :=
      isLocalizedModule_restrictₗ M hU f rfl (X.basicOpen_le f)
    (H.toSubmodule.obj (.op U)).localized' (Γ(X, X.basicOpen f))
        (Submonoid.powers f) (restrictₗ M (X.basicOpen_le f)) =
      H.toSubmodule.obj (.op (X.basicOpen f)) := by
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  let := moduleOfLE M (X.basicOpen_le f)
  let := isScalarTowerOfLE M (X.basicOpen_le f)
  let := moduleOfLE H.toSheafOfModules (X.basicOpen_le f)
  let := isScalarTowerOfLE H.toSheafOfModules (X.basicOpen_le f)
  let : Module Γ(X, U) Γ(M, U) := (M.val.obj (.op U)).isModule
  let : Module Γ(X, U) Γ(H.toSheafOfModules, U) :=
    (H.toSheafOfModules.val.obj (.op U)).isModule
  have hM : IsLocalizedModule (Submonoid.powers f) (restrictₗ M (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ M hU f rfl (X.basicOpen_le f)
  have hH : IsLocalizedModule (Submonoid.powers f)
      (restrictₗ H.toSheafOfModules (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ H.toSheafOfModules hU f rfl (X.basicOpen_le f)
  apply le_antisymm
  · refine (Submodule.localized'_eq_span (Γ(X, X.basicOpen f)) (Submonoid.powers f)
      (restrictₗ M (X.basicOpen_le f)) (H.toSubmodule.obj (.op U))).trans_le
      (Submodule.span_le.mpr ?_)
    rintro y ⟨x, hx, rfl⟩
    show (M.val.map (homOfLE (X.basicOpen_le f)).op).hom x ∈ _
    exact H.toSubmodule.map_mem (homOfLE (X.basicOpen_le f)).op hx
  · intro y hy
    change y ∈ H.toSubmodule.obj (.op (X.basicOpen f)) at hy
    obtain ⟨⟨x, s⟩, hs⟩ := hH.surj (⟨y, hy⟩ : Γ(H.toSheafOfModules, X.basicOpen f))
    exact ⟨x.1, x.2, s, IsLocalizedModule.mk'_eq_iff.mpr
      (congrArg (fun z => (H.toSubmodule.ι.app (.op (X.basicOpen f))).hom z) hs.symm)⟩

private noncomputable abbrev sectionsIdeal {X : Scheme.{u}}
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule) (V : X.Opens) : Ideal Γ(X, V) :=
  I.toSubmodule.obj (op V)

private noncomputable abbrev idealPowSmulInf {X : Scheme.{u}} (F : X.Modules) (G : F.Submodule)
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule) (a b : ℕ)
    (U : X.affineOpens) : Submodule Γ(X, U.1) Γ(F, U.1) :=
  sectionsIdeal I U.1 ^ a •
    ((sectionsIdeal I U.1 ^ b • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
      G.toSubmodule.obj (op U.1))

private theorem idealPowSmulInf_basicOpen {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (G : F.Submodule)
    [G.toSheafOfModules.IsQuasicoherent]
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] (a b : ℕ)
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    Submodule.span Γ(X, X.basicOpen f)
      (F.presheaf.map (homOfLE (X.basicOpen_le f)).op ''
        (idealPowSmulInf F G I a b U : Set Γ(F, U.1))) =
      idealPowSmulInf F G I a b (X.affineBasicOpen f) := by
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  let := moduleOfLE F (X.basicOpen_le f)
  let := isScalarTowerOfLE F (X.basicOpen_le f)
  let : Module Γ(X, U.1) Γ(F, U.1) := (F.val.obj (.op U.1)).isModule
  have hF : IsLocalizedModule (Submonoid.powers f) (restrictₗ F (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ F U.2 f rfl (X.basicOpen_le f)
  have hG := submodule_sections_localized F G U.2 f
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (CategoryTheory.Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} =>
        SheafOfModules.unit X.ringCatSheaf))
      (inferInstanceAs
        (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent)
  have hI := submodule_sections_localized (SheafOfModules.unit X.ringCatSheaf) I U.2 f
  have hI' : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (sectionsIdeal I U.1) =
      sectionsIdeal I (X.basicOpen f) :=
    (Ideal.localized'_eq_map _ (Submonoid.powers f) _).symm.trans hI
  have e1 : (sectionsIdeal I U.1 ^ a •
        ((sectionsIdeal I U.1 ^ b • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          G.toSubmodule.obj (op U.1))).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
        (restrictₗ F (X.basicOpen_le f)) =
      (sectionsIdeal I U.1 ^ a).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
          (Algebra.linearMap _ _) •
        ((sectionsIdeal I U.1 ^ b • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          G.toSubmodule.obj (op U.1)).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
          (restrictₗ F (X.basicOpen_le f)) :=
    Submodule.localized'_smul _ _ _ _ _
  have hmap (k : ℕ) :
      Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (sectionsIdeal I U.1 ^ k) =
        sectionsIdeal I (X.basicOpen f) ^ k :=
    (Ideal.map_pow _ _ k).trans congr($hI' ^ k)
  have e2 : ((sectionsIdeal I U.1 ^ b • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
        G.toSubmodule.obj (op U.1)).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
        (restrictₗ F (X.basicOpen_le f)) =
      sectionsIdeal I (X.basicOpen f) ^ b •
          (⊤ : Submodule Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)) ⊓
        G.toSubmodule.obj (op (X.basicOpen f)) :=
    (Submodule.localized'_inf _ _ _ _ _).trans
      congr($((Submodule.localized'_smul_top (Submonoid.powers f) (sectionsIdeal I U.1 ^ b)
          Γ(X, X.basicOpen f) (restrictₗ F (X.basicOpen_le f))).trans
        congr($(hmap b) • (⊤ : Submodule Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)))) ⊓ $hG)
  have e3 : (sectionsIdeal I U.1 ^ a).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
        (Algebra.linearMap _ _) = sectionsIdeal I (X.basicOpen f) ^ a :=
    (Ideal.localized'_eq_map _ _ _).trans (hmap a)
  exact (Submodule.localized'_eq_span Γ(X, X.basicOpen f) (Submonoid.powers f)
    (restrictₗ F (X.basicOpen_le f)) (idealPowSmulInf F G I a b U)).symm.trans
      (e1.trans congr($e3 • $e2))

/-- On the spectrum of a ring, a quasi-coherent module of finite type has finite global
sections.

`private` on purpose, and it must stay so: `AlgebraicGeometry.moduleFinite_of_isFiniteType_qc`
is already declared publicly, with the same statement, at
`StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints/Finiteness.lean:84`, and both modules
are in the umbrella — so a public declaration here makes the library import fail outright. The
duplication itself is a dedup defect worth closing later: this file should consume the
`Divisors.AssociatedPoints` one rather than carry its own copy. The only use here is
`moduleFinite_sections` below. -/
private lemma moduleFinite_of_isFiniteType_qc (R : CommRingCat.{u})
    (F : (Spec R).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite (↑R) (moduleSpecΓFunctor.obj F) :=
  (tilde_isFiniteType_iff _).mp
    (Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso F.fromTildeΓ).symm)

/-- The sections of a coherent sheaf over an affine open of a locally Noetherian scheme form a
finite module over the ring of sections of the structure sheaf. -/
lemma moduleFinite_sections {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(F, U.1) := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  have := (isQuasicoherent_isFiniteType_of_isCoherent F).2
  have : (F.restrict U.2.fromSpec).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.2.fromSpec F
  have : (F.restrict U.2.fromSpec).IsFiniteType := isFiniteType_restrict U.2.fromSpec F
  have : Module.Finite Γ(X, U.1) Γ(F.restrict U.2.fromSpec, ⊤) :=
    moduleFinite_of_isFiniteType_qc (CommRingCat.of Γ(X, U.1)) (F.restrict U.2.fromSpec)
  exact Module.Finite.equiv (affineSectionsLinearEquiv F U.2)

/-! ### A uniform Artin-Rees constant -/

/-- **Artin-Rees on one affine open**, from the module-level statement over the Noetherian ring
of sections. Only local Noetherianness is used: the ring of sections over the affine open is
Noetherian and the module of sections of a coherent sheaf over it is finite.

The uniform constant of `AlgebraicGeometry.exists_ideal_pow_smul_inf_eq` is the supremum of these
over a finite affine cover, so on a scheme which is not quasi-compact this one-chart statement is
all that survives. -/
theorem exists_local_shift {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (G : F.Submodule)
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule) (U : X.affineOpens) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      (show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ n •
            (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          G.toSubmodule.obj (op U.1) =
        (show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ (n - c) •
          (((show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ c •
              (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
            G.toSubmodule.obj (op U.1)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections F U
  exact Ideal.exists_pow_inf_eq_pow_smul (M := Γ(F, U.1)) (sectionsIdeal I U.1)
    (G.toSubmodule.obj (op U.1))

/-- An Artin-Rees constant may be enlarged. -/
private theorem artinRees_enlarge_exponent {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M)
    {c C : ℕ} (hc : c ≤ C)
    (h : ∀ n : ℕ, c ≤ n → I ^ n • (⊤ : Submodule R M) ⊓ N =
      I ^ (n - c) • (I ^ c • (⊤ : Submodule R M) ⊓ N)) :
    ∀ n : ℕ, C ≤ n → I ^ n • (⊤ : Submodule R M) ⊓ N =
      I ^ (n - C) • (I ^ C • (⊤ : Submodule R M) ⊓ N) := by
  intro n hn
  rw [h n (hc.trans hn), h C hc, ← mul_smul, ← pow_add, Nat.sub_add_sub_cancel hn hc]

/-- One Artin-Rees constant for a finite family of affine opens, as the supremum of the
constants of its members. -/
private theorem exists_uniform_shift_on_finite_affine_family
    {X : Scheme.{u}} [IsNoetherian X] {ι : Type*} [Finite ι]
    (F : X.Modules) [F.IsCoherent] (G : F.Submodule)
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule) (U : ι → X.affineOpens) :
    ∃ C : ℕ, ∀ n : ℕ, C ≤ n → ∀ i,
      sectionsIdeal I (U i).1 ^ n • (⊤ : Submodule Γ(X, (U i).1) Γ(F, (U i).1)) ⊓
          G.toSubmodule.obj (op (U i).1) =
        sectionsIdeal I (U i).1 ^ (n - C) •
          ((sectionsIdeal I (U i).1 ^ C • (⊤ : Submodule Γ(X, (U i).1) Γ(F, (U i).1))) ⊓
            G.toSubmodule.obj (op (U i).1)) := by
  let := Fintype.ofFinite ι
  choose ci hci using fun i => exists_local_shift F G I (U i)
  exact ⟨Finset.univ.sup ci, fun n hn i => artinRees_enlarge_exponent (M := Γ(F, (U i).1))
    (sectionsIdeal I (U i).1) (G.toSubmodule.obj (op (U i).1))
    (Finset.le_sup (Finset.mem_univ i)) (hci i) n hn⟩

/-! ### Comparing the two sides on every affine open -/

/-- A family of submodules of the sections of `F`, compatible with passing to a basic open and
local on spanning families of basic opens, is determined by its values on an affine cover. -/
private theorem submoduleFamily_eq_of_affine_cover {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent]
    (A B : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1))
    (hA : ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Submodule.span Γ(X, X.basicOpen f)
        (F.presheaf.map (homOfLE (X.basicOpen_le f)).op '' (A U : Set Γ(F, U.1))) =
          A (X.affineBasicOpen f))
    (hB : ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Submodule.span Γ(X, X.basicOpen f)
        (F.presheaf.map (homOfLE (X.basicOpen_le f)).op '' (B U : Set Γ(F, U.1))) =
          B (X.affineBasicOpen f))
    {ι : Type*} (V : ι → X.affineOpens) (hV : ⨆ i, (V i).1 = ⊤)
    (h : ∀ i, A (V i) = B (V i)) (U : X.affineOpens) : A U = B U := by
  refine of_affine_open_cover (P := fun U => A U = B U) V hV U ?_ ?_ h
  · intro W f hW
    rw [← hA W f, ← hB W f, hW]
  · intro W s hs hlocal
    let (r : (s : Set Γ(X, W.1))) :
        Module Γ(X, X.basicOpen r.1) Γ(F, X.basicOpen r.1) :=
      (F.val.obj (.op (X.basicOpen r.1))).isModule
    let (r : (s : Set Γ(X, W.1))) := moduleOfLE F (X.basicOpen_le r.1)
    let (r : (s : Set Γ(X, W.1))) := isScalarTowerOfLE F (X.basicOpen_le r.1)
    let (r : (s : Set Γ(X, W.1))) : IsLocalization.Away r.1 Γ(X, X.basicOpen r.1) :=
      W.2.isLocalization_basicOpen r.1
    have (r : (s : Set Γ(X, W.1))) :
        IsLocalizedModule (Submonoid.powers r.1) (restrictₗ F (X.basicOpen_le r.1)) :=
      isLocalizedModule_restrictₗ F W.2 r.1 rfl (X.basicOpen_le r.1)
    refine Submodule.eq_of_isLocalized'_span (s : Set Γ(X, W.1)) hs
      (fun r => Γ(X, X.basicOpen r.1)) (fun r => Γ(F, X.basicOpen r.1))
      (fun r => restrictₗ F (X.basicOpen_le r.1)) fun r => ?_
    rw [Submodule.localized'_eq_span, Submodule.localized'_eq_span]
    exact (hA W r.1).trans ((hlocal r).trans (hB W r.1).symm)

/-- **Stacks Project, Tag 01YA.** Artin-Rees for a coherent sheaf and a quasi-coherent subsheaf
on a Noetherian scheme: the equality holds on every affine open with a single constant. -/
@[stacks 01YA, ega "0 7.3.2.1"]
theorem exists_ideal_pow_smul_inf_eq {X : Scheme.{u}} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (G : F.Submodule) [G.toSheafOfModules.IsQuasicoherent]
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    [I.toSheafOfModules.IsQuasicoherent] :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ U : X.affineOpens,
      (show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ (n - c) •
          (((show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ c •
            (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
            G.toSubmodule.obj (op U.1)) =
        ((show Ideal Γ(X, U.1) from I.toSubmodule.obj (op U.1)) ^ n •
          (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          G.toSubmodule.obj (op U.1) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let V : 𝒰.I₀ → X.affineOpens := fun i =>
    ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
  have hV : ⨆ i, (V i).1 = ⊤ := 𝒰.iSup_opensRange
  obtain ⟨c, hc⟩ := exists_uniform_shift_on_finite_affine_family F G I V
  have := (isQuasicoherent_isFiniteType_of_isCoherent F).1
  refine ⟨c, fun n hn U => ?_⟩
  have h0 (W : X.affineOpens) (k : ℕ) : idealPowSmulInf F G I 0 k W =
      sectionsIdeal I W.1 ^ k • (⊤ : Submodule Γ(X, W.1) Γ(F, W.1)) ⊓
        G.toSubmodule.obj (op W.1) := by
    show sectionsIdeal I W.1 ^ 0 • _ = _
    rw [pow_zero, one_smul]
  exact (submoduleFamily_eq_of_affine_cover F
    (idealPowSmulInf F G I 0 n) (idealPowSmulInf F G I (n - c) c)
    (idealPowSmulInf_basicOpen F G I 0 n)
    (idealPowSmulInf_basicOpen F G I (n - c) c) V hV
    (fun i => (h0 (V i) n).trans (hc n hn i)) U).symm.trans (h0 U n)

end AlgebraicGeometry
