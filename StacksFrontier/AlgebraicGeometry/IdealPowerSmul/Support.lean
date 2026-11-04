module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen

/-!
# The support of `I ^ n • F` for `I` the ideal of a closed subset

Let `X` be a Noetherian scheme, `F` a coherent module on `X` whose support is contained in the
union of two closed subsets `Z₁ ∪ Z₂`, and let `I₂` be the quasi-coherent ideal sheaf of the
reduced induced structure on `Z₂`. Then for a suitable `n` the subsheaf `I₂ ^ n • F` is
supported inside `Z₁`.

This is the half of [Stacks, Tag 01YD] which [Stacks, Tag 01Y9] supplies there. The argument is
affine-local throughout: over an affine open `U` the support of `F` is the support of the
`Γ(X, U)`-module `Γ(F, U)` ([Stacks, Tag 056I]), so the containment of the support in `Z₁ ∪ Z₂`
says that every prime containing the annihilator of `Γ(F, U)` contains the product
`I₁(U) · I₂(U)` of the two vanishing ideals; since that product is finitely generated, a power
of it annihilates `Γ(F, U)`. Quasi-compactness turns the exponents on the members of a finite
affine cover into one.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSmul.mem_closed_iff_vanishingIdeal_le`: a point of an affine
  open lies in a closed set exactly when the vanishing ideal of that closed set is contained in
  the corresponding prime.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.exists_pow_mul_le_annihilator`: on one affine open, a
  power of the product of the two vanishing ideals annihilates the sections of `F`.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.exists_supp_idealPowSmul_subset`:
  **[Stacks, Tag 01Y9] in the form [Stacks, Tag 01YD] uses it** — for some `n` the subsheaf
  `I₂ ^ n • F` is supported in `Z₁`.

## Implementation notes

`Module.support` is indexed by primes and `SheafOfModules.supp` by points, so the two are
matched by `AlgebraicGeometry.IsAffineOpen.primeIdealOf` in one direction and by
`AlgebraicGeometry.IsAffineOpen.fromSpec` in the other; `primeIdealOf_fromSpec` below is the
round trip, which needs the injectivity of `fromSpec` and is not in Mathlib.

The exponent is produced on the members of `X.affineCover.finiteSubcover`, and the conclusion is
read at a *single* affine open containing the point in question — which is legitimate because
[Stacks, Tag 056I] is an `Iff` at every affine open separately. No affine-locality statement
about `I ^ n • F` beyond the compatibility of `idealPowFamily` is needed.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 056I](https://stacks.math.columbia.edu/tag/056I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentFinite

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerSmul

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Closed subsets read on an affine open -/

/-- The quasi-coherent ideal sheaf of the reduced induced structure on a closed subset. -/
abbrev closedIdeal (Z : Closeds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal Z

/-- Every prime of the ring of functions on an affine open gives a point of that open. -/
theorem fromSpec_mem (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1)) :
    U.2.fromSpec p ∈ U.1 :=
  U.2.range_fromSpec.le (Set.mem_range_self p)

/-- The prime attached to the point attached to a prime is that prime. -/
theorem primeIdealOf_fromSpec (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1)) :
    U.2.primeIdealOf ⟨U.2.fromSpec p, fromSpec_mem U p⟩ = p :=
  have := U.2.isOpenImmersion_fromSpec
  U.2.fromSpec.isOpenEmbedding.injective
    (U.2.fromSpec_primeIdealOf ⟨U.2.fromSpec p, fromSpec_mem U p⟩)

/-- **A point of an affine open lies in a closed set exactly when the vanishing ideal of that
closed set is contained in the corresponding prime.** -/
theorem mem_closed_iff_vanishingIdeal_le (Z : Closeds X) (U : X.affineOpens) (x : X)
    (hx : x ∈ U.1) :
    x ∈ (Z : Set X) ↔
      (closedIdeal Z).ideal U ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hpt : U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) = x :=
    U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  rw [show (closedIdeal Z).ideal U = PrimeSpectrum.vanishingIdeal
    (U.2.fromSpec ⁻¹' (Z : Set X)) from rfl]
  refine ⟨fun hxZ f hf ↦ (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf _
    (Set.mem_preimage.mpr (by rwa [hpt])), fun hle ↦ ?_⟩
  have h1 : U.2.primeIdealOf ⟨x, hx⟩ ∈
      PrimeSpectrum.zeroLocus
        ((PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X)) : Ideal Γ(X, U.1)) :
          Set Γ(X, U.1)) :=
    (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr hle)
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at h1
  rw [← hpt]
  exact (Z.isClosed.preimage U.2.fromSpec.continuous).closure_subset h1

/-! ### A power of the product of the two ideals annihilates the sections -/

/-- On a locally Noetherian scheme, if the support of a coherent module `F` lies in `Z₁ ∪ Z₂`,
then on each affine open `U` some power of `I₁(U) · I₂(U)` annihilates `Γ(F, U)`. -/
theorem exists_pow_mul_le_annihilator_of_isLocallyNoetherian [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (Z₁ Z₂ : Closeds X)
    (hsupp : SheafOfModules.supp F ⊆ (Z₁ : Set X) ∪ (Z₂ : Set X)) (U : X.affineOpens) :
    ∃ t : ℕ, ((closedIdeal Z₁).ideal U * (closedIdeal Z₂).ideal U) ^ t ≤
      Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  have hNoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hFft : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hMfin : Module.Finite Γ(X, U.1) Γ(F, U.1) := finite_sections F U.2
  have hrad : (closedIdeal Z₁).ideal U * (closedIdeal Z₂).ideal U ≤
      (Module.annihilator Γ(X, U.1) Γ(F, U.1)).radical := by
    intro f hf
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro p ⟨hple, hpprime⟩
    have hxU : U.2.fromSpec (⟨p, hpprime⟩ : PrimeSpectrum Γ(X, U.1)) ∈ U.1 := fromSpec_mem U _
    have hkey : U.2.primeIdealOf ⟨_, hxU⟩ = (⟨p, hpprime⟩ : PrimeSpectrum Γ(X, U.1)) :=
      primeIdealOf_fromSpec U _
    have hxsupp : U.2.fromSpec (⟨p, hpprime⟩ : PrimeSpectrum Γ(X, U.1)) ∈
        SheafOfModules.supp F :=
      (Scheme.Modules.mem_support_sections_iff_mem_supp F U _ hxU).mp
        (by rw [hkey]; exact Module.mem_support_iff_of_finite.mpr hple)
    exact (hsupp hxsupp).elim
      (fun hx ↦ by
        simpa only [hkey] using
          (mem_closed_iff_vanishingIdeal_le Z₁ U _ hxU).mp hx (Ideal.mul_le_inf hf).1)
      fun hx ↦ by
        simpa only [hkey] using
          (mem_closed_iff_vanishingIdeal_le Z₂ U _ hxU).mp hx (Ideal.mul_le_inf hf).2
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

/-- **On one affine open, a power of `I₁(U) · I₂(U)` annihilates `Γ(F, U)`.** Every prime
containing the annihilator is in the support of `Γ(F, U)`, hence corresponds to a point of the
support of `F`, hence lies in `Z₁` or in `Z₂`, hence contains `I₁(U)` or `I₂(U)`. -/
theorem exists_pow_mul_le_annihilator [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (Z₁ Z₂ : Closeds X)
    (hsupp : SheafOfModules.supp F ⊆ (Z₁ : Set X) ∪ (Z₂ : Set X)) (U : X.affineOpens) :
    ∃ t : ℕ, ((closedIdeal Z₁).ideal U * (closedIdeal Z₂).ideal U) ^ t ≤
      Module.annihilator Γ(X, U.1) Γ(F, U.1) :=
  exists_pow_mul_le_annihilator_of_isLocallyNoetherian F Z₁ Z₂ hsupp U

/-- **One exponent for a finite family of affine opens.** -/
theorem exists_uniform_pow_mul_le_annihilator [IsNoetherian X] (F : X.Modules) [F.IsCoherent]
    (Z₁ Z₂ : Closeds X)
    (hsupp : SheafOfModules.supp F ⊆ (Z₁ : Set X) ∪ (Z₂ : Set X))
    {ι : Type*} [Finite ι] (V : ι → X.affineOpens) :
    ∃ n : ℕ, ∀ i, ((closedIdeal Z₁).ideal (V i) * (closedIdeal Z₂).ideal (V i)) ^ n ≤
      Module.annihilator Γ(X, (V i).1) Γ(F, (V i).1) := by
  classical
  let _ := Fintype.ofFinite ι
  choose t ht using fun i ↦ exists_pow_mul_le_annihilator F Z₁ Z₂ hsupp (V i)
  exact ⟨Finset.univ.sup t, fun i ↦
    (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i))).trans (ht i)⟩

/-! ### The support of `I₂ ^ n • F` -/

/-- **A point of an affine open at which a scalar outside the corresponding prime annihilates
every section of a quasi-coherent submodule is outside its support.** -/
theorem notMem_supp_of_smul_eq_zero (F : X.Modules) (G : F.Submodule)
    (hG : G.toSheafOfModules.IsQuasicoherent) (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (r : Γ(X, U.1)) (hr : r ∉ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)
    (hzero : ∀ m ∈ (show Submodule Γ(X, U.1) Γ(F, U.1) from G.toSubmodule.obj (op U.1)),
      r • m = 0) :
    x ∉ SheafOfModules.supp G.toSheafOfModules := by
  have := hG
  intro hmem
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp
    ((Scheme.Modules.mem_support_sections_iff_mem_supp G.toSheafOfModules U x hx).mpr hmem)
  exact hm r hr (Subtype.ext (hzero (show Γ(F, U.1) from m.1) m.2))

/-- **[Stacks, Tag 01Y9] in the form the splitting of [Stacks, Tag 01YD] uses it.** For a
coherent module whose support is contained in `Z₁ ∪ Z₂`, some power of the ideal sheaf of `Z₂`
cuts `F` down to a subsheaf supported in `Z₁`. -/
theorem exists_supp_idealPowSmul_subset [IsNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsCoherent] (Z₁ Z₂ : Closeds X)
    (hsupp : SheafOfModules.supp F ⊆ (Z₁ : Set X) ∪ (Z₂ : Set X)) :
    ∃ n : ℕ, SheafOfModules.supp
      (idealPowSmul (closedIdeal Z₂) n F).toSheafOfModules ⊆ (Z₁ : Set X) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let V : 𝒰.I₀ → X.affineOpens := fun i ↦
    ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
  have hV : ⨆ i, (V i).1 = ⊤ := 𝒰.iSup_opensRange
  obtain ⟨n, hn⟩ := exists_uniform_pow_mul_le_annihilator F Z₁ Z₂ hsupp V
  refine ⟨n, fun x hxsupp ↦ ?_⟩
  by_contra hxZ
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, (V i).1 by rw [hV]; trivial)
  obtain ⟨f, hf, hfp⟩ := SetLike.not_le_iff_exists.mp fun h ↦
    hxZ ((mem_closed_iff_vanishingIdeal_le Z₁ (V i) x hxi).mpr h)
  refine notMem_supp_of_smul_eq_zero F (idealPowSmul (closedIdeal Z₂) n F)
    (isQuasicoherent_idealPowSmul _ n F) (V i) x hxi (f ^ n) ?_ ?_ hxsupp
  · exact fun hmem ↦ hfp (((V i).2.primeIdealOf ⟨x, hxi⟩).2.mem_of_pow_mem n hmem)
  · intro m hm
    rw [obj_idealPowSmul (closedIdeal Z₂) n F (V i)] at hm
    have hn' := hn i
    rw [mul_pow] at hn'
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro a ha z _
      rw [smul_smul]
      exact Module.mem_annihilator.mp
        (hn' (Ideal.mul_mem_mul (Ideal.pow_mem_pow hf n) ha)) z
    · intro y z hy hz
      rw [smul_add, hy, hz, add_zero]

end Stacks.AlgebraicGeometry.IdealPowerSmul

end
