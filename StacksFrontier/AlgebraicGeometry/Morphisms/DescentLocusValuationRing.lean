module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.Descent.NonvanishingSectionNearFibre
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.Basic
public import StacksFrontier.RingTheory.Coherent.Bezout
public import StacksFrontier.RingTheory.AssociatedPrime.FlatOverValuationRing
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# Triviality of an invertible module over a valuation ring

Let `A` be a valuation ring with fraction field `K`, let `f : X ⟶ Spec A` be proper, flat and of
finite presentation, and let `L` be an invertible `𝒪_X`-module. If `L` is trivial on the generic
fibre `X_K`, the closed fibre `X_0` is integral and `H⁰(X_K, 𝒪_{X_K}) = K`, then `L` is trivial.
This is [Stacks, Tag 0EX8]. The one input of the source's proof from outside this file is
[Stacks, Tag 0A1H],
`AlgebraicGeometry.isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`.

## The proof

The source's general (valuation ring) argument, with its two appeals to limits replaced by
direct arguments on germs:

* `Γ(X, L)` is a finite `A`-module: `RΓ(X, L)` is perfect ([Stacks, Tag 0B91] from 0A1H, read
  over the affine base), so its cohomology is coherent ([Stacks, Tag 0EX6]); this is
  `finite_sections_of_isInvertible`.
* `Γ(X, L)` is torsion-free, `L` being flat over the domain `A`
  (`eq_zero_of_appLE_smul_eq_zero`), hence flat over the Bézout ring `A`, hence free
  (`free_sections_of_isFlatOver`).
* By flat base change in degree zero ([Stacks, Tag 02KH]) the pullbacks of a basis span
  `Γ(X_K, L_K) ≅ Γ(X_K, 𝒪) = K`, so some basis element `s` restricts to a nowhere vanishing
  section of `L_K` (`exists_basis_mem_nonvanishingLocus`).
* On the closed fibre the germ of `s` lies in `𝔪_A L` either at every point or at none
  (`germ_mem_map_maximalIdeal_iff_of_isIntegral`, through the integrality of `X_0`). If at every
  point, then `s` is divisible by a non-unit of `A` near every point of `X_0`, hence globally
  (`exists_eq_smul_of_forall_mem`: valuation ring divisibility and torsion-freeness glue the
  quotients), which a basis element is not. This replaces the source's use of
  [Stacks, Tag 01Z0].
* If at no point, then at a point `x` of `X_0` where `s` vanished the local equation of `s`
  would be regular on the closed fibre, so the zero scheme of `s` would be flat over `A` near
  `x` ([Stacks, Tag 062Y]) and going down would produce a point over the generic point where `s`
  vanishes (`mem_nonvanishingLocus_of_not_mem`). So `s` vanishes nowhere on `X_0`.
* Every point of `X` specializes to a point of `X_0` (`f` is closed and `Spec A` local), so `s`
  vanishes nowhere and trivializes `L`.

## Main results

* `AlgebraicGeometry.ValuativeTriviality.isTrivial_of_isTrivial_genericFiber`:
  **[Stacks, Tag 0EX8]**.

## Implementation notes

The generic fibre is the base change along `Spec K ⟶ Spec A` for a fraction field `K` of `A`,
and "`H⁰(X_K, 𝒪) = K`" is the bijectivity of `Γ(Spec K, 𝒪) ⟶ Γ(X_K, 𝒪)`, the spelling of the
fibre condition of `Stacks.AlgebraicGeometry.ProperFlatFamilyUnit` (part (a) of
[Stacks, Tag 0E62]). The closed fibre is Mathlib's `Scheme.Hom.fiber` at the closed point.

## References

* [Stacks Project, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8)
* [Stacks Project, Tag 0EX6](https://stacks.math.columbia.edu/tag/0EX6)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open AlgebraicGeometry.ProperFlatBaseChange
open Stacks.AlgebraicGeometry.CoherentBaseCohomology
  (isCoherent_cohomology_of_isPerfect_derivedGlobalSections)

universe u

namespace AlgebraicGeometry.ValuativeTriviality

open Stacks.AlgebraicGeometry.PushforwardRegularity
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top)
open Stacks.ValuationRingFibre (exists_smul_eq_of_mem_smul_top restrictScalars_map_smul_top)

variable {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- A ring isomorphic to a valuation ring is a valuation ring. -/
theorem valuationRing_of_ringEquiv {R T : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing T] [IsDomain T] (e : R ≃+* T) : ValuationRing T :=
  ValuationRing.iff_dvd_total.2 ⟨fun a b => (ValuationRing.dvd_total (e.symm a) (e.symm b)).imp
    (fun h => by simpa using map_dvd e h) (fun h => by simpa using map_dvd e h)⟩

/-- Torsion-freeness of the sections of a module flat over a domain base. -/
theorem eq_zero_of_appLE_smul_eq_zero (L : X.Modules) (hflat : IsFlatOver f.toLRSHom.toShHom L)
    {W : X.Opens} (r : Γ(Spec (.of A), ⊤)) (hr : r ≠ 0) (ξ : Γ(L, W))
    (h : (f.appLE ⊤ W (le_preimage_top f W) r) • ξ = 0) : ξ = 0 := by
  refine section_ext_F L ξ 0 fun y hy => ?_
  have h1 := germ_smul_appLE f L (le_preimage_top f W) r ξ y hy
  rw [h, germF_zero] at h1
  obtain ⟨k, c, m, hc, hx⟩ := exists_stalk_smul_repr_of_smul_eq_zero f L hflat
    (isAffineOpen_top _) y _ r _ h1.symm
  have hc0 : ∀ j, c j = 0 := fun j => (mul_eq_zero.mp (hc j)).resolve_left hr
  rw [hx, germF_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hc0 j]
  simp only [stalkPullback, map_zero, zero_smul]

/-- A valuation ring `A` has valuation ring of global functions on `Spec A`. -/
private theorem valuationRing_Γ_Spec [ValuationRing A] : ValuationRing Γ(Spec (.of A), ⊤) :=
  valuationRing_of_ringEquiv (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv

/-- Divisibility near a point from divisibility of the germ. -/
theorem exists_res_eq_smul_of_germ_mem [ValuationRing A] (L : X.Modules) (s : Γ(L, ⊤)) (x : X)
    (hs : (L.presheaf.Γgerm x).hom s ∈
      (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)))) •
        (⊤ : Submodule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x))) :
    ∃ (W : X.Opens) (_ : x ∈ W) (r : Γ(Spec (.of A), ⊤)),
      r ∈ ((isAffineOpen_top (Spec (.of A))).primeIdealOf ⟨f x, trivial⟩).asIdeal ∧
      ∃ t : Γ(L, W), resF L le_top s = (f.appLE ⊤ W (le_preimage_top f W) r) • t := by
  classical
  have := valuationRing_Γ_Spec (A := A)
  set R := Γ(Spec (.of A), ⊤)
  let xs : (⊤ : (Spec (.of A)).Opens) := ⟨f x, trivial⟩
  set p := (isAffineOpen_top (Spec (.of A))).primeIdealOf ⟨f x, trivial⟩ with hp
  let Ox := X.presheaf.stalk x
  let Lx := TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x
  let ψ : R →+* Ox := (f.stalkMap x).hom.comp ((Spec (.of A)).presheaf.germ ⊤ (f x) trivial).hom
  let : Algebra R Ox := ψ.toAlgebra
  let : Module R Lx := Module.compHom Lx ψ
  have : IsScalarTower R Ox Lx := ⟨fun a b n => mul_smul (ψ a) b n⟩
  have hI : Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x))) =
      p.asIdeal.map (algebraMap R Ox) := by
    let : Algebra R ((Spec (.of A)).presheaf.stalk (f x)) :=
      (Spec (.of A)).presheaf.algebra_section_stalk xs
    have := (isAffineOpen_top (Spec (.of A))).isLocalization_stalk xs
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal, Ideal.map_map]
    rfl
  rw [hI] at hs
  have hs' : (L.presheaf.Γgerm x).hom s ∈ p.asIdeal • (⊤ : Submodule R Lx) := by
    rwa [← restrictScalars_map_smul_top (B := Ox)]
  obtain ⟨r, hr, n, hn⟩ := exists_smul_eq_of_mem_smul_top hs'
  obtain ⟨W', hxW', t', ht'⟩ := TopCat.Presheaf.exists_germ_eq L.presheaf n
  have hg : TopCat.Presheaf.germ L.val.presheaf ⊤ x trivial s =
      TopCat.Presheaf.germ L.val.presheaf W' x hxW'
        ((f.appLE ⊤ W' (le_preimage_top f W') r) • t') := by
    rw [germ_smul_appLE f L (le_preimage_top f W') r t' x hxW']
    change (L.presheaf.Γgerm x).hom s = _
    rw [hn]
    change ψ r • n = _
    rw [← ht']
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial r
  obtain ⟨W, hxW, iU, iV, he⟩ :=
    TopCat.Presheaf.germ_eq L.val.presheaf (U := ⊤) x trivial hxW' _ _ hg
  exact ⟨W, hxW, r, hr, resF L iV.le t',
    he.trans (resF_smul_appLE f L (le_preimage_top f W') iV.le r t')⟩

/-- In a Bézout ring, finitely many elements of an ideal have a common divisor in that ideal. -/
private theorem exists_mem_forall_dvd {R ι : Type*} [CommRing R] [IsBezout R] {P : Ideal R}
    (T : Finset ι) (r : ι → R) (hr : ∀ i ∈ T, r i ∈ P) : ∃ π ∈ P, ∀ i ∈ T, π ∣ r i := by
  classical
  obtain ⟨π, hπ⟩ := IsBezout.isPrincipal_of_FG (Ideal.span (r '' T)) ⟨T.image r, by simp⟩
  have hπmem : π ∈ Ideal.span (r '' T) := by
    rw [hπ]
    exact Submodule.mem_span_singleton_self π
  have hle : r '' T ⊆ P := by
    rintro _ ⟨i, hi, rfl⟩
    exact hr i hi
  refine ⟨π, Ideal.span_le.2 hle hπmem, fun i hi => ?_⟩
  have : r i ∈ Ideal.span (r '' T) := Ideal.subset_span ⟨i, hi, rfl⟩
  rw [hπ] at this
  exact Ideal.mem_span_singleton.1 this

/-- **Divisibility by local divisibility.** Let `C ⊆ X` be compact, with every point of `X`
specializing to a point of `C`, and let `P` be an ideal of `Γ(Spec A, ⊤)`. If near every point
of `C` the section `s` is a multiple of a section of `𝒪_{Spec A}` lying in `P`, then `s` is
globally a multiple of an element of `P`. -/
theorem exists_eq_smul_of_forall_mem [ValuationRing A] (L : X.Modules)
    (hflat : IsFlatOver f.toLRSHom.toShHom L) (s : Γ(L, ⊤)) (P : Ideal Γ(Spec (.of A), ⊤))
    (C : Set X) (hC : IsCompact C) (hspec : ∀ x : X, ∃ c ∈ C, x ⤳ c)
    (H : ∀ x ∈ C, ∃ (W : X.Opens) (_ : x ∈ W) (r : Γ(Spec (.of A), ⊤)), r ∈ P ∧
      ∃ t : Γ(L, W), resF L le_top s = (f.appLE ⊤ W (le_preimage_top f W) r) • t) :
    ∃ r ∈ P, ∃ t : Γ(L, ⊤), s = (f.appLE ⊤ ⊤ (le_preimage_top f ⊤) r) • t := by
  classical
  have := valuationRing_Γ_Spec (A := A)
  choose! W hxW r hrP t ht using H
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover (fun c : C => (W c : Set X)) (fun c => (W c).2)
    (fun c hc => Set.mem_iUnion.2 ⟨⟨c, hc⟩, hxW c hc⟩)
  have hcov : ∀ y : X, ∃ c ∈ T, y ∈ W c := by
    intro y
    obtain ⟨c, hc, hyc⟩ := hspec y
    obtain ⟨c', hc'T, hc'⟩ := Set.mem_iUnion₂.1 (hT hc)
    exact ⟨c', hc'T, hyc.mem_open (W c').2 hc'⟩
  obtain ⟨π, hπP, hdvd⟩ : ∃ π ∈ P, ∀ c ∈ T, π ∣ r c :=
    exists_mem_forall_dvd T _ fun c _ => hrP c c.2
  choose! d hd using hdvd
  let ι := {c : C // c ∈ T}
  let U : ι → X.Opens := fun c => W c.1
  let u : ∀ c : ι, Γ(L, U c) := fun c =>
    (f.appLE ⊤ (U c) (le_preimage_top f (U c)) (d c.1)) • t c.1
  have hsu : ∀ c : ι, resF L le_top s = (f.appLE ⊤ (U c) (le_preimage_top f (U c)) π) • u c := by
    intro c
    rw [ht c.1 c.1.2, hd c.1 c.2, map_mul, mul_smul]
  have hcovU : (⊤ : X.Opens) ≤ ⨆ c : ι, U c := fun y _ => by
    obtain ⟨c, hc, hyc⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨⟨c, hc⟩, hyc⟩
  by_cases hπ0 : π = 0
  · refine ⟨π, hπP, 0, ?_⟩
    rw [smul_zero]
    refine section_ext_F L s 0 fun y _ => ?_
    obtain ⟨c, hc, hyc⟩ := hcov y
    rw [← germ_resF L (le_top : W c ≤ ⊤) s y hyc, hsu ⟨c, hc⟩, hπ0, map_zero, zero_smul,
      germF_zero, germF_zero]
  have hres : ∀ (c : ι) {V : X.Opens} (hV : V ≤ U c),
      (f.appLE ⊤ V (le_preimage_top f V) π) • resF L hV (u c) = resF L le_top s := by
    intro c V hV
    rw [← resF_smul_appLE f L (le_preimage_top f (U c)) hV π (u c), ← hsu c, resF_resF]
  have hcompat : ∀ c c' : ι, resF L (inf_le_left : U c ⊓ U c' ≤ U c) (u c) =
      resF L (inf_le_right : U c ⊓ U c' ≤ U c') (u c') := by
    intro c c'
    refine sub_eq_zero.1 (eq_zero_of_appLE_smul_eq_zero f L hflat π hπ0 _ ?_)
    rw [smul_sub, hres c, hres c', sub_self]
  obtain ⟨ζ, hζ⟩ := exists_glue L ⊤ U hcovU (fun _ => le_top) u hcompat
  refine ⟨π, hπP, ζ, section_ext_F L s _ fun y _ => ?_⟩
  obtain ⟨c, hc, hyc⟩ := hcov y
  rw [← germ_resF L (le_top : W c ≤ ⊤) s y hyc,
    ← germ_resF L (le_top : W c ≤ ⊤) _ y hyc, resF_smul_appLE f L (le_preimage_top f ⊤) le_top π ζ,
    hζ ⟨c, hc⟩, hsu ⟨c, hc⟩]

/-- **Membership in the extended maximal ideal, read on the fibre.** For a point `z` of `X` over
`y` and a point `z'` of the fibre over `y` lying over `z`, the germ at `z` of a function `c`
lies in the ideal generated by the maximal ideal of `𝒪_{S, y}` exactly when the restriction of
`c` to the fibre has zero germ at `z'`. -/
theorem germ_mem_map_maximalIdeal_iff {X S : Scheme.{u}} (f : X ⟶ S) (z : X) (y : S)
    (h : f z = y) (z' : f.fiber y) (hz : f.fiberι y z' = z) {U : X.Opens} (hzU : z ∈ U)
    (c : Γ(X, U)) :
    (X.presheaf.germ U z hzU c) ∈ Ideal.map (f.stalkMap z).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f z))) ↔
      (f.fiber y).presheaf.germ (f.fiberι y ⁻¹ᵁ U) z' (show f.fiberι y z' ∈ U from hz ▸ hzU)
        ((f.fiberι y).app U c) = 0 := by
  subst h
  obtain rfl : z' = f.asFiber z :=
    (f.fiberι _).isEmbedding.injective (by rw [hz, f.fiberι_asFiber])
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← (quotientStalkEquivFiberStalk f z).map_eq_zero_iff,
    quotientStalkEquivFiberStalk_mk]
  rw [← Scheme.Hom.germ_stalkMap_apply]
  exact Iff.of_eq (congrArg (· = 0) (congrArg ((f.fiberι (f z)).stalkMap (f.asFiber z)).hom
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hzU
      (Inseparable.of_eq (f.fiberι_asFiber z).symm).ge c)))

/-- **On an integral fibre, membership of a germ in the extended maximal ideal does not depend on
the point.** -/
theorem germ_mem_map_maximalIdeal_iff_of_isIntegral {X S : Scheme.{u}} (f : X ⟶ S) (y : S)
    [IsIntegral (f.fiber y)] {x ξ : X} (hx : f x = y) (hξ : f ξ = y) {U : X.Opens}
    (hxU : x ∈ U) (hξU : ξ ∈ U) (c : Γ(X, U)) :
    (X.presheaf.germ U x hxU c) ∈ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) ↔
      (X.presheaf.germ U ξ hξU c) ∈ Ideal.map (f.stalkMap ξ).hom
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f ξ))) := by
  obtain ⟨x', hx'⟩ : x ∈ Set.range (f.fiberι y) := by rwa [Scheme.Hom.range_fiberι]
  obtain ⟨ξ', hξ'⟩ : ξ ∈ Set.range (f.fiberι y) := by rwa [Scheme.Hom.range_fiberι]
  rw [germ_mem_map_maximalIdeal_iff f x y hx x' hx' hxU c,
    germ_mem_map_maximalIdeal_iff f ξ y hξ ξ' hξ' hξU c]
  have key : ∀ (z : f.fiber y) (hz : z ∈ f.fiberι y ⁻¹ᵁ U),
      (f.fiber y).presheaf.germ (f.fiberι y ⁻¹ᵁ U) z hz ((f.fiberι y).app U c) = 0 ↔
        (f.fiberι y).app U c = 0 := fun z hz =>
    ⟨fun h => germ_injective_of_isIntegral (f.fiber y) z hz (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  exact (key x' _).trans (key ξ' _).symm

omit [IsDomain A] in
/-- The pullback to a stalk of `X` of a function on `Spec A` vanishing at the image point lies in
the ideal generated by the maximal ideal of the base. -/
theorem stalkPullback_mem_map_maximalIdeal (z : X) (r : Γ(Spec (.of A), ⊤))
    (hr : r ∈ ((isAffineOpen_top (Spec (.of A))).primeIdealOf ⟨f z, trivial⟩).asIdeal) :
    stalkPullback f ⊤ z trivial r ∈ Ideal.map (f.stalkMap z).hom
      (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f z))) := by
  let zs : (⊤ : (Spec (.of A)).Opens) := ⟨f z, trivial⟩
  let : Algebra Γ(Spec (.of A), ⊤) ((Spec (.of A)).presheaf.stalk (f z)) :=
    (Spec (.of A)).presheaf.algebra_section_stalk zs
  have := (isAffineOpen_top (Spec (.of A))).isLocalization_stalk zs
  have h1 := Ideal.mem_map_of_mem (f.stalkMap z).hom
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff _
      ((isAffineOpen_top (Spec (.of A))).primeIdealOf zs).asIdeal r).2 hr)
  change (f.stalkMap z).hom ((Spec (.of A)).presheaf.germ ⊤ (f z) trivial r) ∈ _ at h1
  convert h1 using 1
  exact (Scheme.Hom.germ_stalkMap_apply f ⊤ z trivial r).symm

/-- **Membership of a germ in `𝔪_{S} · L_z`, read through a trivialization.** On an open `U`
inside a trivializing open `V`, the germ of a global section `s` lies in the submodule generated by
the maximal ideal of the base exactly when the germ of its trivializing function does. -/
theorem Γgerm_mem_smul_top_iff [ValuationRing A] (L : X.Modules) (s : Γ(L, ⊤)) {V U : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf L.val V) (hUV : U ≤ V) {z : X}
    (hz : z ∈ U) :
    (L.presheaf.Γgerm z).hom s ∈
      (Ideal.map (f.stalkMap z).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f z)))) •
        (⊤ : Submodule (X.presheaf.stalk z) (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf z)) ↔
    X.presheaf.germ U z hz (Stacks.NonvanishingOpen.triv t (homOfLE hUV) (resF L le_top s)) ∈
      Ideal.map (f.stalkMap z).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f z))) := by
  constructor
  · intro hs
    obtain ⟨W, hzW, r, hr, t', ht'⟩ := exists_res_eq_smul_of_germ_mem f L s z hs
    have hW'U : W ⊓ U ≤ U := inf_le_right
    have hW'W : W ⊓ U ≤ W := inf_le_left
    have hzW' : z ∈ W ⊓ U := ⟨hzW, hz⟩
    have hc : X.presheaf.map (homOfLE hW'U).op
        (Stacks.NonvanishingOpen.triv t (homOfLE hUV) (resF L le_top s)) =
        (f.appLE ⊤ (W ⊓ U) (le_preimage_top f _) r) *
          Stacks.NonvanishingOpen.triv t (homOfLE (hW'U.trans hUV)) (resF L hW'W t') := by
      rw [← Stacks.NonvanishingOpen.triv_res t (homOfLE hUV) (homOfLE hW'U)
        (homOfLE (hW'U.trans hUV))]
      change Stacks.NonvanishingOpen.triv t _ (resF L hW'U (resF L le_top s)) = _
      rw [resF_resF, ← resF_resF L (le_top : W ≤ ⊤) hW'W, ht',
        resF_smul_appLE, Stacks.NonvanishingOpen.triv_smul]
    rw [← X.presheaf.germ_res_apply (homOfLE hW'U) z hzW', hc, map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    rw [germ_appLE f (le_preimage_top f _) r z hzW']
    exact stalkPullback_mem_map_maximalIdeal f z r hr
  · intro hc
    have he := t.eq_smul_basisAt (homOfLE hUV) (resF L le_top s)
    rw [← TopCat.Presheaf.Γgerm_res_apply L.presheaf (i := homOfLE (le_top : U ≤ ⊤)) z hz s]
    change TopCat.Presheaf.germ L.val.presheaf U z hz (resF L le_top s) ∈ _
    rw [he]
    have h := Submodule.smul_mem_smul hc
      (Submodule.mem_top (x := (L.presheaf.germ U z hz).hom (t.basisAt (homOfLE hUV))))
    have e := Stacks.ModuleStalk.germ_smul L z U hz ((t.θ U (homOfLE hUV)) (resF L le_top s))
      (t.basisAt (homOfLE hUV))
    exact e ▸ h

/-- Every point of the support of an invertible module has an affine neighbourhood inside a
trivializing open. -/
private theorem exists_affineOpen_trivialization (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (x : X) :
    ∃ (U V : X.Opens), IsAffineOpen U ∧ x ∈ U ∧ U ≤ V ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf L.val V) := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hxz⟩ : ∃ z : X, x ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxz (V z).2
  exact ⟨U, V z, hU, hxU, hUV, htriv z⟩

/-- A function on an affine open vanishing at `x` lies in the vanishing ideal of the closure of
`x`. -/
private theorem mem_vanishingIdeal_closure_of_notMem_basicOpen {Y : Scheme.{u}} {U : Y.Opens}
    (hU : IsAffineOpen U) {x : Y} {c : Γ(Y, U)} (hxb : x ∉ Y.basicOpen c) :
    c ∈ (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure {x}, isClosed_closure⟩ : Closeds Y)).ideal ⟨U, hU⟩ := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun p hp => ?_
  have hspec : x ⤳ hU.fromSpec p := specializes_iff_mem_closure.2 hp
  by_contra hcp
  have hpb : hU.fromSpec p ∈ Y.basicOpen c := by
    rw [hU.mem_basicOpen_iff_notMem_primeIdealOf c (hU.fromSpec_mem p),
      hU.primeIdealOf_fromSpec]
    exact hcp
  exact hxb (hspec.mem_open (Y.basicOpen c).2 hpb)

/-- **Going down along a flat quotient.** If `Γ(X, V') ⧸ (a)` is flat over `Γ(S, W)` and `a`
vanishes at `x ∈ V'`, then `a` vanishes at a point of `V'` over every generization of `f x`. -/
private theorem exists_mem_primeIdealOf_of_flat_quotient {X S : Scheme.{u}} (f : X ⟶ S)
    {W : S.Opens} (hW : IsAffineOpen W) {V' : X.Opens} (hV' : IsAffineOpen V')
    (hV'W : V' ≤ f ⁻¹ᵁ W) {a : Γ(X, V')}
    (hflat : RingHom.Flat ((Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V' hV'W).hom))
    {x : X} (hxV' : x ∈ V') (haq : a ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal)
    {η : S} (hηx : η ⤳ f x) :
    ∃ (y : X) (hyV' : y ∈ V'), f y = η ∧ a ∈ (hV'.primeIdealOf ⟨y, hyV'⟩).asIdeal := by
  let φ : Γ(S, W) →+* Γ(X, V') ⧸ Ideal.span {a} :=
    (Ideal.Quotient.mk (Ideal.span {a})).comp (f.appLE W V' hV'W).hom
  let : Algebra Γ(S, W) (Γ(X, V') ⧸ Ideal.span {a}) := φ.toAlgebra
  have : Module.Flat Γ(S, W) (Γ(X, V') ⧸ Ideal.span {a}) := hflat
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {a})) ≤
      (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact haq
  let Q : Ideal (Γ(X, V') ⧸ Ideal.span {a}) :=
    (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal.map (Ideal.Quotient.mk _)
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hQunder : Q.under Γ(S, W) = (hW.primeIdealOf ⟨f x, hV'W hxV'⟩).asIdeal := by
    change Q.comap φ = _
    rw [← Ideal.comap_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      sup_eq_left.2 hker]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W hW V' hV' hV'W hxV')
  have hηW : η ∈ W := hηx.mem_open W.2 (hV'W hxV')
  have hle : (hW.primeIdealOf ⟨η, hηW⟩).asIdeal ≤ (hW.primeIdealOf ⟨f x, hV'W hxV'⟩).asIdeal := by
    refine (PrimeSpectrum.le_iff_specializes _ _).2 ?_
    refine Specializes.map ?_ (hW.isoSpec.hom.continuous)
    exact (Topology.IsInducing.subtypeVal.specializes_iff).1 hηx
  have : Q.LiesOver (hW.primeIdealOf ⟨f x, hV'W hxV'⟩).asIdeal := ⟨hQunder.symm⟩
  obtain ⟨P, -, hP, hPover⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  let P'' : PrimeSpectrum Γ(X, V') := ⟨P.comap (Ideal.Quotient.mk _), Ideal.comap_isPrime _ _⟩
  have hyV' : hV'.fromSpec P'' ∈ V' := hV'.fromSpec_mem P''
  have hyP : hV'.primeIdealOf ⟨_, hyV'⟩ = P'' := hV'.primeIdealOf_fromSpec P'' hyV'
  refine ⟨hV'.fromSpec P'', hyV', ?_, ?_⟩
  · have h1 := IsAffineOpen.comap_primeIdealOf_appLE W hW V' hV' hV'W hyV'
    rw [hyP] at h1
    have h2 : hW.primeIdealOf ⟨f (hV'.fromSpec P''), hV'W hyV'⟩ = hW.primeIdealOf ⟨η, hηW⟩ := by
      rw [← h1]
      ext1
      change (P.comap (Ideal.Quotient.mk _)).comap (f.appLE W V' hV'W).hom = _
      rw [Ideal.comap_comap]
      exact hPover.over.symm
    have h3 := congrArg hW.fromSpec h2
    rwa [hW.fromSpec_primeIdealOf, hW.fromSpec_primeIdealOf] at h3
  · rw [hyP]
    change Ideal.Quotient.mk _ a ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)]
    exact P.zero_mem

/-- **A section that is regular on the closed fibre at a point, and vanishes nowhere over the
generic point, does not vanish at that point.** This is the local flatness argument of
[Stacks, Tag 0EX8]: were `s` to vanish at `x`, the zero scheme of `s` would be flat over `A`
near `x` (Stacks 062Y), and flatness would carry its point `x` of the closed fibre to a point of
the generic fibre at which `s` vanishes. -/
theorem mem_nonvanishingLocus_of_not_mem [ValuationRing A] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤))
    (hgen : ∀ y : X, f y = genericPoint (Spec (.of A)) → y ∈ Stacks.Ample.nonvanishingLocus L s)
    (x : X)
    (hdom : IsDomain (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)))))
    (hx : (L.presheaf.Γgerm x).hom s ∉
      (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)))) •
        (⊤ : Submodule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x))) :
    x ∈ Stacks.Ample.nonvanishingLocus L s := by
  by_contra hxN
  obtain ⟨U, V, hU, hxU, hUV, ⟨t₀⟩⟩ := exists_affineOpen_trivialization L x
  let t := t₀.comp (homOfLE hUV)
  set c : Γ(X, U) := Stacks.NonvanishingOpen.trivTop t s
  have hcI : X.presheaf.germ U x hxU c ∉ Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x))) :=
    fun h => hx ((Γgerm_mem_smul_top_iff f L s t le_rfl hxU).2 h)
  have hreg : IsSMulRegular
      (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x))))
      (Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x))))
        ((X.presheaf.germ U x hxU).hom c)) :=
    (IsRegular.of_ne_zero' (fun h => hcI (Ideal.Quotient.eq_zero_iff_mem.1 h))).left
  -- the closed subscheme cut out by the closure of `x`
  let Z := Scheme.IdealSheafData.vanishingIdeal (⟨closure {x}, isClosed_closure⟩ : Closeds X)
  have hxZ : x ∈ Z.support := by
    change x ∈ (Z.support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact subset_closure rfl
  have hxb : x ∉ X.basicOpen c := fun h =>
    hxN ((Set.ext_iff.1 (Stacks.NonvanishingOpen.nonvanishingLocus_inter t s) x).2 h).1
  obtain ⟨W, hW, V', hV', hV'W, hV'U, hxV', a, ha, hareg, hflat⟩ :=
    Stacks.Divisors.exists_affineOpen_isRegular_flat_quotient_of_mem_ideal f Z x hxZ hU hxU c
      (mem_vanishingIdeal_closure_of_notMem_basicOpen hU hxb) hreg
  -- the point `x`, as a prime of the quotient
  have hxa : x ∉ X.basicOpen a := by
    rw [ha, Scheme.basicOpen_res]
    exact fun h => hxb h.2
  have haq : a ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
    by_contra h
    exact hxa ((hV'.mem_basicOpen_iff_notMem_primeIdealOf a hxV').2 h)
  have hηx : genericPoint (Spec (.of A)) ⤳ f x :=
    (genericPoint_spec (Spec (.of A))).specializes (Set.mem_univ _)
  obtain ⟨y, hyV', hfy, hya⟩ :=
    exists_mem_primeIdealOf_of_flat_quotient f hW hV' hV'W hflat hxV' haq hηx
  -- `s` does not vanish at `y`, yet `a` lies in the prime of `y`
  refine (hV'.mem_basicOpen_iff_notMem_primeIdealOf a hyV').1 ?_ hya
  rw [ha, Scheme.basicOpen_res]
  exact ⟨hyV', (Set.ext_iff.1 (Stacks.NonvanishingOpen.nonvanishingLocus_inter t s) y).1
    ⟨hgen y hfy, hV'U hyV'⟩⟩

/-- **The global sections of a module flat over a valuation ring are free, once finite.** They
are torsion-free (`eq_zero_of_appLE_smul_eq_zero`), hence flat over the Bézout domain `A`, and a
finite flat module over a local ring is free. -/
@[sga "3 VIB 12.8" "special case"]
theorem free_sections_of_isFlatOver [ValuationRing A] (L : X.Modules)
    (hflat : IsFlatOver f.toLRSHom.toShHom L) :
    letI : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
    Module.Finite A Γ(L, ⊤) → Module.Free A Γ(L, ⊤) := by
  let : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
  intro hfin
  have : Module.Flat A Γ(L, ⊤) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro m ⟨⟨a, ha⟩, hm⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change (Stacks.Cech.globalRingHom f).hom a • m = 0 at hm
    refine eq_zero_of_appLE_smul_eq_zero f L hflat ((Scheme.ΓSpecIso (.of A)).inv a)
      (fun h => ha0 ?_) m ?_
    · simpa using congrArg (Scheme.ΓSpecIso (.of A)).hom h
    · convert hm using 2
      change (f.appLE ⊤ (f ⁻¹ᵁ ⊤) le_rfl).hom _ = _
      rw [Scheme.Hom.appLE_eq_app]
      rfl
  exact Module.free_of_flat_of_isLocalRing

/-- A unit global function, as a section of `𝒪_X`, vanishes nowhere. -/
theorem mem_nonvanishingLocus_unitModule_of_isUnit {Y : Scheme.{u}}
    (c : Γ(Stacks.Ample.unitModule Y, ⊤)) (hc : IsUnit (show Γ(Y, ⊤) from c)) (y : Y) :
    y ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.unitModule Y) c := by
  intro h
  have hm := Stacks.Ample.mem_maximalIdeal_of_mem_maximalSmul Y y h
  rw [Stacks.Ample.unitStalkFun_Γgerm] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm (hc.map _)

/-- A nonzero global function on the spectrum of a field is a unit. -/
private theorem isUnit_Γ_Spec_of_ne_zero (K : Type u) [Field K] {κ : Γ(Spec (.of K), ⊤)}
    (hκ : κ ≠ 0) : IsUnit κ := by
  have h1 : (Scheme.ΓSpecIso (.of K)).hom κ ≠ 0 := fun h => hκ (by
    simpa using congrArg (Scheme.ΓSpecIso (.of K)).inv h)
  simpa using (Ne.isUnit h1).map (Scheme.ΓSpecIso (.of K)).inv.hom

/-- If `Γ(Spec K, 𝒪) → Γ(Y, 𝒪)` is bijective for a field `K`, then every nonzero global function
on `Y` is a unit. -/
private theorem isUnit_of_bijective_appTop (K : Type u) [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (hΓ : Function.Bijective g.appTop.hom) {c : Γ(Y, ⊤)} (hc : c ≠ 0) :
    IsUnit c := by
  obtain ⟨κ, rfl⟩ := hΓ.2 c
  exact (isUnit_Γ_Spec_of_ne_zero K fun h => hc (by rw [h, map_zero])).map _

/-- If `Γ(Spec K, 𝒪) → Γ(Y, 𝒪)` is bijective for a field `K`, then `Γ(Y, 𝒪)` is nontrivial. -/
private theorem one_ne_zero_of_bijective_appTop (K : Type u) [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (hΓ : Function.Bijective g.appTop.hom) : (1 : Γ(Y, ⊤)) ≠ 0 := by
  intro h
  have h' : g.appTop.hom 1 = g.appTop.hom 0 := by
    rwa [map_one, map_zero]
  have := hΓ.1 h'
  exact one_ne_zero (α := Γ(Spec (.of K), ⊤)) (by
    simpa using congrArg (Scheme.ΓSpecIso (.of K)).hom this)

/-- Every point of `X` over the generic point of `Spec A` lies on the generic fibre. -/
private theorem mem_range_fst_of_eq_genericPoint (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] {y : X} (hy : f y = genericPoint (Spec (.of A))) :
    y ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))) := by
  rw [Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint K, ?_⟩
  rw [hy, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap A K) (IsLocalRing.maximalIdeal K) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective A K)

omit [IsDomain A] in
/-- The pullback of a global section of `L` to the generic fibre, read as a global function
through a trivialization `ε`. -/
private noncomputable abbrev genericFibreSection (K : Type u) [Field K] [Algebra A K]
    (L : X.Modules)
    (ε : (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap A K))))).obj L ≅ Stacks.Ample.unitModule _) :
    Γ(L, ⊤) →+ Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K))), ⊤) :=
  (ε.hom.app ⊤).hom.comp (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))) L ⊤)

omit [IsDomain A] in
/-- The pullback to the generic fibre of a global section of `L`, read through a trivialization
`ε`, lies in the ideal spanned by the pullbacks of a basis of `Γ(X, L)`. -/
private theorem pullback_mem_span_pullback_basis (K : Type u) [Field K] [Algebra A K]
    (L : X.Modules)
    (ε : (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap A K))))).obj L ≅ Stacks.Ample.unitModule _)
    {ι : Type u} [Finite ι]
    (b : letI : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
      Module.Basis ι A Γ(L, ⊤)) (a : Γ(L, ⊤)) :
    genericFibreSection f K L ε a ∈
      Ideal.span (Set.range fun i => genericFibreSection f K L ε (b i)) := by
  classical
  let := Fintype.ofFinite ι
  let : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have hψsmul : ∀ (r : A) (a : Γ(L, ⊤)), ∃ l : Γ(pullback f g, ⊤),
      genericFibreSection f K L ε (r • a) = l * genericFibreSection f K L ε a := by
    intro r a
    refine ⟨(pullback.fst f g).app ⊤ ((Stacks.Cech.globalRingHom f).hom r), ?_⟩
    change ε.hom.app (pullback.fst f g ⁻¹ᵁ ⊤)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections
      (pullback.fst f g) L ⊤ ((Stacks.Cech.globalRingHom f).hom r • a)) = _
    rw [Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_smul,
      Scheme.Modules.Hom.app_smul]
    rfl
  rw [← b.sum_repr a, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨l, hl⟩ := hψsmul (b.repr a i) (b i)
  rw [hl]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

omit [IsDomain A] in
/-- **The pullbacks of a basis span the unit ideal on the generic fibre.** By flat base change
([Stacks, Tag 02KH] in degree zero), the pullbacks of a basis of `Γ(X, L)`, read through a
trivialization `ε`, generate `Γ(X_K, 𝒪)` as an ideal. -/
private theorem one_mem_span_pullback_basis (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] [IsProper f] (L : X.Modules) [L.IsQuasicoherent]
    (ε : (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap A K))))).obj L ≅ Stacks.Ample.unitModule _)
    {ι : Type u} [Finite ι]
    (b : letI : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
      Module.Basis ι A Γ(L, ⊤)) :
    (1 : Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K))), ⊤)) ∈
      Ideal.span (Set.range fun i => genericFibreSection f K L ε (b i)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have H := IsPullback.of_hasPullback f g
  have : Flat g := Flat.SpecMap_iff.2
    ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat K (nonZeroDivisors A)))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let := Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra g
  let := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule f L ⊤
  let := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule (pullback.fst f g ≫ f)
    ((Scheme.Modules.pullback (pullback.fst f g)).obj L) ⊤
  let := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule (pullback.snd f g)
    ((Scheme.Modules.pullback (pullback.fst f g)).obj L) ⊤
  have := Stacks.AlgebraicGeometry.SectionsBaseChange.baseTower H
    ((Scheme.Modules.pullback (pullback.fst f g)).obj L) ⊤
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange H L
  let χ : (TensorProduct Γ(Spec (.of A), ⊤) Γ(Spec (.of K), ⊤) Γ(L, ⊤)) →+
      Γ(pullback f g, ⊤) :=
    (ε.hom.app ⊤).hom.comp e.toLinearMap.toAddMonoidHom
  have hχ : ∀ (β : Γ(Spec (.of K), ⊤)) (a : Γ(L, ⊤)), ∃ l : Γ(pullback f g, ⊤),
      χ (β ⊗ₜ a) = l * genericFibreSection f K L ε a := by
    intro β a
    refine ⟨((pullback.snd f g).appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom β, ?_⟩
    change ε.hom.app ⊤ (e (β ⊗ₜ a)) = _
    rw [he β a]
    change ε.hom.app ⊤
        (((pullback.snd f g).appLE ⊤ ⊤ _).hom β •
          Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom (pullback.fst f g) L ⊤ ⊤
            _ a) = _
    rw [Scheme.Modules.Hom.app_smul,
      Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom_top]
    rfl
  let one' : Γ(Stacks.Ample.unitModule (pullback f g), ⊤) := (1 : Γ(pullback f g, ⊤))
  obtain ⟨z, hz⟩ : ∃ z, χ z = 1 := ⟨e.symm (ε.inv.app ⊤ one'), by
    change ε.hom.app ⊤ (e (e.symm _)) = _
    rw [LinearEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl⟩
  rw [← hz]
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul β a =>
    obtain ⟨l, hl⟩ := hχ β a
    rw [hl]
    exact Ideal.mul_mem_left _ _ (pullback_mem_span_pullback_basis f K L ε b a)
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add]
    exact Ideal.add_mem _ h₁ h₂

/-- **A basis section vanishing nowhere over the generic point.** Let `K` be the fraction field of
`A` and `X_K` the generic fibre. If `L` is trivial on `X_K` and `K = Γ(X_K, 𝒪)`, then some member
of any basis of `Γ(X, L)` over `A` vanishes at no point of `X` over the generic point of
`Spec A`. By flat base change ([Stacks, Tag 02KH] in degree zero), the pullbacks of the basis
span `Γ(X_K, L_K) ≅ Γ(X_K, 𝒪) = K`, so one of them is a nonzero constant times a trivializing
section. -/
theorem exists_basis_mem_nonvanishingLocus [ValuationRing A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K] [IsProper f] (L : X.Modules) [L.IsQuasicoherent]
    (ε : (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap A K))))).obj L ≅ Stacks.Ample.unitModule _)
    (hΓ : Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K)))).appTop.hom)
    {ι : Type u} [Finite ι]
    (b : letI : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
      Module.Basis ι A Γ(L, ⊤)) :
    ∃ i, ∀ y : X, f y = genericPoint (Spec (.of A)) →
      y ∈ Stacks.Ample.nonvanishingLocus L (b i) := by
  obtain ⟨i, hi⟩ : ∃ i, genericFibreSection f K L ε (b i) ≠ 0 := by
    by_contra! hcon
    have h1J := one_mem_span_pullback_basis f K L ε b
    rw [Ideal.span_eq_bot.2 ((Set.forall_mem_range (p := (· = 0))).2 hcon), Ideal.mem_bot] at h1J
    exact one_ne_zero_of_bijective_appTop K _ hΓ h1J
  let g := Spec.map (CommRingCat.ofHom (algebraMap A K))
  refine ⟨i, fun y hy => ?_⟩
  -- the pulled-back basis section vanishes nowhere on the generic fibre
  have hpN : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback (pullback.fst f g)).obj L)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections (pullback.fst f g) L ⊤
        (b i)) = Set.univ :=
    (Stacks.Ample.nonvanishingLocus_congr ε _).symm.trans (Set.eq_univ_of_forall fun y' =>
      mem_nonvanishingLocus_unitModule_of_isUnit _ (isUnit_of_bijective_appTop K _ hΓ hi) y')
  have hpre := Stacks.NonvanishingPullback.preimage_nonvanishingLocus (pullback.fst f g) L (b i)
  change (pullback.fst f g).base ⁻¹' _ = Stacks.Ample.nonvanishingLocus
    ((Scheme.Modules.pullback (pullback.fst f g)).obj L)
      (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections (pullback.fst f g) L ⊤
        (b i)) at hpre
  rw [hpN] at hpre
  -- every point over the generic point comes from the generic fibre
  obtain ⟨y', rfl⟩ := mem_range_fst_of_eq_genericPoint f K hy
  exact Set.eq_univ_iff_forall.1 hpre y'

section Finiteness

attribute [local instance 10000] HasDerivedCategory.standard

omit [IsDomain A] in
/-- An invertible module on a scheme is finite locally free of rank one, quasi-coherent, of
finite presentation and, over a flat base, flat over the base. -/
theorem isFlatOver_and_isFinitePresentation_of_isInvertible [Flat f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    L.IsQuasicoherent ∧ L.IsFinitePresentation ∧ IsFlatOver f.toLRSHom.toShHom L := by
  have hL1 := Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (X := X.toRingedSpace) L
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have : L.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree L
  have htf := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae L).out 4 1
  exact ⟨inferInstance, (htf.mp inferInstance).2,
    VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f L⟩

/-- **The global sections of an invertible module on a proper flat scheme of finite presentation
over a valuation ring form a finite module**, by [Stacks, Tag 0A1H]: `RΓ(X, L)` is
perfect ([Stacks, Tag 0B91]), so its cohomology is coherent ([Stacks, Tag 0EX6]). -/
theorem finite_sections_of_isInvertible
    [ValuationRing A] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
    Module.Finite A Γ(L, ⊤) := by
  obtain ⟨hqc, hfpL, hflat⟩ := isFlatOver_and_isFinitePresentation_of_isInvertible f L
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hperf : StacksDraft.Perfect.IsPerfect
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase f L) := by
    refine isPerfect_derivedGlobalSectionsOverBase_of_isPerfect_derivedPushforward f L ?_
    exact Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app L))
      (isPerfect_derivedPushforward_module f hfp inferInstance L hfpL hflat)
  have hsupp : ∃ Z : TopologicalSpace.Closeds X,
      (Z : Set X) = SheafOfModules.supp L ∧ IsProperOver f Z := by
    refine ⟨⊤, ?_, Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper f⟩
    ext x
    simp only [TopologicalSpace.Closeds.coe_top, Set.mem_univ, true_iff]
    obtain ⟨U, V, -, hxU, hUV, ⟨t⟩⟩ := exists_affineOpen_trivialization L x
    exact ⟨(L.presheaf.germ V x (hUV hxU)).hom (Stacks.NonvanishingOpen.basis t), fun h =>
      Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis t (hUV hxU)
        (h ▸ Submodule.zero_mem _)⟩
  have hcoh := isCoherent_cohomology_of_isPerfect_derivedGlobalSections f L hflat hsupp hperf 0
  have e := (ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).mapIso
    ((moduleGlobalSections X).rightDerivedZeroIsoSelf.app L)
  let : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
  have := Module.IsCoherent.finite (R := A) (M := ((ModuleCat.restrictScalars
    (Stacks.Cech.globalRingHom f).hom).obj (((moduleGlobalSections X).rightDerived 0).obj L)))
  exact Module.Finite.equiv e.toLinearEquiv

/-- Over a valuation ring, every point of a proper scheme specializes to a point of the closed
fibre. -/
private theorem exists_specializes_closedPoint_of_isProper [ValuationRing A] [IsProper f] (y : X) :
    ∃ c : X, y ⤳ c ∧ f c = IsLocalRing.closedPoint A := by
  have hcl : IsClosed (f.base '' closure {y}) := f.isClosedMap _ isClosed_closure
  obtain ⟨c, hc, hcm⟩ :=
    (IsLocalRing.specializes_closedPoint (f y)).mem_closed hcl ⟨y, subset_closure rfl, rfl⟩
  exact ⟨c, specializes_iff_mem_closure.2 hc, hcm⟩

/-- **On an integral fibre, membership of the germ of a section in `𝔪 · L` does not depend on the
point.** For points `x` and `ξ ⤳ x` of an integral fibre, the germ of `s` lies in the submodule
generated by the maximal ideal of the base at `x` exactly when it does at `ξ`. -/
private theorem Γgerm_mem_smul_top_iff_of_isIntegral [ValuationRing A] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (s : Γ(L, ⊤))
    (m : Spec (.of A)) [IsIntegral (f.fiber m)] {x ξ : X} (hx : f x = m) (hξm : f ξ = m)
    (hξx : ξ ⤳ x) :
    (L.presheaf.Γgerm x).hom s ∈ (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)))) •
        (⊤ : Submodule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x)) ↔
      (L.presheaf.Γgerm ξ).hom s ∈ (Ideal.map (f.stalkMap ξ).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f ξ)))) •
        (⊤ : Submodule (X.presheaf.stalk ξ)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf ξ)) := by
  obtain ⟨U, V, -, hxU, hUV, ⟨t⟩⟩ := exists_affineOpen_trivialization L x
  have hξU : ξ ∈ U := hξx.mem_open U.2 hxU
  rw [Γgerm_mem_smul_top_iff f L s t hUV hxU, Γgerm_mem_smul_top_iff f L s t hUV hξU]
  exact germ_mem_map_maximalIdeal_iff_of_isIntegral f m hx hξm hxU hξU _

/-- **A basis element is not divisible on the closed fibre.** If at every point of the closed
fibre the germ of a basis element of `Γ(X, L)` lay in `𝔪_A · L`, then the basis element would be
globally divisible by a non-unit of `A`, which it is not. -/
private theorem not_forall_Γgerm_mem_smul_top_of_basis [ValuationRing A] [IsProper f]
    (L : X.Modules)
    (hflat : IsFlatOver f.toLRSHom.toShHom L) {ι : Type*}
    (b : letI : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
      Module.Basis ι A Γ(L, ⊤)) (i : ι)
    (H : ∀ x : X, f x = IsLocalRing.closedPoint A →
      (L.presheaf.Γgerm x).hom (b i) ∈ (Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)))) •
        (⊤ : Submodule (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x))) : False := by
  let : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
  set m : Spec (.of A) := IsLocalRing.closedPoint A
  set P := ((isAffineOpen_top (Spec (.of A))).primeIdealOf ⟨m, trivial⟩).asIdeal
  have H' : ∀ x ∈ f.base ⁻¹' {m}, ∃ (W : X.Opens) (_ : x ∈ W) (r : Γ(Spec (.of A), ⊤)),
      r ∈ P ∧ ∃ t : Γ(L, W), resF L le_top (b i) = (f.appLE ⊤ W (le_preimage_top f W) r) • t := by
    intro x hx
    obtain ⟨W, hxW, r, hr, t, ht⟩ := exists_res_eq_smul_of_germ_mem f L (b i) x (H x hx)
    have hpt : (⟨f x, trivial⟩ : (⊤ : (Spec (.of A)).Opens)) = ⟨m, trivial⟩ := Subtype.ext hx
    rw [hpt] at hr
    exact ⟨W, hxW, r, hr, t, ht⟩
  obtain ⟨r, hrP, t, hst⟩ := exists_eq_smul_of_forall_mem f L hflat (b i) P (f.base ⁻¹' {m})
    (f.isCompact_preimage_singleton m)
    (fun y => (exists_specializes_closedPoint_of_isProper f y).elim fun c hc => ⟨c, hc.2, hc.1⟩) H'
  set a : A := (Scheme.ΓSpecIso (.of A)).hom r
  have hsa : b i = a • t := by
    rw [hst]
    change _ = (Stacks.Cech.globalRingHom f).hom a • t
    congr 1
    change (f.appLE ⊤ (f ⁻¹ᵁ ⊤) le_rfl).hom r = _
    rw [Scheme.Hom.appLE_eq_app]
    change _ = (f.appTop).hom ((Scheme.ΓSpecIso (.of A)).inv a)
    simp only [a, ← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply]
    rfl
  have h1 := congrArg (fun z => b.repr z i) hsa
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h1
  have hua : IsUnit a := IsUnit.of_mul_eq_one _ h1.symm
  have hur : IsUnit r := by
    simpa [a] using hua.map (Scheme.ΓSpecIso (.of A)).inv.hom
  exact ((isAffineOpen_top (Spec (.of A))).primeIdealOf ⟨m, trivial⟩).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hrP hur)

/-- **[Stacks, Tag 0EX8].** Let `f : X ⟶ Spec A` be a proper flat
morphism of finite presentation over a valuation ring `A` with fraction field `K`, and let `L` be
an invertible `𝒪_X`-module. Assume that `L` is trivial on the generic fibre `X_K`, that the closed
fibre is integral, and that `K = H⁰(X_K, 𝒪_{X_K})`. Then `L` is trivial. -/
@[stacks 0EX8]
theorem isTrivial_of_isTrivial_genericFiber
    [ValuationRing A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hgen : SheafOfModules.IsTrivial
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K)))).presheaf
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A K)))).ringCatSheaf.2
      ((modulePullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap A K)))).toLRSHom.toShHom).obj L))
    [IsIntegral (f.fiber (IsLocalRing.closedPoint A))]
    (hΓ : Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A K)))).appTop.hom) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.2 L := by
  obtain ⟨hqc, hfpL, hflat⟩ := isFlatOver_and_isFinitePresentation_of_isInvertible f L
  let : Module A Γ(L, ⊤) := Module.compHom _ (Stacks.Cech.globalRingHom f).hom
  have hfin := finite_sections_of_isInvertible f L
  have := free_sections_of_isFlatOver f L hflat hfin
  let b := Module.Free.chooseBasis A Γ(L, ⊤)
  obtain ⟨ε⟩ := hgen
  obtain ⟨i, hgen'⟩ := exists_basis_mem_nonvanishingLocus f K L ε hΓ b
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  set m : Spec (.of A) := IsLocalRing.closedPoint A
  -- the generic point of the closed fibre
  set ξ : X := f.fiberι m (genericPoint (f.fiber m))
  have hξm : f ξ = m := by
    have : ξ ∈ Set.range (f.fiberι m) := ⟨_, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at this
  have hξx : ∀ x : X, f x = m → ξ ⤳ x := by
    intro x hx
    obtain ⟨x', rfl⟩ : x ∈ Set.range (f.fiberι m) := by rwa [Scheme.Hom.range_fiberι]
    exact ((genericPoint_spec (f.fiber m)).specializes (Set.mem_univ x')).map
      (f.fiberι m).continuous
  -- the closed fibre lies in the nonvanishing locus
  have hX0 : ∀ x : X, f x = m → x ∈ Stacks.Ample.nonvanishingLocus L (b i) := by
    by_cases hξs : (L.presheaf.Γgerm ξ).hom (b i) ∈ (Ideal.map (f.stalkMap ξ).hom
        (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f ξ)))) •
        (⊤ : Submodule (X.presheaf.stalk ξ) (TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf ξ))
    · -- `s` would be divisible by a non-unit of `A`
      exact (not_forall_Γgerm_mem_smul_top_of_basis f L hflat b i fun x hx =>
        (Γgerm_mem_smul_top_iff_of_isIntegral f L (b i) m hx hξm (hξx x hx)).2 hξs).elim
    · intro x hx
      have hdom : IsDomain (X.presheaf.stalk x ⧸ Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)))) := by
        have : IsIntegral (f.fiber (f x)) := by rw [hx]; infer_instance
        exact MulEquiv.isDomain _ (quotientStalkEquivFiberStalk f x).toMulEquiv
      exact mem_nonvanishingLocus_of_not_mem f L (b i) hgen' x hdom fun h =>
        hξs ((Γgerm_mem_smul_top_iff_of_isIntegral f L (b i) m hx hξm (hξx x hx)).1 h)
  -- hence everywhere, every point specializing into the closed fibre
  have hN : Stacks.Ample.nonvanishingLocus L (b i) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨c, hyc, hc⟩ := exists_specializes_closedPoint_of_isProper f y
    exact hyc.mem_open (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X L (b i)) (hX0 c hc)
  refine isTrivial_of_nonvanishingLocus_eq_univ L (Stacks.SheafOfModules.sectionsOfTop L (b i)) ?_
  rwa [nonvanishingLocus_sectionsOfTop_eq]

end Finiteness

end AlgebraicGeometry.ValuativeTriviality

end
