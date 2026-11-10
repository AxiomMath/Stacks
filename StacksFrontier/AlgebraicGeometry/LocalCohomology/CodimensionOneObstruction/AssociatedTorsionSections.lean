module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPoleLocus
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.QuasicoherentSections

/-!
# Torsion sections at an associated point

Let `X` be a locally Noetherian scheme, `V₀` an affine open, `F` a quasi-coherent `𝒪_X`-module
and `x ∈ Ass(F)` a point of `V₀`. Write `p_x ⊆ Γ(X, V₀)` for the prime of `x`, so that `V(p_x)` is
the closure `X'` of `x` inside `V₀`. For an open `S ≤ V₀` containing `x` this file studies the
sections of `F` over `S` annihilated by `p_x`, the sections "living on `X'`", in the situation of
the first paragraph of [Stacks, Tag 0AWC].

## Main results

* `exists_section_smul_eq_zero_of_isAssociatedPoint`, in the namespace
  `Stacks.AlgebraicGeometry.CodimensionOneObstruction`: from `x ∈ Ass(F)` there is a section of
  `F` over `S` killed by `p_x` whose germ at `x` is nonzero. Together with
  `germ_mem_maximalIdeal_of_smul_eq_zero` this exhibits `𝒪_{X'}` inside `F` at the level of
  sections over the (possibly non-affine) `S`.
* `exists_section_smul_eq_smul_of_notMem_primeIdealOf`, in the same namespace: such sections
  can be divided by any function not vanishing at `x`, up to a function not vanishing at `z`,
  provided `z` lies in the closure of `x`, `S` avoids `z`, and `dim 𝒪_{X', z} ≤ 1`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.QcqsLocalization

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {X : Scheme.{u}}

/-! ### A torsion section with nonzero germ at an associated point -/

/-- A function killing a section whose germ at `x` is nonzero vanishes at `x`. -/
theorem germ_mem_maximalIdeal_of_smul_eq_zero (F : X.Modules) {S : X.Opens} {x : X}
    (hxS : x ∈ S) {m : Γ(F, S)} (hm : germAt F S x hxS m ≠ 0) {a : Γ(X, S)}
    (ha : a • m = 0) :
    X.presheaf.germ S x hxS a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  by_contra hu
  rw [IsLocalRing.notMem_maximalIdeal] at hu
  have hu' : IsUnit (ringGermAt X S x hxS a) := hu
  refine hm (hu'.smul_eq_zero.mp ?_)
  rw [← germAt_smul' F hxS a m, ha]
  exact germAt_zero F hxS

/-- A vector killed by the image of every element of a set is killed by the image of every element
of its span. -/
private theorem smul_eq_zero_of_mem_span {R S M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [Module S M] (φ : R →+* S) {T : Set R} {m : M} {a : R}
    (ha : a ∈ Ideal.span T) (h : ∀ a ∈ T, φ a • m = 0) : φ a • m = 0 := by
  induction ha using Submodule.span_induction with
  | mem a haT => exact h a haT
  | zero => rw [map_zero, zero_smul]
  | add a b _ _ ha hb => rw [map_add, add_smul, ha, hb, add_zero]
  | smul r a _ ha => rw [smul_eq_mul, map_mul, mul_smul, ha, smul_zero]

/-- The restriction of a function to an open contained in its basic open is a unit. -/
private theorem isUnit_res_of_le_basicOpen {V W : X.Opens} {a : Γ(X, V)} (hWa : W ≤ X.basicOpen a)
    (hWV : W ≤ V) : IsUnit (X.presheaf.map (homOfLE hWV).op a) := by
  have h1 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  have h2 := (X.presheaf.map (homOfLE hWa).op).hom.isUnit_map h1
  rwa [presheaf_map_map hWa (X.basicOpen_le a) hWV a] at h2

/-- **From an associated point to a torsion section over a non-affine open.** Let `X` be locally
Noetherian, `V₀` an affine open, `F` a quasi-coherent `𝒪_X`-module, `x ∈ Ass(F)` a point of `V₀`,
and `S` any open of `X` with `x ∈ S ≤ V₀`. Then `F` has a section `m` over `S` whose germ at `x`
is nonzero and which is annihilated by the restriction to `S` of every function on `V₀` vanishing
at `x`. -/
theorem exists_section_smul_eq_zero_of_isAssociatedPoint [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (F : X.Modules) [F.IsQuasicoherent] {x : X}
    (hx : x ∈ V₀) (hass : Stacks.Divisors.IsAssociatedPoint F x)
    {S : X.Opens} (hSV : S ≤ V₀) (hxS : x ∈ S) :
    ∃ m : Γ(F, S), germAt F S x hxS m ≠ 0 ∧
      ∀ a ∈ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal,
        X.presheaf.map (homOfLE hSV).op a • m = 0 := by
  classical
  obtain ⟨W, hW, hxW, hWS : W ≤ S⟩ := exists_isAffineOpen_mem_and_subset hxS
  have hWV : W ≤ V₀ := hWS.trans hSV
  have hnV : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  obtain ⟨-, mW, hmW⟩ :=
    (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F W hW hxW).mpr hass
  have hmWne : germAt F W x hxW mW ≠ 0 := fun h0 => by
    obtain ⟨r, hr, hrm⟩ := (germ_eq_zero_iff_exists_smul_eq_zero_affine F W hW x hxW mW).mp h0
    rw [← hmW] at hr
    exact hr (Submodule.mem_colon_span_singleton.mpr (by simpa using hrm))
  obtain ⟨h, hhW, hxh⟩ := hV₀.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
  set hS : Γ(X, S) := X.presheaf.map (homOfLE hSV).op h with hhS
  have hbas : X.basicOpen hS = X.basicOpen h := by
    rw [hhS, Scheme.basicOpen_res]
    exact inf_eq_right.mpr (hhW.trans hWS)
  have hsubW : X.basicOpen hS ≤ W := hbas ▸ hhW
  have hsubV : X.basicOpen hS ≤ V₀ := hsubW.trans hWV
  have hxbas : x ∈ X.basicOpen hS := hbas ▸ hxh
  have hcpt : IsCompact (S : Set X) := isCompact_of_le_isAffineOpen hV₀ hSV
  obtain ⟨n, y, hy⟩ := exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated F hcpt
    ((isQuasiSeparated_univ (α := X)).of_subset (Set.subset_univ _)) hS
    (F.presheaf.map (homOfLE hsubW).op mW)
  have hunit : IsUnit (ringGermAt X S x hxS hS) := (X.mem_basicOpen hS x hxS).mp hxbas
  have hgermy : germAt F S x hxS y = ringGermAt X S x hxS hS ^ n • germAt F W x hxW mW := by
    have h0 := congrArg (germAt F (X.basicOpen hS) x hxbas) hy
    have h1 : ringGermAt X (X.basicOpen hS) x hxbas
        (X.presheaf.map (homOfLE (X.basicOpen_le hS)).op hS ^ n)
        = ringGermAt X (X.basicOpen hS) x hxbas
            (X.presheaf.map (homOfLE (X.basicOpen_le hS)).op hS) ^ n := map_pow _ _ _
    rwa [germAt_map F (X.basicOpen_le hS) hxbas y, germAt_smul' F hxbas _ _, h1,
      ringGermAt_map (X.basicOpen_le hS) hxbas hS, germAt_map F hsubW hxbas mW] at h0
  have hyne : germAt F S x hxS y ≠ 0 := by
    rw [hgermy]
    exact fun h0 => hmWne ((hunit.pow n).smul_eq_zero.mp h0)
  set p := (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal
  have hkillW : ∀ a ∈ p, X.presheaf.map (homOfLE hWV).op a • mW = 0 := by
    intro a ha
    have hresmem : X.presheaf.map (homOfLE hWV).op a ∈ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      rw [mem_primeIdealOf_iff_germ_mem_maximalIdeal hW hxW,
        TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hWV) x hxW a]
      exact (mem_primeIdealOf_iff_germ_mem_maximalIdeal hV₀ hx a).mp ha
    rw [← hmW] at hresmem
    simpa using Submodule.mem_colon_span_singleton.mp hresmem
  have hzeroD : ∀ a ∈ p, F.presheaf.map (homOfLE (X.basicOpen_le hS)).op
      (X.presheaf.map (homOfLE hSV).op a • y) = 0 := by
    intro a ha
    have e1 : F.presheaf.map (homOfLE (X.basicOpen_le hS)).op
        (X.presheaf.map (homOfLE hSV).op a • y)
        = X.presheaf.map (homOfLE (X.basicOpen_le hS)).op (X.presheaf.map (homOfLE hSV).op a)
          • F.presheaf.map (homOfLE (X.basicOpen_le hS)).op y := F.map_smul _ _ _
    have e2 : X.presheaf.map (homOfLE (X.basicOpen_le hS)).op
        (X.presheaf.map (homOfLE hSV).op a) = X.presheaf.map (homOfLE hsubV).op a :=
      presheaf_map_map (X.basicOpen_le hS) hSV hsubV a
    have e3 : X.presheaf.map (homOfLE hsubV).op a
        = X.presheaf.map (homOfLE hsubW).op (X.presheaf.map (homOfLE hWV).op a) :=
      (presheaf_map_map hsubW hWV hsubV a).symm
    have e4 : X.presheaf.map (homOfLE hsubV).op a
          • F.presheaf.map (homOfLE hsubW).op mW = 0 := by
      have e5 : X.presheaf.map (homOfLE hsubW).op (X.presheaf.map (homOfLE hWV).op a)
            • F.presheaf.map (homOfLE hsubW).op mW
          = F.presheaf.map (homOfLE hsubW).op (X.presheaf.map (homOfLE hWV).op a • mW) :=
        (F.map_smul _ _ _).symm
      rw [e3, e5, hkillW a ha, map_zero]
    rw [e1, e2, hy, smul_comm, e4, smul_zero]
  obtain ⟨T, hT⟩ := Ideal.FG.of_isNoetherianRing p
  have hpow : ∀ a ∈ p, ∃ k : ℕ, hS ^ k • (X.presheaf.map (homOfLE hSV).op a • y) = 0 :=
    fun a ha => exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact F hcpt hS rfl
      (X.basicOpen_le hS) _ (hzeroD a ha)
  choose! k hk using hpow
  set N := T.sup k
  refine ⟨hS ^ N • y, ?_, ?_⟩
  · rw [germAt_smul' F hxS,
      show ringGermAt X S x hxS (hS ^ N) = ringGermAt X S x hxS hS ^ N from map_pow _ _ _]
    exact fun h0 => hyne ((hunit.pow N).smul_eq_zero.mp h0)
  · have hgen : ∀ a ∈ T, X.presheaf.map (homOfLE hSV).op a • (hS ^ N • y) = 0 := by
      intro a haT
      have hka : k a ≤ N := Finset.le_sup haT
      rw [smul_comm, ← pow_sub_mul_pow hS hka, mul_smul,
        hk a (by rw [← hT]; exact Ideal.subset_span haT), smul_zero]
    exact fun a ha => smul_eq_zero_of_mem_span _ (hT ▸ ha) hgen

/-! ### Dividing a torsion section by a function not vanishing at `x` -/

/-- A section killed by a function `a` restricts to zero on any open where `a` is invertible. -/
theorem res_eq_zero_of_le_basicOpen (F : X.Modules) {V₀ S W : X.Opens} (hSV : S ≤ V₀)
    (hWS : W ≤ S) {a : Γ(X, V₀)} (hWa : W ≤ X.basicOpen a) {w : Γ(F, S)}
    (hw : X.presheaf.map (homOfLE hSV).op a • w = 0) :
    F.presheaf.map (homOfLE hWS).op w = 0 := by
  have hWV : W ≤ V₀ := hWS.trans hSV
  have hu := isUnit_res_of_le_basicOpen hWa hWV
  have e1 : F.presheaf.map (homOfLE hWS).op (X.presheaf.map (homOfLE hSV).op a • w)
      = X.presheaf.map (homOfLE hWS).op (X.presheaf.map (homOfLE hSV).op a)
        • F.presheaf.map (homOfLE hWS).op w := F.map_smul _ _ _
  rw [hw, map_zero, presheaf_map_map hWS hSV hWV a] at e1
  exact hu.smul_eq_zero.mp e1.symm

/-- Restriction of sections of a module is semilinear over restriction of functions, along an
inclusion `V ≤ U`. -/
theorem res_smul (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (t : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op (a • t)
      = X.presheaf.map (homOfLE h).op a • F.presheaf.map (homOfLE h).op t :=
  F.map_smul _ _ _

/-- **Division of a torsion section by a function not vanishing at `x`.** In the situation of
[Stacks, Tag 0AWC] — `V₀` an affine open of a locally Noetherian `X`, `x` a point of `V₀` whose
closure contains a point `z` of `V₀` with `dim 𝒪_{closure x, z} ≤ 1`, and `S ≤ V₀` an open
avoiding `z` — let `w` be a section over `S` of a quasi-coherent `F`, annihilated by every
function on `V₀` vanishing at `x`. Then for every `s : Γ(X, V₀)` not vanishing at `x` there are a
section `w'` over `S` with the same annihilation property and a function `g` not vanishing at `z`
such that `s • w' = g • w`. -/
theorem exists_section_smul_eq_smul_of_notMem_primeIdealOf [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) (F : X.Modules) [F.IsQuasicoherent]
    {x z : X} (hx : x ∈ V₀) (hz : z ∈ V₀) (hxz : x ⤳ z)
    (hdim : ((hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.map
        (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal)).height ≤ 1)
    {S : X.Opens} (hSV : S ≤ V₀) (hzS : z ∉ S)
    {w : Γ(F, S)} (hw : ∀ a ∈ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal,
      X.presheaf.map (homOfLE hSV).op a • w = 0)
    {s : Γ(X, V₀)} (hs : s ∉ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (w' : Γ(F, S)) (g : Γ(X, V₀)), g ∉ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal ∧
      (∀ a ∈ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal,
        X.presheaf.map (homOfLE hSV).op a • w' = 0) ∧
      X.presheaf.map (homOfLE hSV).op s • w'
        = X.presheaf.map (homOfLE hSV).op g • w := by
  classical
  have hnV : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  have hxs : x ∈ X.basicOpen s := (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hx s).mpr hs
  obtain ⟨g, hzg, hg⟩ := exists_basicOpen_forall_mem_basicOpen hV₀ hx hz hxz hdim hzS hxs
  obtain ⟨T, hT⟩ := Ideal.FG.of_isNoetherianRing (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal
  have hTp : ∀ a : Γ(X, V₀), a ∈ T → a ∈ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal :=
    fun a haT => by rw [← hT]; exact Ideal.subset_span haT
  have hDinf : X.basicOpen (X.presheaf.map (homOfLE hSV).op g) = S ⊓ X.basicOpen g :=
    Scheme.basicOpen_res _ _ _
  have hDS : X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ≤ S :=
    X.basicOpen_le (X.presheaf.map (homOfLE hSV).op g)
  have hDV : X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ≤ V₀ := hDS.trans hSV
  let U : Option {a : Γ(X, V₀) // a ∈ T} → X.Opens := fun i =>
    Option.rec (X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ⊓ X.basicOpen s)
      (fun a => X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ⊓ X.basicOpen a.1) i
  have hUD : ∀ i, U i ≤ X.basicOpen (X.presheaf.map (homOfLE hSV).op g) := by
    intro i; cases i <;> exact inf_le_left
  have hUS : ∀ i, U i ≤ S := fun i => (hUD i).trans hDS
  have hUV : ∀ i, U i ≤ V₀ := fun i => (hUD i).trans hDV
  have hcover : X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ≤ iSup U := by
    intro y hy
    have hyV : y ∈ V₀ := hDV hy
    rw [Opens.mem_iSup]
    by_cases hex : ∃ a : {a : Γ(X, V₀) // a ∈ T}, y ∈ X.basicOpen a.1
    · obtain ⟨a, ha⟩ := hex
      exact ⟨some a, ⟨hy, ha⟩⟩
    · push Not at hex
      have hple : (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal
          ≤ (hV₀.primeIdealOf ⟨y, hyV⟩).asIdeal := by
        rw [← hT]
        refine Ideal.span_le.mpr fun a haT => ?_
        by_contra hna
        exact hex ⟨a, haT⟩ ((mem_basicOpen_iff_notMem_primeIdealOf hV₀ hyV a).mpr hna)
      have hyg : y ∈ X.basicOpen g := (hDinf ▸ hy).2
      exact ⟨none, ⟨hy, hg y hyV (hDS hy) hyg hple⟩⟩
  have hsu : IsUnit (X.presheaf.map (homOfLE (hUV none)).op s) :=
    isUnit_res_of_le_basicOpen inf_le_right (hUV none)
  let c : Γ(X, U none) := ↑hsu.unit⁻¹
  have hcs : c * X.presheaf.map (homOfLE (hUV none)).op s = 1 := hsu.unit.inv_val
  let sf : ∀ i : Option {a : Γ(X, V₀) // a ∈ T}, Γ(F, U i) := fun i =>
    Option.rec (c • F.presheaf.map (homOfLE (hUS none)).op w) (fun _ => 0) i
  have hsfsome : ∀ a, sf (some a) = 0 := fun _ => rfl
  have hgq : g ∉ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal :=
    (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hz g).mp hzg
  have hkey : ∀ (W : X.Opens) (f : W ⟶ U none) (a : Γ(X, V₀)), a ∈ T → W ≤ X.basicOpen a →
      F.presheaf.map f.op (sf none) = 0 := by
    intro W f a haT hWa
    have hWn : W ≤ U none := f.le
    have hWS : W ≤ S := hWn.trans (hUS none)
    have h1 : F.presheaf.map (homOfLE hWn).op (c • F.presheaf.map (homOfLE (hUS none)).op w)
        = X.presheaf.map (homOfLE hWn).op c
          • F.presheaf.map (homOfLE hWn).op
            (F.presheaf.map (homOfLE (hUS none)).op w) := F.map_smul _ _ _
    have h2 : F.presheaf.map (homOfLE hWn).op (F.presheaf.map (homOfLE (hUS none)).op w)
        = F.presheaf.map (homOfLE hWS).op w := map_map F hWn (hUS none) hWS w
    have h3 : F.presheaf.map (homOfLE hWS).op w = 0 :=
      res_eq_zero_of_le_basicOpen F hSV hWS hWa (hw a (hTp a haT))
    rw [Subsingleton.elim f (homOfLE hWn)]
    change F.presheaf.map (homOfLE hWn).op (c • F.presheaf.map (homOfLE (hUS none)).op w) = 0
    rw [h1, h2, h3, smul_zero]
  have hcompat : TopCat.Presheaf.IsCompatible (abSheaf F).1 U sf := by
    change ∀ i j, F.presheaf.map (Opens.infLELeft (U i) (U j)).op (sf i)
        = F.presheaf.map (Opens.infLERight (U i) (U j)).op (sf j)
    intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        rw [Subsingleton.elim (Opens.infLELeft (U none) (U none))
          (Opens.infLERight (U none) (U none))]
      | some a =>
        rw [hkey _ (Opens.infLELeft (U none) (U (some a))) a.1 a.2
          (inf_le_right.trans inf_le_right), hsfsome a, map_zero]
    | some a =>
      cases j with
      | none =>
        rw [hkey _ (Opens.infLERight (U (some a)) (U none)) a.1 a.2
          (inf_le_left.trans inf_le_right), hsfsome a, map_zero]
      | some b => rw [hsfsome a, hsfsome b, map_zero, map_zero]
  obtain ⟨ν, hν⟩ : ∃ ν : Γ(F, X.basicOpen (X.presheaf.map (homOfLE hSV).op g)),
      ∀ i, F.presheaf.map (homOfLE (hUD i)).op ν = sf i := by
    obtain ⟨ν, hν, -⟩ := (abSheaf F).existsUnique_gluing' U _ (fun i => homOfLE (hUD i)) hcover
      sf hcompat
    exact ⟨ν, hν⟩
  have hνnone : F.presheaf.map (homOfLE (hUD none)).op ν
      = c • F.presheaf.map (homOfLE (hUS none)).op w := hν none
  have hνsome : ∀ a, F.presheaf.map (homOfLE (hUD (some a))).op ν = 0 := fun a => hν (some a)
  have hsν : X.presheaf.map (homOfLE hDV).op s • ν = F.presheaf.map (homOfLE hDS).op w := by
    refine (abSheaf F).eq_of_locally_eq' U _ (fun i => homOfLE (hUD i)) hcover _ _ fun i => ?_
    have key : F.presheaf.map (homOfLE (hUD i)).op (X.presheaf.map (homOfLE hDV).op s • ν)
        = F.presheaf.map (homOfLE (hUD i)).op (F.presheaf.map (homOfLE hDS).op w) := by
      rw [res_smul F (hUD i), presheaf_map_map (hUD i) hDV (hUV i) s,
        map_map F (hUD i) hDS (hUS i) w]
      cases i with
      | none => rw [hνnone, smul_smul, mul_comm, hcs, one_smul]
      | some a =>
        rw [hνsome a, smul_zero, res_eq_zero_of_le_basicOpen F hSV (hUS (some a))
          (inf_le_right : U (some a) ≤ X.basicOpen a.1) (hw a.1 (hTp a.1 a.2))]
    exact key
  have haν : ∀ a : Γ(X, V₀), a ∈ T → X.presheaf.map (homOfLE hDV).op a • ν = 0 := by
    intro a haT
    refine (abSheaf F).eq_of_locally_eq' U _ (fun i => homOfLE (hUD i)) hcover _ _ fun i => ?_
    have key : F.presheaf.map (homOfLE (hUD i)).op (X.presheaf.map (homOfLE hDV).op a • ν)
        = F.presheaf.map (homOfLE (hUD i)).op (0 : Γ(F, X.basicOpen
            (X.presheaf.map (homOfLE hSV).op g))) := by
      rw [res_smul F (hUD i), presheaf_map_map (hUD i) hDV (hUV i) a, map_zero]
      cases i with
      | none =>
        rw [hνnone, smul_smul, mul_comm, ← smul_smul,
          ← presheaf_map_map (hUS none) hSV (hUV none) a, ← res_smul F (hUS none),
          hw a (hTp a haT), map_zero, smul_zero]
      | some b => rw [hνsome b, smul_zero]
    exact key
  have hcpt : IsCompact (S : Set X) := isCompact_of_le_isAffineOpen hV₀ hSV
  obtain ⟨n, w₁, hw₁⟩ := exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated F hcpt
    ((isQuasiSeparated_univ (α := X)).of_subset (Set.subset_univ _))
    (X.presheaf.map (homOfLE hSV).op g) ν
  have hgDg : X.presheaf.map (homOfLE hDS).op (X.presheaf.map (homOfLE hSV).op g)
      = X.presheaf.map (homOfLE hDV).op g := presheaf_map_map hDS hSV hDV g
  have hzT : ∀ a : Γ(X, V₀), a ∈ T → ∃ k : ℕ,
      X.presheaf.map (homOfLE hSV).op g ^ k • (X.presheaf.map (homOfLE hSV).op a • w₁) = 0 := by
    intro a haT
    refine exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact F hcpt
      (X.presheaf.map (homOfLE hSV).op g) rfl hDS _ ?_
    rw [res_smul F hDS, presheaf_map_map hDS hSV hDV a, hw₁, hgDg, smul_smul,
      mul_comm (X.presheaf.map (homOfLE hDV).op a) (X.presheaf.map (homOfLE hDV).op g ^ n),
      ← smul_smul, haν a haT, smul_zero]
  obtain ⟨ks, hks⟩ : ∃ k : ℕ, X.presheaf.map (homOfLE hSV).op g ^ k •
      (X.presheaf.map (homOfLE hSV).op s • w₁
        - X.presheaf.map (homOfLE hSV).op (g ^ n) • w) = 0 := by
    refine exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact F hcpt
      (X.presheaf.map (homOfLE hSV).op g) rfl hDS _ ?_
    rw [map_sub, res_smul F hDS, res_smul F hDS, presheaf_map_map hDS hSV hDV s,
      presheaf_map_map hDS hSV hDV (g ^ n), map_pow, hw₁, hgDg, smul_smul,
      mul_comm (X.presheaf.map (homOfLE hDV).op s) (X.presheaf.map (homOfLE hDV).op g ^ n),
      ← smul_smul, hsν, sub_self]
  choose! kT hkT using hzT
  let K := max ks (T.sup kT)
  have hpowmul : ∀ (k : ℕ) (hk : k ≤ K) (v : Γ(F, S)),
      X.presheaf.map (homOfLE hSV).op g ^ k • v = 0 →
      X.presheaf.map (homOfLE hSV).op g ^ K • v = 0 := by
    intro k hk v hv
    rw [← pow_sub_mul_pow _ hk, mul_smul, hv, smul_zero]
  refine ⟨X.presheaf.map (homOfLE hSV).op g ^ K • w₁, g ^ (n + K), ?_, ?_, ?_⟩
  · exact fun hmem => hgq ((hV₀.primeIdealOf ⟨z, hz⟩).isPrime.mem_of_pow_mem _ hmem)
  · have hgen : ∀ a : Γ(X, V₀), a ∈ T → X.presheaf.map (homOfLE hSV).op a •
        (X.presheaf.map (homOfLE hSV).op g ^ K • w₁) = 0 := by
      intro a haT
      rw [smul_smul,
        mul_comm (X.presheaf.map (homOfLE hSV).op a) (X.presheaf.map (homOfLE hSV).op g ^ K),
        ← smul_smul]
      exact hpowmul (kT a) (le_trans (Finset.le_sup haT) (le_max_right _ _)) _ (hkT a haT)
    exact fun a ha => smul_eq_zero_of_mem_span _ (hT ▸ ha) hgen
  · have hK := hpowmul ks (le_max_left _ _) _ hks
    rw [smul_sub, sub_eq_zero] at hK
    rw [smul_smul,
      mul_comm (X.presheaf.map (homOfLE hSV).op s) (X.presheaf.map (homOfLE hSV).op g ^ K),
      ← smul_smul, hK, smul_smul, map_pow, map_pow]
    congr 1
    ring

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
