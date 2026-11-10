module

public import StacksFrontier.RingTheory.LocalCohomology.BasicOpenSections
public import StacksFrontier.RingTheory.LocalCohomology.BasicOpenSections.Glue
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Naturality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally fractional sections: vanishing, extension and comparison

This file proves elementary facts about `Stacks.LocalCohomology.moduleSections`, the `A`-module
`Γ(V, M̃)` of locally fractional sections of the quasi-coherent module attached to an `A`-module
`M` on an open `V ⊆ Spec A`.

A section on `V` is a function on the points of `V` taking its value at `x` in the localization
`M_x`, subject to being locally a single fraction.

## Main results

* `Stacks.Algebraization.FormalSections.smul_eq_zero_of_forall_smul_eq_zero` — a scalar
  annihilating the module annihilates all of its sections.
* `Stacks.Algebraization.FormalSections.bijective_moduleSectionsRestrict_of_smul_eq_zero` — if
  `a` annihilates `M` then sections of `M̃` extend uniquely across the locus where `a` is
  invertible: restriction `Γ(U, M̃) ⟶ Γ(V, M̃)` is bijective whenever `V ⊆ U` and every point of
  `U` outside `V` lies in `D(a)`.
* `Stacks.Algebraization.FormalSections.exists_pow_smul_eq_zero_of_restrict_basicOpen_eq_zero` —
  on a quasi-compact open covered by finitely many standard opens, a section vanishing on `D(g)`
  is annihilated by a power of `g`.
* `Stacks.Algebraization.FormalSections.bijective_moduleSectionsMap` — a module map which is
  injective and surjective "up to denominators outside `p`" at every `p ∈ V` induces a bijection
  on sections over `V`.
* `Stacks.Algebraization.FormalSections.exists_moduleSectionsMap_eq_of_map_eq_zero` — the
  left exactness of sections: a section of `Ñ` killed by `N ⟶ P` comes from `M̃` when
  `0 ⟶ M ⟶ N ⟶ P` is exact.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)

universe u v

namespace Stacks.Algebraization.FormalSections

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-! ### Values of sections -/

/-- A locally fractional section is determined by its values at the points of the open. -/
theorem ext_moduleSections {M : ModuleCat.{v} A} {U : Opens (PrimeSpectrum.Top A)}
    {s t : moduleSections M U} (h : ∀ x : U, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext h)

/-- The value of the image of a section under a module map is the localized map applied to the
value. -/
theorem moduleSectionsMap_apply_val {M N : ModuleCat.{v} A} (g : M ⟶ N)
    (U : Opens (PrimeSpectrum.Top A)) (s : moduleSections M U) (x : U) :
    (moduleSectionsMap g U s).1 x =
      IsLocalizedModule.map x.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap _ (M : Type v))
        (LocalizedModule.mkLinearMap _ (N : Type v)) g.hom (s.1 x) :=
  rfl

/-! ### Modules annihilated by a scalar -/

/-- The localization of a module annihilated by `a` vanishes at every prime avoiding `a`. -/
theorem localizedModule_eq_zero_of_smul_eq_zero {M : Type v} [AddCommGroup M] [Module A M]
    {p : PrimeSpectrum A} {a : A} (hp : a ∉ p.asIdeal) (hM : ∀ m : M, a • m = 0)
    (z : LocalizedModule p.asIdeal.primeCompl M) : z = 0 := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    refine Eq.trans (LocalizedModule.mk_eq.2 ⟨⟨a, hp⟩, ?_⟩) (LocalizedModule.zero_mk s)
    change (a • (s • m) : M) = a • (s • (0 : M))
    rw [smul_zero, smul_zero, smul_comm, hM, smul_zero]

/-- A scalar annihilating a module annihilates every section of the associated module. -/
theorem smul_eq_zero_of_forall_smul_eq_zero {M : ModuleCat.{v} A} {a : A}
    (hM : ∀ m : M, a • m = 0) {U : Opens (PrimeSpectrum.Top A)} (s : moduleSections M U) :
    a • s = 0 := by
  refine ext_moduleSections fun x ↦ ?_
  change a • s.1 x = 0
  induction (s.1 x) using LocalizedModule.induction_on with
  | _ m t =>
    refine Eq.trans (LocalizedModule.smul'_mk a m t) ?_
    rw [hM]
    exact LocalizedModule.zero_mk t

/-- A module annihilated by `a` has no nonzero sections on an open inside `D(a)`. -/
theorem moduleSections_eq_zero_of_le_basicOpen {M : ModuleCat.{v} A} {a : A}
    (hM : ∀ m : M, a • m = 0) {U : Opens (PrimeSpectrum.Top A)} (hU : U ≤ basicOpen a)
    (s : moduleSections M U) : s = 0 :=
  ext_moduleSections fun x ↦
    localizedModule_eq_zero_of_smul_eq_zero (hU x.2) hM (s.1 x)

/-! ### Extension across the locus where the annihilating scalar is invertible -/

/-- **Sections of a module annihilated by `a` extend uniquely across `D(a)`.** If every point of
`U` outside the smaller open `V` lies in `D(a)`, then restriction of sections from `U` to `V` is
bijective: the complement of `V` in `U` carries no sections at all. -/
theorem bijective_moduleSectionsRestrict_of_smul_eq_zero {M : ModuleCat.{v} A} {a : A}
    (hM : ∀ m : M, a • m = 0) {U V : Opens (PrimeSpectrum.Top A)} (hVU : V ≤ U)
    (hcov : ∀ x ∈ U, x ∉ V → a ∉ x.asIdeal) :
    Function.Bijective (moduleSectionsRestrict M hVU) := by
  classical
  constructor
  · intro s t hst
    refine ext_moduleSections fun x ↦ ?_
    by_cases hx : x.1 ∈ V
    · exact congrFun (congrArg Subtype.val hst) ⟨x.1, hx⟩
    · exact (localizedModule_eq_zero_of_smul_eq_zero (hcov x.1 x.2 hx) hM _).trans
        (localizedModule_eq_zero_of_smul_eq_zero (hcov x.1 x.2 hx) hM _).symm
  · intro t
    set F : (x : U) → LocalizedModule x.1.asIdeal.primeCompl (M : Type v) :=
      fun x ↦ if h : x.1 ∈ V then t.1 ⟨x.1, h⟩ else 0 with hFdef
    have hFV : ∀ (y : PrimeSpectrum A) (hyU : y ∈ U) (hyV : y ∈ V),
        F ⟨y, hyU⟩ = t.1 ⟨y, hyV⟩ := fun y hyU hyV ↦ dite_eq_left hyV
    have hFzero : ∀ (y : PrimeSpectrum A) (hyU : y ∈ U), a ∉ y.asIdeal → F ⟨y, hyU⟩ = 0 := by
      intro y hyU hy
      by_cases hyV : y ∈ V
      · exact (hFV y hyU hyV).trans (localizedModule_eq_zero_of_smul_eq_zero hy hM _)
      · exact dite_eq_right hyV
    have hmem : ((moduleIsFractionPrelocal M).sheafify).pred F := by
      intro x
      by_cases hx : x.1 ∈ V
      · obtain ⟨W, hxW, i, m, b, hmb⟩ := t.2 ⟨x.1, hx⟩
        refine ⟨W, hxW, i ≫ homOfLE hVU, m, b, fun y ↦ ?_⟩
        obtain ⟨hby, hy⟩ := hmb y
        exact ⟨hby, (hFV y.1 ((i ≫ homOfLE hVU) y).2 (i y).2).trans hy⟩
      · refine ⟨U ⊓ basicOpen a, ⟨x.2, hcov x.1 x.2 hx⟩, homOfLE inf_le_left, 0, 1, fun y ↦ ?_⟩
        refine ⟨by simp [Ideal.IsPrime.one_notMem], ?_⟩
        exact (hFzero y.1 ((inf_le_left : U ⊓ basicOpen a ≤ U) y.2) y.2.2).trans
          (LocalizedModule.zero_mk 1).symm
    refine ⟨⟨F, hmem⟩, ext_moduleSections fun x ↦ ?_⟩
    exact hFV x.1 (hVU x.2) x.2

/-! ### Sections killed on a standard open -/

/-- **A section vanishing on `D(g)` is annihilated by a power of `g`**, on an open covered by
finitely many standard opens. -/
@[ega "I 1.4.1" "a ⇒ d2, d2 for F = M̃|V"]
theorem exists_pow_smul_eq_zero_of_restrict_basicOpen_eq_zero {M : ModuleCat.{v} A}
    {r : ℕ} (gs : Fin r → A) {U : Opens (PrimeSpectrum.Top A)}
    (hU : U = ⨆ i, basicOpen (gs i)) {g : A} (hg : basicOpen g ≤ U)
    (s : moduleSections M U) (hs : moduleSectionsRestrict M hg s = 0) :
    ∃ k : ℕ, g ^ k • s = 0 := by
  classical
  have hle : ∀ i : Fin r, basicOpen (gs i) ≤ U := fun i ↦
    (le_iSup (fun j ↦ basicOpen (gs j)) i).trans hU.ge
  have key : ∀ i : Fin r, ∃ e : ℕ,
      g ^ e • moduleSectionsRestrict M (hle i) s = 0 := by
    intro i
    obtain ⟨n, m, hnm⟩ :=
      exists_pow_smul_eq_moduleSectionsMk M (gs i) (moduleSectionsRestrict M (hle i) s)
    have hprod : basicOpen (gs i * g) ≤ basicOpen (gs i) := by
      rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
    have hprodg : basicOpen (gs i * g) ≤ basicOpen g := by
      rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_right
    have hzero : moduleSectionsMk M (basicOpen (gs i * g)) m = 0 := by
      have h1 : moduleSectionsRestrict M hprod (moduleSectionsMk M (basicOpen (gs i)) m) =
          moduleSectionsMk M (basicOpen (gs i * g)) m :=
        LinearMap.congr_fun (moduleSectionsRestrict_comp_moduleSectionsMk M hprod) m
      rw [← h1, ← hnm, map_smul]
      have h2 : moduleSectionsRestrict M hprod (moduleSectionsRestrict M (hle i) s) =
          moduleSectionsRestrict M hprodg (moduleSectionsRestrict M hg s) := rfl
      rw [h2, hs, map_zero, smul_zero]
    obtain ⟨e, he⟩ :=
      exists_pow_smul_eq_zero_of_moduleSectionsMk_eq_zero M (gs i * g) m hzero
    refine ⟨e, ?_⟩
    have hmk : (gs i ^ e * g ^ e) • moduleSectionsMk M (basicOpen (gs i)) m = 0 := by
      rw [← map_smul]
      rw [show (gs i ^ e * g ^ e) • m = (gs i * g) ^ e • m by rw [mul_pow]]
      rw [he, map_zero]
    have hc : (gs i ^ (e + n) * g ^ e) • moduleSectionsRestrict M (hle i) s = 0 := by
      rw [← hnm, smul_smul] at hmk
      rw [show gs i ^ (e + n) * g ^ e = gs i ^ e * g ^ e * gs i ^ n by ring]
      exact hmk
    have hpow : Function.Bijective ((algebraMap A
        (Module.End A (moduleSections M (basicOpen (gs i)))) (gs i ^ (e + n))) ·) := by
      have hunit : IsUnit (algebraMap A
          (Module.End A (moduleSections M (basicOpen (gs i)))) (gs i)) :=
        isUnit_algebraMap_moduleSections_basicOpen M (gs i)
      have : IsUnit (algebraMap A
          (Module.End A (moduleSections M (basicOpen (gs i)))) (gs i ^ (e + n))) := by
        rw [map_pow]; exact hunit.pow _
      exact (Module.End.isUnit_iff _).1 this
    refine hpow.1 ?_
    change (gs i ^ (e + n)) • (g ^ e • moduleSectionsRestrict M (hle i) s) =
      (gs i ^ (e + n)) • (0 : moduleSections M (basicOpen (gs i)))
    rw [smul_zero, smul_smul]
    exact hc
  choose e he using key
  refine ⟨Finset.univ.sup e, ext_moduleSections fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.le x.2)
  have hvan : (g ^ Finset.univ.sup e) • moduleSectionsRestrict M (hle i) s = 0 := by
    have hdvd : e i ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ i)
    rw [show Finset.univ.sup e = (Finset.univ.sup e - e i) + e i by omega, pow_add, mul_smul,
      he i, smul_zero]
  have hval := congrFun (congrArg Subtype.val hvan) ⟨x.1, hi⟩
  exact hval


/-! ### The localization of a module map at a prime -/

/-- The localization at a prime of a map of modules. This is the map on values of sections
induced by `Stacks.LocalCohomology.moduleSectionsMap`. -/
abbrev locMap {M N : ModuleCat.{v} A} (u : M ⟶ N) (p : PrimeSpectrum A) :
    LocalizedModule p.asIdeal.primeCompl (M : Type v) →ₗ[A]
      LocalizedModule p.asIdeal.primeCompl (N : Type v) :=
  IsLocalizedModule.map p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap _ (M : Type v)) (LocalizedModule.mkLinearMap _ (N : Type v)) u.hom

/-- The localization of `u` at `p` sends the fraction `m / t` to `u m / t`. -/
theorem locMap_mk {M N : ModuleCat.{v} A} (u : M ⟶ N) (p : PrimeSpectrum A) (m : M)
    (t : p.asIdeal.primeCompl) :
    locMap u p (LocalizedModule.mk m t) = LocalizedModule.mk (u m) t :=
  IsLocalizedModule.map_LocalizedModules p.asIdeal.primeCompl u.hom m t

/-- The map on sections induced by `g` sends the global section defined by `m` to the section
defined by `g m`. -/
theorem moduleSectionsMap_moduleSectionsMk {M N : ModuleCat.{v} A} (g : M ⟶ N)
    (U : Opens (PrimeSpectrum.Top A)) (m : M) :
    moduleSectionsMap g U (moduleSectionsMk M U m) = moduleSectionsMk N U (g m) :=
  LinearMap.congr_fun (moduleSectionsMap_comp_moduleSectionsMk g U) m

/-- The restriction to `V` of the section on `U` defined by `m` is the section on `V` defined
by `m`. -/
theorem moduleSectionsRestrict_moduleSectionsMk {M : ModuleCat.{v} A}
    {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U) (m : M) :
    moduleSectionsRestrict M h (moduleSectionsMk M U m) = moduleSectionsMk M V m := rfl

/-- The value at `x` of the image of a section `s` under `u` is the localization of `u` at `x`
applied to the value of `s` at `x`. -/
theorem moduleSectionsMap_apply_val' {M N : ModuleCat.{v} A} (u : M ⟶ N)
    (U : Opens (PrimeSpectrum.Top A)) (s : moduleSections M U) (x : U) :
    (moduleSectionsMap u U s).1 x = locMap u x.1 (s.1 x) :=
  rfl

/-- A fraction vanishes exactly when its numerator is annihilated by the multiplicative set. -/
theorem localizedModule_mk_eq_zero_iff {M : Type v} [AddCommGroup M] [Module A M]
    {S : Submonoid A} (m : M) (t : S) :
    LocalizedModule.mk m t = 0 ↔ ∃ c : S, (c : A) • m = 0 := by
  rw [show (0 : LocalizedModule S M) = LocalizedModule.mk 0 t from
      (LocalizedModule.zero_mk t).symm, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * t, ?_⟩
    have : ((c : A) * (t : A)) • m = 0 := by
      rw [mul_smul]
      simpa only [Submonoid.smul_def, smul_zero] using hc
    simpa only [Submonoid.coe_mul] using this
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simp only [Submonoid.smul_def, smul_zero]
    rw [smul_comm, hc, smul_zero]

/-! ### Local bijectivity -/

/-- If `c • z = u m`, the fraction `z / b` is the image under `u` of the fraction `m / (c * b)`. -/
private theorem mk_eq_locMap_mk_of_smul_eq {M N : ModuleCat.{v} A} (u : M ⟶ N)
    {p : PrimeSpectrum A} {z : N} {m : M} {c b : A} (hc : c ∉ p.asIdeal) (hb : b ∉ p.asIdeal)
    (hcm : c • z = u m) :
    LocalizedModule.mk z (⟨b, hb⟩ : p.asIdeal.primeCompl) =
      locMap u p (LocalizedModule.mk m (⟨c, hc⟩ * ⟨b, hb⟩ : p.asIdeal.primeCompl)) := by
  rw [locMap_mk]
  refine (LocalizedModule.mk_eq).2 ⟨1, ?_⟩
  change (1 : A) • (c * b) • z = (1 : A) • b • u m
  rw [one_smul, one_smul, ← hcm, mul_smul, smul_comm]

/-- If every element of `M` killed by `u` is killed by an element outside `p`, then the
localization of `u` at `p` is injective. -/
theorem injective_locMap {M N : ModuleCat.{v} A} (u : M ⟶ N) {p : PrimeSpectrum A}
    (hinj : ∀ m : M, u m = 0 → ∃ c ∈ p.asIdeal.primeCompl, c • m = 0) :
    Function.Injective (locMap u p) := by
  intro z w hzw
  have hsub : locMap u p (z - w) = 0 := by rw [map_sub, hzw, sub_self]
  suffices h : ∀ y, locMap u p y = 0 → y = 0 by
    have := h _ hsub
    rwa [sub_eq_zero] at this
  intro y hy
  induction y using LocalizedModule.induction_on with
  | _ m t =>
    rw [locMap_mk, localizedModule_mk_eq_zero_iff] at hy
    obtain ⟨c, hc⟩ := hy
    have hum : u ((c : A) • m) = 0 := by
      rw [map_smul]
      exact hc
    obtain ⟨d, hd, hdm⟩ := hinj _ hum
    refine (localizedModule_mk_eq_zero_iff m t).2 ⟨⟨d * (c : A), ?_⟩, ?_⟩
    · exact Submonoid.mul_mem _ hd c.2
    · rw [show ((⟨d * (c : A), Submonoid.mul_mem _ hd c.2⟩ :
          p.asIdeal.primeCompl) : A) = d * (c : A) from rfl, mul_smul]
      exact hdm

/-- If every element of `N` becomes a value of `u` after multiplication by an element outside
`p`, then the localization of `u` at `p` is surjective. -/
theorem surjective_locMap {M N : ModuleCat.{v} A} (u : M ⟶ N) {p : PrimeSpectrum A}
    (hsurj : ∀ z : N, ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M, c • z = u m) :
    Function.Surjective (locMap u p) := by
  intro w
  induction w using LocalizedModule.induction_on with
  | _ z t =>
    obtain ⟨c, hc, m, hcm⟩ := hsurj z
    refine ⟨LocalizedModule.mk m ⟨c * (t : A), Submonoid.mul_mem _ hc t.2⟩, ?_⟩
    rw [locMap_mk]
    refine (LocalizedModule.mk_eq).2 ⟨1, ?_⟩
    change (1 : A) • (t : A) • u m = (1 : A) • (c * (t : A)) • z
    rw [one_smul, one_smul, ← hcm, mul_smul, smul_comm]

/-- **A locally bijective module map is bijective on sections.** If at every point of `V` the
map `u` is injective and surjective up to denominators outside that point, then `u` induces a
bijection on the sections of the associated modules over `V`. -/
theorem bijective_moduleSectionsMap {M N : ModuleCat.{v} A} (u : M ⟶ N)
    {V : Opens (PrimeSpectrum.Top A)}
    (hinj : ∀ p ∈ V, ∀ m : M, u m = 0 → ∃ c ∈ p.asIdeal.primeCompl, c • m = 0)
    (hsurj : ∀ p ∈ V, ∀ z : N, ∃ c ∈ p.asIdeal.primeCompl, ∃ m : M, c • z = u m) :
    Function.Bijective (moduleSectionsMap u V) := by
  classical
  have hI : ∀ x : V, Function.Injective (locMap u x.1) := fun x ↦
    injective_locMap u (hinj x.1 x.2)
  have hS : ∀ x : V, Function.Surjective (locMap u x.1) := fun x ↦
    surjective_locMap u (hsurj x.1 x.2)
  constructor
  · intro s₁ s₂ h
    refine ext_moduleSections fun x ↦ hI x ?_
    exact congrFun (congrArg Subtype.val h) x
  · intro t
    choose F hF using fun x : V ↦ hS x (t.1 x)
    have hmem : ((moduleIsFractionPrelocal M).sheafify).pred F := by
      intro x
      obtain ⟨W, hxW, i, z, b, hzb⟩ := t.2 x
      obtain ⟨c, hc, m, hcm⟩ := hsurj x.1 x.2 z
      refine ⟨W ⊓ basicOpen c, ⟨hxW, hc⟩,
        homOfLE ((inf_le_left : W ⊓ basicOpen c ≤ W).trans i.le), m, c * b, fun y ↦ ?_⟩
      have hby : b ∉ y.1.asIdeal := (hzb ⟨y.1, y.2.1⟩).1
      have hcy : c ∉ y.1.asIdeal := y.2.2
      refine ⟨fun hmem ↦ (y.1.2.mem_or_mem hmem).elim hcy hby, hI _ ?_⟩
      rw [hF]
      exact (hzb ⟨y.1, y.2.1⟩).2.trans (mk_eq_locMap_mk_of_smul_eq u hcy hby hcm)
    refine ⟨⟨F, hmem⟩, ext_moduleSections fun x ↦ hF x⟩

/-! ### Left exactness -/

/-- **Sections are left exact.** If `0 ⟶ M ⟶ N ⟶ P` is exact then a section of `Ñ` over `V`
annihilated by the map to `P̃` is the image of a section of `M̃`. -/
theorem exists_moduleSectionsMap_eq_of_map_eq_zero {M N P : ModuleCat.{v} A}
    (a : M ⟶ N) (b : N ⟶ P) (hinj : Function.Injective a.hom)
    (hex : Function.Exact a.hom b.hom) (V : Opens (PrimeSpectrum.Top A))
    (s : moduleSections N V) (hs : moduleSectionsMap b V s = 0) :
    ∃ t : moduleSections M V, moduleSectionsMap a V t = s := by
  classical
  have hIa : ∀ p : PrimeSpectrum A, Function.Injective (locMap a p) := fun p ↦
    IsLocalizedModule.map_injective p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (M : Type v))
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (N : Type v)) a.hom hinj
  have hExa : ∀ p : PrimeSpectrum A, Function.Exact (locMap a p) (locMap b p) := fun p ↦
    LocalizedModule.map_exact _ a.hom b.hom hex
  have hval : ∀ x : V, ∃ w, locMap a x.1 w = s.1 x := by
    intro x
    refine (hExa x.1 (s.1 x)).1 ?_
    exact congrFun (congrArg Subtype.val hs) x
  choose T hT using hval
  have hmem : ((moduleIsFractionPrelocal M).sheafify).pred T := by
    intro x
    obtain ⟨W, hxW, i, z, d, hzd⟩ := s.2 x
    have hzx : locMap b x.1 (s.1 x) = 0 := congrFun (congrArg Subtype.val hs) x
    have hmkb : LocalizedModule.mk (b z) ((⟨d, (hzd ⟨x.1, hxW⟩).1⟩ :
        x.1.asIdeal.primeCompl)) = 0 := by
      rw [← locMap_mk b x.1 z]
      refine Eq.trans (congrArg (locMap b x.1) ?_) hzx
      exact ((hzd ⟨x.1, hxW⟩).2).symm
    obtain ⟨c, hc⟩ := (localizedModule_mk_eq_zero_iff (b z) _).1 hmkb
    obtain ⟨m, hm⟩ := (hex ((c : A) • z)).1 (by rw [map_smul]; exact hc)
    refine ⟨W ⊓ basicOpen (c : A), ⟨hxW, c.2⟩,
      homOfLE ((inf_le_left : W ⊓ basicOpen (c : A) ≤ W).trans i.le), m, (c : A) * d, fun y ↦ ?_⟩
    have hdy : d ∉ y.1.asIdeal := (hzd ⟨y.1, y.2.1⟩).1
    have hcy : (c : A) ∉ y.1.asIdeal := y.2.2
    refine ⟨fun hmem ↦ (y.1.2.mem_or_mem hmem).elim hcy hdy, hIa _ ?_⟩
    rw [hT]
    exact (hzd ⟨y.1, y.2.1⟩).2.trans (mk_eq_locMap_mk_of_smul_eq a hcy hdy hm.symm)
  exact ⟨⟨T, hmem⟩, ext_moduleSections fun x ↦ hT x⟩


/-! ### Functoriality in the module -/

/-- Localization at a prime is compatible with composition of module maps. -/
theorem locMap_comp {M N P : ModuleCat.{v} A} (u : M ⟶ N) (v : N ⟶ P) (p : PrimeSpectrum A)
    (z : LocalizedModule p.asIdeal.primeCompl (M : Type v)) :
    locMap (u ≫ v) p z = locMap v p (locMap u p z) := by
  induction z using LocalizedModule.induction_on with
  | _ m t => rw [locMap_mk, locMap_mk, locMap_mk]; rfl

/-- The map on sections induced by a composite `u ≫ v` is the composite of the maps induced by
`u` and by `v`. -/
theorem moduleSectionsMap_comp_apply {M N P : ModuleCat.{v} A} (u : M ⟶ N) (v : N ⟶ P)
    (U : Opens (PrimeSpectrum.Top A)) (s : moduleSections M U) :
    moduleSectionsMap (u ≫ v) U s = moduleSectionsMap v U (moduleSectionsMap u U s) :=
  ext_moduleSections fun x ↦ locMap_comp u v x.1 (s.1 x)

/-- The localization at a prime of multiplication by `a` is multiplication by `a`. -/
theorem locMap_lsmul {M : ModuleCat.{v} A} (a : A) (p : PrimeSpectrum A)
    (z : LocalizedModule p.asIdeal.primeCompl (M : Type v)) :
    locMap (ModuleCat.ofHom (LinearMap.lsmul A (M : Type v) a)) p z = a • z := by
  induction z using LocalizedModule.induction_on with
  | _ m t => rw [locMap_mk]; exact (LocalizedModule.smul'_mk a m t).symm

/-- The map on sections induced by multiplication by `a` on `M` is multiplication by `a`. -/
theorem moduleSectionsMap_lsmul {M : ModuleCat.{v} A} (a : A)
    (U : Opens (PrimeSpectrum.Top A)) (s : moduleSections M U) :
    moduleSectionsMap (ModuleCat.ofHom (LinearMap.lsmul A (M : Type v) a)) U s = a • s :=
  ext_moduleSections fun x ↦ locMap_lsmul a x.1 (s.1 x)

/-- An injective module map induces an injective map on sections over any open. -/
theorem injective_moduleSectionsMap {M N : ModuleCat.{v} A} (u : M ⟶ N)
    (hu : Function.Injective u.hom) (U : Opens (PrimeSpectrum.Top A)) :
    Function.Injective (moduleSectionsMap u U) := by
  intro s₁ s₂ h
  refine ext_moduleSections fun x ↦ IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (M : Type v))
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (N : Type v)) u.hom hu ?_
  exact congrFun (congrArg Subtype.val h) x

/-- The identity of `M` induces the identity on sections. -/
theorem moduleSectionsMap_id {M : ModuleCat.{v} A} (U : Opens (PrimeSpectrum.Top A))
    (s : moduleSections M U) : moduleSectionsMap (𝟙 M) U s = s := by
  refine ext_moduleSections fun x ↦ ?_
  rw [moduleSectionsMap_apply_val']
  induction (s.1 x) using LocalizedModule.induction_on with
  | _ m t => rw [locMap_mk]; rfl

end Stacks.Algebraization.FormalSections

end
