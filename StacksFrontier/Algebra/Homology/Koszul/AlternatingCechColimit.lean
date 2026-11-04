module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk
public import StacksFrontier.Algebra.Homology.Koszul.AlternatingCechFunctor
public import StacksFrontier.Algebra.Homology.Koszul.ContragredientComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree

/-!
# The alternating Čech complex as a colimit of contragredient Koszul complexes

Let `A` be a commutative ring and `f₀, …, f_{r-1}` a finite family of elements of `A`. The
basic opens `D(f_i)` cover an open of `Spec A`, and for an `A`-module `M` the alternating Čech
complex of the quasi-coherent sheaf `M^~` with respect to this family is canonically the
filtered colimit, over the exponent `e`, of the contragredient complexes
`Hom_A(I^•(f^{e+1}), M)` of the truncated Koszul complexes.

Explicitly, a linear form `t` on the `(p+1)`-st exterior power at stage `e` is sent to the
alternating Čech cochain whose value on the tuple `(i₀, …, i_p)` is the fraction

`(-1)^p · t([i₀, …, i_p]) / ∏_j f(i_j)^(e+1) ∈ M^~(D(f_{i₀}) ∩ ⋯ ∩ D(f_{i_p}))`.

## Main definitions

* `AlgebraicGeometry.sectionFraction`: the section `m / a` on an open contained in `D(a)`.
* `Koszul.moduleAlternatingCechComplex`: the alternating Čech complex of `M^~` for the basic
  opens of a finite family.
* `Koszul.koszulBasisWedge`: the standard exterior basis vector `[i₀, …, i_p]`.
* `Koszul.koszulCechFraction`: the displayed fraction.
* `Koszul.koszulCocone`: the resulting cocone on the direct system of contragredient complexes.

## Main results

* `Koszul.koszulCoconeIsColimit`: that cocone is a colimit.
* `Koszul.alternatingCechComplexIso`: the resulting canonical isomorphism, together with
  `Koszul.alternatingCechComplexIso_naturality` and
  `Koszul.alternatingCechComplexIso_ι_apply`, which say that it is natural in the module and
  that it is given by the displayed fraction formula.

## Implementation notes

The ring and the coefficient module have independent universes. The sections of `M^~` are
therefore built here rather than taken from `AlgebraicGeometry.StructureSheaf`, whose binders
place the ring and the module in one and the same universe;
`Stacks.LocalCohomology.associatedAbPresheaf_eq_tilde` records that in the common universe the two
constructions agree definitionally.

The source indexes the inverse system of Koszul complexes by the exponent, starting at one;
here the direct system is indexed by `e : ℕ` with exponent `e + 1`.

That the cocone is a colimit is checked degreewise, and in each degree by the two conditions
for a filtered colimit of abelian groups: every alternating Čech cochain is the image of some
linear form at some stage, and a linear form whose cochain vanishes dies at a later stage.
Both reduce to the corresponding statements for a single fraction `m / g^{e+1}` on a basic open
`D(g)`, which are `sectionFraction_surjective` and
`LocalizedModule.mk_powers_eq_zero_iff`.

## References

* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.LocalCohomology (associatedAbPresheaf associatedAbPresheafMap)

namespace AlgebraicGeometry

universe u v

variable {A : Type u} [CommRing A]

/-- Restriction in the locally fractional presheaf is restriction of functions. -/
theorem associatedAbPresheaf_restr_apply {M : ModuleCat.{v} A}
    {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U)
    (s : (associatedAbPresheaf M).obj (op U)) (x : V) :
    ((associatedAbPresheaf M).map (homOfLE h).op s).1 x = s.1 ⟨x.1, h x.2⟩ := rfl

/-- The locally fractional section `m / a` on an open contained in the basic open `D(a)`. -/
noncomputable def sectionFraction (M : ModuleCat.{v} A) (m : M) (a : A)
    (U : Opens (PrimeSpectrum.Top A)) (h : U ≤ PrimeSpectrum.basicOpen a) :
    Stacks.LocalCohomology.moduleSections M U :=
  ⟨fun x ↦ LocalizedModule.mk m ⟨a, h x.2⟩,
    TopCat.PrelocalPredicate.sheafifyOf (P := Stacks.LocalCohomology.moduleIsFractionPrelocal M)
      ⟨m, a, fun x ↦ ⟨h x.2, rfl⟩⟩⟩

/-- Every locally fractional section is, near each point of its domain, the restriction of a
fraction `m / g` defined on a basic open neighbourhood contained in the domain. -/
theorem sectionFraction_exists (M : ModuleCat.{v} A)
    (U : Opens (PrimeSpectrum.Top A)) (s : Stacks.LocalCohomology.moduleSections M U)
    (x : PrimeSpectrum.Top A) (hx : x ∈ U) :
    ∃ (g : A) (_ : x ∈ PrimeSpectrum.basicOpen g) (i : PrimeSpectrum.basicOpen g ≤ U)
      (m : M), sectionFraction M m g _ le_rfl =
        (associatedAbPresheaf M).map (homOfLE i).op s := by
  obtain ⟨V, hxV, iVU, m, g, hmg⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨g', rfl⟩, rfl⟩, hxg', hg'U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  refine ⟨g' * g, ?_, ?_, g' • m, Subtype.ext <| funext fun ⟨y, hy⟩ ↦ ?_⟩ <;>
    simp only [PrimeSpectrum.basicOpen_mul]
  · exact ⟨hxg', (hmg ⟨x, hxV⟩).1⟩
  · exact inf_le_left.trans (hg'U.trans iVU.le)
  · rw [PrimeSpectrum.basicOpen_mul] at hy
    obtain ⟨hgy, H⟩ := hmg ⟨y, hg'U hy.1⟩
    refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans H.symm
    simp [Submonoid.smul_def, ← smul_assoc]; ring_nf

/-- Two fractions with denominators powers of `g` that agree in every localization at a prime
of `D(g)` are equal in the localization at the powers of `g`. -/
theorem away_mk_eq_of_stalks (M : ModuleCat.{v} A) (g : A)
    (m n : M) (s t : Submonoid.powers g)
    (hs : ∀ x : PrimeSpectrum.basicOpen g, (s : A) ∈ x.1.asIdeal.primeCompl)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, (t : A) ∈ x.1.asIdeal.primeCompl)
    (h : ∀ x : PrimeSpectrum.basicOpen g,
      LocalizedModule.mk m ⟨(s : A), hs x⟩ = LocalizedModule.mk n ⟨(t : A), ht x⟩) :
    LocalizedModule.mk m s = LocalizedModule.mk n t := by
  suffices g ∈ ((⊥ : Submodule A M).colon {(t : A) • m - (s : A) • n}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨k, hk⟩ := this
    exact ⟨⟨g ^ k, k, rfl⟩, by
      simpa [sub_eq_zero, smul_sub, Submonoid.smul_def] using!
        Submodule.mem_colon.mp hk _ rfl⟩
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro p hgp
  contrapose hgp
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp (h ⟨p, hgp⟩)
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  exact ⟨u.1, by simpa [sub_eq_zero, smul_sub, Submonoid.smul_def] using hu, u.2⟩

/-- Locally fractional sections which are equal take equal values at every point. -/
private theorem moduleSections_apply_congr {M : ModuleCat.{v} A}
    {U : Opens (PrimeSpectrum.Top A)} {s t : Stacks.LocalCohomology.moduleSections M U}
    (h : s = t) (x : U) : s.1 x = t.1 x :=
  congrFun (congrArg Subtype.val h) x

/-- On a quasi-compact open, a locally fractional section is given by finitely many fractions
`a i / b i` with compatible numerators, on a finite cover by basic opens. -/
theorem sectionFraction_finite_cover (M : ModuleCat.{v} A)
    (U : Opens (PrimeSpectrum.Top A)) (hU : IsCompact (U : Set (PrimeSpectrum.Top A)))
    (s : Stacks.LocalCohomology.moduleSections M U) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → A)
      (ibU : ∀ i, PrimeSpectrum.basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, PrimeSpectrum.basicOpen (b i)) ∧ (∀ i j, b j • a i = b i • a j) ∧
      ∀ i, (associatedAbPresheaf M).map (homOfLE (ibU i)).op s =
        sectionFraction M (a i) (b i) _ le_rfl := by
  classical
  choose g hxg igU a H using fun x : U ↦ sectionFraction_exists M U s x.1 x.2
  have (i j : U) : LocalizedModule.mk (g i • a j)
      (⟨g i * g j, Submonoid.mem_powers _⟩ : Submonoid.powers (g i * g j)) =
      LocalizedModule.mk (g j • a i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    apply away_mk_eq_of_stalks M (g i * g j) _ _
      ⟨g i * g j, Submonoid.mem_powers _⟩
      ⟨g i * g j, Submonoid.mem_powers _⟩ (fun x ↦ x.2) (fun x ↦ x.2)
    intro x
    have hi : x.1 ∈ PrimeSpectrum.basicOpen (g i) :=
      (PrimeSpectrum.basicOpen_mul (g i) (g j)).le x.2 |>.1
    have hj : x.1 ∈ PrimeSpectrum.basicOpen (g j) :=
      (PrimeSpectrum.basicOpen_mul (g i) (g j)).le x.2 |>.2
    have Hi := moduleSections_apply_congr (H i) ⟨x.1, hi⟩
    have Hj := moduleSections_apply_congr (H j) ⟨x.1, hj⟩
    exact (LocalizedModule.mk_cancel_common_left ⟨g i, hi⟩ ⟨g j, hj⟩ (a j)).trans
      (Hj.trans (Hi.symm.trans
        (LocalizedModule.mk_cancel_common_right ⟨g i, hi⟩ ⟨g j, hj⟩ (a i)).symm))
  simp only [LocalizedModule.mk_eq, Submonoid.smul_def, Subtype.exists,
    Submonoid.mem_powers_iff, exists_prop, exists_exists_eq_and,
    ← mul_smul, ← pow_succ, ← mul_assoc _ (_ * _)] at this
  choose n hn using this
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun i ↦ (PrimeSpectrum.basicOpen (g i) : Set (PrimeSpectrum A)))
    (fun _ ↦ (PrimeSpectrum.basicOpen _).2)
    (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  let N := (t ×ˢ t).sup fun x ↦ n x.1 x.2 + 1
  refine ⟨t, inferInstance, fun i ↦ g i ^ N • a i, fun i ↦ g i ^ (N + 1),
    fun x ↦ by simpa using igU x.1, fun x hx ↦ by simpa using ht hx,
    fun i j ↦ ?_, fun i ↦ ?_⟩
  · dsimp
    convert_to (g i * g ↑j) ^ N • g j • a i = (g i * g ↑j) ^ N • g i • a j
    · module
    · module
    have hN : n i j + 1 ≤ N :=
      (t ×ˢ t).le_sup (f := fun x ↦ n x.1 x.2 + 1) (b := ⟨_, _⟩) (by simp)
    rw [← Nat.sub_add_cancel hN, pow_add, mul_smul, mul_smul]
    congr 1
    convert! (hn i j).symm using 1 <;> module
  · apply Subtype.ext
    funext x
    have hx : x.1 ∈ PrimeSpectrum.basicOpen (g i) := by simpa using x.2
    have Hi := moduleSections_apply_congr (H i) ⟨x.1, hx⟩
    refine Hi.symm.trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
    simp [Submonoid.smul_def, pow_succ', mul_smul]

/-- Every locally fractional section on a basic open `D(g)` is a single fraction with
denominator a positive power of `g`. -/
theorem sectionFraction_surjective (M : ModuleCat.{v} A) (g : A)
    (s : Stacks.LocalCohomology.moduleSections M (PrimeSpectrum.basicOpen g)) :
    ∃ (n : ℕ) (m : M), s = sectionFraction M m (g ^ (n + 1)) _
      (by simp) := by
  classical
  obtain ⟨ι, _, a, b, ibU, iU, hab, H⟩ := sectionFraction_finite_cover M _
    (PrimeSpectrum.isCompact_basicOpen _) s
  obtain ⟨n, hn⟩ : g ∈ (Ideal.span (Set.range b)).radical := by
    have hz : PrimeSpectrum.zeroLocus (Set.range b) ⊆ PrimeSpectrum.zeroLocus {g} := by
      simpa [← SetLike.coe_subset_coe, ← Set.compl_iInter,
        ← PrimeSpectrum.zeroLocus_iUnion, ← PrimeSpectrum.zeroLocus_iUnion,
        PrimeSpectrum.Top] using iU
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.mem_vanishingIdeal]
    exact fun x hx ↦ by simpa using hz hx
  replace hn := Ideal.mul_mem_right g _ hn
  rw [← pow_succ, Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Finsupp.sum_fintype _ _ (by simp)] at hc
  refine ⟨n, ∑ i, c i • a i, ?_⟩
  apply Subtype.ext
  funext x
  obtain ⟨i, hi⟩ : ∃ i, x.1 ∈ PrimeSpectrum.basicOpen (b i) := by
    simpa only [Opens.mem_iSup] using iU x.2
  have Hi := moduleSections_apply_congr (H i) ⟨x.1, hi⟩
  refine Hi.trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
  simp_rw [one_smul, Finset.smul_sum, Submonoid.smul_def,
    smul_comm (b i), hab _ i, ← smul_assoc, ← Finset.sum_smul, hc]

end AlgebraicGeometry

namespace LocalizedModule

/-- Forming a fraction with a fixed denominator, as a linear map. -/
private noncomputable def numeratorMap {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] {S : Submonoid R} (d : S) :
    E →ₗ[R] LocalizedModule S E where
  toFun m := LocalizedModule.mk m d
  map_add' m n := by
    rw [LocalizedModule.mk_add_mk, ← smul_add]
    exact (LocalizedModule.mk_cancel_common_left d d (m + n)).symm
  map_smul' a m := (LocalizedModule.smul'_mk a m d).symm

/-- A fraction whose numerator is a finite sum is the sum of the fractions. -/
theorem mk_finset_sum {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    {S : Submonoid R} (d : S) (s : Finset ι) (m : ι → E) :
    LocalizedModule.mk (∑ i ∈ s, m i) d = ∑ i ∈ s, LocalizedModule.mk (m i) d :=
  map_sum (numeratorMap d) m s

/-- A fraction with denominator a power of `g` vanishes exactly when some power of `g`
annihilates its numerator. -/
theorem mk_powers_eq_zero_iff {R E : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] (g : R) (m : E) (d : Submonoid.powers g) :
    LocalizedModule.mk m d = 0 ↔ ∃ k : ℕ, g ^ k • m = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers g), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨u, k, rfl⟩, hu⟩
    exact ⟨k, by simpa [Submonoid.smul_def] using hu⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨g ^ k, k, rfl⟩, by simpa [Submonoid.smul_def] using hk⟩

end LocalizedModule

namespace Koszul

open AlgebraicGeometry CechCochains

universe u v

variable {A : Type u} [CommRing A]

/-- The alternating Čech complex of the sheaf associated to `M`, for the basic opens
belonging to `f`. -/
noncomputable abbrev moduleAlternatingCechComplex {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) :=
  Stacks.Cech.alternatingCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
    (associatedAbPresheaf M)

/-- The map of alternating Čech complexes induced by a map of modules. -/
noncomputable abbrev moduleAlternatingCechMap {r : ℕ} (f : Fin r → A)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) :=
  Stacks.Cech.alternatingCechMap (fun i ↦ PrimeSpectrum.basicOpen (f i))
    (associatedAbPresheafMap g)

/-- The basis wedge `[i₀, …, iₚ]` in the degree-`p` Koszul ideal complex. -/
noncomputable def koszulBasisWedge {r : ℕ} (p : ℕ) (i : Fin (p + 1) → Fin r) :
    ⋀[A]^(p + 1) (Fin r → A) :=
  exteriorPower.ιMulti A (p + 1) (fun j ↦ Pi.single (i j) 1)

/-- The fraction `(-1)^p t([i₀, …, iₚ]) / ∏ⱼ f(iⱼ)^(e+1)` on the intersection
of the indicated basic opens. The stage `e` corresponds to source exponent `e + 1`. -/
noncomputable def koszulCechFraction {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e p : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) :
    (associatedAbPresheaf M).obj
      (op (inter (fun j ↦ PrimeSpectrum.basicOpen (f j)) i)) := by
  let U := inter (X := PrimeSpectrum.Top A)
    (fun j ↦ PrimeSpectrum.basicOpen (f j)) i
  let m := (-1 : A) ^ p • t (koszulBasisWedge p i)
  let a := ∏ j, f (i j) ^ (e + 1)
  have ha (x : U) : a ∈ x.1.asIdeal.primeCompl :=
    Submonoid.prod_mem _ fun j _ ↦
      Submonoid.pow_mem _ ((iInf_le (fun j ↦ PrimeSpectrum.basicOpen (f (i j))) j) x.2) _
  exact ⟨fun x ↦ LocalizedModule.mk m ⟨a, ha x⟩,
    TopCat.PrelocalPredicate.sheafifyOf (P := Stacks.LocalCohomology.moduleIsFractionPrelocal M)
      ⟨m, a, fun x ↦ ⟨ha x, rfl⟩⟩⟩

/-- A point of the intersection of the basic opens `D(f (i j))` does not lie in the vanishing
locus of any product of powers of the `f (i j)`. -/
private lemma prod_pow_mem_primeCompl {r q : ℕ} (f : Fin r → A) (i : Fin q → Fin r) (n : ℕ)
    (x : inter (X := PrimeSpectrum.Top A) (fun j ↦ PrimeSpectrum.basicOpen (f j)) i) :
    ∏ j, f (i j) ^ n ∈ x.1.asIdeal.primeCompl :=
  Submonoid.prod_mem _ fun j _ ↦
    Submonoid.pow_mem _ ((iInf_le (fun j ↦ PrimeSpectrum.basicOpen (f (i j))) j) x.2) _

private lemma koszulCechFraction_add {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e p : ℕ)
    (t s : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) :
    koszulCechFraction f M e p (t + s) i =
      koszulCechFraction f M e p t i + koszulCechFraction f M e p s i := by
  apply Subtype.ext
  funext x
  let d : x.1.asIdeal.primeCompl := ⟨∏ j, f (i j) ^ (e + 1), prod_pow_mem_primeCompl f i _ x⟩
  let m := (-1 : A) ^ p • t (koszulBasisWedge p i)
  let n := (-1 : A) ^ p • s (koszulBasisWedge p i)
  change LocalizedModule.mk ((-1 : A) ^ p •
      (t (koszulBasisWedge p i) + s (koszulBasisWedge p i))) d =
    LocalizedModule.mk m d + LocalizedModule.mk n d
  rw [smul_add]
  change LocalizedModule.mk (m + n) d = LocalizedModule.mk m d + LocalizedModule.mk n d
  rw [LocalizedModule.mk_add_mk]
  calc
    LocalizedModule.mk (m + n) d = LocalizedModule.mk (d • (m + n)) (d * d) :=
      (LocalizedModule.mk_cancel_common_left d d (m + n)).symm
    _ = LocalizedModule.mk (d • m + d • n) (d * d) := by rw [smul_add]

private lemma koszulCechFraction_zero {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e p : ℕ) (i : Fin (p + 1) → Fin r) :
    koszulCechFraction f M e p (0 : _ →ₗ[A] M) i = 0 := by
  apply Subtype.ext
  funext x
  change LocalizedModule.mk ((-1 : A) ^ p • (0 : M)) _ = 0
  simp

private lemma koszulCechFraction_map {r : ℕ} (f : Fin r → A)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) (e p : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) :
    koszulCechFraction f N e p (g.hom.comp t) i =
      (associatedAbPresheafMap g).app
        (op (inter (fun j ↦ PrimeSpectrum.basicOpen (f j)) i))
        (koszulCechFraction f M e p t i) := by
  apply Subtype.ext
  funext x
  change LocalizedModule.mk
      ((-1 : A) ^ p • g.hom (t (koszulBasisWedge p i))) _ =
    IsLocalizedModule.map x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g.hom
      (LocalizedModule.mk
        ((-1 : A) ^ p • t (koszulBasisWedge p i)) _)
  rw [IsLocalizedModule.map_LocalizedModules, map_smul]

private lemma koszulCechFraction_face_factor {r p : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e : ℕ) (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 2) → Fin r) (j : Fin (p + 2))
    (x : inter (X := PrimeSpectrum.Top A)
      (fun k ↦ PrimeSpectrum.basicOpen (f k)) i) :
    ((associatedAbPresheaf M).map
        (homOfLE (inter_le_omit (X := PrimeSpectrum.Top A)
          (fun k ↦ PrimeSpectrum.basicOpen (f k)) i j)).op
        (koszulCechFraction f M e p t (i ∘ j.succAbove))).1 x =
      f (i j) ^ (e + 1) • LocalizedModule.mk (S := x.1.asIdeal.primeCompl)
        ((-1 : A) ^ p • t (koszulBasisWedge p (i ∘ j.succAbove)))
        ⟨∏ k, f (i k) ^ (e + 1), prod_pow_mem_primeCompl f i _ x⟩ := by
  let U : Fin (p + 2) → Opens (PrimeSpectrum.Top A) :=
    fun k ↦ PrimeSpectrum.basicOpen (f (i k))
  let dface := ∏ k, f ((i ∘ j.succAbove) k) ^ (e + 1)
  let dfull := ∏ k, f (i k) ^ (e + 1)
  have ha : f (i j) ^ (e + 1) ∈ x.1.asIdeal.primeCompl := Submonoid.pow_mem _ ((iInf_le U j) x.2) _
  have hb : dface ∈ x.1.asIdeal.primeCompl :=
    Submonoid.prod_mem _ fun k _ ↦ Submonoid.pow_mem _ ((iInf_le U (j.succAbove k)) x.2) _
  have hd : dfull ∈ x.1.asIdeal.primeCompl := prod_pow_mem_primeCompl f i _ x
  have hden : dfull = f (i j) ^ (e + 1) * dface := by
    dsimp [dfull, dface]
    simpa only [Function.comp_def] using
      Fin.prod_univ_succAbove (fun k ↦ f (i k) ^ (e + 1)) j
  have hden' : (⟨dfull, hd⟩ : x.1.asIdeal.primeCompl) =
      ⟨f (i j) ^ (e + 1), ha⟩ * ⟨dface, hb⟩ :=
    Subtype.ext hden
  let m := (-1 : A) ^ p • t (koszulBasisWedge p (i ∘ j.succAbove))
  rw [associatedAbPresheaf_restr_apply]
  change LocalizedModule.mk m ⟨dface, hb⟩ =
    f (i j) ^ (e + 1) • LocalizedModule.mk m ⟨dfull, hd⟩
  rw [hden', LocalizedModule.smul'_mk]
  exact (LocalizedModule.mk_cancel_common_left
    ⟨f (i j) ^ (e + 1), ha⟩ ⟨dface, hb⟩ m).symm

private lemma ιMulti_smul_factors {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (n : ℕ) (v : Fin n → E) (a : Fin n → R) :
    ExteriorAlgebra.ιMulti R n (fun i => a i • v i) =
      (∏ i, a i) • ExteriorAlgebra.ιMulti R n v := by
  induction n with
  | zero => simp [ExteriorAlgebra.ιMulti]
  | succ n ih =>
    rw [Koszul.ιMulti_succ_apply, Koszul.ιMulti_succ_apply]
    simp only [Fin.tail_def]
    rw [ih]
    simp only [Fin.prod_univ_succ]
    simp only [map_smul, mul_smul_comm]
    rw [smul_mul_assoc, smul_smul]
    congr 1
    ring

private lemma transition_wedge {r p : ℕ} (f : Fin r → A)
    (i : Fin (p + 1) → Fin r) :
    exteriorPower.map (p + 1) (coordinatewiseMul f) (koszulBasisWedge p i) =
        (∏ j, f (i j)) • koszulBasisWedge p i := by
  apply Subtype.ext
  simp only [koszulBasisWedge, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMulti_apply_coe, SetLike.val_smul]
  have h : (coordinatewiseMul f) ∘ (fun j => Pi.single (i j) 1) =
      fun j => f (i j) • Pi.single (i j) 1 := by
    funext j
    ext k
    by_cases hki : k = i j <;>
      simp [coordinatewiseMul, hki]
  rw [h, ιMulti_smul_factors]

private lemma systemTransition_wedge {r p : ℕ} (f : Fin r → A) (e : ℕ)
    (i : Fin (p + 1) → Fin r) :
    ((koszulIdealComplexSystem f).transition e).f p (koszulBasisWedge p i) =
      (∏ j, f (i j)) • koszulBasisWedge p i := by
  rw [KoszulIdealComplexSystem.transition_f]
  exact transition_wedge f i

/-- A linear form on the stage-`e` term, read on the transition of a basis wedge, picks up the
product of the entries of `f` along the tuple. The terms of the truncated Koszul complex are the
exterior powers only up to unfolding, so this is stated for the linear form rather than left to
`map_smul` at the point of use. -/
@[ega "III 1.2.2" "partial"]
private lemma systemTransition_wedge_apply {r p : ℕ} (f : Fin r → A) (e : ℕ)
    {M : ModuleCat.{v} A} (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) :
    t (((koszulIdealComplexSystem f).transition e).f p (koszulBasisWedge p i)) =
      (∏ j, f (i j)) • t (koszulBasisWedge p i) :=
  (congrArg t (systemTransition_wedge f e i)).trans (map_smul t _ _)

private lemma koszulBasisWedge_eq_zero {r p : ℕ} (i : Fin (p + 1) → Fin r)
    (hi : ¬ Function.Injective i) : koszulBasisWedge (A := A) p i = 0 := by
  apply Subtype.ext
  simp only [koszulBasisWedge, exteriorPower.ιMulti_apply_coe]
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro hinj
  apply hi
  intro j k hjk
  apply hinj
  ext a
  simp [hjk]

private lemma koszulCechFraction_eq_zero_of_not_injective {r : ℕ}
    (f : Fin r → A) (M : ModuleCat.{v} A) (e p : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) (hi : ¬ Function.Injective i) :
    koszulCechFraction f M e p t i = 0 := by
  apply Subtype.ext
  funext x
  change LocalizedModule.mk
    ((-1 : A) ^ p • t (koszulBasisWedge p i)) _ = 0
  have ht : t (koszulBasisWedge p i) = 0 := by
    calc
      t (koszulBasisWedge p i) = t 0 :=
        congrArg t (koszulBasisWedge_eq_zero i hi)
      _ = 0 := t.map_zero
  rw [ht, smul_zero]
  exact LocalizedModule.zero_mk _

private lemma koszulBasisWedge_swap {r p : ℕ} (i : Fin (p + 1) → Fin r)
    (j k : Fin (p + 1)) (hjk : j ≠ k) :
    koszulBasisWedge (A := A) p (i ∘ Equiv.swap j k) =
      (-1 : A) • koszulBasisWedge (A := A) p i := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A (p + 1)
      (fun l ↦ Pi.single (i ((Equiv.swap j k) l)) 1) =
    - ExteriorAlgebra.ιMulti A (p + 1) (fun l ↦ Pi.single (i l) 1)
  simpa only [Function.comp_def, Fin.tail_def] using
    (ExteriorAlgebra.ιMulti A (p + 1)).map_swap
      (fun j ↦ Pi.single (i j) 1) hjk

private lemma koszulCechDenominator_swap {r p : ℕ} (f : Fin r → A)
    (e : ℕ) (i : Fin (p + 1) → Fin r) (j k : Fin (p + 1)) :
    (∏ l, f ((i ∘ Equiv.swap j k) l) ^ (e + 1)) =
      ∏ l, f (i l) ^ (e + 1) := by
  simpa only [Function.comp_def] using
    (Equiv.prod_comp (Equiv.swap j k) (fun l ↦ f (i l) ^ (e + 1)))

private lemma koszulIdealDifferential_wedge {r : ℕ} (f : Fin r → A) (e p : ℕ)
    (i : Fin (p + 2) → Fin r) :
    (((koszulIdealComplexPower f e).d (p + 1) p).hom) (koszulBasisWedge (p + 1) i) =
      -∑ j : Fin (p + 2), ((-1 : A) ^ j.val * f (i j) ^ (e + 1)) •
        koszulBasisWedge p (i ∘ j.succAbove) := by
  dsimp [koszulIdealComplexPower, koszulIdealComplex]
  rw [Koszul.seqComplex_d]
  change -(Koszul.d (Koszul.seqDual (fun k ↦ f k ^ (e + 1))) (p + 1))
    (koszulBasisWedge (p + 1) i) = _
  rw [neg_inj]
  apply Subtype.ext
  simp only [koszulBasisWedge, exteriorPower.ιMulti_apply_coe, Koszul.d_apply_coe,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  rw [Koszul.contraction_ιMulti]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [Koszul.seqDual_apply_single]

/-- A linear form on the stage-`e` term, read on the differential of a basis wedge, is the
signed alternating sum of its values on the faces. -/
private lemma koszulIdealDifferential_wedge_apply {r p : ℕ} (f : Fin r → A) (e : ℕ)
    {M : ModuleCat.{v} A} (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 2) → Fin r) :
    t (((koszulIdealComplexPower f e).d (p + 1) p).hom (koszulBasisWedge (p + 1) i)) =
      -∑ j : Fin (p + 2), ((-1 : A) ^ j.val * f (i j) ^ (e + 1)) •
        t (koszulBasisWedge p (i ∘ j.succAbove)) :=
  (congrArg t (koszulIdealDifferential_wedge f e p i)).trans <|
    (map_neg t _).trans <| congrArg Neg.neg <|
      (map_sum t _ Finset.univ).trans <|
        Finset.sum_congr rfl fun _ _ ↦ map_smul t _ _

private lemma koszulCechFraction_swap {r p : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) (j k : Fin (p + 1)) (hjk : j ≠ k) :
    koszulCechFraction f M e p t (i ∘ Equiv.swap j k) =
      -permIso (fun l ↦ PrimeSpectrum.basicOpen (f l))
        (associatedAbPresheaf M) i (Equiv.swap j k) (koszulCechFraction f M e p t i) := by
  have hnum : (-1 : A) ^ p • t (koszulBasisWedge p (i ∘ Equiv.swap j k)) =
      -((-1 : A) ^ p • t (koszulBasisWedge p i)) := by
    calc
      _ = (-1 : A) ^ p • t ((-1 : A) • koszulBasisWedge p i) := by
        rw [koszulBasisWedge_swap i j k hjk]
        rfl
      _ = (-1 : A) ^ p • ((-1 : A) • t (koszulBasisWedge p i)) :=
        congrArg (fun z ↦ (-1 : A) ^ p • z) (map_smul t (-1 : A) _)
      _ = (-1 : A) • ((-1 : A) ^ p • t (koszulBasisWedge p i)) := by
        rw [smul_comm]
      _ = _ := neg_one_smul A _
  apply Subtype.ext
  funext x
  have hopen : inter (X := PrimeSpectrum.Top A)
        (fun l ↦ PrimeSpectrum.basicOpen (f l)) (i ∘ Equiv.swap j k) =
      inter (X := PrimeSpectrum.Top A)
        (fun l ↦ PrimeSpectrum.basicOpen (f l)) i :=
    inter_comp_perm (X := PrimeSpectrum.Top A)
      (fun l ↦ PrimeSpectrum.basicOpen (f l)) i (Equiv.swap j k)
  simp only [permIso]
  change LocalizedModule.mk
      ((-1 : A) ^ p • t (koszulBasisWedge p (i ∘ Equiv.swap j k))) _ =
    - (koszulCechFraction f M e p t i).1 ((eqToHom hopen) x)
  rw [hnum]
  simp only [LocalizedModule.mk_neg]
  rw [neg_inj]
  simp only [koszulCechFraction]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simpa [Submonoid.smul_def] using
    congrArg (fun c : A ↦ c • ((-1 : A) ^ p • t (koszulBasisWedge p i)))
      (koszulCechDenominator_swap f e i j k).symm

private lemma koszulCechFraction_transition {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e p : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) :
    koszulCechFraction f M e p t i =
      koszulCechFraction f M (e + 1) p
        (t.comp (((koszulIdealComplexSystem f).transition e).f p).hom) i := by
  apply Subtype.ext
  funext x
  let b : A := ∏ j, f (i j)
  let d : A := ∏ j, f (i j) ^ (e + 1)
  have hb : b ∈ x.1.asIdeal.primeCompl := by simpa using prod_pow_mem_primeCompl f i 1 x
  have hd : d ∈ x.1.asIdeal.primeCompl := prod_pow_mem_primeCompl f i _ x
  have hden : (∏ j, f (i j) ^ (e + 1 + 1)) = b * d := by
    dsimp [b, d]
    simp only [pow_succ]
    rw [Finset.prod_mul_distrib]
    ring
  have hden' : (⟨∏ j, f (i j) ^ (e + 1 + 1), by rw [hden]; exact Submonoid.mul_mem _ hb hd⟩ :
      x.1.asIdeal.primeCompl) = ⟨b, hb⟩ * ⟨d, hd⟩ :=
    Subtype.ext hden
  change LocalizedModule.mk ((-1 : A) ^ p • t (koszulBasisWedge p i)) ⟨d, hd⟩ =
    LocalizedModule.mk
      ((-1 : A) ^ p • t ((((koszulIdealComplexSystem f).transition e).f p)
        (koszulBasisWedge p i)))
      ⟨∏ j, f (i j) ^ (e + 1 + 1), _⟩
  rw [systemTransition_wedge_apply, hden',
    show (-1 : A) ^ p • (b • t (koszulBasisWedge p i)) =
      b • ((-1 : A) ^ p • t (koszulBasisWedge p i)) by rw [smul_comm]]
  symm
  exact LocalizedModule.mk_cancel_common_left ⟨b, hb⟩ ⟨d, hd⟩
    ((-1 : A) ^ p • t (koszulBasisWedge p i))

/-- The degree-`p` component of the comparison map from the stage-`e` contragredient
complex to the alternating Čech complex. -/
noncomputable def koszulStageComponent {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e p : ℕ) :
    AddCommGrpCat.of ((koszulIdealComplexPower f e).X p →ₗ[A] M) ⟶
      AddCommGrpCat.of (alternatingSubgroup
        (fun i ↦ PrimeSpectrum.basicOpen (f i)) (associatedAbPresheaf M) p) :=
  AddCommGrpCat.ofHom
    { toFun := fun t ↦ ⟨fun i ↦ koszulCechFraction f M e p t i,
        by
          refine ⟨?_, ?_⟩
          · intro i hi
            exact koszulCechFraction_eq_zero_of_not_injective f M e p t i hi
          · intro i j k hjk
            exact koszulCechFraction_swap (f := f) (M := M) (e := e) (p := p)
              t i j k hjk⟩
      map_zero' := by exact Subtype.ext <| funext fun i ↦ koszulCechFraction_zero f M e p i
      map_add' t s := by
        exact Subtype.ext <| funext fun i ↦ koszulCechFraction_add f M e p t s i }

/-- The comparison map from the stage-`e` contragredient complex to the alternating Čech
complex. -/
noncomputable def koszulStageMap {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e : ℕ) :
    koszulHomComplex (koszulIdealComplexPower f e) M ⟶ moduleAlternatingCechComplex f M :=
  CochainComplex.ofHom (fun p ↦ koszulStageComponent f M e p) (by
    intro p
    simp only [Stacks.Cech.alternatingCechComplex_d, koszulHomComplex, CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    apply Subtype.ext
    funext i
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (associatedAbPresheaf M).map
        (homOfLE (inter_le_omit _ i j)).op
        (koszulCechFraction f M e p t (i ∘ j.succAbove))) =
      koszulCechFraction f M e (p + 1)
        (t.comp ((koszulIdealComplexPower f e).d (p + 1) p).hom) i
    apply Subtype.ext
    funext x
    let ev : Stacks.LocalCohomology.moduleSections M (inter
        (fun j ↦ PrimeSpectrum.basicOpen (f j)) i) →+ LocalizedModule x.1.asIdeal.primeCompl M :=
      { toFun := fun s ↦ s.1 x
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (associatedAbPresheaf M).map
        (homOfLE (inter_le_omit _ i j)).op
        (koszulCechFraction f M e p t (i ∘ j.succAbove))) = _
    refine (map_sum ev _ Finset.univ).trans ?_
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      ((associatedAbPresheaf M).map
        (homOfLE (inter_le_omit _ i j)).op
        (koszulCechFraction f M e p t (i ∘ j.succAbove))).1 x) =
      LocalizedModule.mk ((-1 : A) ^ (p + 1) •
        t (((koszulIdealComplexPower f e).d (p + 1) p).hom
          (koszulBasisWedge (p + 1) i))) _
    simp only [koszulCechFraction_face_factor, koszulIdealDifferential_wedge_apply]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg,
      neg_neg, Finset.smul_sum, Finset.sum_neg_distrib]
    rw [LocalizedModule.mk_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Int.cast_smul_eq_zsmul A, Int.cast_pow, Int.cast_neg, Int.cast_one,
      LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
    congr 1
    module)

/-- The comparison maps are compatible with the transitions of the direct system. -/
theorem koszulStageMap_transition {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e : ℕ) :
    (koszulHomDiagram f M).map (homOfLE (Nat.le_succ e)) ≫
      koszulStageMap f M (e + 1) = koszulStageMap f M e := by
  rw [koszulHomDiagram_map_succ]
  ext p t
  exact Subtype.ext <| funext fun i ↦ (koszulCechFraction_transition f M e p t i).symm

/-- The cocone on the direct system of contragredient Koszul complexes with vertex the
alternating Čech complex. -/
noncomputable def koszulCocone {r : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A) :
    Cocone (koszulHomDiagram f M) where
  pt := moduleAlternatingCechComplex f M
  ι := NatTrans.ofSequence (koszulStageMap f M)
    (fun e ↦ (koszulStageMap_transition f M e).trans (Category.comp_id _).symm)

/-- The leg of the cocone at a stage is the comparison map of that stage. -/
theorem koszulCocone_ι_app {r : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A) (e : ℕ) :
    (koszulCocone f M).ι.app e = koszulStageMap f M e :=
  rfl

private lemma koszulStageMap_naturality {r : ℕ} (f : Fin r → A)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) (e : ℕ) :
    koszulStageMap f M e ≫ moduleAlternatingCechMap f g =
      koszulHomComplexMap (koszulIdealComplexPower f e) g ≫ koszulStageMap f N e := by
  ext p t
  exact Subtype.ext <| funext fun i ↦ (koszulCechFraction_map f g e p t i).symm

private lemma koszulHomDiagram_map_wedge {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e k p : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) :
    (show (koszulIdealComplexPower f (e + k)).X p →ₗ[A] M from
      ((koszulHomDiagram f M).map (homOfLE (Nat.le_add_right e k))).f p t)
      (koszulBasisWedge p i) = (∏ j, f (i j)) ^ k • t (koszulBasisWedge p i) := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
    rw [show homOfLE (Nat.le_add_right e (k + 1)) =
      homOfLE (Nat.le_add_right e k) ≫ homOfLE (Nat.le_succ (e + k)) from rfl,
      Functor.map_comp, HomologicalComplex.comp_f, koszulHomDiagram_map_succ]
    change (show (koszulIdealComplexPower f (e + k)).X p →ₗ[A] M from
      ((koszulHomDiagram f M).map (homOfLE (Nat.le_add_right e k))).f p t)
      (((koszulIdealComplexSystem f).transition (e + k)).f p
        (koszulBasisWedge p i)) = _
    rw [systemTransition_wedge_apply, ih, smul_smul, pow_succ']

private noncomputable def orderedIndexEquiv (r p : ℕ) :
    OrdIndex (I := Fin r) p ≃ Set.powersetCard (Fin r) (p + 1) :=
  (show OrdIndex (I := Fin r) p ≃ (Fin (p + 1) ↪o Fin r) from
    { toFun := fun i ↦ OrderEmbedding.ofStrictMono i.1 i.2
      invFun := fun i ↦ ⟨i, i.strictMono⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }).trans Set.powersetCard.ofFinEmbEquiv

private noncomputable def orderedExteriorBasis (r p : ℕ) :
    Module.Basis (OrdIndex (I := Fin r) p) A (⋀[A]^(p + 1) (Fin r → A)) :=
  (Stacks.RegularSequence.wedgeBasis A r (p + 1)).reindex (orderedIndexEquiv r p).symm

private lemma orderedExteriorBasis_apply {r p : ℕ} (i : OrdIndex (I := Fin r) p) :
    orderedExteriorBasis (A := A) r p i = koszulBasisWedge p i.1 := by
  rw [orderedExteriorBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    Stacks.RegularSequence.wedgeBasis_apply]
  simp only [orderedIndexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  simp only [koszulBasisWedge]
  rfl

private lemma alternating_ext_ordered {r p : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A)
    {s t : alternatingSubgroup (X := PrimeSpectrum.Top A)
      (fun i ↦ PrimeSpectrum.basicOpen (f i)) (associatedAbPresheaf M) p}
    (h : ∀ i : OrdIndex (I := Fin r) p, s.1 i.1 = t.1 i.1) : s = t :=
  (cAddEquiv (X := PrimeSpectrum.Top A) (fun i ↦ PrimeSpectrum.basicOpen (f i))
    (associatedAbPresheaf M) p).symm.injective (funext h)

private lemma inter_basicOpen {r q : ℕ} (f : Fin r → A) (i : Fin q → Fin r) :
    inter (X := PrimeSpectrum.Top A) (fun j ↦ PrimeSpectrum.basicOpen (f j)) i =
      PrimeSpectrum.basicOpen (∏ j, f (i j)) := by
  classical
  apply le_antisymm
  · intro x hx
    change (∏ j, f (i j)) ∈ x.asIdeal.primeCompl
    exact Submonoid.prod_mem _ (fun j _ ↦
      (iInf_le (fun j ↦ PrimeSpectrum.basicOpen (f (i j))) j) hx)
  · refine le_iInf fun j x hx ↦ ?_
    change f (i j) ∉ x.asIdeal
    change (∏ j, f (i j)) ∉ x.asIdeal at hx
    exact fun h ↦ hx (Ideal.IsPrime.prod_mem_iff.mpr ⟨j, Finset.mem_univ j, h⟩)

private lemma tupleFraction_surjective {r p : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (i : Fin (p + 1) → Fin r)
    (s : Stacks.LocalCohomology.moduleSections M (inter (X := PrimeSpectrum.Top A)
      (fun j ↦ PrimeSpectrum.basicOpen (f j)) i)) :
    ∃ (e : ℕ) (m : M), s = sectionFraction M m
      ((∏ j, f (i j)) ^ (e + 1)) _
      (by rw [inter_basicOpen]; simp) := by
  have H (U : Opens (PrimeSpectrum.Top A))
      (hU : U = PrimeSpectrum.basicOpen (∏ j, f (i j)))
      (s : Stacks.LocalCohomology.moduleSections M U) :
      ∃ (e : ℕ) (m : M) (h : U ≤ PrimeSpectrum.basicOpen ((∏ j, f (i j)) ^ (e + 1))),
        s = sectionFraction M m ((∏ j, f (i j)) ^ (e + 1)) U h := by
    subst U
    obtain ⟨e, m, hm⟩ := sectionFraction_surjective M (∏ j, f (i j)) s
    exact ⟨e, m, by simp, hm⟩
  obtain ⟨e, m, h, hm⟩ := H _ (inter_basicOpen f i) s
  exact ⟨e, m, hm⟩

private lemma koszulCechFraction_eq_zero {r p : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (i : Fin (p + 1) → Fin r) (h : koszulCechFraction f M e p t i = 0) :
    ∃ k, (∏ j, f (i j)) ^ k • t (koszulBasisWedge p i) = 0 := by
  let g := ∏ j, f (i j)
  have hz : LocalizedModule.mk ((-1 : A) ^ p • t (koszulBasisWedge p i))
      (⟨g ^ (e + 1), e + 1, rfl⟩ : Submonoid.powers g) = 0 := by
    rw [← LocalizedModule.zero_mk (1 : Submonoid.powers g)]
    apply away_mk_eq_of_stalks M g _ _ ⟨g ^ (e + 1), e + 1, rfl⟩ 1
      (fun x ↦ pow_mem (S := x.1.asIdeal.primeCompl) (show g ∈ x.1.asIdeal.primeCompl from x.2) _)
      (fun x ↦ x.1.asIdeal.primeCompl.one_mem)
    intro x
    have hx : x.1 ∈ inter (X := PrimeSpectrum.Top A)
        (fun j ↦ PrimeSpectrum.basicOpen (f j)) i :=
      (inter_basicOpen f i).ge x.2
    have H := moduleSections_apply_congr h ⟨x.1, hx⟩
    change LocalizedModule.mk ((-1 : A) ^ p • t (koszulBasisWedge p i))
      ⟨∏ j, f (i j) ^ (e + 1), _⟩ = 0 at H
    simpa only [Finset.prod_pow, LocalizedModule.zero_mk] using H
  obtain ⟨k, hk⟩ := (LocalizedModule.mk_powers_eq_zero_iff g _ _).mp hz
  refine ⟨k, ?_⟩
  have H := congrArg (fun z : M ↦ (-1 : A) ^ p • z) hk
  have hsign (z : M) : (-1 : A) ^ p • ((-1 : A) ^ p • z) = z := by
    rw [smul_smul, ← mul_pow]
    simp
  rw [smul_comm ((-1 : A) ^ p) (g ^ k), hsign, smul_zero] at H
  exact H

/-- A linear form whose associated alternating Čech cochain vanishes is killed by a transition
of the direct system. -/
theorem koszulStageComponent_eventually_zero {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e p : ℕ)
    (t : (koszulIdealComplexPower f e).X p →ₗ[A] M)
    (h : koszulStageComponent f M e p t = 0) :
    ∃ k, ((koszulHomDiagram f M).map (homOfLE (Nat.le_add_right e k))).f p t = 0 := by
  classical
  let I := OrdIndex (I := Fin r) p
  let : Fintype I := Fintype.ofFinite I
  have hk (i : I) : ∃ k, (∏ j, f (i.1 j)) ^ k • t (koszulBasisWedge p i.1) = 0 :=
    koszulCechFraction_eq_zero f M e t i.1
      (congrArg (fun s ↦ s.1 i.1) h)
  choose k hk using hk
  let N := ∑ i, k i
  refine ⟨N, ?_⟩
  apply (orderedExteriorBasis (A := A) r p).ext
  intro i
  have hN : k i ≤ N := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  rw [orderedExteriorBasis_apply]
  refine (koszulHomDiagram_map_wedge f M e N p t i.1).trans ?_
  change (∏ j, f (i.1 j)) ^ N • t (koszulBasisWedge p i.1) = 0
  rw [← Nat.sub_add_cancel hN, pow_add, mul_smul, hk, smul_zero]

/-- Every alternating Čech cochain comes from a linear form at some stage of the direct
system. -/
theorem koszulStageComponent_jointly_surjective {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (p : ℕ)
    (s : alternatingSubgroup (X := PrimeSpectrum.Top A)
      (fun i ↦ PrimeSpectrum.basicOpen (f i)) (associatedAbPresheaf M) p) :
    ∃ e t, koszulStageComponent f M e p t = s := by
  classical
  let I := OrdIndex (I := Fin r) p
  let : Fintype I := Fintype.ofFinite I
  choose e m hm using fun i : I ↦ tupleFraction_surjective f M i.1 (s.1 i.1)
  let N := ∑ i, e i
  let t : (⋀[A]^(p + 1) (Fin r → A)) →ₗ[A] M :=
    (orderedExteriorBasis (A := A) r p).constr A
      (fun i ↦ (-1 : A) ^ p • ((∏ j, f (i.1 j)) ^ (N - e i) • m i))
  refine ⟨N, t, alternating_ext_ordered f M fun i ↦ ?_⟩
  change koszulCechFraction f M N p t i.1 = s.1 i.1
  rw [hm]
  apply Subtype.ext; funext x
  have ht : t (koszulBasisWedge p i.1) =
      (-1 : A) ^ p • ((∏ j, f (i.1 j)) ^ (N - e i) • m i) := by
    rw [← orderedExteriorBasis_apply, Module.Basis.constr_basis]
  change LocalizedModule.mk ((-1 : A) ^ p • t (koszulBasisWedge p i.1)) _ =
    LocalizedModule.mk (m i) _
  rw [ht, smul_smul, ← mul_pow]
  simp only [neg_mul, one_mul, neg_neg, one_pow, one_smul]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  have hN : e i ≤ N := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  simp only [one_smul, Submonoid.smul_def, smul_smul, ← pow_add, Finset.prod_pow]
  congr 2
  omega

/-- **Stacks Project, Tag 08D0.** The alternating Čech complex of `M^~` for the basic opens of
a finite family is the filtered colimit of the contragredient complexes of the truncated Koszul
complexes on the powers of that family. -/
@[ega "III 2.1.2" "special case"]
noncomputable def koszulCoconeIsColimit {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) : IsColimit (koszulCocone f M) := by
  apply HomologicalComplex.isColimitOfEval
  intro p
  let E := HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℕ) p
  let F := koszulHomDiagram f M ⋙ E
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{max u v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{max u v, max u v} _
  letI : ReflectsColimit F (forget AddCommGrpCat.{max u v}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget AddCommGrpCat.{max u v})
    (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · change ∀ s : alternatingSubgroup (X := PrimeSpectrum.Top A)
      (fun i ↦ PrimeSpectrum.basicOpen (f i)) (associatedAbPresheaf M) p,
        ∃ e t, s = koszulStageComponent f M e p t
    exact fun s ↦ (koszulStageComponent_jointly_surjective f M p s).imp fun _ ⟨t, h⟩ ↦ ⟨t, h.symm⟩
  · intro e t s h
    change ((koszulIdealComplexPower f e).X p →ₗ[A] M) at t s
    change koszulStageComponent f M e p t = koszulStageComponent f M e p s at h
    have hz : koszulStageComponent f M e p (t - s) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨k, hk⟩ := koszulStageComponent_eventually_zero f M e p (t - s) hz
    refine ⟨e + k, homOfLE (Nat.le_add_right e k), ?_⟩
    change ((koszulHomDiagram f M).map (homOfLE (Nat.le_add_right e k))).f p t =
      ((koszulHomDiagram f M).map (homOfLE (Nat.le_add_right e k))).f p s
    exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans hk)

/-- **Stacks Project, Tag 08D0.** The canonical identification between the colimit of the
contragredient Koszul complexes and the alternating Čech complex of `M^~`. -/
@[stacks 08D0, ega "III 2.1.2" "special case"]
noncomputable def alternatingCechComplexIso {r : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A) :
    colimit (koszulHomDiagram f M) ≅ moduleAlternatingCechComplex f M :=
  colimit.isoColimitCocone ⟨koszulCocone f M, koszulCoconeIsColimit f M⟩

/-- The identification composed with the colimit inclusion of a stage is the comparison map of
that stage. -/
theorem colimit_ι_alternatingCechComplexIso_hom {r : ℕ} (f : Fin r → A)
    (M : ModuleCat.{v} A) (e : ℕ) :
    colimit.ι (koszulHomDiagram f M) e ≫ (alternatingCechComplexIso f M).hom =
      koszulStageMap f M e :=
  colimit.isoColimitCocone_ι_hom ⟨koszulCocone f M, koszulCoconeIsColimit f M⟩ e

/-- **Stacks Project, Tag 08D0.** The identification is natural in the module. -/
@[stacks 08D0]
theorem alternatingCechComplexIso_naturality {r : ℕ} (f : Fin r → A)
    (M N : ModuleCat.{v} A) (g : M ⟶ N) :
    (alternatingCechComplexIso f M).hom ≫ moduleAlternatingCechMap f g =
      koszulHomColimitMap f g ≫ (alternatingCechComplexIso f N).hom := by
  apply colimit.hom_ext
  intro e
  rw [← Category.assoc, colimit_ι_alternatingCechComplexIso_hom, koszulHomColimitMap,
    colim_map, ι_colimMap_assoc]
  change _ = (koszulHomDiagramMap f g).app e ≫
    colimit.ι (koszulHomDiagram f N) e ≫ (alternatingCechComplexIso f N).hom
  rw [colimit_ι_alternatingCechComplexIso_hom]
  exact koszulStageMap_naturality f g e

/-- **Stacks Project, Tag 08D0.** On the stage-`e` linear form `t` the identification takes the
value `(-1)^p t([i₀, …, iₚ]) / ∏ⱼ f(iⱼ)^(e+1)` at the tuple `i`. -/
@[stacks 08D0]
theorem alternatingCechComplexIso_ι_apply {r : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A)
    (e p : ℕ) (t : (koszulIdealComplexPower f e).X p →ₗ[A] M) (i : Fin (p + 1) → Fin r) :
    (((colimit.ι (koszulHomDiagram f M) e ≫
        (alternatingCechComplexIso f M).hom).f p) t).1 i =
      koszulCechFraction f M e p t i :=
  congrArg
    (fun φ : koszulHomComplex (koszulIdealComplexPower f e) M ⟶
      moduleAlternatingCechComplex f M ↦ ((φ.f p) t).1 i)
    (colimit_ι_alternatingCechComplexIso_hom f M e)

end Koszul
