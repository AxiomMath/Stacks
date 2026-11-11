module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.CompatibleFractions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Surjectivity of the canonical map to sections away from a vanishing locus

Let `A` be a commutative ring, `I ⊆ A` a finitely generated ideal and `M` an `A`-module. The
canonical map
`colim_n Hom_A(I ^ n, M) ⟶ Γ(Spec(A) \ V(I), M̃)`
of `IdealPowerSections.Basic` is here shown to hit every section, once the target of the
representatives is replaced by the quotient of `M` by the submodule annihilated by a power of
`I` — which Tag 01PN shows is unavoidable.

## Main results

* `exists_compatible_numerators_tilde`, `exists_compatible_numerators_of_section` — a section
  restricts on each basic open `D(fᵢ)` of a finite family of elements to a fraction `xᵢ / fᵢⁿ` with
  a single exponent, whose numerators satisfy the cross relation `fⱼⁿ • xᵢ = fᵢⁿ • xⱼ`;
  respectively for a tilde sheaf on an arbitrary open and for the sections module of
  `IdealPowerSections.Basic`.
* `section_eq_of_restrict_basicOpen_eq` — two sections away from `V(I)` that agree on the basic
  opens of a generating family are equal.
* `exists_hom_idealPow_representing_section` — **the surjectivity statement.** For every section
  `s` there are an exponent `N` and an `A`-linear map `φ : I ^ N ⟶ M / M_N` such that on every
  basic open `D(f)` with `f ∈ I`, and for every representative `m` of `φ (f ^ N)`, the section `s`
  restricts to `m / f ^ N`.
* `canonicalMapToSections_surjective` and `epi_canonicalMapToSections` — when `I` annihilates no
  nonzero element of `M`, the quotient is trivial and the map of `Basic` is itself surjective.
* `exists_normalizedFractionData` — a section of `Ñ` over *any* quasi-compact open `U` of
  `Spec R` is given by fractions `a i / b i` on a finite cover of `U` by basic opens
  `D(b i) ⊆ U`, produced from the section rather than prescribed, whose numerators and
  denominators satisfy `b j • a i = b i • a j` in `N` on the nose rather than after localizing.
* `spanRangeLift` and `smul_linearCombination_eq` — the linear algebra of such data: the cross
  relations say exactly that `ker (Finsupp.linearCombination A b) ≤ ker
  (Finsupp.linearCombination A a)`, so `b i ↦ a i` induces a map out of `span (range b)`.

## Implementation notes

Sections of a tilde sheaf are subtypes of dependent functions on the open, and restriction along
an inclusion of opens restricts those functions. So extensionality over a cover is
`Subtype.ext ∘ funext` together with the observation that every point of the complement of `V(I)`
misses some generator; no sheaf gluing is invoked. The localization input is Mathlib's
`IsLocalizedModule.Away` instance for `tilde.toOpen N (basicOpen f)`.

The displayed condition of `exists_hom_idealPow_representing_section` is the local formula by
which the canonical map out of the system `n ↦ Hom_A(I ^ n, M / Mₙ)` is pinned, so the statement
says that `s` is in the image of that map with no comparison of `M̃` with `(M/M_N)~` needed: the
only thing such a comparison would supply is that a change of representative `m` does not change
`m / f ^ N`, and that holds because `f ^ N` already annihilates `M_N`.

The submodule `Mₙ` of elements annihilated by `I ^ n` is Mathlib's `Submodule.torsionBySet`.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.StructureSheaf

universe u v w

namespace Stacks.AlgebraicGeometry.IdealPowerSections

/-!
### Sections of a tilde sheaf as dependent functions
-/

section Tilde

variable {R : CommRingCat.{w}} (N : ModuleCat.{w} R)

/-- Restricting a section of `Ñ` along an inclusion of opens restricts the underlying dependent
function. -/
public lemma tilde_section_val_res {U V : Opens (PrimeSpectrum R)} (h : V ≤ U)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U)) (x : ↥V) :
    ((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE h).op s).1 x
      = s.1 ⟨x.1, h x.2⟩ := rfl

/-- Two sections of `Ñ` on the same open with the same underlying function are equal. -/
public lemma tilde_section_ext {U : Opens (PrimeSpectrum R)}
    {s t : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U)}
    (h : ∀ x : ↥U, s.1 x = t.1 x) : s = t := Subtype.ext (funext h)

/-- Restriction of sections of `Ñ` is transitive on the nose. -/
public lemma tilde_section_res_res {U V W : Opens (PrimeSpectrum R)} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U)) :
    (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE h₂).op
        ((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE h₁).op s)
      = (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE (h₂.trans h₁)).op s :=
  tilde_section_ext N fun _ => rfl

/-- Sections of `Ñ` that agree on each member of a family of opens covering `U` are equal. -/
public lemma tilde_section_ext_of_cover {U : Opens (PrimeSpectrum R)} {ι : Type*}
    (V : ι → Opens (PrimeSpectrum R)) (hVU : ∀ i, V i ≤ U)
    (hcover : ∀ p ∈ U, ∃ i, p ∈ V i)
    {s t : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U)}
    (h : ∀ i, (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE (hVU i)).op s
      = (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE (hVU i)).op t) :
    s = t := by
  refine tilde_section_ext N fun x => ?_
  obtain ⟨i, hi⟩ := hcover x.1 x.2
  exact (tilde_section_val_res N (hVU i) s ⟨x.1, hi⟩).symm.trans
    ((congrFun (congrArg Subtype.val (h i)) ⟨x.1, hi⟩).trans
      (tilde_section_val_res N (hVU i) t ⟨x.1, hi⟩))

/-- Every section of `Ñ` on a basic open `D(f)` is a fraction `m / f ^ k`. -/
public lemma exists_tildeBasicOpenFraction_eq (f : R)
    (t : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op (PrimeSpectrum.basicOpen f))) :
    ∃ (k : ℕ) (m : N), tildeBasicOpenFraction N f k m = t := by
  obtain ⟨⟨m, ⟨a, ha⟩⟩, h⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom t
  obtain ⟨k, rfl⟩ := ha
  exact ⟨k, m, IsLocalizedModule.mk'_eq_iff.mpr h.symm⟩

/-- Clearing the denominator of `m / f ^ k` returns the image of `m`. -/
public lemma pow_smul_tildeBasicOpenFraction (f : R) (k : ℕ) (m : N) :
    (f ^ k) • tildeBasicOpenFraction N f k m
      = (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom m := by
  have h := IsLocalizedModule.mk'_cancel' (S := Submonoid.powers f)
    (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom m ⟨f ^ k, ⟨k, rfl⟩⟩
  rwa [Submonoid.smul_def] at h

/-- The fraction `m / f ^ k` is also `f ^ j • m / f ^ (k + j)`. -/
public lemma tildeBasicOpenFraction_pow_smul (f : R) (k j : ℕ) (m : N) :
    tildeBasicOpenFraction N f (k + j) (f ^ j • m) = tildeBasicOpenFraction N f k m := by
  refine (IsLocalizedModule.mk'_eq_mk'_iff (S := Submonoid.powers f)
    (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom _ _ _ _).mpr ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def]
  rw [pow_add, mul_smul]

/-- Scalar multiplication by a power of `f` is injective on sections of `Ñ` over `D(f)`. -/
public lemma tilde_section_eq_of_pow_smul_eq (f : R) (k : ℕ)
    {s t : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op (PrimeSpectrum.basicOpen f))}
    (h : (f ^ k) • s = (f ^ k) • t) : s = t :=
  (IsLocalizedModule.smul_inj (S := Submonoid.powers f)
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom ⟨f ^ k, ⟨k, rfl⟩⟩ s t).mp
    (by simpa only [Submonoid.smul_def] using h)

/-- Clearing the denominator of the restriction of `m / c ^ k` to a smaller open. -/
public lemma pow_smul_restrict_tildeBasicOpenFraction (c : R) (k : ℕ) (m : N)
    {V : Opens (PrimeSpectrum R)} (hVc : V ≤ PrimeSpectrum.basicOpen c) :
    (c ^ k) • (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hVc).op
        (tildeBasicOpenFraction N c k m)
      = (tilde.toOpen N V).hom m := by
  have h₁ : (c ^ k) • (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hVc).op
        (tildeBasicOpenFraction N c k m)
      = (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hVc).op
        ((c ^ k) • tildeBasicOpenFraction N c k m) :=
    (((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hVc).op).hom.map_smul _ _).symm
  rw [h₁, pow_smul_tildeBasicOpenFraction]
  exact rfl

/-- If a section restricts to the fraction `m / c ^ k` on `D(c)`, then on any smaller open its
`c ^ k`-multiple is the image of `m`. -/
public lemma pow_smul_restrict_eq_toOpen {U : Opens (PrimeSpectrum R)} (c : R) (k : ℕ) (m : N)
    (hcU : PrimeSpectrum.basicOpen c ≤ U)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U))
    (hm : (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hcU).op s
      = tildeBasicOpenFraction N c k m)
    {V : Opens (PrimeSpectrum R)} (hVc : V ≤ PrimeSpectrum.basicOpen c) (hVU : V ≤ U) :
    (c ^ k) • (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hVU).op s
      = (tilde.toOpen N V).hom m := by
  have hres := tilde_section_res_res N hcU hVc s
  rw [hm] at hres
  rw [← hres]
  exact pow_smul_restrict_tildeBasicOpenFraction N c k m hVc

/-- **Clearing denominators on an overlap.** If one section of `Ñ` restricts to `a / f ^ k` on
`D(f)` and to `b / g ^ k` on `D(g)`, then the numerators satisfy the cross relation
`g ^ k • a = f ^ k • b` after multiplication by a power of `f * g`. -/
public lemma exists_pow_smul_eq_of_restrict_eq {U : Opens (PrimeSpectrum R)} (f g : R) (k : ℕ)
    (a b : N) (hfU : PrimeSpectrum.basicOpen f ≤ U) (hgU : PrimeSpectrum.basicOpen g ≤ U)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U))
    (ha : (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hfU).op s
      = tildeBasicOpenFraction N f k a)
    (hb : (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hgU).op s
      = tildeBasicOpenFraction N g k b) :
    ∃ q : ℕ, (f * g) ^ q • (g ^ k • a) = (f * g) ^ q • (f ^ k • b) := by
  have h₁ := PrimeSpectrum.basicOpen_mul_le_left f g
  have h₂ := PrimeSpectrum.basicOpen_mul_le_right f g
  have hA := pow_smul_restrict_eq_toOpen N f k a hfU s ha h₁ (h₁.trans hfU)
  have hB := pow_smul_restrict_eq_toOpen N g k b hgU s hb h₂ (h₁.trans hfU)
  have hswap : (g ^ k) • ((f ^ k) • (modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE (h₁.trans hfU)).op s)
      = (f ^ k) • ((g ^ k) • (modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE (h₁.trans hfU)).op s) :=
    (smul_smul _ _ _).trans
      ((congrArg (fun r : R => r • (modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE (h₁.trans hfU)).op s) (mul_comm (g ^ k) (f ^ k))).trans
          (smul_smul _ _ _).symm)
  have hfinal : (tilde.toOpen N (PrimeSpectrum.basicOpen (f * g))).hom (g ^ k • a)
      = (tilde.toOpen N (PrimeSpectrum.basicOpen (f * g))).hom (f ^ k • b) :=
    (map_smul _ (g ^ k) a).trans
      ((congrArg (fun z => (g ^ k) • z) hA.symm).trans
        (hswap.trans
          ((congrArg (fun z => (f ^ k) • z) hB).trans (map_smul _ (f ^ k) b).symm)))
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (f * g))
    (tilde.toOpen N (PrimeSpectrum.basicOpen (f * g))).hom).mp hfinal
  obtain ⟨q, hq⟩ := c.2
  exact ⟨q, by simpa only [Submonoid.smul_def, hq] using hc⟩

/-- **The overlap match.** Let `s` be a section of `Ñ` over `U` restricting on `D(d)` to the
fraction `y / d ^ k`, and let `t = z / c ^ l` be a section over `D(c)`, with `D(c)` and `D(d)`
inside `U`. If scalars `r, r'` factor one power of `c * d` as `r * d ^ k` and as `r' * c ^ l`
and satisfy `r • y = r' • z`, then `s` and `t` agree on `D(c * d)`. -/
public lemma restrict_eq_restrict_of_pow_smul_eq {U : Opens (PrimeSpectrum R)}
    (c d : R) (k l j : ℕ) (y z : N) (r r' : R)
    (hcU : PrimeSpectrum.basicOpen c ≤ U) (hdU : PrimeSpectrum.basicOpen d ≤ U)
    (hcd : PrimeSpectrum.basicOpen (c * d) ≤ PrimeSpectrum.basicOpen c)
    (hcd' : PrimeSpectrum.basicOpen (c * d) ≤ PrimeSpectrum.basicOpen d)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U))
    (hy : (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hdU).op s
      = tildeBasicOpenFraction N d k y)
    (t : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op (PrimeSpectrum.basicOpen c)))
    (ht : t = tildeBasicOpenFraction N c l z)
    (hr : (c * d) ^ j = r * d ^ k) (hr' : (c * d) ^ j = r' * c ^ l)
    (hyz : r • y = r' • z) :
    (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hcd).op
        ((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hcU).op s)
      = (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hcd).op t := by
  refine tilde_section_eq_of_pow_smul_eq N (c * d) j ?_
  have hu := pow_smul_restrict_eq_toOpen N d k y hdU s hy hcd' (hcd.trans hcU)
  have hv := pow_smul_restrict_tildeBasicOpenFraction N c l z hcd
  have hL : ((c * d) ^ j) • ((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hcd).op
        ((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE hcU).op s))
      = (tilde.toOpen N (PrimeSpectrum.basicOpen (c * d))).hom (r • y) := by
    rw [tilde_section_res_res N hcU hcd s, hr, mul_smul, hu]
    exact (map_smul _ _ _).symm
  have hR : ((c * d) ^ j) • ((modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE hcd).op t)
      = (tilde.toOpen N (PrimeSpectrum.basicOpen (c * d))).hom (r' • z) := by
    rw [ht, hr', mul_smul, hv]
    exact (map_smul _ _ _).symm
  exact hL.trans ((congrArg (fun w =>
    (tilde.toOpen N (PrimeSpectrum.basicOpen (c * d))).hom w) hyz).trans hR.symm)

/-- **Compatible numerators for a section of a tilde sheaf.** A section of `Ñ` on an open
containing the basic opens of a finite family `g` determines a single exponent `k` and
numerators `x i` satisfying the cross relation `g j ^ k • x i = g i ^ k • x j`, such that the
section restricts on each `D(g i)` to the fraction `x i / g i ^ k`. -/
public theorem exists_compatible_numerators_tilde {U : Opens (PrimeSpectrum R)} {ι : Type*}
    [Finite ι] (g : ι → R) (hgU : ∀ i, PrimeSpectrum.basicOpen (g i) ≤ U)
    (s : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (.op U)) :
    ∃ (k : ℕ) (x : ι → N), (∀ i j, g j ^ k • x i = g i ^ k • x j) ∧
      ∀ i, (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE (hgU i)).op s
        = tildeBasicOpenFraction N (g i) k (x i) := by
  classical
  obtain ⟨fι⟩ : Nonempty (Fintype ι) := ⟨Fintype.ofFinite ι⟩
  choose e y hey using fun i =>
    exists_tildeBasicOpenFraction_eq N (g i)
      ((modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE (hgU i)).op s)
  obtain ⟨k₀, a, hfrac⟩ : ∃ (k₀ : ℕ) (a : ι → N), ∀ i,
      (modulesSpecToSheaf.obj (tilde N)).presheaf.map (homOfLE (hgU i)).op s
        = tildeBasicOpenFraction N (g i) k₀ (a i) := by
    refine ⟨Finset.univ.sup e, fun i => g i ^ (Finset.univ.sup e - e i) • y i, fun i => ?_⟩
    have hle : e i ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ i)
    rw [← hey i]
    exact (tildeBasicOpenFraction_pow_smul N (g i) (e i) (Finset.univ.sup e - e i) (y i)).symm.trans
      (by rw [Nat.add_sub_cancel' hle])
  obtain ⟨Q, hbump⟩ : ∃ Q : ℕ, ∀ i j,
      (g i * g j) ^ Q • (g j ^ k₀ • a i) = (g i * g j) ^ Q • (g i ^ k₀ • a j) := by
    choose q hq using fun i j =>
      exists_pow_smul_eq_of_restrict_eq N (g i) (g j) k₀ (a i) (a j) (hgU i) (hgU j) s
        (hfrac i) (hfrac j)
    refine ⟨Finset.univ.sup fun i => Finset.univ.sup (q i), fun i j => ?_⟩
    have hqQ : q i j ≤ Finset.univ.sup fun i => Finset.univ.sup (q i) :=
      le_trans (Finset.le_sup (f := q i) (Finset.mem_univ j))
        (Finset.le_sup (f := fun i => Finset.univ.sup (q i)) (Finset.mem_univ i))
    obtain ⟨d, hd⟩ : ∃ d, (Finset.univ.sup fun i => Finset.univ.sup (q i)) = q i j + d :=
      ⟨_, (Nat.add_sub_cancel' hqQ).symm⟩
    rw [hd, pow_add, mul_comm ((g i * g j) ^ q i j) ((g i * g j) ^ d), mul_smul, mul_smul]
    exact congrArg _ (hq i j)
  refine ⟨k₀ + Q, fun i => g i ^ Q • a i, fun i j => ?_, fun i => ?_⟩
  · have h := hbump i j
    rw [smul_smul, smul_smul] at h
    rw [smul_smul, smul_smul,
      show g j ^ (k₀ + Q) * g i ^ Q = (g i * g j) ^ Q * g j ^ k₀ from by ring,
      show g i ^ (k₀ + Q) * g j ^ Q = (g i * g j) ^ Q * g i ^ k₀ from by ring]
    exact h
  · rw [hfrac i]
    exact (tildeBasicOpenFraction_pow_smul N (g i) k₀ Q (a i)).symm

end Tilde

/-! ### An element annihilating a module element locally annihilates it up to a power -/

section Radical

variable {R : Type w} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]

/-- If every prime not containing `g` contains some element annihilating `z`, then a power of
`g` annihilates `z`. This is the statement that `g` lies in the radical of the annihilator
of `z`. -/
public lemma exists_pow_smul_eq_zero_of_forall_prime {g : R} {z : N}
    (h : ∀ p : PrimeSpectrum R, g ∉ p.asIdeal → ∃ u, u ∉ p.asIdeal ∧ u • z = 0) :
    ∃ m : ℕ, g ^ m • z = 0 := by
  have hrad : g ∈ (Submodule.span R {z}).annihilator.radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hg
    obtain ⟨u, hu, huz⟩ := h p hg
    exact hu (hp ((Submodule.mem_annihilator_span_singleton z u).mpr huz))
  obtain ⟨m, hm⟩ := hrad
  exact ⟨m, (Submodule.mem_annihilator_span_singleton z _).mp hm⟩

end Radical

/-! ### Normalized local fractions for a section over a quasi-compact open

The extraction above is relative to a chosen generating family of `I`. The two statements here
are the shape in which a section of `Ñ` over an *arbitrary* quasi-compact open is given by
fractions: the cover is produced from the section rather than prescribed, and the cross
relations hold in `N` on the nose rather than after localizing. -/

section Normalize

variable {R : Type w} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]

/-- A section of `Ñ` over `U` is, near each point of `U`, the fraction `c / g` for a single
pair `(c, g)` valid at *every* point of `D(g)`. -/
public lemma exists_fraction_on_basicOpen (U : Opens (PrimeSpectrum R))
    (s : (structureSheafInType R N).1.obj (Opposite.op U)) (x : PrimeSpectrum R) (hx : x ∈ U) :
    ∃ (g : R) (_ : x ∈ PrimeSpectrum.basicOpen g) (_ : PrimeSpectrum.basicOpen g ≤ U) (c : N),
      ∀ (p : PrimeSpectrum R) (hp : g ∉ p.asIdeal) (hpU : p ∈ U),
        s.1 ⟨p, hpU⟩ = LocalizedModule.mk c ⟨g, hp⟩ := by
  obtain ⟨g, hxg, igU, c, H⟩ := exists_const U s x hx
  exact ⟨g, hxg, igU, c, fun p hp _ => (congrFun (congrArg Subtype.val H) ⟨p, hp⟩).symm⟩

/-- **Normalized local data.** A section of `Ñ` over a quasi-compact open `U` is given by
fractions `a i / b i` on a finite cover of `U` by basic opens `D (b i) ⊆ U`, with the
numerators and denominators satisfying the cross relations `b j • a i = b i • a j` exactly,
not merely after localizing. -/
public lemma exists_normalizedFractionData (U : Opens (PrimeSpectrum R))
    (hU : IsCompact (↑U : Set (PrimeSpectrum R)))
    (s : (structureSheafInType R N).1.obj (Opposite.op U)) :
    ∃ (ι : Type w) (_ : Fintype ι) (a : ι → N) (b : ι → R),
      (∀ i, PrimeSpectrum.basicOpen (b i) ≤ U) ∧
      ((↑U : Set (PrimeSpectrum R)) ⊆
        ⋃ i, (↑(PrimeSpectrum.basicOpen (b i)) : Set (PrimeSpectrum R))) ∧
      (∀ i j, b j • a i = b i • a j) ∧
      (∀ (i : ι) (p : PrimeSpectrum R) (hb : b i ∉ p.asIdeal) (hp : p ∈ U),
        s.1 ⟨p, hp⟩ = LocalizedModule.mk (a i) ⟨b i, hb⟩) := by
  classical
  choose g hxg igU c key using fun x : U => exists_fraction_on_basicOpen U s x.1 x.2
  obtain ⟨T, hT⟩ := hU.elim_finite_subcover
    (fun x : U => (↑(PrimeSpectrum.basicOpen (g x)) : Set (PrimeSpectrum R)))
    (fun _ => (PrimeSpectrum.basicOpen _).2)
    (fun p hp => Set.mem_iUnion_of_mem (⟨p, hp⟩ : U) (hxg ⟨p, hp⟩))
  have hcross : ∀ i j : {x : U // x ∈ T}, ∃ mm : ℕ,
      (g i.1 * g j.1) ^ mm • (g j.1 • c i.1 - g i.1 • c j.1) = 0 := by
    intro i j
    apply exists_pow_smul_eq_zero_of_forall_prime
    intro p hp
    have hpi : g i.1 ∉ p.asIdeal := fun h => hp (Ideal.mul_mem_right _ _ h)
    have hpj : g j.1 ∉ p.asIdeal := fun h => hp (Ideal.mul_mem_left _ _ h)
    have hpU : p ∈ U := igU i.1 hpi
    obtain ⟨u, hu⟩ :=
      LocalizedModule.mk_eq.mp ((key i.1 p hpi hpU).symm.trans (key j.1 p hpj hpU))
    refine ⟨u.1, u.2, ?_⟩
    rw [smul_sub, sub_eq_zero]
    simpa [Submonoid.smul_def] using hu
  choose mfun hmfun using hcross
  set mm : ℕ := Finset.univ.sup (fun ij : {x : U // x ∈ T} × {x : U // x ∈ T} =>
    mfun ij.1 ij.2) with hmdef
  have hm : ∀ i j : {x : U // x ∈ T},
      (g i.1 * g j.1) ^ mm • (g j.1 • c i.1 - g i.1 • c j.1) = 0 := by
    intro i j
    have hle : mfun i j ≤ mm := Finset.le_sup
      (f := fun ij : {x : U // x ∈ T} × {x : U // x ∈ T} => mfun ij.1 ij.2)
      (Finset.mem_univ (i, j))
    have hsplit : (g i.1 * g j.1) ^ mm
        = (g i.1 * g j.1) ^ (mm - mfun i j) * (g i.1 * g j.1) ^ (mfun i j) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_smul, hmfun i j, smul_zero]
  refine ⟨{x : U // x ∈ T}, inferInstance,
    fun i => g i.1 ^ mm • c i.1, fun i => g i.1 ^ (mm + 1), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [PrimeSpectrum.basicOpen_pow _ _ (Nat.succ_pos mm)]
    exact igU i.1
  · intro p hp
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp (hT hp)
    exact Set.mem_iUnion_of_mem (⟨x, hx⟩ : {x : U // x ∈ T}) (by
      simpa [PrimeSpectrum.basicOpen_pow _ _ (Nat.succ_pos mm)] using hpx)
  · intro i j
    have h := hm i j
    rw [smul_sub, sub_eq_zero, smul_smul, smul_smul, mul_pow] at h
    rw [smul_smul, smul_smul]
    convert h using 2 <;> ring
  · intro i p hb hp
    have hgi : g i.1 ∉ p.asIdeal := fun h => hb (Ideal.pow_mem_of_mem _ h _ (Nat.succ_pos mm))
    refine (key i.1 p hgi hp).trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩)
    simp only [Submonoid.smul_def, one_smul, smul_smul]
    congr 1
    ring

/-- The complement of the vanishing locus of a finitely generated ideal is quasi-compact. -/
public lemma isCompact_zeroLocus_compl {J : Ideal R} (hJ : J.FG) :
    IsCompact ((PrimeSpectrum.zeroLocus (J : Set R))ᶜ) :=
  (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨J, hJ, rfl⟩).1

end Normalize

/-! ### The linear algebra of the normalized data -/

section Algebra

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- If no nonzero element of `M` is annihilated by all of `I`, then no nonzero element is
annihilated by all of `I ^ n`. -/
public lemma eq_zero_of_forall_pow_smul_eq_zero {I : Ideal A}
    (hM : ∀ x : M, (∀ r ∈ I, r • x = 0) → x = 0) (n : ℕ) (x : M)
    (hx : ∀ r ∈ I ^ n, r • x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa using hx 1 (by simp)
  | succ n ih =>
    refine hM x fun r hr => ih (r • x) fun t ht => ?_
    rw [smul_smul]
    exact hx _ (by rw [pow_succ]; exact Ideal.mul_mem_mul ht hr)

/-- An element annihilated by every member of a family is annihilated by the ideal the family
generates. -/
public lemma smul_eq_zero_of_mem_span_range {ι : Type*} (b : ι → A) (y : M)
    (hy : ∀ i, b i • y = 0) : ∀ r ∈ Ideal.span (Set.range b), r • y = 0 := by
  intro r hr
  induction hr using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hy i
  | zero => simp
  | add x y hx hy hx' hy' => rw [add_smul, hx', hy', add_zero]
  | smul c x hx hx' => rw [smul_eq_mul, mul_smul, hx', smul_zero]

/-- The linear map on `span (range b) = range (Finsupp.linearCombination A b)` induced by
`b i ↦ a i`. It exists exactly when the relations between the `b i` are relations between
the `a i`, which is the hypothesis `hker`. -/
public noncomputable def spanRangeLift {ι : Type*} (a : ι → M) (b : ι → A)
    (hker : LinearMap.ker (Finsupp.linearCombination A b)
      ≤ LinearMap.ker (Finsupp.linearCombination A a)) :
    ↥(LinearMap.range (Finsupp.linearCombination A b)) →ₗ[A] M :=
  (Submodule.liftQ _ (Finsupp.linearCombination A a) hker).comp
    (Finsupp.linearCombination A b).quotKerEquivRange.symm.toLinearMap

/-- `spanRangeLift` sends the value of a linear combination of the `b i` to the corresponding
linear combination of the `a i`. -/
public lemma spanRangeLift_apply_of_val_eq {ι : Type*} (a : ι → M) (b : ι → A)
    (hker : LinearMap.ker (Finsupp.linearCombination A b)
      ≤ LinearMap.ker (Finsupp.linearCombination A a)) (cf : ι →₀ A)
    (y : ↥(LinearMap.range (Finsupp.linearCombination A b)))
    (hy : (y : A) = Finsupp.linearCombination A b cf) :
    spanRangeLift a b hker y = Finsupp.linearCombination A a cf := by
  have hy' : y = ⟨Finsupp.linearCombination A b cf, ⟨cf, rfl⟩⟩ := Subtype.ext hy
  subst hy'
  have hq : (Finsupp.linearCombination A b).quotKerEquivRange.symm
      ⟨Finsupp.linearCombination A b cf, ⟨cf, rfl⟩⟩ = Submodule.Quotient.mk cf :=
    (LinearEquiv.symm_apply_eq _).mpr
      (Subtype.ext (LinearMap.quotKerEquivRange_apply_mk _ cf).symm)
  change (Submodule.liftQ _ (Finsupp.linearCombination A a) hker)
    ((Finsupp.linearCombination A b).quotKerEquivRange.symm
      ⟨Finsupp.linearCombination A b cf, ⟨cf, rfl⟩⟩) = _
  rw [hq]
  exact Submodule.liftQ_apply _ _ cf

/-- The cross relations `b j • a i = b i • a j` let one move `b i` across a linear
combination: `b i • Σ cₖ aₖ = (Σ cₖ bₖ) • a i`. -/
public lemma smul_linearCombination_eq {ι : Type*} (a : ι → M) (b : ι → A)
    (hcr : ∀ i j, b j • a i = b i • a j) (i : ι) (cf : ι →₀ A) :
    b i • Finsupp.linearCombination A a cf = (Finsupp.linearCombination A b cf) • a i := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.smul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, ← hcr i k, smul_smul, smul_eq_mul]

end Algebra

/-!
### The extraction, for the sections module of Tag 01PM
-/

section Affine

variable (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- Every prime outside the lifted vanishing locus misses one of the generators. -/
public lemma exists_notMem_of_mem_complementVanishing {ι : Type*} (g : ι → A)
    (hspan : I ≤ Ideal.span (Set.range g)) (p : PrimeSpectrum (ULift.{v} A))
    (hp : p ∈ complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I)) :
    ∃ i, (ULift.up.{v} (g i) : ULift.{v} A) ∉ p.asIdeal := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  refine hp fun b hb => ?_
  have hdown : ULift.down.{v} b ∈ Ideal.span (Set.range g) :=
    hspan ((mem_liftedIdeal A I).mp hb)
  have key : ∀ z ∈ Ideal.span (Set.range g), (ULift.up.{v} z : ULift.{v} A) ∈ p.asIdeal := by
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      exact hc i
    · exact p.asIdeal.zero_mem
    · intro z₁ z₂ _ _ hz₁ hz₂
      exact p.asIdeal.add_mem hz₁ hz₂
    · intro c z _ hz
      exact p.asIdeal.mul_mem_left _ hz
  exact key _ hdown

/-- **Compatible numerators for a section away from `V(I)`.** A section of `M̃` on
`Spec(A) \ V(I)` determines an exponent `n` and numerators `x i`, indexed by any finite family of
elements of `I`, satisfying the cross relation `g j ^ n • x i = g i ^ n • x j`, such that the
section restricts on each basic open `D(g i)` to the fraction `x i / g i ^ n`. -/
public theorem exists_compatible_numerators_of_section {ι : Type*} [Finite ι] (g : ι → A)
    (hg : ∀ i, g i ∈ I) (s : sectionsOnComplement A I M) :
    ∃ (n : ℕ) (x : ι → M), (∀ i j, g j ^ n • x i = g i ^ n • x j) ∧
      ∀ i, restrictToBasicOpen A I M (g i) (hg i) s = basicOpenFraction A M (g i) n (x i) := by
  obtain ⟨n, x, hx, hfrac⟩ :=
    exists_compatible_numerators_tilde (R := CommRingCat.of (ULift.{v} A))
      (ModuleCat.of (ULift.{v} A) (ULift.{u} M))
      (U := complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I))
      (g := fun i => ULift.up.{v} (g i))
      (hgU := fun i => basicOpen_le_complementVanishing (ULift.{v} A)
        (liftedIdeal.{u, v} A I) (ULift.up (g i)) (hg i)) (s := s)
  exact ⟨n, fun i => (x i).down, fun i j => congrArg ULift.down (hx i j), fun i => hfrac i⟩

/-- Two sections of `M̃` on `Spec(A) \ V(I)` that agree on the basic opens of a generating family
of `I` are equal. -/
public theorem section_eq_of_restrict_basicOpen_eq {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)
    (hspan : I ≤ Ideal.span (Set.range g)) {s t : sectionsOnComplement A I M}
    (h : ∀ i, restrictToBasicOpen A I M (g i) (hg i) s
      = restrictToBasicOpen A I M (g i) (hg i) t) : s = t :=
  tilde_section_ext_of_cover (R := CommRingCat.of (ULift.{v} A))
    (ModuleCat.of (ULift.{v} A) (ULift.{u} M))
    (U := complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I))
    (V := fun i => PrimeSpectrum.basicOpen (ULift.up.{v} (g i)))
    (hVU := fun i => basicOpen_le_complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I)
      (ULift.up (g i)) (hg i))
    (hcover := fun p hp => exists_notMem_of_mem_complementVanishing A I g hspan p hp) (h := h)

/-!
### The match: the extracted map has the section as its image
-/

/-- **Every section is represented by a map out of a power of `I`.** For a finitely generated
ideal `I` and any section `s` of `M̃` on `Spec(A) \ V(I)` there are an exponent `N` and an
`A`-linear map `φ : I ^ N ⟶ M / M_N`, where `M_N` is the submodule annihilated by `I ^ N`, such
that on every basic open `D(f)` with `f ∈ I` the section `s` restricts to `m / f ^ N` for every
representative `m` of `φ (f ^ N)`.

The displayed condition is exactly the local formula by which the canonical map out of the
system `n ↦ Hom_A(I ^ n, M / Mₙ)` is pinned, so the statement says that `s` is in the image of
that map. -/
public theorem exists_hom_idealPow_representing_section (hI : I.FG)
    (s : sectionsOnComplement A I M) :
    ∃ (N : ℕ) (φ : (I ^ N : Ideal A) →ₗ[A]
        M ⧸ Submodule.torsionBySet A M ((I ^ N : Ideal A) : Set A)),
      ∀ (f : A) (hf : f ∈ I) (m : M),
        φ ⟨f ^ N, Ideal.pow_mem_pow hf N⟩ = Submodule.Quotient.mk m →
          restrictToBasicOpen A I M f hf s = basicOpenFraction A M f N m := by
  classical
  obtain ⟨t, g, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  rw [Ideal.submodule_span_eq] at hspan
  subst hspan
  have hg : ∀ i, g i ∈ Ideal.span (Set.range g) := fun i =>
    Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨n, x, hx, hfrac⟩ :=
    exists_compatible_numerators_of_section A (Ideal.span (Set.range g)) M g hg s
  obtain ⟨N, φ, hφN, hnN⟩ : ∃ (N : ℕ) (φ : (Ideal.span (Set.range g) ^ N : Ideal A) →ₗ[A]
      M ⧸ Submodule.torsionBySet A M
        ((Ideal.span (Set.range g) ^ N : Ideal A) : Set A)),
      (∀ i, φ ⟨g i ^ N, Ideal.pow_mem_pow (hg i) N⟩
        = Submodule.Quotient.mk (g i ^ (N - n) • x i)) ∧ (Nonempty (Fin t) → n ≤ N) := by
    obtain ⟨ψ, hψ⟩ := exists_hom_idealPow_of_compatible_pow_smul (M := M) g n x hx
    refine ⟨Fintype.card (Fin t) * n + 1,
      (Submodule.mapQ _ _ LinearMap.id
        (by simpa using torsionBySet_range_pow_le_torsionBySet_idealPow (M := M) g n)) ∘ₗ ψ,
      fun i => ?_, fun hne => ?_⟩
    · rw [LinearMap.comp_apply, hψ i]
      rfl
    · exact (Nat.le_mul_of_pos_left n (Fintype.card_pos_iff.mpr hne)).trans (Nat.le_succ _)
  refine ⟨N, φ, ?_⟩
  intro f hf m hm
  have hfU : PrimeSpectrum.basicOpen (ULift.up.{v} f)
      ≤ complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A (Ideal.span (Set.range g))) :=
    basicOpen_le_complementVanishing (ULift.{v} A)
      (liftedIdeal.{u, v} A (Ideal.span (Set.range g))) (ULift.up f) hf
  refine tilde_section_ext_of_cover (R := CommRingCat.of (ULift.{v} A))
    (ModuleCat.of (ULift.{v} A) (ULift.{u} M))
    (U := PrimeSpectrum.basicOpen (ULift.up.{v} f))
    (V := fun i => PrimeSpectrum.basicOpen (ULift.up.{v} f * ULift.up.{v} (g i)))
    (hVU := fun i => PrimeSpectrum.basicOpen_mul_le_left _ _)
    (hcover := fun p hp => ?_) (h := fun i => ?_)
  · obtain ⟨i, hi⟩ := exists_notMem_of_mem_complementVanishing A
      (Ideal.span (Set.range g)) g le_rfl p (hfU hp)
    exact ⟨i, Submonoid.mul_mem p.asIdeal.primeCompl hp hi⟩
  · have hiN : n ≤ N := hnN ⟨i⟩
    have hcomm := smul_apply_comm (S := Ideal.span (Set.range g) ^ N) φ
      (Ideal.pow_mem_pow hf N) (Ideal.pow_mem_pow (hg i) N)
    rw [hm, hφN i] at hcomm
    have h2 : (Submodule.torsionBySet A M
            ((Ideal.span (Set.range g) ^ N : Ideal A) : Set A)).mkQ (g i ^ N • m)
        = (Submodule.torsionBySet A M
            ((Ideal.span (Set.range g) ^ N : Ideal A) : Set A)).mkQ
          (f ^ N • (g i ^ (N - n) • x i)) := by
      rw [map_smul, map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
      exact hcomm
    have hmemK : (g i ^ N • m - f ^ N • (g i ^ (N - n) • x i))
        ∈ Submodule.torsionBySet A M
          ((Ideal.span (Set.range g) ^ N : Ideal A) : Set A) := by
      refine (Submodule.Quotient.mk_eq_zero _).mp ?_
      rw [← Submodule.mkQ_apply, map_sub, sub_eq_zero]
      exact h2
    have hkill : ((f * g i) ^ N) • (g i ^ N • m - f ^ N • (g i ^ (N - n) • x i)) = 0 := by
      have h3 := (Submodule.mem_torsionBySet_iff _ _).mp hmemK
        ⟨(f * g i) ^ N, Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hf) N⟩
      simpa using h3
    have hstar : (f ^ N * g i ^ (N + N)) • m
        = (f ^ (N + N) * g i ^ (N + (N - n))) • x i := by
      rw [smul_sub, sub_eq_zero] at hkill
      simp only [smul_smul] at hkill
      rw [show f ^ N * g i ^ (N + N) = (f * g i) ^ N * g i ^ N from by ring,
        show f ^ (N + N) * g i ^ (N + (N - n))
          = (f * g i) ^ N * (f ^ N * g i ^ (N - n)) from by ring]
      exact hkill
    have hexpL : (f * g i) ^ (N + N)
        = f ^ (N + N) * g i ^ (N + (N - n)) * g i ^ n := by
      rw [mul_pow, mul_assoc, ← pow_add, show N + (N - n) + n = N + N from by omega]
    have hexpR : (f * g i) ^ (N + N) = f ^ N * g i ^ (N + N) * f ^ N := by ring
    have hLexp : ((ULift.up.{v} f * ULift.up.{v} (g i)) : ULift.{v} A) ^ (N + N)
        = ULift.up.{v} (f ^ (N + N) * g i ^ (N + (N - n))) * ULift.up.{v} (g i) ^ n :=
      congrArg ULift.up hexpL
    have hRexp : ((ULift.up.{v} f * ULift.up.{v} (g i)) : ULift.{v} A) ^ (N + N)
        = ULift.up.{v} (f ^ N * g i ^ (N + N)) * ULift.up.{v} f ^ N :=
      congrArg ULift.up hexpR
    exact restrict_eq_restrict_of_pow_smul_eq (R := CommRingCat.of (ULift.{v} A))
      (ModuleCat.of (ULift.{v} A) (ULift.{u} M)) (ULift.up.{v} f) (ULift.up.{v} (g i))
      n N (N + N) (ULift.up.{u} (x i)) (ULift.up.{u} m)
      (ULift.up.{v} (f ^ (N + N) * g i ^ (N + (N - n))))
      (ULift.up.{v} (f ^ N * g i ^ (N + N))) hfU
      (basicOpen_le_complementVanishing (ULift.{v} A)
        (liftedIdeal.{u, v} A (Ideal.span (Set.range g))) (ULift.up (g i)) (hg i))
      (PrimeSpectrum.basicOpen_mul_le_left _ _)
      (PrimeSpectrum.basicOpen_mul_le_right _ _) s (hfrac i)
      (basicOpenFraction A M f N m) rfl hLexp hRexp
      (congrArg ULift.up hstar.symm)

/-!
### The lifted ideal
-/

/-- The ideal `I` transported to the universe lift of `A` is the image of `I` under the inverse
of the canonical ring isomorphism. -/
public lemma liftedIdeal_eq_map :
    liftedIdeal.{u, v} A I
      = Ideal.map (ULift.ringEquiv.symm.toRingHom : A →+* ULift.{v} A) I := by
  refine le_antisymm (fun y hy => ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx => hx)
  exact Ideal.mem_map_of_mem _ ((mem_liftedIdeal A I).mp hy)

/-- Finite generation passes to the universe lift. -/
public lemma liftedIdeal_fg (hI : I.FG) : (liftedIdeal.{u, v} A I).FG := by
  rw [liftedIdeal_eq_map]
  exact hI.map _

/-!
### The torsion-free case
-/

/-- If `I` annihilates no nonzero element of `M`, neither does any power of `I`. -/
public lemma eq_zero_of_forall_mem_idealPow_smul_eq_zero
    (hM : ∀ y : M, (∀ a ∈ I, a • y = 0) → y = 0) (N : ℕ) (z : M)
    (hz : ∀ a ∈ (I ^ N : Ideal A), a • z = 0) : z = 0 :=
  eq_zero_of_forall_pow_smul_eq_zero hM N z hz

/-- If `I` annihilates no nonzero element of `M`, the submodule annihilated by a power of `I` is
trivial. -/
public lemma torsionBySet_idealPow_eq_bot
    (hM : ∀ y : M, (∀ a ∈ I, a • y = 0) → y = 0) (N : ℕ) :
    Submodule.torsionBySet A M ((I ^ N : Ideal A) : Set A) = ⊥ := by
  refine le_antisymm (fun z hz => ?_) bot_le
  have hzero : z = 0 :=
    eq_zero_of_forall_mem_idealPow_smul_eq_zero A I M hM N z fun a ha =>
      (Submodule.mem_torsionBySet_iff _ _).mp hz ⟨a, ha⟩
  rw [hzero]
  exact Submodule.zero_mem _

/-- **Surjectivity in the torsion-free case.** If `I` is finitely generated and annihilates no
nonzero element of `M`, the canonical map `colim_n Hom_A(I ^ n, M) ⟶ Γ(Spec(A) \ V(I), M̃)` is
surjective. -/
public theorem canonicalMapToSections_surjective (hI : I.FG)
    (hM : ∀ y : M, (∀ a ∈ I, a • y = 0) → y = 0) :
    Function.Surjective (canonicalMapToSections A I M) := by
  classical
  intro s
  obtain ⟨N, φ, hφ⟩ := exists_hom_idealPow_representing_section A I M hI s
  have hbot : Submodule.torsionBySet A M ((I ^ N : Ideal A) : Set A) = ⊥ :=
    torsionBySet_idealPow_eq_bot A I M hM N
  refine ⟨colimit.ι (idealPowersHom A I M) N
    ((Submodule.quotEquivOfEqBot _ hbot).toLinearMap ∘ₗ φ), ?_⟩
  obtain ⟨t, g, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  rw [Ideal.submodule_span_eq] at hspan
  have hg : ∀ i, g i ∈ I := fun i => hspan ▸ Ideal.subset_span (Set.mem_range_self i)
  refine section_eq_of_restrict_basicOpen_eq A I M g hg (le_of_eq hspan.symm) fun i => ?_
  rw [canonicalMapToSections_restrict_ι A I M N
    ((Submodule.quotEquivOfEqBot _ hbot).toLinearMap ∘ₗ φ) (g i) (hg i)]
  refine (hφ (g i) (hg i)
    (((Submodule.quotEquivOfEqBot _ hbot).toLinearMap ∘ₗ φ)
      ⟨g i ^ N, Ideal.pow_mem_pow (hg i) N⟩) ?_).symm
  exact ((Submodule.quotEquivOfEqBot _ hbot).symm_apply_apply _).symm.trans
    (Submodule.quotEquivOfEqBot_symm_apply _ hbot _)

/-- If `I` is finitely generated and annihilates no nonzero element of `M`, the canonical map
`colim_n Hom_A(I ^ n, M) ⟶ Γ(Spec(A) \ V(I), M̃)` is an epimorphism of `A`-modules. -/
public theorem epi_canonicalMapToSections (hI : I.FG)
    (hM : ∀ y : M, (∀ a ∈ I, a • y = 0) → y = 0) : Epi (canonicalMapToSections A I M) :=
  ConcreteCategory.epi_of_surjective _ (canonicalMapToSections_surjective A I M hI hM)

end Affine

end Stacks.AlgebraicGeometry.IdealPowerSections
