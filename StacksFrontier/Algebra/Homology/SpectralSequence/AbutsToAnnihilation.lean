module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToVanishing
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution

/-!
# Annihilation of the abutment of a spectral sequence of modules

Let `R` be a commutative ring, `J ⊆ R` an ideal and `E` a cohomological spectral sequence of
`R`-modules which abuts to a graded family `H`.  Fix a total degree `n` and suppose that along the
antidiagonal `p + q = n` of some page `E_s` every term is annihilated by `J`, and that the terms
outside the band `0 ≤ p < N` vanish.  Then `H n` carries a filtration

`⊤ = F 0 ⊇ F 1 ⊇ ⋯ ⊇ F N = ⊥`   with   `J • F k ⊆ F (k + 1)`,

a filtration in `N` steps whose graded pieces are annihilated by `J`.

This is the module-theoretic half of the argument the Stacks project runs in [Stacks, Tag 0GA1]:
there the spectral sequence is the hypercohomology spectral sequence [Stacks, Tag 0G9Q] of
`Lp^*M̃(q)` on the blowup, the vanishing outside a band is the cohomological-dimension bound
[Stacks, Tag 071L], and the annihilation of the second page is [Stacks, Tag 0GA0].  What is here
is everything *after* those three inputs: given them, a filtration in the shape the hypothesis
`hfilt` of `Stacks.LocalCohomology.UniformityII`
`.exists_pow_le_annihilator_tor_quotient_pow` asks for comes out, and that statement turns it
into the uniform annihilation of the high `Tor`.

## The two steps

Annihilation propagates up the pages for the same reason vanishing does
(`StacksFrontier/Algebra/Homology/SpectralSequence/AbutsToVanishing.lean`): a term of `E_{r+1}` is
the homology of a short complex whose middle object is the term of `E_r`, and homology is a
quotient of a submodule, so an element killing the middle object kills the homology.  That is
`mem_annihilator_homology_of_mem_annihilator`, already available for a complex of modules.  From
the page `max s (E.rMin pq)` the infinity page is read off, so the annihilation reaches `E_∞`.

The abutment then supplies a finite decreasing filtration of `H n` by *categorical* subobjects
whose graded pieces are the terms of `E_∞`.  A graded piece is a cokernel, and annihilation of a
cokernel in `ModuleCat R` says exactly that `J` carries the larger submodule into the smaller
one; that translation is `smul_sub_le_of_mem_annihilator_cokernel`, and it is what turns the
subobject filtration into the submodule filtration asked for.  The bounds `⊤` and `⊥` of the
abutment's filtration sit at unspecified indices, and the vanishing outside the band is what
moves them to `0` and `N`: where a graded piece is zero the filtration is constant.

## Main results

* `Stacks.SpectralSequence.Annihilation.mem_annihilator_pageInfinity_of_mem_annihilator_page`:
  an element annihilating a term of a page annihilates the corresponding term of the infinity
  page.
* `Stacks.SpectralSequence.Annihilation.AbutsTo.exists_filtration_of_mem_annihilator`: **the
  abutment of an annihilated spectral sequence is filtered in `N` steps with graded pieces
  annihilated by `J`.**
* `Stacks.SpectralSequence.Annihilation.AbutsTo.exists_filtration_of_mem_annihilator_of_iso`:
  the same conclusion for any module isomorphic to `H n`, which is the form a consumer that has
  identified the abutment with something else asks for.

## Implementation notes

The submodule attached to a subobject is `LinearMap.range S.arrow.hom` rather than the image of
`CategoryTheory.Subobject` under `ModuleCat.subobjectModule`: the order isomorphism carries no
simp lemma describing it, whereas the range is exactly what `CategoryTheory.Subobject.ofLE_arrow`
computes with.  It is given the local name `sub`.

## References

* [Stacks Project, Tag 0GA1](https://stacks.math.columbia.edu/tag/0GA1)
* [Stacks Project, Tag 0GA0](https://stacks.math.columbia.edu/tag/0GA0)
* [Stacks Project, Tag 0G9Q](https://stacks.math.columbia.edu/tag/0G9Q)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SpectralSequence.Annihilation

variable {R : Type u} [CommRing R]

/-! ### Annihilation of a cokernel, read on submodules -/

/-- **An element annihilating `coker f` carries `Y` into the image of `f`.**  Multiplying a
section of `Y` by `a` lands in the kernel of the projection to the cokernel, which is the range
of `f`. -/
theorem smul_mem_range_of_mem_annihilator_cokernel {X Y : ModuleCat.{u} R} (f : X ⟶ Y) {a : R}
    (ha : a ∈ Module.annihilator R (cokernel f : ModuleCat.{u} R)) (y : Y) :
    a • y ∈ LinearMap.range f.hom := by
  have hzero : (cokernel.π f).hom (a • y) = 0 := by
    rw [map_smul]
    exact Module.mem_annihilator.mp ha _
  have hcomm := congrArg (fun φ : Y ⟶ ModuleCat.of R (Y ⧸ LinearMap.range f.hom) =>
    φ.hom (a • y)) (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom f)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hzero, map_zero,
    ModuleCat.hom_ofHom, Submodule.mkQ_apply] at hcomm
  exact (Submodule.Quotient.mk_eq_zero _).mp hcomm.symm

/-- The submodule of `Y` cut out by a categorical subobject: the range of its arrow. -/
noncomputable def sub {Y : ModuleCat.{u} R} (S : Subobject Y) : Submodule R Y :=
  LinearMap.range S.arrow.hom

/-- The comparison map of two nested subobjects, read on sections: it is a factorisation of the
arrow of the smaller one through the arrow of the larger. -/
theorem arrow_ofLE_apply {Y : ModuleCat.{u} R} {S T : Subobject Y} (h : S ≤ T)
    (x : (S : ModuleCat.{u} R)) : T.arrow.hom ((Subobject.ofLE S T h).hom x) = S.arrow.hom x := by
  have h1 := congrArg (fun φ : (S : ModuleCat.{u} R) ⟶ Y => φ.hom x) (Subobject.ofLE_arrow h)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  exact h1

/-- Nested subobjects cut out nested submodules. -/
theorem sub_mono {Y : ModuleCat.{u} R} {S T : Subobject Y} (h : S ≤ T) : sub S ≤ sub T := by
  rintro y ⟨x, rfl⟩
  exact ⟨(Subobject.ofLE S T h).hom x, arrow_ofLE_apply h x⟩

/-- The largest subobject cuts out the whole module. -/
theorem sub_top {Y : ModuleCat.{u} R} : sub (⊤ : Subobject Y) = ⊤ := by
  have : IsIso ((⊤ : Subobject Y).arrow) :=
    (Subobject.isIso_arrow_iff_eq_top (⊤ : Subobject Y)).2 rfl
  rw [sub, LinearMap.range_eq_top]
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The smallest subobject cuts out the zero submodule. -/
theorem sub_bot {Y : ModuleCat.{u} R} : sub (⊥ : Subobject Y) = ⊥ := by
  rw [sub, Subobject.bot_arrow]
  simp

/-- **Annihilation of a graded piece, read on submodules.**  If `a` annihilates the cokernel of
the inclusion of `S` into `T`, then `a` carries the submodule cut out by `T` into the submodule
cut out by `S`. -/
theorem smul_sub_le_of_mem_annihilator_cokernel {Y : ModuleCat.{u} R} {S T : Subobject Y}
    (h : S ≤ T) {a : R}
    (ha : a ∈ Module.annihilator R (cokernel (Subobject.ofLE S T h) : ModuleCat.{u} R))
    {y : Y} (hy : y ∈ sub T) : a • y ∈ sub S := by
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz⟩ := smul_mem_range_of_mem_annihilator_cokernel (Subobject.ofLE S T h) ha x
  exact ⟨z, by rw [← arrow_ofLE_apply h z, hz, map_smul]⟩

/-! ### Annihilation propagates to the infinity page -/

/-- **Annihilation propagates up the pages.**  A term of the page `E_{r+1}` is the homology of a
short complex whose middle object is the corresponding term of `E_r`; homology is a quotient of a
submodule, so an element annihilating the term of `E_r` annihilates every later one. -/
theorem mem_annihilator_page_of_mem_annihilator_page {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) r₀) {r : ℤ} (hr : r₀ ≤ r)
    (pq : ℤ × ℤ) {a : R} (ha : a ∈ Module.annihilator R ((E.page r hr).X pq)) :
    ∀ s : ℤ, r ≤ s → ∀ hs : r₀ ≤ s, a ∈ Module.annihilator R ((E.page s hs).X pq) := by
  intro s hle
  induction s, hle using Int.leInduction with
  | base => exact fun _ => ha
  | succ m hm ih =>
    intro _
    have hm0 : r₀ ≤ m := hr.trans hm
    exact mem_annihilator_of_moduleCat_iso (E.iso m (m + 1) pq rfl hm0)
      (mem_annihilator_homology_of_mem_annihilator (E.page m hm0) pq (ih hm0))

/-- **Annihilation propagates to the infinity page.**  An element annihilating a term of the page
`E_r` annihilates it on the page `max r (E.rMin pq)`, from which the infinity page is read
off. -/
theorem mem_annihilator_pageInfinity_of_mem_annihilator_page {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) r₀) {r : ℤ} (hr : r₀ ≤ r)
    (pq : ℤ × ℤ) [E.HasPageInfinityAt pq] {a : R}
    (ha : a ∈ Module.annihilator R ((E.page r hr).X pq)) :
    a ∈ Module.annihilator R (E.pageInfinity pq) := by
  have hsr : r ≤ max r (E.rMin pq) := le_max_left _ _
  have hs0 : r₀ ≤ max r (E.rMin pq) := hr.trans hsr
  have : E.HasEdgeMonoAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rToMin_LE_rMin pq).trans (le_max_right _ _)⟩
  have : E.HasEdgeEpiAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rFromMin_LE_rMin pq).trans (le_max_right _ _)⟩
  exact mem_annihilator_of_moduleCat_iso (E.pageInfinityIso pq (max r (E.rMin pq))).symm
    (mem_annihilator_page_of_mem_annihilator_page E hr pq ha _ hsr hs0)

/-! ### The filtration of the abutment -/

open CategoryTheory.SpectralSequence in
/-- **The abutment of an annihilated spectral sequence is filtered with annihilated graded
pieces.**  Let `E` be a cohomological spectral sequence of `R`-modules abutting to `H`, let `J` be
an ideal, and fix a total degree `n`.  If along the antidiagonal of the page `E_s` every term is
annihilated by `J`, and the terms with `p < 0` or `p ≥ N` vanish, then `H n` carries a filtration
`⊤ = F 0, …, F N = ⊥` in `N` steps with `J • F k ≤ F (k + 1)`.

This is the shape the hypothesis `hfilt` of `Stacks.LocalCohomology.UniformityII`
`.exists_pow_le_annihilator_tor_quotient_pow` is stated in, and
`Stacks.LocalCohomology.UniformityII.pow_mul_le_annihilator_of_filtration` turns it into the
annihilation of `H n` by `J ^ N`. -/
theorem AbutsTo.exists_filtration_of_mem_annihilator {r₀ : ℤ}
    {E : CohomologicalSpectralSequence (ModuleCat.{u} R) r₀} {H : ℤ → ModuleCat.{u} R}
    (hE : AbutsTo E H) {s : ℤ} (hs : r₀ ≤ s) (J : Ideal R) (n : ℤ) (N : ℕ)
    (hvanish : ∀ p : ℤ, p < 0 ∨ (N : ℤ) ≤ p → IsZero ((E.page s hs).X (p, n - p)))
    (hann : ∀ p : ℤ, J ≤ Module.annihilator R ((E.page s hs).X (p, n - p))) :
    ∃ F : ℕ → Submodule R (H n), F 0 = ⊤ ∧ F N = ⊥ ∧ ∀ k, J • F k ≤ F (k + 1) := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  have hIso : ∀ p : ℤ, E.pageInfinity (p, n - p) ≅
      cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) := by
    intro p
    have heq : p + (n - p) = n := by omega
    conv_rhs => rw [← heq]
    exact (hgr p (n - p)).some
  have hannGr : ∀ p : ℤ, J ≤ Module.annihilator R
      (cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) : ModuleCat.{u} R) := by
    intro p a haJ
    have : E.HasPageInfinityAt (p, n - p) := hinf p (n - p)
    exact mem_annihilator_of_moduleCat_iso (hIso p)
      (mem_annihilator_pageInfinity_of_mem_annihilator_page E hs (p, n - p) (hann p haJ))
  have hstep : ∀ p : ℤ, p < 0 ∨ (N : ℤ) ≤ p → F n (p + 1) = F n p := by
    intro p hp
    have : E.HasPageInfinityAt (p, n - p) := hinf p (n - p)
    have hzc : IsZero (cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) :=
      IsZero.of_iso (isZero_pageInfinity_of_isZero_page E hs (p, n - p) (hvanish p hp))
        (hIso p).symm
    have : Epi (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) :=
      Preadditive.epi_of_isZero_cokernel _ hzc
    have : IsIso (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) :=
      isIso_of_mono_of_epi _
    refine le_antisymm (hF n (by omega)) (Subobject.le_of_comm
      (inv (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) ?_)
    rw [← Subobject.ofLE_arrow (hF n (show p ≤ p + 1 by omega)), IsIso.inv_hom_id_assoc]
  obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
  have hFtop : F n 0 = ⊤ := by
    rcases le_or_gt a 0 with hA | hA
    · have key : ∀ m : ℤ, a ≤ m → m ≤ 0 → F n m = F n a := by
        intro m ham
        induction m, ham using Int.leInduction with
        | base => exact fun _ => rfl
        | succ c hc ih => exact fun hc0 => by rw [hstep c (Or.inl (by omega)), ih (by omega)]
      rw [key 0 hA le_rfl, ha]
    · refine le_antisymm le_top ?_
      rw [← ha]
      exact hF n hA.le
  have hFbot : F n (N : ℤ) = ⊥ := by
    rcases le_or_gt (N : ℤ) b with hB | hB
    · have key : ∀ m : ℤ, (N : ℤ) ≤ m → F n m = F n (N : ℤ) := by
        intro m hm
        induction m, hm using Int.leInduction with
        | base => rfl
        | succ c hc ih => rw [hstep c (Or.inr (by omega)), ih]
      rw [← hb]
      exact (key b hB).symm
    · refine le_antisymm ?_ bot_le
      rw [← hb]
      exact hF n hB.le
  refine ⟨fun k => sub (F n (k : ℤ)), ?_, ?_, fun k => ?_⟩
  · show sub (F n ((0 : ℕ) : ℤ)) = ⊤
    rw [Nat.cast_zero, hFtop]
    exact sub_top
  · show sub (F n ((N : ℕ) : ℤ)) = ⊥
    rw [hFbot]
    exact sub_bot
  · refine Submodule.smul_le.mpr fun c hcJ y hy => ?_
    show c • y ∈ sub (F n (((k + 1 : ℕ)) : ℤ))
    rw [Nat.cast_add, Nat.cast_one]
    exact smul_sub_le_of_mem_annihilator_cokernel _ (hannGr (k : ℤ) hcJ) hy

open CategoryTheory.SpectralSequence in
/-- **The filtration, transported along an identification of the abutment.**
`AbutsTo.exists_filtration_of_mem_annihilator` for any module `T` isomorphic to `H n`: a
consumer which knows the abutment only up to an isomorphism — as the proof of
[Stacks, Tag 0GA1] knows `H^{-i}(X, Lp^*M̃(q))` only as `Tor_i^A(M, I^q)`, through
[Stacks, Tag 0G9Z] — gets the filtration on its own module. -/
theorem AbutsTo.exists_filtration_of_mem_annihilator_of_iso {r₀ : ℤ}
    {E : CohomologicalSpectralSequence (ModuleCat.{u} R) r₀} {H : ℤ → ModuleCat.{u} R}
    (hE : AbutsTo E H) {s : ℤ} (hs : r₀ ≤ s) (J : Ideal R) (n : ℤ) (N : ℕ)
    (hvanish : ∀ p : ℤ, p < 0 ∨ (N : ℤ) ≤ p → IsZero ((E.page s hs).X (p, n - p)))
    (hann : ∀ p : ℤ, J ≤ Module.annihilator R ((E.page s hs).X (p, n - p)))
    {T : ModuleCat.{u} R} (e : H n ≅ T) :
    ∃ F : ℕ → Submodule R T, F 0 = ⊤ ∧ F N = ⊥ ∧ ∀ k, J • F k ≤ F (k + 1) := by
  obtain ⟨F, h0, hN, hstep⟩ :=
    AbutsTo.exists_filtration_of_mem_annihilator hE hs J n N hvanish hann
  refine ⟨fun k => (F k).map (e.toLinearEquiv : (H n) →ₗ[R] T), ?_, ?_, fun k => ?_⟩
  · show (F 0).map (e.toLinearEquiv : (H n) →ₗ[R] T) = ⊤
    rw [h0, Submodule.map_top, LinearMap.range_eq_top]
    exact e.toLinearEquiv.surjective
  · show (F N).map (e.toLinearEquiv : (H n) →ₗ[R] T) = ⊥
    rw [hN, Submodule.map_bot]
  · show J • (F k).map (e.toLinearEquiv : (H n) →ₗ[R] T)
      ≤ (F (k + 1)).map (e.toLinearEquiv : (H n) →ₗ[R] T)
    rw [← Submodule.map_smul'']
    exact Submodule.map_mono (hstep k)

end Stacks.SpectralSequence.Annihilation

end
