module

public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Length
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lengths along a spectral sequence of modules, and degeneration

Let `R` be a commutative ring and let `E` be a cohomological spectral sequence of `R`-modules,
abutting to `H^*`. Every page is a subquotient of the previous one, so the length of `E_r^{p,q}`
decreases with `r`, and `H^n` has a finite filtration whose graded pieces are the `E_∞^{p,n-p}`.
Hence, for every page `r` and every total degree `n`,

`ℓ(H^n) ≤ ∑_{p + q = n} ℓ(E_r^{p, q})`,

and when all these lengths are finite, equality in every total degree holds exactly when the
spectral sequence degenerates at `E_r`.

Over a field the length is the dimension, so this says that a spectral sequence of finite
dimensional vector spaces degenerates at `E_r` if and only if `dim H^n = ∑_{p+q=n} dim E_r^{p,q}`
for all `n`. This is the numerical criterion through which `E_1`-degeneration of the
Hodge-to-de Rham spectral sequence is expressed and used ([Stacks, Tag 0FMN] asserts the finite
local freeness of `ℋ^q_dR(X/Y)` for a proper smooth `f` over `ℚ`, whose proof goes through it).

## Main results

* `CategoryTheory.ShortComplex.moduleCat_length_X₂_eq`: for a short complex `S` of modules,
  `ℓ(S.X₂) = ℓ(im S.f) + ℓ(H(S)) + ℓ(im S.g)`.
* `HomologicalComplex.moduleCat_d_eq_zero_of_length_homology_eq`: if the homology of a complex
  of modules at `i` is as long as the term there, and that length is finite, the differentials
  into and out of `i` vanish.
* `CategoryTheory.SpectralSequence.length_page_le`: lengths decrease along the pages.
* `CategoryTheory.SpectralSequence.length_abutment_le_sum`: `ℓ(H^n) ≤ ∑_{p} ℓ(E_r^{p, n - p})`.
* `CategoryTheory.SpectralSequence.degeneratesAt_iff_length_eq`: with finite lengths, `E`
  degenerates at `E_r` iff `ℓ(H^n) = ∑_{p} ℓ(E_r^{p, n - p})` for every `n`.
* `CategoryTheory.SpectralSequence.degeneratesAt_and_length_eq_of_sum_le`: Deligne's squeeze:
  bounds `ℓ(E_r^{p,q}) ≤ b_{p,q}` with `∑_{p} b_{p, n - p} ≤ ℓ(H^n) < ⊤` force degeneration at
  `E_r` and `ℓ(E_r^{p,q}) = b_{p,q}`.

No `@[stacks]` attribute is carried: these are tools.

## References

* [Stacks Project, Tag 011O](https://stacks.math.columbia.edu/tag/011O)
* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{v} R))

/-- **Length is additive on short exact sequences of modules.** -/
@[ega "0 11.10.2" "special case"]
lemma moduleCat_length_eq_add_of_shortExact (hS : S.ShortExact) :
    Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ :=
  Module.length_eq_add_of_exact S.f.hom S.g.hom hS.moduleCat_injective_f
    hS.moduleCat_surjective_g ((ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)

/-- `ℓ(Z(S)) = ℓ(im S.f) + ℓ(H(S))`, where `Z(S)` is the module of cycles. -/
lemma moduleCat_length_cycles_eq :
    Module.length R S.cycles =
      Module.length R (LinearMap.range S.toCycles.hom) + Module.length R S.homology := by
  have hex : (ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel
  refine Module.length_eq_add_of_exact (LinearMap.range S.toCycles.hom).subtype S.homologyπ.hom
    (Submodule.subtype_injective _) ?_ ?_
  · exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  · rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact hex.moduleCat_range_eq_ker.symm

/-- `ℓ(S.X₂) = ℓ(Z(S)) + ℓ(im S.g)`. -/
lemma moduleCat_length_X₂_eq_cycles :
    Module.length R S.X₂ =
      Module.length R S.cycles + Module.length R (LinearMap.range S.g.hom) := by
  have hex : (ShortComplex.mk S.iCycles S.g S.iCycles_g).Exact :=
    ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel
  refine Module.length_eq_add_of_exact S.iCycles.hom S.g.hom.rangeRestrict
    ((ModuleCat.mono_iff_injective _).1 inferInstance) (LinearMap.surjective_rangeRestrict _) ?_
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
  exact hex.moduleCat_range_eq_ker.symm

/-- **`ℓ(S.X₂) = ℓ(im S.f) + ℓ(H(S)) + ℓ(im S.g)`** for a short complex `S` of modules. -/
lemma moduleCat_length_X₂_eq :
    Module.length R S.X₂ =
      Module.length R (LinearMap.range S.toCycles.hom) + Module.length R S.homology +
        Module.length R (LinearMap.range S.g.hom) := by
  rw [moduleCat_length_X₂_eq_cycles, moduleCat_length_cycles_eq]

/-- The homology of a short complex of modules is no longer than its middle term. -/
lemma moduleCat_length_homology_le :
    Module.length R S.homology ≤ Module.length R S.X₂ := by
  rw [moduleCat_length_X₂_eq]
  exact le_add_right le_add_self

/-- The map `S.X₁ ⟶ Z(S)` to the cycles vanishes if and only if `S.f` does. -/
lemma moduleCat_toCycles_eq_zero_iff : S.toCycles = 0 ↔ S.f = 0 := by
  constructor
  · intro h
    rw [← S.toCycles_i, h, zero_comp]
  · intro h
    rw [← cancel_mono S.iCycles, S.toCycles_i, h, zero_comp]

/-- A morphism of modules whose image has length zero is zero. -/
lemma moduleCat_eq_zero_of_range_subsingleton {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (h : Module.length R (LinearMap.range f.hom) = 0) : f = 0 := by
  rw [Module.length_eq_zero_iff] at h
  ext x
  have : (⟨f.hom x, x, rfl⟩ : LinearMap.range f.hom) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

/-- The image of the zero morphism of modules has length zero. -/
lemma moduleCat_length_range_eq_zero {M N : ModuleCat.{v} R} (f : M ⟶ N) (h : f = 0) :
    Module.length R (LinearMap.range f.hom) = 0 := by
  refine Module.length_eq_zero_iff.2 ⟨fun a b => Subtype.ext ?_⟩
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  rw [← hx, ← hy, h]
  rfl

/-- **If the homology of a short complex of modules is as long as its middle term, and that
length is finite, then both maps vanish.** -/
lemma moduleCat_f_eq_zero_and_g_eq_zero_of_length_eq
    (h : Module.length R S.homology = Module.length R S.X₂)
    (htop : Module.length R S.X₂ ≠ ⊤) : S.f = 0 ∧ S.g = 0 := by
  have e := S.moduleCat_length_X₂_eq
  set a := Module.length R (LinearMap.range S.toCycles.hom)
  set c := Module.length R (LinearMap.range S.g.hom)
  set b := Module.length R S.homology
  have hb : b ≠ ⊤ := h ▸ htop
  have ha : a = 0 := by
    have : a + b + c = 0 + b + 0 := by rw [← e, ← h]; simp
    have h1 : a + b ≤ b := by
      calc a + b ≤ a + b + c := le_self_add
        _ = b := by rw [this]; simp
    have h2 : a + b = 0 + b := le_antisymm (by simpa using h1) (by simp)
    exact WithTop.add_right_cancel hb h2
  have hc : c = 0 := by
    have : a + b + c = a + b + 0 := by rw [← e, ← h, ha]; simp
    exact WithTop.add_left_cancel (by rw [ha, zero_add]; exact hb) this
  exact ⟨(moduleCat_toCycles_eq_zero_iff S).1 (moduleCat_eq_zero_of_range_subsingleton _ ha),
    moduleCat_eq_zero_of_range_subsingleton _ hc⟩

/-- If both maps of a short complex of modules vanish, its homology is as long as its middle
term. -/
lemma moduleCat_length_homology_eq_of_f_eq_zero_of_g_eq_zero (hf : S.f = 0) (hg : S.g = 0) :
    Module.length R S.homology = Module.length R S.X₂ := by
  rw [moduleCat_length_X₂_eq,
    moduleCat_length_range_eq_zero _ ((moduleCat_toCycles_eq_zero_iff S).2 hf),
    moduleCat_length_range_eq_zero _ hg, zero_add, add_zero]

end CategoryTheory.ShortComplex

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Isomorphic modules have the same length, in any universe of module objects. -/
lemma _root_.CategoryTheory.Iso.moduleCat_length_eq {M N : ModuleCat.{v} R} (e : M ≅ N) :
    Module.length R M = Module.length R N :=
  e.toLinearEquiv.length_eq

/-- A module has length zero exactly when it is a zero object. -/
lemma length_eq_zero_iff_isZero (M : ModuleCat.{v} R) :
    Module.length R M = 0 ↔ IsZero M := by
  rw [Module.length_eq_zero_iff, ModuleCat.isZero_iff_subsingleton]

/-- A module no longer than a zero module is zero. -/
private lemma isZero_of_length_le {M N : ModuleCat.{v} R}
    (h : Module.length R M ≤ Module.length R N) (hN : IsZero N) : IsZero M :=
  (length_eq_zero_iff_isZero M).1 (le_zero_iff.1 (h.trans ((length_eq_zero_iff_isZero N).2 hN).le))

/-- In a finite family of lengths that is termwise bounded by a second one with a finite sum no
larger than the first one's, the two families agree. -/
lemma _root_.ENat.eq_of_sum_le_sum_of_le {ι : Type*} (s : Finset ι) (a b : ι → ℕ∞)
    (hab : ∀ i ∈ s, a i ≤ b i) (hsum : ∑ i ∈ s, b i ≤ ∑ i ∈ s, a i)
    (htop : ∑ i ∈ s, b i ≠ ⊤) : ∀ i ∈ s, a i = b i := by
  classical
  intro i hi
  refine le_antisymm (hab i hi) (not_lt.1 fun hlt => ?_)
  have hrest : ∑ j ∈ s.erase i, b j ≠ ⊤ :=
    ne_top_of_le_ne_top htop (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have : ∑ j ∈ s, a j < ∑ j ∈ s, b j := by
    rw [← Finset.add_sum_erase s a hi, ← Finset.add_sum_erase s b hi]
    calc a i + ∑ j ∈ s.erase i, a j ≤ a i + ∑ j ∈ s.erase i, b j :=
        add_le_add le_rfl (Finset.sum_le_sum fun j hj => hab j (Finset.mem_of_mem_erase hj))
      _ < b i + ∑ j ∈ s.erase i, b j := ENat.add_lt_add_of_lt_of_le hrest hlt le_rfl
  exact lt_irrefl _ (this.trans_le hsum)

end ModuleCat

namespace CategoryTheory.Subobject

variable {R : Type u} [CommRing R] {M : ModuleCat.{v} R}

/-- For subobjects `X ≤ Y` of a module, `ℓ(Y) = ℓ(X) + ℓ(Y/X)`. -/
lemma moduleCat_length_eq_add_length_cokernel (X Y : Subobject M) (h : X ≤ Y) :
    Module.length R (Y : ModuleCat.{v} R) =
      Module.length R (X : ModuleCat.{v} R) +
        Module.length R (cokernel (C := ModuleCat.{v} R) (ofLE X Y h)) :=
  ShortComplex.moduleCat_length_eq_add_of_shortExact
    (ShortComplex.mk (ofLE X Y h) (cokernel.π _) (cokernel.condition _))
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

/-- The bottom subobject of a module has length zero. -/
lemma moduleCat_length_eq_zero_of_eq_bot (X : Subobject M) (h : X = ⊥) :
    Module.length R (X : ModuleCat.{v} R) = 0 := by
  rw [ModuleCat.length_eq_zero_iff_isZero]
  exact IsZero.of_iso (isZero_zero _) (isoOfEq _ _ h ≪≫ botCoeIsoZero)

/-- The top subobject of a module `M` has the same length as `M`. -/
lemma moduleCat_length_eq_of_eq_top (X : Subobject M) (h : X = ⊤) :
    Module.length R (X : ModuleCat.{v} R) = Module.length R M :=
  CategoryTheory.Iso.moduleCat_length_eq
    (isoOfEq _ _ (h.trans (top_eq_id M)) ≪≫ underlyingIso (𝟙 M))

variable (F : ℤ → Subobject M) (hF : Antitone F)
include hF

/-- **Telescoping the lengths of a filtration.** -/
lemma moduleCat_length_eq_sum_cokernel (a : ℤ) (k : ℕ) :
    Module.length R (F a : ModuleCat.{v} R) =
      (∑ i ∈ Finset.range k, Module.length R
        (cokernel (C := ModuleCat.{v} R) (ofLE (F (a + i + 1)) (F (a + i)) (hF (by omega))))) +
        Module.length R (F (a + k) : ModuleCat.{v} R) := by
  induction k with
  | zero =>
    have e : a + ((0 : ℕ) : ℤ) = a := by omega
    rw [e]
    simp
  | succ k ih =>
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [ih, Finset.sum_range_succ, e,
      moduleCat_length_eq_add_length_cokernel (F (a + k + 1)) (F (a + k)) (hF (by omega))]
    ac_rfl

/-- **The length of a module with a finite filtration is the sum of the lengths of the graded
pieces.** If `F` is a decreasing filtration of `M` with `F a = ⊤` and `F b = ⊥`, then
`ℓ(M) = ∑_{p ∈ s} ℓ(F p / F (p + 1))` for every finite `s` containing `[a, b)`. -/
lemma moduleCat_length_eq_sum_of_filtration (a b : ℤ) (hab : a ≤ b) (ha : F a = ⊤)
    (hb : F b = ⊥) (s : Finset ℤ) (hs : ∀ p, a ≤ p → p < b → p ∈ s) :
    Module.length R M =
      ∑ p ∈ s, Module.length R
        (cokernel (C := ModuleCat.{v} R) (ofLE (F (p + 1)) (F p) (hF (by omega)))) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  rw [← moduleCat_length_eq_of_eq_top (F a) ha, moduleCat_length_eq_sum_cokernel F hF a k,
    moduleCat_length_eq_zero_of_eq_bot _ hb, add_zero]
  let g : ℤ → ℕ∞ := fun p =>
    Module.length R (cokernel (C := ModuleCat.{v} R) (ofLE (F (p + 1)) (F p) (hF (by omega))))
  show ∑ i ∈ Finset.range k, g (a + i) = ∑ p ∈ s, g p
  rw [← Finset.sum_image (s := Finset.range k) (g := fun i : ℕ => a + (i : ℤ)) (f := g)
    (fun i _ j _ hij => by simpa using hij)]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact hs _ (by omega) (by simpa using hi)
  · intro p _ hp
    have hout : p < a ∨ a + k ≤ p := by
      by_contra hcon
      refine hp (Finset.mem_image.2 ⟨(p - a).toNat, ?_, ?_⟩) <;> simp <;> omega
    rcases hout with hlt | hge
    · have h1 : F (p + 1) = ⊤ := top_le_iff.1 (ha ▸ hF (by omega))
      have h2 : F p = ⊤ := top_le_iff.1 (ha ▸ hF (by omega))
      have : IsIso (ofLE (F (p + 1)) (F p) (hF (by omega))) := by
        have e : F (p + 1) = F p := h1.trans h2.symm
        refine ⟨ofLE _ _ e.ge, ?_, ?_⟩ <;> simp [ofLE_comp_ofLE, ofLE_refl]
      exact (ModuleCat.length_eq_zero_iff_isZero _).2 (isZero_cokernel_of_epi _)
    · refine le_antisymm ?_ zero_le
      calc g p ≤ Module.length R (F p : ModuleCat.{v} R) :=
            Module.length_le_of_surjective
              (cokernel.π (C := ModuleCat.{v} R) (ofLE (F (p + 1)) (F p) (hF (by omega)))).hom
              ((ModuleCat.epi_iff_surjective _).1 inferInstance)
        _ = 0 := moduleCat_length_eq_zero_of_eq_bot _ (le_bot_iff.1 (hb ▸ hF hge))

end CategoryTheory.Subobject

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- The homology of a complex of modules is no longer than the term it is computed at. -/
lemma moduleCat_length_homology_le (i : ι) :
    Module.length R (K.homology i) ≤ Module.length R (K.X i) :=
  (K.sc i).moduleCat_length_homology_le

/-- If the homology of a complex of modules at `i` is as long as `K.X i`, and that length is
finite, then the differentials into and out of `i` vanish. -/
lemma moduleCat_d_eq_zero_of_length_homology_eq (i : ι)
    (h : Module.length R (K.homology i) = Module.length R (K.X i))
    (htop : Module.length R (K.X i) ≠ ⊤) (j : ι) : K.d i j = 0 ∧ K.d j i = 0 := by
  obtain ⟨hf, hg⟩ := (K.sc i).moduleCat_f_eq_zero_and_g_eq_zero_of_length_eq h htop
  constructor
  · by_cases hrel : c.Rel i j
    · obtain rfl := c.next_eq' hrel
      exact hg
    · exact K.shape _ _ hrel
  · by_cases hrel : c.Rel j i
    · obtain rfl := c.prev_eq' hrel
      exact hf
    · exact K.shape _ _ hrel

end HomologicalComplex

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [CommRing R] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- **Lengths decrease from a page to the next**: `E_{r+1}^{pq}` is the homology of `E_r` at
`pq`. -/
lemma length_page_succ_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    Module.length R ((E.page r' (by omega)).X pq) ≤ Module.length R ((E.page r hr).X pq) := by
  rw [← CategoryTheory.Iso.moduleCat_length_eq (E.iso r r' pq hrr' hr)]
  exact (E.page r hr).moduleCat_length_homology_le pq

/-- **Lengths decrease along the pages.** -/
lemma length_page_le (pq : κ) (r r' : ℤ) (hrr' : r ≤ r') (hr : r₀ ≤ r) :
    Module.length R ((E.page r' (by omega)).X pq) ≤ Module.length R ((E.page r hr).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ r' hr' ih => exact (E.length_page_succ_le r' (r' + 1) rfl (by omega) pq).trans ih

/-- If `E_{r+1}^{pq}` is as long as `E_r^{pq}`, and that length is finite, then the
differentials of `E_r` into and out of `pq` vanish. -/
lemma d_eq_zero_of_length_page_succ_eq (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ)
    (h : Module.length R ((E.page r' (by omega)).X pq) = Module.length R ((E.page r hr).X pq))
    (htop : Module.length R ((E.page r hr).X pq) ≠ ⊤) (pq' : κ) :
    (E.page r hr).d pq pq' = 0 ∧ (E.page r hr).d pq' pq = 0 := by
  rw [← CategoryTheory.Iso.moduleCat_length_eq (E.iso r r' pq hrr' hr)] at h
  exact (E.page r hr).moduleCat_d_eq_zero_of_length_homology_eq pq h htop pq'

/-- The infinity page is no longer than any page. -/
lemma length_pageInfinity_le (pq : κ) [E.HasPageInfinityAt pq] (r : ℤ) (hr : r₀ ≤ r) :
    Module.length R (E.pageInfinity pq) ≤ Module.length R ((E.page r hr).X pq) := by
  have : E.HasEdgeMonoAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rToMin_LE_rMin pq).trans (le_max_right _ _)⟩
  have : E.HasEdgeEpiAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rFromMin_LE_rMin pq).trans (le_max_right _ _)⟩
  rw [CategoryTheory.Iso.moduleCat_length_eq (E.pageInfinityIso pq (max r (E.rMin pq)))]
  exact E.length_page_le pq r _ (le_max_left _ _) hr

/-- Under degeneration at `E_r`, the infinity page is as long as `E_r`. -/
lemma length_pageInfinity_eq_of_degeneratesAt {r : ℤ} {hr : r₀ ≤ r} (h : E.DegeneratesAt r hr)
    (pq : κ) :
    Module.length R (E.pageInfinity pq) = Module.length R ((E.page r hr).X pq) :=
  CategoryTheory.Iso.moduleCat_length_eq (h.pageInfinityIso pq r le_rfl)

end CategoryTheory.SpectralSequence

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [CommRing R] {r₀ : ℤ}
  {E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀} {H : ℤ → ModuleCat.{v} R}

/-- **The length of the abutment is the sum of the lengths of the infinity page.** If `E`
abuts to `H` and `s` contains every `p` with `E_∞^{p, n - p} ≠ 0`, then
`ℓ(H^n) = ∑_{p ∈ s} ℓ(E_∞^{p, n - p})`. -/
theorem length_abutment_eq_sum_pageInfinity (hE : AbutsTo E H) (n : ℤ) (s : Finset ℤ)
    (hs : ∀ p ∉ s, IsZero (E.pageInfinity (p, n - p))) :
    Module.length R (H n) = ∑ p ∈ s, Module.length R (E.pageInfinity (p, n - p)) := by
  classical
  obtain ⟨-, F, hF, hbounds, hgr⟩ := hE
  obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
  have key : ∀ (m : ℤ) (_ : m = n) (p : ℤ),
      Module.length R (cokernel (C := ModuleCat.{v} R)
        (Subobject.ofLE (F m (p + 1)) (F m p) (hF m (by omega)))) =
      Module.length R (cokernel (C := ModuleCat.{v} R)
        (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) := by
    rintro m rfl p
    rfl
  have hgr' : ∀ p : ℤ, Module.length R (E.pageInfinity (p, n - p)) =
      Module.length R (cokernel (C := ModuleCat.{v} R)
        (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) := fun p =>
    (CategoryTheory.Iso.moduleCat_length_eq (hgr p (n - p)).some).trans (key _ (by omega) p)
  rw [Subobject.moduleCat_length_eq_sum_of_filtration (F n) (hF n) a b hab ha hb
    (s ∪ Finset.Ico a b) (fun p hp hp' => Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨hp, hp'⟩))]
  simp_rw [← hgr']
  refine (Finset.sum_subset Finset.subset_union_left fun p _ hp => ?_).symm
  exact (ModuleCat.length_eq_zero_iff_isZero _).2 (hs p hp)

/-- **`ℓ(H^n) ≤ ∑_{p} ℓ(E_r^{p, n - p})`** for a spectral sequence of modules abutting to `H`,
on every page `r`, the sum running over any finite `s` outside which `E_r^{p, n - p}` vanishes. -/
@[ega "0 11.1.8" "special case"]
theorem length_abutment_le_sum (hE : AbutsTo E H) (n r : ℤ) (hr : r₀ ≤ r) (s : Finset ℤ)
    (hs : ∀ p ∉ s, IsZero ((E.page r hr).X (p, n - p))) :
    Module.length R (H n) ≤ ∑ p ∈ s, Module.length R ((E.page r hr).X (p, n - p)) := by
  have := hE.1
  have hs' : ∀ p ∉ s, IsZero (E.pageInfinity (p, n - p)) := fun p hp =>
    ModuleCat.isZero_of_length_le (E.length_pageInfinity_le _ r hr) (hs p hp)
  rw [length_abutment_eq_sum_pageInfinity hE n s hs']
  exact Finset.sum_le_sum fun p _ => E.length_pageInfinity_le _ r hr

/-- **The numerical criterion for degeneration.** Let `E` be a spectral sequence of modules
abutting to `H`, and let `r` be a page all of whose terms have finite length; for each total
degree `n` let `s n` be a finite set outside which `E_r^{p, n - p}` vanishes. Then `E`
degenerates at `E_r` if and only if `ℓ(H^n) = ∑_{p ∈ s n} ℓ(E_r^{p, n - p})` for every `n`. -/
theorem degeneratesAt_iff_length_eq (hE : AbutsTo E H) (r : ℤ) (hr : r₀ ≤ r)
    (s : ℤ → Finset ℤ) (hs : ∀ n p, p ∉ s n → IsZero ((E.page r hr).X (p, n - p)))
    (hfin : ∀ pq, Module.length R ((E.page r hr).X pq) ≠ ⊤) :
    E.DegeneratesAt r hr ↔
      ∀ n, Module.length R (H n) = ∑ p ∈ s n, Module.length R ((E.page r hr).X (p, n - p)) := by
  have hinf := hE.1
  have hzeroInf : ∀ n p, p ∉ s n → IsZero (E.pageInfinity (p, n - p)) := fun n p hp =>
    ModuleCat.isZero_of_length_le (E.length_pageInfinity_le _ r hr) (hs n p hp)
  constructor
  · intro h n
    rw [length_abutment_eq_sum_pageInfinity hE n (s n) (hzeroInf n)]
    exact Finset.sum_congr rfl fun p _ => E.length_pageInfinity_eq_of_degeneratesAt h _
  · intro heq r' hr' pq pq'
    obtain ⟨p, q⟩ := pq
    obtain ⟨n, rfl⟩ : ∃ n, q = n - p := ⟨p + q, by omega⟩
    by_cases hp : p ∈ s n
    · -- the squeeze `∑ ℓ(E_∞) ≤ ∑ ℓ(E_{r'+1}) ≤ ∑ ℓ(E_{r'}) ≤ ∑ ℓ(E_r) = ℓ(H^n) = ∑ ℓ(E_∞)`
      have h2 : ∑ p ∈ s n, Module.length R ((E.page r' (by omega)).X (p, n - p)) ≤
          ∑ p ∈ s n, Module.length R ((E.page r hr).X (p, n - p)) :=
        Finset.sum_le_sum fun p _ => E.length_page_le _ r r' hr' hr
      have h3 : ∑ p ∈ s n, Module.length R ((E.page r hr).X (p, n - p)) ≤
          ∑ p ∈ s n, Module.length R ((E.page (r' + 1) (by omega)).X (p, n - p)) := by
        rw [← heq n, length_abutment_eq_sum_pageInfinity hE n (s n) (hzeroInf n)]
        exact Finset.sum_le_sum fun p _ => E.length_pageInfinity_le _ (r' + 1) (by omega)
      have htop : ∑ p ∈ s n, Module.length R ((E.page r' (by omega)).X (p, n - p)) ≠ ⊤ :=
        ne_top_of_le_ne_top (WithTop.sum_ne_top.2 fun p _ => hfin _) h2
      have hterm := ENat.eq_of_sum_le_sum_of_le (s n) _ _
        (fun p _ => E.length_page_succ_le r' (r' + 1) rfl (by omega) (p, n - p))
        (h2.trans h3) htop p hp
      refine (E.d_eq_zero_of_length_page_succ_eq r' (r' + 1) rfl (by omega) _ hterm ?_ pq').1
      exact ne_top_of_le_ne_top (hfin _) (E.length_page_le _ r r' hr' hr)
    · exact (ModuleCat.isZero_of_length_le (E.length_page_le _ r r' hr' hr) (hs n p hp)).eq_of_src
        _ _

end CategoryTheory.SpectralSequence

namespace CategoryTheory.SpectralSequence

variable {R : Type u} [CommRing R] {r₀ : ℤ}
  {E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀} {H : ℤ → ModuleCat.{v} R}

/-- **Deligne's numerical squeeze.** Let `E` be a spectral sequence of modules abutting to `H`,
`r` a page, and `b p q` bounds `ℓ(E_r^{p,q}) ≤ b p q`. If, for every total degree `n`, the bounds
over a finite set `s n` outside which `E_r^{p, n - p}` vanishes add up to at most `ℓ(H^n)`, and
`ℓ(H^n)` is finite, then `E` degenerates at `E_r` and every bound is attained:
`ℓ(E_r^{p, n - p}) = b p (n - p)` for `p ∈ s n`.

Over an Artinian local ring `A` with residue field `κ`, with `E` the Hodge-to-de Rham spectral
sequence, `b p q = ℓ(A) · h^{p,q}` and `ℓ(H^n) = ℓ(A) · h^n`, this is the step which deduces
degeneration over `A` and the freeness of the Hodge modules from the equality
`h^n = ∑_{p+q=n} h^{p,q}` over `κ`. -/
theorem degeneratesAt_and_length_eq_of_sum_le (hE : AbutsTo E H) (r : ℤ) (hr : r₀ ≤ r)
    (s : ℤ → Finset ℤ) (hs : ∀ n p, p ∉ s n → IsZero ((E.page r hr).X (p, n - p)))
    (b : ℤ → ℤ → ℕ∞) (hb : ∀ p q, Module.length R ((E.page r hr).X (p, q)) ≤ b p q)
    (hsum : ∀ n, ∑ p ∈ s n, b p (n - p) ≤ Module.length R (H n))
    (htop : ∀ n, Module.length R (H n) ≠ ⊤) :
    E.DegeneratesAt r hr ∧
      ∀ n, ∀ p ∈ s n, Module.length R ((E.page r hr).X (p, n - p)) = b p (n - p) := by
  have hle : ∀ n, Module.length R (H n) ≤
      ∑ p ∈ s n, Module.length R ((E.page r hr).X (p, n - p)) := fun n =>
    length_abutment_le_sum hE n r hr (s n) (hs n)
  have heqb : ∀ n, ∀ p ∈ s n, Module.length R ((E.page r hr).X (p, n - p)) = b p (n - p) :=
    fun n => ENat.eq_of_sum_le_sum_of_le (s n) _ _ (fun p _ => hb p (n - p))
      ((hsum n).trans (hle n)) (ne_top_of_le_ne_top (htop n) (hsum n))
  refine ⟨?_, heqb⟩
  have hfinX : ∀ p q, Module.length R ((E.page r hr).X (p, q)) ≠ ⊤ := by
    intro p q
    obtain ⟨n, rfl⟩ : ∃ n, q = n - p := ⟨p + q, by omega⟩
    by_cases hp : p ∈ s n
    · rw [heqb n p hp]
      exact ne_top_of_le_ne_top (htop n)
        ((Finset.single_le_sum (f := fun p => b p (n - p)) (fun _ _ => zero_le) hp).trans
          (hsum n))
    · rw [(ModuleCat.length_eq_zero_iff_isZero _).2 (hs n p hp)]
      exact ENat.zero_ne_top
  refine (degeneratesAt_iff_length_eq hE r hr s hs fun ⟨p, q⟩ => hfinX p q).2 fun n => ?_
  exact le_antisymm (hle n) ((Finset.sum_le_sum fun p _ => hb p (n - p)).trans (hsum n))

end CategoryTheory.SpectralSequence
