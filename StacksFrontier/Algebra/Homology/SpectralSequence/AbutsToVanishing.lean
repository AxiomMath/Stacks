module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of the abutment of a spectral sequence

If a page of a cohomological spectral sequence vanishes along the antidiagonal `p + q = n`, then
so does the `n`-th term of any graded object it abuts to.

## Main results

* `CategoryTheory.SpectralSequence.isZero_page_of_isZero_page`: vanishing of a term of the page
  `E_r` propagates to every later page.
* `CategoryTheory.SpectralSequence.isZero_pageInfinity_of_isZero_page`: vanishing of a term of
  the page `E_r` propagates to the infinity page.
* `CategoryTheory.SpectralSequence.AbutsTo.isZero_of_isZero_pageInfinity`: an abutment vanishes
  in degree `n` as soon as the infinity page vanishes along `p + q = n`.
* `CategoryTheory.SpectralSequence.AbutsTo.isZero_of_isZero_page`: an abutment vanishes in
  degree `n` as soon as some page vanishes along `p + q = n`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Vanishing propagates up the pages.** A term of the page `E_r` which is zero stays zero on
every later page. -/
@[ega "0 11.1.6" "partial"]
theorem isZero_page_of_isZero_page {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀) {r : ℤ}
    (hr : r₀ ≤ r) (pq : ℤ × ℤ) (hz : IsZero ((E.page r hr).X pq)) :
    ∀ s : ℤ, r ≤ s → ∀ hs : r₀ ≤ s, IsZero ((E.page s hs).X pq) := by
  intro s hle
  induction s, hle using Int.leInduction with
  | base => exact fun _ => hz
  | succ m hm ih =>
    exact fun _ => IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ (ih (hr.trans hm)))
      (E.iso m (m + 1) pq rfl (hr.trans hm)).symm

/-- **Vanishing propagates to the infinity page.** A term of the page `E_r` which is zero is zero
on the infinity page. -/
theorem isZero_pageInfinity_of_isZero_page {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀)
    {r : ℤ} (hr : r₀ ≤ r) (pq : ℤ × ℤ) [E.HasPageInfinityAt pq]
    (hz : IsZero ((E.page r hr).X pq)) : IsZero (E.pageInfinity pq) := by
  have hsr : r ≤ max r (E.rMin pq) := le_max_left _ _
  have hs0 : r₀ ≤ max r (E.rMin pq) := hr.trans hsr
  have : E.HasEdgeMonoAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rToMin_LE_rMin pq).trans (le_max_right _ _)⟩
  have : E.HasEdgeEpiAtFrom pq (max r (E.rMin pq)) :=
    ⟨(E.rFromMin_LE_rMin pq).trans (le_max_right _ _)⟩
  exact IsZero.of_iso (isZero_page_of_isZero_page E hr pq hz _ hsr hs0)
    (E.pageInfinityIso pq (max r (E.rMin pq)))

/-- **An abutment vanishes where the infinity page vanishes.** If a spectral sequence abuts to
`H` and every term `E_∞^{p,q}` with `p + q = n` is zero, then `H n` is zero. -/
theorem AbutsTo.isZero_of_isZero_pageInfinity {r₀ : ℤ} {E : CohomologicalSpectralSequence C r₀}
    {H : ℤ → C} (hE : AbutsTo E H) (n : ℤ)
    (hz : ∀ p q : ℤ, p + q = n → IsZero (E.pageInfinity (p, q))) : IsZero (H n) := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  have hIso : ∀ p : ℤ, E.pageInfinity (p, n - p) ≅
      cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) := by
    intro p
    have heq : p + (n - p) = n := by omega
    conv_rhs => rw [← heq]
    exact (hgr p (n - p)).some
  have hstep : ∀ p : ℤ, F n (p + 1) = F n p := by
    intro p
    have hzc : IsZero (cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) :=
      IsZero.of_iso (hz p (n - p) (by omega)) (hIso p).symm
    have : Epi (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) :=
      Preadditive.epi_of_isZero_cokernel _ hzc
    have : IsIso (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) :=
      isIso_of_mono_of_epi _
    refine le_antisymm (hF n (by omega)) (Subobject.le_of_comm
      (inv (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega)))) ?_)
    rw [← Subobject.ofLE_arrow (hF n (show p ≤ p + 1 by omega)), IsIso.inv_hom_id_assoc]
  have hconst : ∀ a b : ℤ, a ≤ b → F n a = F n b := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => rfl
    | succ m hm ih => rw [ih, hstep m]
  obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
  have htb : (⊥ : Subobject (H n)) = ⊤ := by rw [← hb, ← ha, hconst a b hab]
  have : IsIso ((⊥ : Subobject (H n)).arrow) :=
    (Subobject.isIso_arrow_iff_eq_top (⊥ : Subobject (H n))).2 htb
  exact IsZero.of_epi_eq_zero (⊥ : Subobject (H n)).arrow Subobject.bot_arrow

/-- **An abutment vanishes where a page vanishes.** If a spectral sequence abuts to `H` and
every term `E_r^{p,q}` with `p + q = n` is zero, then `H n` is zero. -/
theorem AbutsTo.isZero_of_isZero_page {r₀ : ℤ} {E : CohomologicalSpectralSequence C r₀}
    {H : ℤ → C} (hE : AbutsTo E H) {r : ℤ} (hr : r₀ ≤ r) (n : ℤ)
    (hz : ∀ p q : ℤ, p + q = n → IsZero ((E.page r hr).X (p, q))) : IsZero (H n) := by
  refine hE.isZero_of_isZero_pageInfinity n fun p q hpq => ?_
  have : E.HasPageInfinityAt (p, q) := hE.1 p q
  exact isZero_pageInfinity_of_isZero_page E hr (p, q) (hz p q hpq)

end CategoryTheory.SpectralSequence

end
