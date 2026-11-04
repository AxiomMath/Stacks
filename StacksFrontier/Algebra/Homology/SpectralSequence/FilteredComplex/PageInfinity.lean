module

public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons

/-!
# The infinity page of the spectral sequence of a filtered complex

Let `(K^•, F)` be a filtered complex of an abelian category `𝒜` such that for every `n` the
cohomology `H^n(F^pK^•)` vanishes for `p ≫ 0` and maps isomorphically to `H^n(K^•)` for `p ≪ 0`.
Then the spectral sequence of `(K^•, F)` has an infinity page at every bidegree, and
`E_∞^{p, q} ≅ gr^pH^{p + q}(K^•)` for the filtration induced on cohomology.

## Main results

* `CochainComplex.Filtered.finite_not_isZero_page_one`: for every `n` only finitely many terms of
  total degree `n` on the first page are nonzero.
* `CochainComplex.Filtered.hasPageInfinityAt_of_eventually`: the spectral sequence has an
  infinity page at every bidegree.
* `CochainComplex.Filtered.nonempty_pageInfinityIso_inducedFiltrationStep`: the infinity page at
  `(p, q)` is the graded piece `F^pH^n(K^•) / F^{p + 1}H^n(K^•)` of the induced filtration, where
  `n = p + q`.

## References

* [Stacks Project, Tag 0BK5](https://stacks.math.columbia.edu/tag/0BK5)
* [Stacks Project, Tag 012V](https://stacks.math.columbia.edu/tag/012V)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Under eventual vanishing and eventual invertibility of the cohomology of the filtration steps,
only finitely many terms of each total degree on the first page are nonzero. -/
theorem finite_not_isZero_page_one (K : Filtered C)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((K.filtration.obj (op p)).homology n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (n : ℤ) :
    {p : ℤ | ¬ IsZero (((spectralSequenceFunctor.obj K).page 1 (by omega)).X (p, n - p))}.Finite :=
  (CochainComplex.isBounded_and_converges_of_eventually_isZero_of_eventually_isIso K
    (filtrationSubobject K) (fun _ _ ↦ rfl)
    (FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K)) (fun _ _ _ ↦ rfl)
    (FilteredComplexSpectralSequence.boundaries K.X (filtrationSubobject K)) (fun _ _ _ ↦ rfl)
    K.inducedFiltrationStep (fun _ _ ↦ rfl) (spectralSequenceFunctor.obj K)
    (exists_pageIso_d K).choose hzero hiso).1 n

/-- Under eventual vanishing and eventual invertibility of the cohomology of the filtration steps,
the spectral sequence of a filtered complex has an infinity page at every bidegree. -/
theorem hasPageInfinityAt_of_eventually (K : Filtered C)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((K.filtration.obj (op p)).homology n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (pq : ℤ × ℤ) :
    (spectralSequenceFunctor.obj K).HasPageInfinityAt pq :=
  SpectralSequence.hasPageInfinityAt_of_finite_page _ 1 (by omega)
    (finite_not_isZero_page_one K hzero hiso) pq

/-- **The infinity page is the associated graded of the induced filtration.** Under eventual
vanishing and eventual invertibility of the cohomology of the filtration steps,
`E_∞^{p, q} ≅ F^pH^n(K^•) / F^{p + 1}H^n(K^•)` with `n = p + q`. -/
theorem nonempty_pageInfinityIso_inducedFiltrationStep (K : Filtered C)
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero ((K.filtration.obj (op p)).homology n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (p q : ℤ) :
    Nonempty ((spectralSequenceFunctor.obj K).pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE (K.inducedFiltrationStep (p + q) (p + 1))
        (K.inducedFiltrationStep (p + q) p)
        (K.inducedFiltrationStep_antitone (p + q) (by omega)))) := by
  classical
  set E := spectralSequenceFunctor.obj K with hEdef
  set F := filtrationSubobject K with hFdef
  set Z := FilteredComplexSpectralSequence.cycles K.X F with hZdef
  set D := FilteredComplexSpectralSequence.boundaries K.X F with hDdef
  have hZ : ∀ r' p' n' : ℤ, Z r' p' n' =
      F p' n' ⊓ (Subobject.pullback (K.X.d n' (n' + 1))).obj (F (p' + r') (n' + 1)) :=
    fun _ _ _ ↦ rfl
  have hD : ∀ r' p' n' : ℤ, D r' p' n' = Z (r' - 1) (p' + 1) n' ⊔
      (Subobject.exists (K.X.d (n' - 1) n')).obj (Z (r' - 1) (p' - r' + 1) (n' - 1)) :=
    fun _ _ _ ↦ rfl
  obtain ⟨e, -⟩ := exists_pageIso_d K
  obtain ⟨hbounded, -, -, -, hcomparison⟩ :=
    CochainComplex.isBounded_and_converges_of_eventually_isZero_of_eventually_isIso
      K F (fun _ _ ↦ rfl) Z (fun _ _ _ ↦ rfl) D (fun _ _ _ ↦ rfl)
      K.inducedFiltrationStep (fun _ _ ↦ rfl) E e hzero hiso
  have := SpectralSequence.hasPageInfinityAt_of_finite_page E 1 (by omega) hbounded (p, q)
  set n := p + q with hn
  set r := max (E.rMin (p, q))
    (max (max 1 ((hzero (n + 1)).choose - p)) (p - (hiso n).choose + 1)) with hrdef
  have hrmin : E.rMin (p, q) ≤ r := le_max_left _ _
  have : E.HasEdgeMonoAtFrom (p, q) r := ⟨(E.rToMin_LE_rMin (p, q)).trans hrmin⟩
  have : E.HasEdgeEpiAtFrom (p, q) r := ⟨(E.rFromMin_LE_rMin (p, q)).trans hrmin⟩
  have hr : 1 ≤ r := by rw [hrdef]; omega
  have hsOut : (hzero (n + 1)).choose ≤ p + r := by rw [hrdef]; omega
  have hsIn : p - r + 1 ≤ (hiso n).choose := by rw [hrdef]; omega
  set V := Z r p n with hVdef
  set W := F (p + 1) n with hWdef
  set N := kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ W with hNdef
  set B := imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ W with hBdef
  have hZcut : V ⊔ W = N := by
    have hb := (hzero (n + 1)).choose_spec (p + r) hsOut
    have hm : Mono (HomologicalComplex.homologyMap
        (K.filtration.ι.app (op (p + r))) (n + 1)) := hb.mono _
    exact CochainComplex.cycles_sup_eq_of_mono_homologyMap K F (fun _ _ ↦ rfl)
      p (p + r) n (by omega)
  have hX : imageSubobject (K.X.d (n - 1) n) ⊓ F p n ≤ V := by
    have hker : imageSubobject (K.X.d (n - 1) n) ≤ kernelSubobject (K.X.d n (n + 1)) :=
      image_le_kernel _ _ (K.X.d_comp_d _ _ _)
    have hpull : kernelSubobject (K.X.d n (n + 1)) ≤
        (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) := by
      rw [Subobject.le_pullback_iff, kernelSubobject_arrow_comp]
      exact Subobject.factors_zero
    exact le_inf inf_le_right (inf_le_left.trans (hker.trans hpull))
  have hZprev : Z (r - 1) (p + 1) n = W ⊓ V := by
    have hle : F (p + 1) n ≤ F p n := _root_.F_antitone K F (fun _ _ ↦ rfl) (by omega) n
    rw [hVdef, hWdef, hZ, hZ, show p + 1 + (r - 1) = p + r by omega, ← inf_assoc,
      inf_eq_left.2 hle]
  have hBoundaryIntersection : D r p n ⊓ V = B ⊓ V := by
    have himage : (Subobject.exists (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)) =
        imageSubobject (K.X.d (n - 1) n) ⊓ F p n := by
      have hb := (hiso n).choose_spec (p - r + 1) (by omega)
      rw [hZ, show p - r + 1 + (r - 1) = p by omega, show n - 1 + 1 = n by omega,
        CategoryTheory.Regular.exists_inf_pullback_eq_exists_inf, inf_comm]
      exact CochainComplex.boundaries_inf_eq_of_mono_homologyMap K F
        (fun _ _ ↦ rfl) p (p - r + 1) n (by omega)
    rw [hD, hZprev, himage, hBdef, sup_comm (W ⊓ V), sup_inf_assoc_of_le _ hX,
      sup_inf_assoc_of_le _ hX, inf_assoc, inf_idem]
  have hWcapD : W ⊓ V ≤ D r p n := by
    rw [hD, hZprev]
    exact le_sup_left
  have hVcapQ : V ⊓ W ≤ D r p n ⊓ V := le_inf ((inf_comm V W).le.trans hWcapD) inf_le_left
  have hQ : (D r p n ⊓ V) ⊔ W = B ⊓ N := by
    calc
      (D r p n ⊓ V) ⊔ W = W ⊔ (V ⊓ B) := by rw [hBoundaryIntersection]; ac_rfl
      _ = (W ⊔ V) ⊓ B := (sup_inf_assoc_of_le V (le_sup_right : W ≤ B)).symm
      _ = B ⊓ N := by rw [inf_comm, sup_comm W V, hZcut]
  have eStable : (E.page r (by omega)).X (p, q) ≅
      cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) := by
    have hleft : (V ⊓ W) ⊔ (D r p n ⊓ V) = D r p n ⊓ V := by rw [sup_eq_right.2 hVcapQ]
    have eSup := Classical.choice
      (Subobject.nonempty_cokernelOfLE_inf_sup_iso V W (D r p n ⊓ V) inf_le_right)
    have eLeft := Subobject.cokernelOfLEIsoOfEq
      (show (V ⊓ W) ⊔ (D r p n ⊓ V) ≤ V from sup_le inf_le_left inf_le_right)
      (show D r p n ⊓ V ≤ V from inf_le_right) hleft (rfl : V = V)
    have eRight := Subobject.cokernelOfLEIsoOfEq
      (show (D r p n ⊓ V) ⊔ W ≤ V ⊔ W from
        sup_le (inf_le_right.trans le_sup_left) le_sup_right)
      (show B ⊓ N ≤ N from inf_le_right) hQ hZcut
    exact e r p q n (by omega) hn ≪≫ eLeft.symm ≪≫ eSup ≪≫ eRight
  have hleFH : K.inducedFiltrationStep n (p + 1) ≤ K.inducedFiltrationStep n p :=
    K.inducedFiltrationStep_antitone n (show p ≤ p + 1 by omega)
  obtain ⟨a, b, eCompare, -, -, -⟩ := hcomparison p n
  have hcomp : HomologicalComplex.homologyMap
        (K.filtration.diagram.map (homOfLE (show p ≤ p + 1 by omega)).op) n ≫
      HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n =
      HomologicalComplex.homologyMap (K.filtration.ι.app (op (p + 1))) n := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun t ↦ HomologicalComplex.homologyMap t n)
      (K.filtration.diagram_map_comp_ι_app _)
  have hnum : imageSubobject (HomologicalComplex.homologyMap
        (K.filtration.diagram.map (homOfLE (show p ≤ p + 1 by omega)).op) n ≫
      HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      K.inducedFiltrationStep n (p + 1) := by
    rw [hcomp]
  exact ⟨E.pageInfinityIso (p, q) r ≪≫ eStable ≪≫ eCompare ≪≫
    Subobject.cokernelImagePreCompIso _ _ ≪≫
    Subobject.cokernelOfLEIsoOfEq (imageSubobject_comp_le _ _) hleFH hnum rfl⟩

end CochainComplex.Filtered

end
