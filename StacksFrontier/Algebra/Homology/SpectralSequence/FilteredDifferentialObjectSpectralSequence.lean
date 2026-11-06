module

public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredDifferentialObject
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.CategoryTheory.DifferentialObject

/-!
# The spectral sequence of a filtered differential object

Let `𝒜` be an abelian category and let `(K, F, d)` be a filtered differential object of `𝒜`: an
object `K` with a decreasing filtration `F^p K` and an endomorphism `d` with `d ∘ d = 0` and
`d(F^p K) ⊆ F^p K`. Inside `K` put
```
Z_r^p = F^p K ∩ d⁻¹(F^{p + r} K),     D_r^p = Z_{r - 1}^{p + 1} + d(Z_{r - 1}^{p - r + 1}),
```
and `E_r^p = Z_r^p / (D_r^p ∩ Z_r^p)`. Then `d` maps `Z_r^p` to `Z_r^{p + r}` and `D_r^p` to
`D_r^{p + r}`, so it induces `d_r^p : E_r^p ⟶ E_r^{p + r}`, and `(E_r, d_r)_{r ≥ 0}` is a spectral
sequence of graded objects of `𝒜`: the cohomology of `(E_r, d_r)` is `E_{r + 1}`. Its pages are the
source's: `E_r^p = Z_r^p / B_r^p` for the subobjects
`Z_r^p = (F^p K ∩ d⁻¹(F^{p + r} K) + F^{p + 1} K) / F^{p + 1} K` and
`B_r^p = (F^p K ∩ d(F^{p - r + 1} K) + F^{p + 1} K) / F^{p + 1} K` of `gr^p K`. Moreover
`E_0^p = gr^p K` with `d_0^p = gr^p(d)`, so that `E_1^p = H(gr^p K)` (Stacks 012C), and under these
identifications `d_1^p` is the boundary map of the short exact sequence of differential objects
`0 → gr^{p + 1} K → F^p K / F^{p + 2} K → gr^p K → 0` (Stacks 012D).

The spectral sequence weakly converges to `H(K)` exactly when equality holds in the inclusions
(012G) and (012H) of Stacks 012F, and it abuts to `H(K)` exactly when moreover
`⋂_p (Ker(d) ∩ F^p K + Im(d)) = Im(d)` and `⋃_p (Ker(d) ∩ F^p K + Im(d)) = Ker(d)` (Stacks 012J).

## Main definitions

* `FilteredDifferentialObject.spectralSequence`: the spectral sequence `(E_r, d_r)_{r ≥ 0}` of
  `(K, F, d)`.
* `FilteredDifferentialObject.pageZeroIso`, `FilteredDifferentialObject.pageOneIso`:
  `E_0^p = gr^p K` and `E_1^p = H(gr^p K)`.
* `FilteredDifferentialObject.grShortExactSequence`: the short exact sequence
  `0 → gr^{p + 1} K → F^p K / F^{p + 2} K → gr^p K → 0`.
* `FilteredDifferentialObject.WeaklyConverges`, `FilteredDifferentialObject.Abuts`: weak
  convergence and abutment of the spectral sequence to `H(K)`.

## Main results

* `FilteredDifferentialObject.exists_page_iso`, `FilteredDifferentialObject.π_spectralSequence_d`,
  `FilteredDifferentialObject.homologyπ_spectralSequence_iso_hom`,
  `FilteredDifferentialObject.spectralSequence_d_zero`: the description of the pages, of the
  differentials, of the page-turn isomorphisms and of `d_0` (Stacks 012C).
* `FilteredDifferentialObject.spectralSequence_d_one`: `d_1` is a boundary map (Stacks 012D).
* `FilteredDifferentialObject.weaklyConverges_iff`, `FilteredDifferentialObject.abuts_iff`: the
  criteria for weak convergence and abutment (Stacks 012J).

## References

* [Stacks, Tag 012C](https://stacks.math.columbia.edu/tag/012C)
* [Stacks, Tag 012D](https://stacks.math.columbia.edu/tag/012D)
* [Stacks, Tag 012J](https://stacks.math.columbia.edu/tag/012J)
-/

@[expose] public section

universe v u

namespace FilteredDifferentialObject

open CategoryTheory Limits Subobject Opposite

variable {A : Type u} [Category.{v} A] [Abelian A] (X : FilteredDifferentialObject A)

section Pages

/-- The differential carries each step of the filtration into itself. -/
lemma le_pullback_d (p : ℤ) : X.F p ≤ (Subobject.pullback X.d).obj (X.F p) :=
  (le_pullback_iff _ _ _).2 (X.d_respects p)

/-- The image under `d` of a step of the filtration lies in that step. -/
lemma exists_d_le (p : ℤ) : (Subobject.exists X.d).obj (X.F p) ≤ X.F p :=
  (Subobject.exists_le_iff_le_pullback _ _ _).2 (X.le_pullback_d p)

/-- The numerator `Z_r^p = F^p K ∩ d⁻¹(F^{p + r} K)` of the cycles of the `r`-th page. -/
noncomputable def pageCycles (r p : ℤ) : Subobject X.X :=
  X.F p ⊓ (Subobject.pullback X.d).obj (X.F (p + r))

/-- The numerator `D_r^p = Z_{r - 1}^{p + 1} + d(Z_{r - 1}^{p - r + 1})` of the boundaries of the
`r`-th page. -/
noncomputable def pageBoundaries (r p : ℤ) : Subobject X.X :=
  X.pageCycles (r - 1) (p + 1) ⊔ (Subobject.exists X.d).obj (X.pageCycles (r - 1) (p - r + 1))

/-- The object `E_r^p = Z_r^p / (D_r^p ∩ Z_r^p)` of the `r`-th page. -/
noncomputable abbrev page (r p : ℤ) : A :=
  cokernel (Subobject.ofLE _ _
    (inf_le_right : X.pageBoundaries r p ⊓ X.pageCycles r p ≤ X.pageCycles r p))

/-- `Z_r^p ⊆ F^p K`. -/
lemma pageCycles_le (r p : ℤ) : X.pageCycles r p ≤ X.F p :=
  inf_le_left

/-- `d(Z_r^p) ⊆ Z_r^{p + r}`. -/
lemma exists_pageCycles_le (r p p' : ℤ) (h : p + r = p') :
    (Subobject.exists X.d).obj (X.pageCycles r p) ≤ X.pageCycles r p' := by
  subst h
  refine le_inf ?_ ?_
  · rw [Subobject.exists_le_iff_le_pullback]
    exact inf_le_right
  · exact exists_le_pullback_of_comp_eq_zero X.d_squared _ _

/-- `d(D_r^p) ⊆ D_r^{p + r}`. -/
lemma exists_pageBoundaries_le (r p p' : ℤ) (h : p + r = p') :
    (Subobject.exists X.d).obj (X.pageBoundaries r p) ≤ X.pageBoundaries r p' := by
  subst h
  have e : p + r - r + 1 = p + 1 := by omega
  rw [pageBoundaries, pageBoundaries, e, (Subobject.existsPullbackAdj X.d).gc.l_sup]
  refine sup_le le_sup_right ?_
  rw [Subobject.exists_le_iff_le_pullback]
  exact (exists_le_pullback_of_comp_eq_zero X.d_squared _ _).trans
    ((Subobject.pullback X.d).monotone le_sup_left)

/-- The restriction `Z_r^p ⟶ Z_r^{p + r}` of `d`. -/
noncomputable def pageδ (r p p' : ℤ) (h : p + r = p') :
    (X.pageCycles r p : A) ⟶ (X.pageCycles r p' : A) :=
  (X.pageCycles r p').factorThru ((X.pageCycles r p).arrow ≫ X.d)
    (factors_arrow_comp_of_exists_le _ (X.exists_pageCycles_le r p p' h))

/-- The morphism `Z_r^p ⟶ Z_r^{p + r}` is the restriction of `d`. -/
@[reassoc (attr := simp)]
lemma pageδ_arrow (r p p' : ℤ) (h : p + r = p') :
    X.pageδ r p p' h ≫ (X.pageCycles r p').arrow = (X.pageCycles r p).arrow ≫ X.d :=
  Subobject.factorThru_arrow _ _ _

/-- The composition of two consecutive restrictions `Z_r^p ⟶ Z_r^{p + r}` of `d` is zero. -/
lemma pageδ_comp_pageδ (r p p' p'' : ℤ) (h : p + r = p') (h' : p' + r = p'') :
    X.pageδ r p p' h ≫ X.pageδ r p' p'' h' = 0 := by
  rw [← cancel_mono (X.pageCycles r p'').arrow, Category.assoc, pageδ_arrow, pageδ_arrow_assoc,
    X.d_squared, comp_zero, zero_comp]

/-- The restriction `Z_r^p ⟶ Z_r^{p + r}` of `d` carries `D_r^p ∩ Z_r^p` to zero in
`E_r^{p + r}`. -/
lemma pageδ_π_eq_zero (r p p' : ℤ) (h : p + r = p') :
    Subobject.ofLE _ _ (inf_le_right : X.pageBoundaries r p ⊓ X.pageCycles r p ≤ _) ≫
      X.pageδ r p p' h ≫ cokernel.π (Subobject.ofLE _ _
        (inf_le_right : X.pageBoundaries r p' ⊓ X.pageCycles r p' ≤ _)) = 0 := by
  rw [← Category.assoc, comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _), Category.assoc,
    pageδ_arrow, ← Category.assoc, Subobject.ofLE_arrow]
  refine factors_arrow_comp_of_exists_le _ ?_
  refine ((Subobject.exists X.d).monotone le_rfl).trans ?_
  refine le_inf ?_ ?_
  · exact ((Subobject.exists X.d).monotone inf_le_left).trans (X.exists_pageBoundaries_le r p p' h)
  · exact ((Subobject.exists X.d).monotone inf_le_right).trans (X.exists_pageCycles_le r p p' h)

/-- The differential `d_r^p : E_r^p ⟶ E_r^{p + r}`, induced by `d`. -/
noncomputable def pageMap (r p p' : ℤ) (h : p + r = p') : X.page r p ⟶ X.page r p' :=
  cokernel.desc _ (X.pageδ r p p' h ≫ cokernel.π _) (X.pageδ_π_eq_zero r p p' h)

/-- The differential `d_r^p` sends the class of `x ∈ Z_r^p` to the class of `d x`. -/
@[reassoc (attr := simp)]
lemma π_pageMap (r p p' : ℤ) (h : p + r = p') :
    cokernel.π _ ≫ X.pageMap r p p' h = X.pageδ r p p' h ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

/-- `d_r^{p + r} ∘ d_r^p = 0`. -/
lemma pageMap_comp_pageMap (r p p' p'' : ℤ) (h : p + r = p') (h' : p' + r = p'') :
    X.pageMap r p p' h ≫ X.pageMap r p' p'' h' = 0 := by
  rw [← cancel_epi (cokernel.π _), π_pageMap_assoc, π_pageMap, ← Category.assoc,
    pageδ_comp_pageδ, zero_comp, comp_zero]

/-- The `r`-th page `(E_r, d_r)`, a complex with differentials `E_r^p ⟶ E_r^{p + r}`. -/
noncomputable abbrev pageComplex (r : ℤ) : HomologicalComplex A (ComplexShape.up' r) where
  X p := X.page r p
  d p p' := if h : p + r = p' then X.pageMap r p p' h else 0
  shape p p' h := dite_eq_right_of_eq_false (eq_false h)
  d_comp_d' p p' p'' (h : p + r = p') (h' : p' + r = p'') := by
    rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h')]
    exact X.pageMap_comp_pageMap r p p' p'' h h'

/-- The differential of the complex `(E_r, d_r)` from `E_r^p` to `E_r^{p + r}` is `d_r^p`. -/
lemma pageComplex_d (r p p' : ℤ) (h : p + r = p') :
    (X.pageComplex r).d p p' = X.pageMap r p p' h :=
  dite_eq_left_of_eq_true (eq_true h)

/-- The numerator `F^p K ∩ d(F^{p - r + 1} K)` of the boundaries `B_r^p` lies in `Z_r^p`. -/
lemma inf_imageSubobject_le_pageCycles (r p : ℤ) :
    X.F p ⊓ imageSubobject ((X.F (p - r + 1)).arrow ≫ X.d) ≤ X.pageCycles r p := by
  refine le_inf inf_le_left (inf_le_right.trans ?_)
  rw [← Subobject.exists_eq_imageSubobject]
  exact exists_le_pullback_of_comp_eq_zero X.d_squared _ _

/-- `D_r^p ∩ Z_r^p = ((F^p K ∩ d(F^{p - r + 1} K)) + F^{p + 1} K) ∩ Z_r^p`. -/
lemma pageBoundaries_inf_pageCycles (r p : ℤ) :
    X.pageBoundaries r p ⊓ X.pageCycles r p =
      (X.F p ⊓ imageSubobject ((X.F (p - r + 1)).arrow ≫ X.d) ⊔ X.F (p + 1)) ⊓
        X.pageCycles r p := by
  have hd : (Subobject.exists X.d).obj (X.pageCycles (r - 1) (p - r + 1)) =
      X.F p ⊓ imageSubobject ((X.F (p - r + 1)).arrow ≫ X.d) := by
    rw [pageCycles, Regular.exists_inf_pullback_eq_exists_inf, Subobject.exists_eq_imageSubobject,
      show p - r + 1 + (r - 1) = p by omega, inf_comm]
  have hZ : X.pageCycles (r - 1) (p + 1) = X.F (p + 1) ⊓ X.pageCycles r p := by
    rw [pageCycles, pageCycles, show p + 1 + (r - 1) = p + r by omega, ← inf_assoc,
      inf_eq_left.2 (X.filtration_antitone (show p ≤ p + 1 by omega))]
  have hB := X.inf_imageSubobject_le_pageCycles r p
  rw [pageBoundaries, hd, hZ, inf_eq_left.2 (sup_le _root_.inf_le_right hB :
    X.F (p + 1) ⊓ X.pageCycles r p ⊔ _ ≤ X.pageCycles r p), sup_inf_assoc_of_le _ hB, sup_comm]

/-- The object `E_r^p` of the `r`-th page is `Z_r^p / B_r^p`, where, inside `gr^p K`,
`Z_r^p = (F^p K ∩ d⁻¹(F^{p + r} K) + F^{p + 1} K) / F^{p + 1} K` and
`B_r^p = (F^p K ∩ d(F^{p - r + 1} K) + F^{p + 1} K) / F^{p + 1} K`; the isomorphism is the identity
on the classes of elements of `F^p K ∩ d⁻¹(F^{p + r} K)`. -/
@[stacks 012C]
theorem exists_page_iso (r p : ℤ) :
    ∃ e : X.page r p ≅ cokernel (Subobject.ofLE
      (X.F p ⊓ imageSubobject ((X.F (p - r + 1)).arrow ≫ X.d) ⊔ X.F (p + 1))
      (X.pageCycles r p ⊔ X.F (p + 1))
      (sup_le_sup_right (X.inf_imageSubobject_le_pageCycles r p) _)),
      cokernel.π _ ≫ e.hom = Subobject.ofLE _ _
        (le_sup_left : X.pageCycles r p ≤ X.pageCycles r p ⊔ X.F (p + 1)) ≫ cokernel.π _ := by
  have : Epi (𝟙 _ ≫ cokernel.π (Subobject.ofLE _ _
      (_root_.inf_le_right : X.pageBoundaries r p ⊓ X.pageCycles r p ≤ _))) := by
    rw [Category.id_comp]; infer_instance
  have := Subobject.epi_ofLE_comp_cokernel_π (Subobject.ofLE _ _
      (sup_le_sup_right (X.inf_imageSubobject_le_pageCycles r p) (X.F (p + 1))))
    (Subobject.ofLE_arrow _) (le_sup_left : X.pageCycles r p ≤ _) le_rfl le_sup_right
  obtain ⟨e, he⟩ := Subobject.exists_iso_cokernel_of_factors_iff
    (Subobject.ofLE _ _ (_root_.inf_le_right : X.pageBoundaries r p ⊓ X.pageCycles r p ≤ _))
    (Subobject.ofLE_arrow _)
    (Subobject.ofLE _ _
      (sup_le_sup_right (X.inf_imageSubobject_le_pageCycles r p) (X.F (p + 1))))
    (Subobject.ofLE_arrow _) (𝟙 _)
    (Subobject.ofLE _ _ (le_sup_left : X.pageCycles r p ≤ X.pageCycles r p ⊔ X.F (p + 1)))
    (fun {T'} g ↦ by
      rw [Category.id_comp, Subobject.ofLE_arrow, X.pageBoundaries_inf_pageCycles,
        Subobject.inf_factors]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, Subobject.factors_comp_arrow g⟩⟩)
  exact ⟨e, by simpa using he⟩

end Pages

section ConstantComplex

/-- The cochain complex `⋯ → K → K → ⋯` with every differential `d`. -/
private noncomputable def toCochainComplex : CochainComplex A ℤ where
  X _ := X.X
  d i j := if i + 1 = j then X.d else 0
  shape i j h := ite_eq_right_of_eq_false _ _ (eq_false h)
  d_comp_d' i j k (h : i + 1 = j) (h' : j + 1 = k) := by
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
    exact X.d_squared

private lemma toCochainComplex_d {i j : ℤ} (h : i + 1 = j) : (toCochainComplex X).d i j = X.d :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

/-- The subcomplex `⋯ → F^p K → F^p K → ⋯`. -/
private noncomputable def stepComplex (p : ℤ) : CochainComplex A ℤ where
  X _ := (X.F p : A)
  d i j := if i + 1 = j then X.dp p else 0
  shape i j h := ite_eq_right_of_eq_false _ _ (eq_false h)
  d_comp_d' i j k (h : i + 1 = j) (h' : j + 1 = k) := by
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
    exact X.dp_sq p

private lemma stepComplex_d (p : ℤ) {i j : ℤ} (h : i + 1 = j) : (stepComplex X p).d i j = X.dp p :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

private noncomputable def stepComplexι (p : ℤ) : stepComplex X p ⟶ toCochainComplex X where
  f _ := (X.F p).arrow
  comm' i j h := by
    rw [toCochainComplex_d X h, stepComplex_d X p h]
    exact (X.dp_comm p).symm

private instance (p : ℤ) : Mono (stepComplexι X p) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦ inferInstanceAs (Mono (X.F p).arrow)

/-- The restricted differentials commute with the inclusions of the filtration. -/
@[reassoc]
lemma ofLE_comp_dp {p q : ℤ} (h : X.F q ≤ X.F p) :
    Subobject.ofLE _ _ h ≫ X.dp p = X.dp q ≫ Subobject.ofLE _ _ h := by
  rw [← cancel_mono (X.F p).arrow]
  simp

private noncomputable def stepComplexMap {p q : ℤ} (h : p ≤ q) :
    stepComplex X q ⟶ stepComplex X p where
  f _ := Subobject.ofLE _ _ (X.filtration_antitone h)
  comm' i j hij := by
    rw [stepComplex_d X p hij, stepComplex_d X q hij]
    exact X.ofLE_comp_dp _

/-- `(K, F, d)` as a filtered cochain complex, constant in the cohomological degree. -/
private noncomputable def toFilteredComplex : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ where
  X := toCochainComplex X
  filtration := ⟨
    { obj n := ⟨Over.mk (stepComplexι X n.unop), inferInstanceAs (Mono (stepComplexι X n.unop))⟩
      map f := MonoOver.homMk (stepComplexMap X (leOfHom f.unop)) (by
        ext
        exact Subobject.ofLE_arrow _)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }⟩

end ConstantComplex

section PageTurn

/-- An isomorphism `H(E_r, d_r)^p ≅ E_{r + 1}^p` sends the class of each `r`-cycle represented by
an element `x` of `Z_{r + 1}^p ⊆ Z_r^p` to the class of `x`. -/
private def IsPageTurn (r p : ℤ) (ψ : (X.pageComplex r).homology p ≅ X.page (r + 1) p) : Prop :=
  ∀ {T : A} (y : T ⟶ (X.pageComplex r).cycles p) (x : T ⟶ (X.pageCycles (r + 1) p : A))
    (x' : T ⟶ (X.pageCycles r p : A)),
    x' ≫ (X.pageCycles r p).arrow = x ≫ (X.pageCycles (r + 1) p).arrow →
    y ≫ (X.pageComplex r).iCycles p = x' ≫ cokernel.π _ →
    y ≫ (X.pageComplex r).homologyπ p ≫ ψ.hom = x ≫ cokernel.π _

private lemma exists_isPageTurn_aux (r : ℤ) (hr : 0 ≤ r) (p : ℤ)
    (E : CohomologicalSpectralSequence A 0)
    (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r), n = p + q → ((E.page r hr).X (p, q) ≅ X.page r p))
    (hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
      ∃ δ : (X.pageCycles r p : A) ⟶ (X.pageCycles r (p + r) : A),
        δ ≫ (X.pageCycles r (p + r)).arrow =
          (X.pageCycles r p).arrow ≫ (toCochainComplex X).d n (n + 1) ∧
        cokernel.π _ ≫ (e r p q n hr hn).inv ≫ (E.page r hr).d (p, q) (p + r, q - r + 1) =
          δ ≫ cokernel.π _ ≫ (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv)
    (ψ₀ : (E.page r hr).homology (p, 0) ≅ (E.page (r + 1) (by omega)).X (p, 0))
    (hψ₀ : ∀ {T : A} (y : T ⟶ (E.page r hr).cycles (p, 0)) (x : T ⟶ (X.pageCycles (r + 1) p : A))
      (x' : T ⟶ (X.pageCycles r p : A)),
      x' ≫ (X.pageCycles r p).arrow = x ≫ (X.pageCycles (r + 1) p).arrow →
      y ≫ (E.page r hr).iCycles (p, 0) = x' ≫ cokernel.π _ ≫ (e r p 0 p hr (by omega)).inv →
      y ≫ (E.page r hr).homologyπ (p, 0) ≫ ψ₀.hom =
        x ≫ cokernel.π _ ≫ (e (r + 1) p 0 p (by omega) (by omega)).inv) :
    ∃ ψ, X.IsPageTurn r p ψ := by
  have key : ∀ (a b n a' b' n' : ℤ) (hn : n = a + b) (ha : a + r = a') (hb : b' = b - r + 1)
      (hn' : n' = n + 1),
      (e r a b n hr hn).inv ≫ (E.page r hr).d (a, b) (a', b') =
        X.pageMap r a a' ha ≫ (e r a' b' n' hr (by omega)).inv := by
    intro a b n a' b' n' hn ha hb hn'
    subst ha hb hn'
    obtain ⟨δ, hδ₁, hδ₂⟩ := hδ r a b n hr hn
    have hδ₃ : δ = X.pageδ r a (a + r) rfl := by
      rw [← cancel_mono (X.pageCycles r (a + r)).arrow, hδ₁, toCochainComplex_d X rfl,
        pageδ_arrow]
      exact rfl
    rw [← cancel_epi (cokernel.π _), hδ₂, hδ₃, π_pageMap_assoc]
  have hPi : (ComplexShape.up' r).prev p = p - r := (ComplexShape.up' r).prev_eq' (by
    show p - r + r = p; omega)
  have hPk : (ComplexShape.up' r).next p = p + r := (ComplexShape.up' r).next_eq' rfl
  have hGi : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev (p, 0) = (p - r, r - 1) :=
    (ComplexShape.up' _).prev_eq' (by
      show ((p - r, r - 1) : ℤ × ℤ) + (r, 1 - r) = (p, 0)
      ext <;> simp)
  have hGk : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next (p, 0) = (p + r, 1 - r) :=
    (ComplexShape.up' _).next_eq' (by
      show ((p, 0) : ℤ × ℤ) + (r, 1 - r) = (p + r, 1 - r)
      ext <;> simp)
  let Φ : (X.pageComplex r).sc' (p - r) p (p + r) ≅
      (E.page r hr).sc' (p - r, r - 1) (p, 0) (p + r, 1 - r) :=
    ShortComplex.isoMk (e r (p - r) (r - 1) (p - 1) hr (by omega)).symm
      (e r p 0 p hr (by omega)).symm (e r (p + r) (1 - r) (p + 1) hr (by omega)).symm
      (by
        show _ ≫ (E.page r hr).d _ _ = (X.pageComplex r).d _ _ ≫ _
        rw [pageComplex_d X r (p - r) p (by omega)]
        exact key _ _ _ _ _ _ _ (by omega) (by omega) (by omega))
      (by
        show _ ≫ (E.page r hr).d _ _ = (X.pageComplex r).d _ _ ≫ _
        rw [pageComplex_d X r p (p + r) rfl]
        exact key _ _ _ _ _ _ _ (by omega) (by omega) (by omega))
  refine ⟨(X.pageComplex r).homologyIsoSc' (p - r) p (p + r) hPi hPk ≪≫
    ShortComplex.homologyMapIso Φ ≪≫ ((E.page r hr).homologyIsoSc' _ _ _ hGi hGk).symm ≪≫ ψ₀ ≪≫
    e (r + 1) p 0 p (by omega) (by omega), ?_⟩
  intro T y x x' hx hy
  let y' : T ⟶ (E.page r hr).cycles (p, 0) :=
    y ≫ ((X.pageComplex r).cyclesIsoSc' _ _ _ hPi hPk).hom ≫
      ShortComplex.cyclesMap Φ.hom ≫ ((E.page r hr).cyclesIsoSc' _ _ _ hGi hGk).inv
  have h₁ : y' ≫ (E.page r hr).iCycles (p, 0) =
      x' ≫ cokernel.π _ ≫ (e r p 0 p hr (by omega)).inv := by
    have e1 : ((E.page r hr).cyclesIsoSc' _ _ _ hGi hGk).inv ≫ (E.page r hr).iCycles (p, 0) =
        ((E.page r hr).sc' (p - r, r - 1) (p, 0) (p + r, 1 - r)).iCycles :=
      HomologicalComplex.cyclesIsoSc'_inv_iCycles _ _ _ _ _ _
    have e2 : ShortComplex.cyclesMap Φ.hom ≫
        ((E.page r hr).sc' (p - r, r - 1) (p, 0) (p + r, 1 - r)).iCycles =
        ((X.pageComplex r).sc' (p - r) p (p + r)).iCycles ≫ Φ.hom.τ₂ := ShortComplex.cyclesMap_i _
    have e3 : ((X.pageComplex r).cyclesIsoSc' _ _ _ hPi hPk).hom ≫
        ((X.pageComplex r).sc' (p - r) p (p + r)).iCycles = (X.pageComplex r).iCycles p :=
      HomologicalComplex.cyclesIsoSc'_hom_iCycles _ _ _ _ _ _
    have s1 : y' ≫ (E.page r hr).iCycles (p, 0) =
        y ≫ ((X.pageComplex r).cyclesIsoSc' _ _ _ hPi hPk).hom ≫ ShortComplex.cyclesMap Φ.hom ≫
          ((E.page r hr).sc' (p - r, r - 1) (p, 0) (p + r, 1 - r)).iCycles := by
      simp only [y', Category.assoc, e1]
    have s2 : y ≫ ((X.pageComplex r).cyclesIsoSc' _ _ _ hPi hPk).hom ≫
        ShortComplex.cyclesMap Φ.hom ≫
          ((E.page r hr).sc' (p - r, r - 1) (p, 0) (p + r, 1 - r)).iCycles =
        y ≫ ((X.pageComplex r).cyclesIsoSc' _ _ _ hPi hPk).hom ≫
          ((X.pageComplex r).sc' (p - r) p (p + r)).iCycles ≫ Φ.hom.τ₂ := by rw [e2]
    have s3 : y ≫ ((X.pageComplex r).cyclesIsoSc' _ _ _ hPi hPk).hom ≫
        ((X.pageComplex r).sc' (p - r) p (p + r)).iCycles ≫ Φ.hom.τ₂ =
        y ≫ (X.pageComplex r).iCycles p ≫ Φ.hom.τ₂ := by rw [reassoc_of% e3]
    have s4 : y ≫ (X.pageComplex r).iCycles p ≫ Φ.hom.τ₂ =
        x' ≫ cokernel.π _ ≫ (e r p 0 p hr (by omega)).inv := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun t ↦ t ≫ (e r p 0 p hr (by omega)).inv) hy).trans ?_
      exact Category.assoc _ _ _
    exact s1.trans (s2.trans (s3.trans s4))
  have h₂ := hψ₀ y' x x' hx h₁
  have h₃ : y ≫ (X.pageComplex r).homologyπ p ≫
      ((X.pageComplex r).homologyIsoSc' (p - r) p (p + r) hPi hPk).hom ≫
      ShortComplex.homologyMap Φ.hom ≫ ((E.page r hr).homologyIsoSc' _ _ _ hGi hGk).inv =
      y' ≫ (E.page r hr).homologyπ (p, 0) := by
    simp only [y', Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
      ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom]
  rw [reassoc_of% h₃, reassoc_of% h₂, Iso.inv_hom_id, Category.comp_id]

/-- The cohomology of `(E_r, d_r)` at `p` is `E_{r + 1}^p`, by an isomorphism sending the class of
an `r`-cycle represented by an element `x` of `Z_{r + 1}^p ⊆ Z_r^p` to the class of `x`. -/
theorem exists_pageHomologyIso (r : ℤ) (hr : 0 ≤ r) (p : ℤ) :
    ∃ ψ : (X.pageComplex r).homology p ≅ X.page (r + 1) p,
      ∀ {T : A} (y : T ⟶ (X.pageComplex r).cycles p) (x : T ⟶ (X.pageCycles (r + 1) p : A))
        (x' : T ⟶ (X.pageCycles r p : A)),
        x' ≫ (X.pageCycles r p).arrow = x ≫ (X.pageCycles (r + 1) p).arrow →
        y ≫ (X.pageComplex r).iCycles p = x' ≫ cokernel.π _ →
        y ≫ (X.pageComplex r).homologyπ p ≫ ψ.hom = x ≫ cokernel.π _ := by
  let K := toFilteredComplex X
  let F : ∀ (_p n : ℤ), Subobject (K.X.X n) := fun p _ ↦ X.F p
  have hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n) :=
    fun p n ↦ (Subobject.mk_arrow (X.F p)).symm
  let Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n) := fun r p _ ↦ X.pageCycles r p
  have hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) := by
    intro r p n
    show X.pageCycles r p =
      X.F p ⊓ (Subobject.pullback ((toCochainComplex X).d n (n + 1))).obj _
    rw [toCochainComplex_d X rfl]
    rfl
  let D : ∀ (_r _p n : ℤ), Subobject (K.X.X n) := fun r p _ ↦ X.pageBoundaries r p
  have hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.exists (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)) := by
    intro r p n
    show X.pageBoundaries r p = _ ⊔
      (Subobject.exists ((toCochainComplex X).d (n - 1) n)).obj _
    rw [toCochainComplex_d X (by omega)]
    rfl
  obtain ⟨E, e, -, hδ, -⟩ := CochainComplex.exists_cohomologicalSpectralSequence K F hF Z hZ D hD
  obtain ⟨ψ₀, hψ₀⟩ := CochainComplex.exists_iso_homology_page_of_mem_cycles K F hF Z hZ D hD E e
    hδ r (r + 1) p 0 p hr rfl (by omega)
  exact X.exists_isPageTurn_aux r hr p E e hδ ψ₀ hψ₀

end PageTurn

section SpectralSequence

/-- The page-turn isomorphism `H(E_r, d_r)^p ≅ E_{r + 1}^p` of `exists_pageHomologyIso`. -/
noncomputable def pageHomologyIso (r : ℤ) (hr : 0 ≤ r) (p : ℤ) :
    (X.pageComplex r).homology p ≅ X.page (r + 1) p :=
  (X.exists_pageHomologyIso r hr p).choose

/-- The page-turn isomorphism sends the class of an `r`-cycle represented by `x ∈ Z_{r + 1}^p` to
the class of `x` in `E_{r + 1}^p`. -/
lemma homologyπ_pageHomologyIso_hom (r : ℤ) (hr : 0 ≤ r) (p : ℤ) {T : A}
    (y : T ⟶ (X.pageComplex r).cycles p) (x : T ⟶ (X.pageCycles (r + 1) p : A))
    (x' : T ⟶ (X.pageCycles r p : A))
    (hx : x' ≫ (X.pageCycles r p).arrow = x ≫ (X.pageCycles (r + 1) p).arrow)
    (hy : y ≫ (X.pageComplex r).iCycles p = x' ≫ cokernel.π _) :
    y ≫ (X.pageComplex r).homologyπ p ≫ (X.pageHomologyIso r hr p).hom = x ≫ cokernel.π _ :=
  (X.exists_pageHomologyIso r hr p).choose_spec y x x' hx hy

/-- The spectral sequence `(E_r, d_r)_{r ≥ 0}` associated to a filtered differential object
`(K, F, d)`: its `r`-th page is the graded object `E_r^p = Z_r^p / (D_r^p ∩ Z_r^p)` with the
differential `d_r^p : E_r^p ⟶ E_r^{p + r}` induced by `d`, and the cohomology of `(E_r, d_r)` is
identified with `E_{r + 1}` by the page-turn isomorphism. -/
@[stacks 012C]
noncomputable def spectralSequence : SpectralSequence A (fun r => ComplexShape.up' r) 0 where
  page r _ := X.pageComplex r
  iso r r' p h hr := X.pageHomologyIso r hr p ≪≫ eqToIso (by subst h; rfl)

/-- The `r`-th page of the spectral sequence is the complex `(E_r, d_r)`. -/
lemma spectralSequence_page (r : ℤ) (hr : 0 ≤ r) :
    X.spectralSequence.page r hr = X.pageComplex r := rfl

/-- The differential `d_r^p : E_r^p ⟶ E_r^{p + r}` of the spectral sequence is induced by
`d : Z_r^p ⟶ Z_r^{p + r}`. -/
@[stacks 012C]
lemma π_spectralSequence_d (r : ℤ) (hr : 0 ≤ r) (p p' : ℤ) (h : p + r = p') :
    cokernel.π _ ≫ (X.spectralSequence.page r hr).d p p' = X.pageδ r p p' h ≫ cokernel.π _ :=
  (congrArg (fun t ↦ cokernel.π _ ≫ t) (X.pageComplex_d r p p' h)).trans (X.π_pageMap r p p' h)

/-- The page-turn isomorphism of the spectral sequence sends the class of an `r`-cycle represented
by `x ∈ Z_{r + 1}^p` to the class of `x` in `E_{r + 1}^p`. -/
@[stacks 012C]
lemma homologyπ_spectralSequence_iso_hom (r : ℤ) (hr : 0 ≤ r) (p : ℤ) {T : A}
    (y : T ⟶ (X.spectralSequence.page r hr).cycles p) (x : T ⟶ (X.pageCycles (r + 1) p : A))
    (x' : T ⟶ (X.pageCycles r p : A))
    (hx : x' ≫ (X.pageCycles r p).arrow = x ≫ (X.pageCycles (r + 1) p).arrow)
    (hy : y ≫ (X.spectralSequence.page r hr).iCycles p = x' ≫ cokernel.π _) :
    y ≫ (X.spectralSequence.page r hr).homologyπ p ≫ (X.spectralSequence.iso r (r + 1) p).hom =
      x ≫ cokernel.π _ := by
  show y ≫ (X.pageComplex r).homologyπ p ≫ (X.pageHomologyIso r hr p).hom ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact X.homologyπ_pageHomologyIso_hom r hr p y x x' hx hy

end SpectralSequence

section GradedPieces

/-- The differential object `(F^p K / F^q K, d)`, for `p ≤ q`. -/
noncomputable abbrev filtrationQuotient (p q : ℤ) (h : p ≤ q) : StacksDifferentialObject A where
  X := cokernel (Subobject.ofLE _ _ (X.filtration_antitone h))
  d := cokernel.desc _ (X.dp p ≫ cokernel.π _) (by
    rw [X.ofLE_comp_dp_assoc, cokernel.condition, comp_zero])
  d_sq := by
    refine coequalizer.hom_ext ?_
    rw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, ← Category.assoc, X.dp_sq,
      zero_comp, comp_zero]

/-- The differential of `F^p K / F^q K` is induced by the restriction of `d` to `F^p K`. -/
@[reassoc (attr := simp)]
lemma π_filtrationQuotient_d (p q : ℤ) (h : p ≤ q) :
    cokernel.π _ ≫ (X.filtrationQuotient p q h).d = X.dp p ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

/-- The graded piece `(gr^p K, gr^p d) = (F^p K / F^{p + 1} K, d)`. -/
noncomputable abbrev gr (p : ℤ) : StacksDifferentialObject A :=
  X.filtrationQuotient p (p + 1) (by omega)

/-- `Z_0^p = F^p K`. -/
lemma pageCycles_zero (p : ℤ) : X.pageCycles 0 p = X.F p := by
  rw [pageCycles, add_zero]
  exact inf_eq_left.2 (X.le_pullback_d p)

/-- `D_0^p ∩ Z_0^p = F^{p + 1} K`. -/
lemma pageBoundaries_zero_inf (p : ℤ) :
    X.pageBoundaries 0 p ⊓ X.pageCycles 0 p = X.F (p + 1) := by
  have h₁ : X.pageCycles (0 - 1) (p + 1) = X.F (p + 1) := by
    rw [pageCycles, show p + 1 + (0 - 1) = p by omega]
    exact inf_eq_left.2 ((X.le_pullback_d (p + 1)).trans
      ((Subobject.pullback X.d).monotone (X.filtration_antitone (by omega))))
  rw [pageBoundaries, h₁, show p - 0 + 1 = p + 1 by omega, h₁, sup_eq_left.2 (X.exists_d_le _),
    pageCycles_zero, inf_eq_left.2 (X.filtration_antitone (by omega))]

/-- `E_0^p = gr^p K`. -/
@[stacks 012C]
noncomputable def pageZeroIso (p : ℤ) : X.page 0 p ≅ (X.gr p).X :=
  Subobject.cokernelOfLEIsoOfEq _ _ (X.pageBoundaries_zero_inf p) (X.pageCycles_zero p)

/-- The isomorphism `E_0^p ≅ gr^p K` sends the class of `x ∈ Z_0^p = F^p K` to the class of `x`. -/
@[reassoc]
lemma π_pageZeroIso_hom (p : ℤ) :
    cokernel.π _ ≫ (X.pageZeroIso p).hom =
      Subobject.ofLE _ _ (X.pageCycles_zero p).le ≫ cokernel.π _ :=
  Subobject.π_cokernelOfLEIsoOfEq_hom _ _ (X.pageBoundaries_zero_inf p) (X.pageCycles_zero p)

@[reassoc]
private lemma pageδ_zero_ofLE (p : ℤ) :
    X.pageδ 0 p p (add_zero p) ≫ Subobject.ofLE _ _ (X.pageCycles_zero p).le =
      Subobject.ofLE _ _ (X.pageCycles_zero p).le ≫ X.dp p := by
  rw [← cancel_mono (X.F p).arrow]
  simp

/-- Under `E_0^p = gr^p K`, the differential `d_0^p` is `gr^p(d)`. -/
@[stacks 012C]
lemma spectralSequence_d_zero (p : ℤ) :
    (X.spectralSequence.page 0).d p p ≫ (X.pageZeroIso p).hom =
      (X.pageZeroIso p).hom ≫ (X.gr p).d := by
  have h : X.pageMap 0 p p (add_zero p) ≫ (X.pageZeroIso p).hom =
      (X.pageZeroIso p).hom ≫ (X.gr p).d := by
    rw [← cancel_epi (cokernel.π _), π_pageMap_assoc, π_pageZeroIso_hom,
      π_pageZeroIso_hom_assoc]
    exact (X.pageδ_zero_ofLE_assoc p _).trans
      ((congrArg (Subobject.ofLE _ _ (X.pageCycles_zero p).le ≫ ·)
        (X.π_filtrationQuotient_d p (p + 1) (by omega)).symm))
  exact (congrArg (fun t ↦ t ≫ (X.pageZeroIso p).hom) (X.pageComplex_d 0 p p (add_zero p))).trans h

/-- `d` carries `Z_1^p` into `F^{p + 1} K`. -/
lemma factors_pageCycles_one_arrow_d (p : ℤ) :
    (X.F (p + 1)).Factors ((X.pageCycles 1 p).arrow ≫ X.d) :=
  (le_pullback_iff _ _ _).1 inf_le_right

/-- `Z_1^p ⊆ Z_0^p`. -/
lemma pageCycles_one_le_zero (p : ℤ) : X.pageCycles 1 p ≤ X.pageCycles 0 p :=
  inf_le_inf_left _ ((Subobject.pullback X.d).monotone (X.filtration_antitone (by omega)))

/-- The image in `gr^p K` of an element of `Z_1^p` is a cycle of `gr^p(d)`. -/
lemma ofLE_π_gr_d (p : ℤ) :
    (Subobject.ofLE _ _ (X.pageCycles_le 1 p) ≫
      cokernel.π (Subobject.ofLE _ _ (X.filtration_antitone (show p ≤ p + 1 by omega)))) ≫
        (X.gr p).d = 0 := by
  rw [Category.assoc, π_filtrationQuotient_d, ← Category.assoc,
    comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _), Category.assoc, dp_comm,
    ← Category.assoc, Subobject.ofLE_arrow]
  exact X.factors_pageCycles_one_arrow_d p

/-- An element of `Z_1^p` is a cycle of `gr^p K`. -/
noncomputable def grCycle (p : ℤ) : (X.pageCycles 1 p : A) ⟶ (X.gr p).toShortComplex.cycles :=
  (X.gr p).toShortComplex.liftCycles _ (X.ofLE_π_gr_d p)

/-- The cycle of `gr^p K` attached to `x ∈ Z_1^p` is the class of `x` in `gr^p K`. -/
lemma grCycle_iCycles (p : ℤ) :
    X.grCycle p ≫ (X.gr p).toShortComplex.iCycles =
      Subobject.ofLE _ _ (X.pageCycles_le 1 p) ≫ cokernel.π _ :=
  ShortComplex.liftCycles_i _ _ _

/-- `E_0` and `gr K` as short complexes at `p`. -/
noncomputable def pageZeroScIso (p : ℤ) :
    (X.pageComplex 0).sc' p p p ≅ (X.gr p).toShortComplex :=
  ShortComplex.isoMk (X.pageZeroIso p) (X.pageZeroIso p) (X.pageZeroIso p)
    (X.spectralSequence_d_zero p).symm (X.spectralSequence_d_zero p).symm

/-- `E_1^p = H(gr^p K, gr^p(d))`. -/
@[stacks 012C]
noncomputable def pageOneIso (p : ℤ) : X.page 1 p ≅ (X.gr p).homology :=
  (X.pageHomologyIso 0 le_rfl p).symm ≪≫
    (X.pageComplex 0).homologyIsoSc' p p p ((ComplexShape.up' 0).prev_eq' (add_zero p))
      ((ComplexShape.up' 0).next_eq' (add_zero p)) ≪≫
    ShortComplex.homologyMapIso (X.pageZeroScIso p)

/-- The isomorphism `E_1^p = H(gr^p K)` sends the class of `x ∈ Z_1^p` to the class of the cycle
`x` of `gr^p K`. -/
@[reassoc]
lemma π_pageOneIso_hom (p : ℤ) :
    cokernel.π _ ≫ (X.pageOneIso p).hom =
      X.grCycle p ≫ (X.gr p).toShortComplex.homologyπ := by
  have hk : (ComplexShape.up' (0 : ℤ)).next p = p := (ComplexShape.up' 0).next_eq' (add_zero p)
  have hi : (ComplexShape.up' (0 : ℤ)).prev p = p := (ComplexShape.up' 0).prev_eq' (add_zero p)
  have hy : (Subobject.ofLE _ _ (X.pageCycles_one_le_zero p) ≫ cokernel.π _) ≫
      (X.pageComplex 0).d p p = 0 := by
    rw [X.pageComplex_d 0 p p (add_zero p), Category.assoc, π_pageMap, ← Category.assoc,
      comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _), X.pageBoundaries_zero_inf p,
      Category.assoc, pageδ_arrow, ← Category.assoc, Subobject.ofLE_arrow]
    exact X.factors_pageCycles_one_arrow_d p
  let y := (X.pageComplex 0).liftCycles _ p hk hy
  have h₁ : y ≫ (X.pageComplex 0).homologyπ p ≫ (X.pageHomologyIso 0 le_rfl p).hom =
      𝟙 _ ≫ cokernel.π _ :=
    X.homologyπ_pageHomologyIso_hom 0 le_rfl p y (𝟙 _) _ (by simp)
      (HomologicalComplex.liftCycles_i _ _ _ _ _)
  have h₂ : cokernel.π _ ≫ (X.pageHomologyIso 0 le_rfl p).inv =
      y ≫ (X.pageComplex 0).homologyπ p := by
    rw [← cancel_mono (X.pageHomologyIso 0 le_rfl p).hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.assoc, h₁, Category.id_comp]
  let c := ((X.pageComplex 0).cyclesIsoSc' p p p hi hk).hom
  let m := ShortComplex.cyclesMap (X.pageZeroScIso p).hom
  have f₁ : m ≫ (X.gr p).toShortComplex.iCycles =
      ((X.pageComplex 0).sc' p p p).iCycles ≫ (X.pageZeroScIso p).hom.τ₂ :=
    ShortComplex.cyclesMap_i _
  have f₂ : c ≫ ((X.pageComplex 0).sc' p p p).iCycles = (X.pageComplex 0).iCycles p :=
    HomologicalComplex.cyclesIsoSc'_hom_iCycles _ _ _ _ _ _
  have f₃ : y ≫ (X.pageComplex 0).iCycles p =
      Subobject.ofLE _ _ (X.pageCycles_one_le_zero p) ≫ cokernel.π _ :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  have f₄ := X.π_pageZeroIso_hom p
  have e : (y ≫ c ≫ m) ≫ (X.gr p).toShortComplex.iCycles =
      Subobject.ofLE _ _ (X.pageCycles_le 1 p) ≫ cokernel.π _ :=
    calc ((y ≫ c ≫ m) ≫ (X.gr p).toShortComplex.iCycles : _ ⟶ (X.gr p).X)
        = (y ≫ c ≫ (m ≫ (X.gr p).toShortComplex.iCycles) : _ ⟶ (X.gr p).X) :=
          (Category.assoc _ _ _).trans (congrArg (y ≫ ·) (Category.assoc _ _ _))
      _ = (y ≫ c ≫ ((X.pageComplex 0).sc' p p p).iCycles ≫ (X.pageZeroScIso p).hom.τ₂ :
          _ ⟶ (X.gr p).X) := congrArg (fun t ↦ y ≫ c ≫ t) f₁
      _ = (y ≫ (X.pageComplex 0).iCycles p ≫ (X.pageZeroScIso p).hom.τ₂ : _ ⟶ (X.gr p).X) :=
          congrArg (fun t ↦ y ≫ t) ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (X.pageZeroScIso p).hom.τ₂) f₂))
      _ = ((Subobject.ofLE _ _ (X.pageCycles_one_le_zero p) ≫ cokernel.π _) ≫
          (X.pageZeroIso p).hom : _ ⟶ (X.gr p).X) :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (X.pageZeroIso p).hom) f₃)
      _ = (Subobject.ofLE _ _ (X.pageCycles_one_le_zero p) ≫ Subobject.ofLE _ _
          (X.pageCycles_zero p).le ≫ cokernel.π _ : _ ⟶ (X.gr p).X) :=
          (Category.assoc _ _ _).trans
            (congrArg (Subobject.ofLE _ _ (X.pageCycles_one_le_zero p) ≫ ·) f₄)
      _ = _ := by rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  have h₃ : y ≫ c ≫ m = X.grCycle p :=
    (cancel_mono (X.gr p).toShortComplex.iCycles).1 (e.trans (X.grCycle_iCycles p).symm)
  have g₁ : (X.pageComplex 0).homologyπ p ≫
      ((X.pageComplex 0).homologyIsoSc' p p p hi hk).hom =
      c ≫ ((X.pageComplex 0).sc' p p p).homologyπ :=
    HomologicalComplex.π_homologyIsoSc'_hom _ _ _ _ _ _
  have g₂ : ((X.pageComplex 0).sc' p p p).homologyπ ≫
      ShortComplex.homologyMap (X.pageZeroScIso p).hom =
      m ≫ (X.gr p).toShortComplex.homologyπ := ShortComplex.homologyπ_naturality _
  let S := ((X.pageComplex 0).homologyIsoSc' p p p hi hk).hom
  let H := ShortComplex.homologyMap (X.pageZeroScIso p).hom
  show cokernel.π _ ≫ (X.pageHomologyIso 0 le_rfl p).inv ≫ S ≫ H = _
  calc (cokernel.π _ ≫ (X.pageHomologyIso 0 le_rfl p).inv ≫ S ≫ H : _ ⟶ (X.gr p).homology)
      = ((cokernel.π _ ≫ (X.pageHomologyIso 0 le_rfl p).inv) ≫ S ≫ H :
          _ ⟶ (X.gr p).homology) := (Category.assoc _ _ _).symm
    _ = ((y ≫ (X.pageComplex 0).homologyπ p) ≫ S ≫ H : _ ⟶ (X.gr p).homology) :=
          congrArg (· ≫ S ≫ H) h₂
    _ = (y ≫ ((X.pageComplex 0).homologyπ p ≫ S) ≫ H : _ ⟶ (X.gr p).homology) := by
          simp only [Category.assoc]
    _ = (y ≫ (c ≫ ((X.pageComplex 0).sc' p p p).homologyπ) ≫ H : _ ⟶ (X.gr p).homology) :=
          congrArg (fun t ↦ y ≫ t ≫ H) g₁
    _ = (y ≫ c ≫ (((X.pageComplex 0).sc' p p p).homologyπ ≫ H) :
          _ ⟶ (X.gr p).homology) := by simp only [Category.assoc]
    _ = (y ≫ c ≫ (m ≫ (X.gr p).toShortComplex.homologyπ) : _ ⟶ (X.gr p).homology) :=
          congrArg (fun t ↦ y ≫ c ≫ t) g₂
    _ = ((y ≫ c ≫ m) ≫ (X.gr p).toShortComplex.homologyπ : _ ⟶ (X.gr p).homology) := by
          simp only [Category.assoc]
    _ = _ := congrArg (· ≫ (X.gr p).toShortComplex.homologyπ) h₃

end GradedPieces

section FirstDifferential

/-- The short exact sequence of differential objects
`0 → gr^{p + 1} K → F^p K / F^{p + 2} K → gr^p K → 0`. -/
noncomputable def grShortExactSequence (p : ℤ) : StacksDifferentialObject.ShortExactSequence A where
  A := X.gr (p + 1)
  B := X.filtrationQuotient p (p + 1 + 1) (by omega)
  C := X.gr p
  f :=
    { f := Subobject.quotientMap (X.filtration_antitone (show p + 1 ≤ p + 1 + 1 by omega))
        (X.filtration_antitone (show p ≤ p + 1 by omega))
      comm := by
        refine coequalizer.hom_ext ?_
        dsimp
        rw [Subobject.π_quotientMap_assoc, π_filtrationQuotient_d, π_filtrationQuotient_d_assoc,
          Subobject.π_quotientMap, X.ofLE_comp_dp_assoc]
        all_goals omega }
  g :=
    { f := Subobject.enlargeDen (X.filtration_antitone (show p + 1 ≤ p + 1 + 1 by omega))
        (X.filtration_antitone (show p ≤ p + 1 by omega))
      comm := by
        refine coequalizer.hom_ext ?_
        dsimp
        rw [Subobject.π_enlargeDen_assoc, π_filtrationQuotient_d, π_filtrationQuotient_d_assoc,
          Subobject.π_enlargeDen]
        all_goals omega }
  zero := by
    refine coequalizer.hom_ext ?_
    dsimp
    rw [Subobject.π_quotientMap_assoc, Subobject.π_enlargeDen, cokernel.condition, comp_zero]
  shortExact := by
    refine ShortComplex.ShortExact.mk' ?_ (by dsimp; infer_instance) (by dsimp; infer_instance)
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x₂ hx₂
    obtain ⟨T', w, hw, t, fac⟩ := surjective_up_to_refinements_of_epi (cokernel.π _) x₂
    have ht : t ≫ cokernel.π (Subobject.ofLE (X.F (p + 1)) (X.F p)
        (X.filtration_antitone (by omega))) = 0 := by
      have := congrArg (· ≫ Subobject.enlargeDen
        (X.filtration_antitone (show p + 1 ≤ p + 1 + 1 by omega))
        (X.filtration_antitone (show p ≤ p + 1 by omega))) fac
      dsimp at this hx₂
      rw [Category.assoc, hx₂, comp_zero, Category.assoc, Subobject.π_enlargeDen] at this
      exact this.symm
    rw [comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _)] at ht
    refine ⟨T', w, hw, (X.F (p + 1)).factorThru _ ht ≫ cokernel.π _, ?_⟩
    dsimp
    rw [fac, Category.assoc, Subobject.π_quotientMap, ← Category.assoc]
    congr 1
    rw [← cancel_mono (X.F p).arrow]
    simp

/-- Under the identifications `E_1^p = H(gr^p K)` and `E_1^{p + 1} = H(gr^{p + 1} K)`, the
differential `d_1^p` of the spectral sequence is the boundary map in homology of the short exact
sequence `0 → gr^{p + 1} K → F^p K / F^{p + 2} K → gr^p K → 0`. -/
@[stacks 012D]
theorem spectralSequence_d_one (p : ℤ) :
    (X.spectralSequence.page 1).d p (p + 1) ≫ (X.pageOneIso (p + 1)).hom =
      (X.pageOneIso p).hom ≫ (X.grShortExactSequence p).δ := by
  show (X.pageComplex 1).d p (p + 1) ≫ _ = _
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _
    (inf_le_right : X.pageBoundaries 1 p ⊓ X.pageCycles 1 p ≤ _)))).1
  refine (congrArg (fun t ↦ cokernel.π _ ≫ t ≫ (X.pageOneIso (p + 1)).hom)
    (X.pageComplex_d 1 p (p + 1) rfl)).trans ?_
  refine (X.π_pageMap_assoc 1 p (p + 1) rfl _).trans ?_
  refine (congrArg (X.pageδ 1 p (p + 1) rfl ≫ ·) (X.π_pageOneIso_hom (p + 1))).trans ?_
  refine Eq.trans ?_ (X.π_pageOneIso_hom_assoc p (X.grShortExactSequence p).δ).symm
  have hS := (X.grShortExactSequence p).toComplexes_shortExact
  have hx₂ : (Subobject.ofLE _ _ (X.pageCycles_le 1 p) ≫ cokernel.π _) ≫
      Subobject.enlargeDen (X.filtration_antitone (show p + 1 ≤ p + 1 + 1 by omega))
        (X.filtration_antitone (show p ≤ p + 1 by omega)) =
      Subobject.ofLE _ _ (X.pageCycles_le 1 p) ≫ cokernel.π _ := by
    rw [Category.assoc, Subobject.π_enlargeDen]
  have hx₁ : (X.pageδ 1 p (p + 1) rfl ≫
      Subobject.ofLE _ _ (X.pageCycles_le 1 (p + 1)) ≫ cokernel.π _) ≫
      Subobject.quotientMap (X.filtration_antitone (show p + 1 ≤ p + 1 + 1 by omega))
        (X.filtration_antitone (show p ≤ p + 1 by omega)) =
      (Subobject.ofLE _ _ (X.pageCycles_le 1 p) ≫ cokernel.π _) ≫
        (X.filtrationQuotient p (p + 1 + 1) (by omega)).d := by
    rw [Category.assoc, Category.assoc, Subobject.π_quotientMap, Category.assoc,
      π_filtrationQuotient_d, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono (X.F p).arrow]
    simp
  refine Eq.trans ?_ (hS.δ_eq () () rfl _ (X.ofLE_π_gr_d p) _ hx₂ _ hx₁ () rfl).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (ShortComplex.comp_liftCycles _ _ _ _))

end FirstDifferential

section Convergence

private lemma imageSubobject_epi_comp {P Q R : A} (e : P ⟶ Q) [Epi e] (f : Q ⟶ R) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  rw [Subobject.imageSubobject_comp_eq_exists, Subobject.imageSubobject_eq_top_of_epi,
    Subobject.exists_obj_top]

/-- The cycles of `(K, d)` lying in `F^p K`, that is `Ker(d) ∩ F^p K`, as a subobject of the cycles
`Ker(d)`. -/
noncomputable abbrev cyclesInStep (p : ℤ) : Subobject X.shortComplex.cycles :=
  (Subobject.pullback X.shortComplex.iCycles).obj (X.F p)

/-- The induced filtration `F^p H(K) = Im(H(F^p K) ⟶ H(K))` is the image of the cycles of `K` lying
in `F^p K`. -/
lemma inducedFiltration_eq_imageSubobject (p : ℤ) :
    X.inducedFiltration p =
      imageSubobject ((X.cyclesInStep p).arrow ≫ X.shortComplex.homologyπ) := by
  let S := X.shortComplex
  let φ := X.shortComplexFHom p
  have e₁ : X.inducedFiltration p = imageSubobject (ShortComplex.cyclesMap φ ≫ S.homologyπ) := by
    show imageSubobject (ShortComplex.homologyMap φ) = _
    rw [← imageSubobject_epi_comp (X.shortComplexF p).homologyπ,
      ShortComplex.homologyπ_naturality]
  have ha : (X.cyclesInStep p).Factors (ShortComplex.cyclesMap φ) := by
    rw [pullback_factors_iff, ShortComplex.cyclesMap_i]
    exact Subobject.factors_comp_arrow _
  have hw : (X.F p).Factors ((X.cyclesInStep p).arrow ≫ S.iCycles) :=
    (pullback_factors_iff _ _ _).1 (Subobject.factors_self _)
  have hw' : (X.F p).factorThru _ hw ≫ X.dp p = 0 := by
    rw [← cancel_mono (X.F p).arrow, Category.assoc, dp_comm, Subobject.factorThru_arrow_assoc,
      Category.assoc]
    exact (congrArg ((X.cyclesInStep p).arrow ≫ ·) S.iCycles_g).trans (by simp)
  let b := (X.shortComplexF p).liftCycles _ hw'
  have hb : b ≫ ShortComplex.cyclesMap φ = (X.cyclesInStep p).arrow := by
    rw [← cancel_mono S.iCycles, Category.assoc, ShortComplex.cyclesMap_i,
      ShortComplex.liftCycles_i_assoc]
    exact Subobject.factorThru_arrow _ _ _
  rw [e₁]
  refine le_antisymm ?_ ?_
  · rw [← (X.cyclesInStep p).factorThru_arrow _ ha, Category.assoc]
    exact imageSubobject_comp_le _ _
  · rw [← hb, Category.assoc]
    exact imageSubobject_comp_le _ _

/-- The numerator `(Ker(d) ∩ F^p K) + F^{p + 1} K` of the right hand side of (012G). -/
noncomputable abbrev stableCyclesBound (p : ℤ) : Subobject X.X :=
  kernelSubobject X.d ⊓ X.F p ⊔ X.F (p + 1)

/-- The numerator `(Im(d) ∩ F^p K) + F^{p + 1} K` of the right hand side of (012H). -/
noncomputable abbrev stableBoundariesBound (p : ℤ) : Subobject X.X :=
  imageSubobject X.d ⊓ X.F p ⊔ X.F (p + 1)

/-- `(Im(d) ∩ F^p K) + F^{p + 1} K ⊆ (Ker(d) ∩ F^p K) + F^{p + 1} K`. -/
lemma stableBoundariesBound_le (p : ℤ) : X.stableBoundariesBound p ≤ X.stableCyclesBound p :=
  sup_le_sup_right (inf_le_inf_right _ (image_le_kernel _ _ X.d_squared)) _

/-- The numerators `Z_r^p + F^{p + 1} K` of the cycles of the spectral sequence, `r ≥ 0`. -/
noncomputable abbrev cyclesNumerator (p : ℤ) (r : ℕ) : Subobject X.X :=
  X.pageCycles r p ⊔ X.F (p + 1)

/-- The numerators `(F^p K ∩ d(F^{p - r} K)) + F^{p + 1} K` of the boundaries `B_{r + 1}^p` of the
spectral sequence, `r ≥ 0`. -/
noncomputable abbrev boundariesNumerator (p : ℤ) (r : ℕ) : Subobject X.X :=
  X.F p ⊓ imageSubobject ((X.F (p - r)).arrow ≫ X.d) ⊔ X.F (p + 1)

/-- The spectral sequence of `(K, F, d)` *weakly converges* to `H(K)` (Stacks 012I): for every `p`
the limit term `E_∞^p = Z_∞^p / B_∞^p` exists, i.e. the numerators of the cycles have an
intersection `Z_∞^p` and those of the boundaries a union `B_∞^p`, and `gr^p H(K) = E_∞^p` via the
comparison of Stacks 012F: there is an isomorphism `Z_∞^p / B_∞^p ≅ gr^p H(K)` compatible with the
canonical maps to both from `Ker(d) ∩ F^p K`. -/
def WeaklyConverges : Prop :=
  ∀ p : ℤ, ∃ Zinf Binf : Subobject X.X,
    IsGLB (Set.range (X.cyclesNumerator p)) Zinf ∧
    IsLUB (Set.range (X.boundariesNumerator p)) Binf ∧
    ∃ (h : Binf ≤ Zinf) (a : (X.cyclesInStep p : A) ⟶ (Zinf : A))
      (b : (X.cyclesInStep p : A) ⟶ (X.inducedFiltration p : A))
      (e : cokernel (Subobject.ofLE _ _ h) ≅ X.grH p),
      a ≫ Zinf.arrow = (X.cyclesInStep p).arrow ≫ X.shortComplex.iCycles ∧
      b ≫ (X.inducedFiltration p).arrow =
        (X.cyclesInStep p).arrow ≫ X.shortComplex.homologyπ ∧
      a ≫ cokernel.π _ ≫ e.hom = b ≫ cokernel.π (X.inducedFiltrationInclusionSucc p)

/-- The spectral sequence of `(K, F, d)` *abuts* to `H(K)` (Stacks 012I): it weakly converges and
the induced filtration on `H(K)` is separated, `⋂_p F^p H(K) = 0`, and exhaustive,
`⋃_p F^p H(K) = H(K)`. -/
def Abuts : Prop :=
  X.WeaklyConverges ∧ IsGLB (Set.range X.inducedFiltration) ⊥ ∧
    IsLUB (Set.range X.inducedFiltration) ⊤

/-- The inclusion of the cycles `Ker(d) ⟶ K` composed with `d` is zero. -/
lemma iCycles_d : X.shortComplex.iCycles ≫ X.d = 0 :=
  X.shortComplex.iCycles_g

private lemma factors_stableCyclesBound (p : ℤ) :
    (X.stableCyclesBound p).Factors ((X.cyclesInStep p).arrow ≫ X.shortComplex.iCycles) := by
  refine Subobject.factors_of_le _ le_sup_left ((Subobject.inf_factors _).2 ⟨?_, ?_⟩)
  · exact kernelSubobject_factors _ _ (by rw [Category.assoc, X.iCycles_d, comp_zero])
  · exact (pullback_factors_iff _ _ _).1 (Subobject.factors_self _)

private lemma factors_inducedFiltration (p : ℤ) :
    (X.inducedFiltration p).Factors ((X.cyclesInStep p).arrow ≫ X.shortComplex.homologyπ) := by
  rw [inducedFiltration_eq_imageSubobject]
  exact (Subobject.factors_iff _ _).2 ⟨_, imageSubobject_arrow_comp _⟩

private lemma stableBounds_compare (p : ℤ) {Zinf Binf : Subobject X.X}
    (hZ : IsGLB (Set.range (X.cyclesNumerator p)) Zinf)
    (hB : IsLUB (Set.range (X.boundariesNumerator p)) Binf) :
    Binf ≤ X.stableBoundariesBound p ∧ X.stableBoundariesBound p ≤ X.stableCyclesBound p ∧
      X.stableCyclesBound p ≤ Zinf ∧
      ∃ e : cokernel (Subobject.ofLE _ _ (X.stableBoundariesBound_le p)) ≅ X.grH p,
        (X.stableCyclesBound p).factorThru _ (X.factors_stableCyclesBound p) ≫
          cokernel.π _ ≫ e.hom =
        (X.inducedFiltration p).factorThru _ (X.factors_inducedFiltration p) ≫
          cokernel.π (X.inducedFiltrationInclusionSucc p) :=
  CategoryTheory.gr_homology_isSubquotient_stablePage X.d_squared (X.filtration_antitone (by omega))
    hZ hB rfl rfl _ (Subobject.ofLE_arrow _) rfl rfl
    (X.inducedFiltration_eq_imageSubobject p) (X.inducedFiltration_eq_imageSubobject (p + 1))
    _ (Subobject.ofLE_arrow _) _ (Subobject.factorThru_arrow _ _ _) _
    (Subobject.factorThru_arrow _ _ _)

private lemma le_stableCyclesBound_of_epi (p : ℤ) {Zinf Binf : Subobject X.X} (hBZ : Binf ≤ Zinf)
    (h₁ : Binf ≤ X.stableBoundariesBound p) (a : (X.cyclesInStep p : A) ⟶ (Zinf : A))
    (ha : a ≫ Zinf.arrow = (X.cyclesInStep p).arrow ≫ X.shortComplex.iCycles)
    [Epi (a ≫ cokernel.π (Subobject.ofLE _ _ hBZ))] : Zinf ≤ X.stableCyclesBound p := by
  obtain ⟨T, w, hw, s, fac⟩ := surjective_up_to_refinements_of_epi
    (a ≫ cokernel.π (Subobject.ofLE _ _ hBZ)) (cokernel.π (Subobject.ofLE _ _ hBZ))
  have hzero : (w - s ≫ a) ≫ cokernel.π (Subobject.ofLE _ _ hBZ) = 0 := by
    rw [Preadditive.sub_comp, fac, Category.assoc, sub_self]
  rw [comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _)] at hzero
  refine Subobject.le_of_factors (Subobject.factors_of_epi_comp w _ ?_)
  rw [show w ≫ Zinf.arrow = (w - s ≫ a) ≫ Zinf.arrow + s ≫ a ≫ Zinf.arrow by
    rw [Preadditive.sub_comp, Category.assoc, sub_add_cancel]]
  refine Subobject.factors_add _ _ (Subobject.factors_of_le _ (h₁.trans
    (X.stableBoundariesBound_le p)) hzero) ?_
  rw [ha]
  exact Subobject.factors_of_factors_right _ (X.factors_stableCyclesBound p)

private lemma stableBoundariesBound_le_of_iso (p : ℤ) {Zinf Binf : Subobject X.X}
    (hB : IsLUB (Set.range (X.boundariesNumerator p)) Binf) (hBZ : Binf ≤ Zinf)
    (a : (X.cyclesInStep p : A) ⟶ (Zinf : A)) (e : cokernel (Subobject.ofLE _ _ hBZ) ≅ X.grH p)
    (ha : a ≫ Zinf.arrow = (X.cyclesInStep p).arrow ≫ X.shortComplex.iCycles)
    (hab : a ≫ cokernel.π (Subobject.ofLE _ _ hBZ) ≫ e.hom =
      (X.inducedFiltration p).factorThru _ (X.factors_inducedFiltration p) ≫
        cokernel.π (X.inducedFiltrationInclusionSucc p))
    (e' : cokernel (Subobject.ofLE _ _ (X.stableBoundariesBound_le p)) ≅ X.grH p)
    (he' : (X.stableCyclesBound p).factorThru _ (X.factors_stableCyclesBound p) ≫
        cokernel.π _ ≫ e'.hom =
      (X.inducedFiltration p).factorThru _ (X.factors_inducedFiltration p) ≫
        cokernel.π (X.inducedFiltrationInclusionSucc p)) :
    X.stableBoundariesBound p ≤ Binf := by
  refine sup_le ?_ (le_sup_right.trans (hB.1 ⟨0, rfl⟩))
  let I := imageSubobject X.d ⊓ X.F p
  have hI : I.arrow ≫ X.d = 0 := Subobject.arrow_comp_eq_zero_of_le_kernelSubobject
    (inf_le_left.trans (image_le_kernel _ _ X.d_squared))
  have hc : (X.cyclesInStep p).Factors (X.shortComplex.liftCycles I.arrow hI) := by
    rw [pullback_factors_iff, ShortComplex.liftCycles_i]
    exact Subobject.factors_of_le _ inf_le_right (Subobject.factors_self _)
  let g := (X.cyclesInStep p).factorThru _ hc
  have hg : g ≫ (X.cyclesInStep p).arrow ≫ X.shortComplex.iCycles = I.arrow := by
    rw [Subobject.factorThru_arrow_assoc, ShortComplex.liftCycles_i]
  have h₀ : g ≫ (X.stableCyclesBound p).factorThru _ (X.factors_stableCyclesBound p) ≫
      cokernel.π (Subobject.ofLE _ _ (X.stableBoundariesBound_le p)) = 0 := by
    rw [← Category.assoc, comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _),
      Category.assoc, Subobject.factorThru_arrow, hg]
    exact Subobject.factors_of_le _ le_sup_left (Subobject.factors_self _)
  have h₀' : g ≫ a ≫ cokernel.π (Subobject.ofLE _ _ hBZ) = 0 := by
    rw [← cancel_mono e.hom, zero_comp, Category.assoc, Category.assoc, hab, ← he',
      reassoc_of% h₀, zero_comp]
  rw [← Category.assoc, comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _),
    Category.assoc, ha, hg] at h₀'
  exact Subobject.le_of_factors h₀'

/-- The spectral sequence of a filtered differential object weakly converges to `H(K)` if and only
if equality holds in (012G) and (012H) for every `p`: the intersection of the numerators of the
cycles is `(Ker(d) ∩ F^p K) + F^{p + 1} K` and the union of the numerators of the boundaries is
`(Im(d) ∩ F^p K) + F^{p + 1} K`. -/
@[stacks 012J "(1)"]
theorem weaklyConverges_iff : X.WeaklyConverges ↔ ∀ p : ℤ,
    IsGLB (Set.range (X.cyclesNumerator p)) (X.stableCyclesBound p) ∧
    IsLUB (Set.range (X.boundariesNumerator p)) (X.stableBoundariesBound p) := by
  refine ⟨fun h p ↦ ?_, fun h p ↦ ?_⟩
  · obtain ⟨Zinf, Binf, hZ, hB, hBZ, a, b, e, ha, hb, hab⟩ := h p
    obtain ⟨h₁, -, h₃, e', he'⟩ := X.stableBounds_compare p hZ hB
    have : Epi b := Subobject.epi_of_comp_arrow_eq (X.inducedFiltration_eq_imageSubobject p) b hb
    obtain rfl : b = (X.inducedFiltration p).factorThru _ (X.factors_inducedFiltration p) := by
      rw [← cancel_mono (X.inducedFiltration p).arrow, hb, Subobject.factorThru_arrow]
    have : Epi (a ≫ cokernel.π (Subobject.ofLE _ _ hBZ)) := by
      have : Epi ((a ≫ cokernel.π (Subobject.ofLE _ _ hBZ)) ≫ e.hom) := by
        rw [Category.assoc, hab]
        exact epi_comp _ (cokernel.π (X.inducedFiltrationInclusionSucc p))
      rw [show a ≫ cokernel.π (Subobject.ofLE _ _ hBZ) =
        ((a ≫ cokernel.π (Subobject.ofLE _ _ hBZ)) ≫ e.hom) ≫ e.inv by simp]
      infer_instance
    have hZ' := le_antisymm (X.le_stableCyclesBound_of_epi p hBZ h₁ a ha) h₃
    have hB' := le_antisymm h₁ (X.stableBoundariesBound_le_of_iso p hB hBZ a e ha hab e' he')
    exact ⟨hZ' ▸ hZ, hB' ▸ hB⟩
  · obtain ⟨-, -, -, e, he⟩ := X.stableBounds_compare p (h p).1 (h p).2
    exact ⟨_, _, (h p).1, (h p).2, X.stableBoundariesBound_le p, _, _, e,
      Subobject.factorThru_arrow _ _ _, Subobject.factorThru_arrow _ _ _, he⟩

/-- The correspondence `T ↦ Z(T)`, the cycles of `K` whose class lies in `T`, between subobjects of
`H(K)` and subobjects of `K` lying between `Im(d)` and `Ker(d)`. -/
private noncomputable def homologyCorr (T : Subobject X.homology) : Subobject X.X :=
  (Subobject.exists X.shortComplex.iCycles).obj
    ((Subobject.pullback X.shortComplex.homologyπ).obj T)

private lemma homologyCorr_le_homologyCorr_iff (T T' : Subobject X.homology) :
    X.homologyCorr T ≤ X.homologyCorr T' ↔ T ≤ T' := by
  rw [homologyCorr, homologyCorr, Subobject.exists_le_exists_iff_of_mono,
    Abelian.Subobject.pullback_le_pullback_iff_of_epi]

private lemma kernelSubobject_homologyπ :
    kernelSubobject X.shortComplex.homologyπ = imageSubobject X.shortComplex.toCycles := by
  refine le_antisymm (Subobject.le_of_factors ?_)
    (image_le_kernel _ _ X.shortComplex.toCycles_comp_homologyπ)
  obtain ⟨T, z, hz, ρ, fac⟩ :=
    (Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
      X.shortComplex.homologyIsCokernel _).1 (kernelSubobject_arrow_comp X.shortComplex.homologyπ)
  refine Subobject.factors_of_epi_comp z _ ?_
  rw [fac]
  exact imageSubobject_factors_comp_self _ _

private lemma exists_iCycles_kernelSubobject_homologyπ :
    (Subobject.exists X.shortComplex.iCycles).obj (kernelSubobject X.shortComplex.homologyπ) =
      imageSubobject X.d := by
  rw [kernelSubobject_homologyπ, ← Subobject.imageSubobject_comp_eq_exists,
    X.shortComplex.toCycles_i]

private lemma mk_iCycles : Subobject.mk X.shortComplex.iCycles = kernelSubobject X.d :=
  Subobject.mk_eq_mk_of_comm _ _ X.shortComplex.cyclesIsoKernel (by simp)

private lemma homologyCorr_bot : X.homologyCorr ⊥ = imageSubobject X.d := by
  rw [homologyCorr, Subobject.pullback_bot, exists_iCycles_kernelSubobject_homologyπ]

private lemma homologyCorr_top : X.homologyCorr ⊤ = kernelSubobject X.d := by
  rw [homologyCorr, Subobject.pullback_top, Subobject.exists_obj_top, imageSubobject_mono,
    mk_iCycles]

private lemma homologyCorr_inducedFiltration (p : ℤ) :
    X.homologyCorr (X.inducedFiltration p) =
      kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d := by
  rw [homologyCorr, inducedFiltration_eq_imageSubobject, ← Subobject.exists_eq_imageSubobject,
    Abelian.Subobject.pullback_exists_eq_sup,
    (Subobject.existsPullbackAdj X.shortComplex.iCycles).gc.l_sup,
    Subobject.exists_pullback_eq_inf_of_mono, mk_iCycles,
    exists_iCycles_kernelSubobject_homologyπ, inf_comm]

private lemma exists_homologyCorr_eq {L : Subobject X.X} (h₁ : imageSubobject X.d ≤ L)
    (h₂ : L ≤ kernelSubobject X.d) : ∃ T, X.homologyCorr T = L := by
  have hker : kernelSubobject X.shortComplex.homologyπ ≤
      (Subobject.pullback X.shortComplex.iCycles).obj L := by
    rw [← Subobject.pullback_exists_eq_self_of_mono X.shortComplex.iCycles
      (kernelSubobject X.shortComplex.homologyπ), exists_iCycles_kernelSubobject_homologyπ]
    exact (Subobject.pullback _).monotone h₁
  refine ⟨(Subobject.exists X.shortComplex.homologyπ).obj
    ((Subobject.pullback X.shortComplex.iCycles).obj L), ?_⟩
  rw [homologyCorr, Abelian.Subobject.pullback_exists_eq_sup, sup_eq_left.2 hker,
    Subobject.exists_pullback_eq_inf_of_mono, mk_iCycles, inf_eq_left.2 h₂]

private lemma image_homologyCorr_range_inducedFiltration :
    X.homologyCorr '' Set.range X.inducedFiltration =
      Set.range fun p => kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext X.homologyCorr_inducedFiltration)

/-- The induced filtration on `H(K)` is separated if and only if
`⋂_p ((Ker(d) ∩ F^p K) + Im(d)) = Im(d)`. -/
lemma isGLB_inducedFiltration_iff :
    IsGLB (Set.range X.inducedFiltration) ⊥ ↔
      IsGLB (Set.range fun p => kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d)
        (imageSubobject X.d) := by
  constructor
  · intro h
    refine ⟨Set.forall_mem_range.2 fun _ ↦ le_sup_right, fun L hL ↦ ?_⟩
    have hL' : ∀ p, L ⊔ imageSubobject X.d ≤ kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d :=
      fun p ↦ sup_le (hL ⟨p, rfl⟩) le_sup_right
    obtain ⟨T, hT⟩ := X.exists_homologyCorr_eq (le_sup_right : _ ≤ L ⊔ imageSubobject X.d)
      ((hL' 0).trans (sup_le inf_le_left (image_le_kernel _ _ X.d_squared)))
    have hbot : T = ⊥ := le_bot_iff.1 (h.2 (Set.forall_mem_range.2 fun p ↦ by
      rw [← homologyCorr_le_homologyCorr_iff, hT, homologyCorr_inducedFiltration]
      exact hL' p))
    rw [hbot, homologyCorr_bot] at hT
    exact le_sup_left.trans hT.symm.le
  · exact fun h ↦ IsGLB.of_image (X.homologyCorr_le_homologyCorr_iff _ _) (by
      rwa [image_homologyCorr_range_inducedFiltration, homologyCorr_bot])

/-- The induced filtration on `H(K)` is exhaustive if and only if
`⋃_p ((Ker(d) ∩ F^p K) + Im(d)) = Ker(d)`. -/
lemma isLUB_inducedFiltration_iff :
    IsLUB (Set.range X.inducedFiltration) ⊤ ↔
      IsLUB (Set.range fun p => kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d)
        (kernelSubobject X.d) := by
  constructor
  · intro h
    refine ⟨Set.forall_mem_range.2 fun _ ↦ sup_le inf_le_left (image_le_kernel _ _ X.d_squared),
      fun U hU ↦ ?_⟩
    have hU' : ∀ p, kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d ≤
        U ⊓ kernelSubobject X.d :=
      fun p ↦ le_inf (hU ⟨p, rfl⟩) (sup_le inf_le_left (image_le_kernel _ _ X.d_squared))
    obtain ⟨T, hT⟩ := X.exists_homologyCorr_eq (le_sup_right.trans (hU' 0))
      (inf_le_right : U ⊓ kernelSubobject X.d ≤ _)
    have htop : T = ⊤ := top_le_iff.1 (h.2 (Set.forall_mem_range.2 fun p ↦ by
      rw [← homologyCorr_le_homologyCorr_iff, hT, homologyCorr_inducedFiltration]
      exact hU' p))
    rw [htop, homologyCorr_top] at hT
    exact hT.le.trans inf_le_left
  · exact fun h ↦ IsLUB.of_image (X.homologyCorr_le_homologyCorr_iff _ _) (by
      rwa [image_homologyCorr_range_inducedFiltration, homologyCorr_top])

/-- The spectral sequence of a filtered differential object abuts to `H(K)` if and only if it
weakly converges to `H(K)`, `⋂_p ((Ker(d) ∩ F^p K) + Im(d)) = Im(d)` and
`⋃_p ((Ker(d) ∩ F^p K) + Im(d)) = Ker(d)`. -/
@[stacks 012J "(2)"]
theorem abuts_iff : X.Abuts ↔ X.WeaklyConverges ∧
    IsGLB (Set.range fun p => kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d)
      (imageSubobject X.d) ∧
    IsLUB (Set.range fun p => kernelSubobject X.d ⊓ X.F p ⊔ imageSubobject X.d)
      (kernelSubobject X.d) := by
  rw [Abuts, isGLB_inducedFiltration_iff, isLUB_inducedFiltration_iff]

end Convergence

end FilteredDifferentialObject
