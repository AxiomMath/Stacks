module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Order.SuccPred.Int
public import StacksFrontier.Algebra.Homology.EulerCharacteristicHomology
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo

/-!
# The Euler characteristic of a convergent spectral sequence of vector spaces

Let `E` be a cohomological spectral sequence of vector spaces over a field `k` which abuts to a
graded vector space `H`, in the sense of `CategoryTheory.SpectralSequence.AbutsTo`. Suppose that
on some page `E_r` every term is finite-dimensional and only finitely many terms are nonzero.
Then every `Hⁿ` is finite-dimensional, only finitely many of them are nonzero, and

`∑ₙ (-1)ⁿ dim Hⁿ = ∑_{p,q} (-1)^{p+q} dim E_r^{p,q}`.

This is the computation at the end of the proof of [Stacks, Tag 0EDD]: the alternating sum of
the dimensions of the terms of a page does not change when passing to the next page, the pages
are eventually constant, and the abutment has a finite filtration whose graded pieces are the
terms of the infinity page.

## Main results

* `ComplexShape.eulerCharSignsSpectralSequence`: the signs `(p, q) ↦ (-1)^{p+q}`, which
  alternate along the differentials of every page of a cohomological spectral sequence.
* `CategoryTheory.Subobject.finrank_eq_finsum_finrank_cokernel_ofLE`: the dimension of a vector
  space with a finite decreasing filtration is the sum of the dimensions of its graded pieces.
* `CategoryTheory.SpectralSequence.eulerChar_page_eq`: the Euler characteristic of a page with
  finitely many nonzero finite-dimensional terms equals that of every later page.
* `CategoryTheory.SpectralSequence.AbutsTo.finsum_finrank_eq`: the identity above.

## References

* [Stacks Project, Tag 0EDD](https://stacks.math.columbia.edu/tag/0EDD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ComplexShape

/-- The signs `(p, q) ↦ (-1)^{p+q}` on `ℤ × ℤ`. They alternate along the differentials
`E_r^{p,q} ⟶ E_r^{p+r,q-r+1}` of the `r`-th page of a cohomological spectral sequence, which
raise the total degree `p + q` by one. -/
instance eulerCharSignsSpectralSequence (r : ℤ) :
    (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next := by
    rintro pq _ rfl
    simp only [Prod.fst_add, Prod.snd_add]
    rw [show pq.1 + r + (pq.2 + (1 - r)) = pq.1 + pq.2 + 1 by ring, Int.negOnePow_succ]

end ComplexShape

namespace CategoryTheory.Subobject

variable {k : Type u} [Field k]

/-- For a monomorphism `f : A ⟶ B` of vector spaces with `A` and `cokernel f`
finite-dimensional, `B` is finite-dimensional of dimension `dim A + dim (cokernel f)`. -/
theorem finite_and_finrank_eq_of_mono {A B : ModuleCat.{v} k} (f : A ⟶ B) [Mono f]
    [Module.Finite k A] (hc : Module.Finite k (cokernel f : ModuleCat.{v} k)) :
    Module.Finite k B ∧
      Module.finrank k B =
        Module.finrank k A + Module.finrank k (cokernel f : ModuleCat.{v} k) := by
  let e := (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv
  have hq : Module.Finite k (B ⧸ LinearMap.range f.hom) := Module.Finite.equiv e
  have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 inferInstance
  have hB : Module.Finite k B :=
    Module.Finite.of_exact f.hom.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  refine ⟨hB, ?_⟩
  rw [e.finrank_eq, ← (LinearMap.range f.hom).finrank_quotient_add_finrank,
    LinearMap.finrank_range_of_inj hinj, add_comm]

/-- `Subobject.ofLE X Y` is an isomorphism when `X = Y`. -/
theorem isIso_ofLE_of_eq {B : ModuleCat.{v} k} {X Y : Subobject B} (h : X ≤ Y) (he : X = Y) :
    IsIso (ofLE X Y h) :=
  ⟨ofLE Y X he.ge, by simp [ofLE_comp_ofLE, ofLE_refl], by simp [ofLE_comp_ofLE, ofLE_refl]⟩

/-- **The dimension of a finitely filtered vector space is the sum of the dimensions of its
graded pieces.** Let `F` be a decreasing filtration of a vector space `H` by subobjects, with
`F a = ⊤` and `F b = ⊥` for some `a ≤ b`, whose graded pieces `F p / F (p + 1)` are all
finite-dimensional. Then `H` is finite-dimensional, only the graded pieces with `a ≤ p < b`
can be nonzero, and `dim H` is the sum of the dimensions of the graded pieces. -/
theorem finrank_eq_finsum_finrank_cokernel_ofLE {H : ModuleCat.{v} k} (F : ℤ → Subobject H)
    (hF : Antitone F) {a b : ℤ} (hab : a ≤ b) (ha : F a = ⊤) (hb : F b = ⊥)
    (hgr : ∀ p, Module.Finite k (cokernel (ofLE (F (p + 1)) (F p) (hF (by omega))) :
      ModuleCat.{v} k)) :
    Module.Finite k H ∧
      (Function.support fun p => Module.finrank k
        (cokernel (ofLE (F (p + 1)) (F p) (hF (by omega))) : ModuleCat.{v} k)).Finite ∧
      Module.finrank k H = ∑ᶠ p, Module.finrank k
        (cokernel (ofLE (F (p + 1)) (F p) (hF (by omega))) : ModuleCat.{v} k) := by
  classical
  let g : ℤ → ℕ := fun p => Module.finrank k
    (cokernel (ofLE (F (p + 1)) (F p) (hF (by omega))) : ModuleCat.{v} k)
  let Q : ℤ → Prop := fun p =>
    Module.Finite k (F p : ModuleCat.{v} k) ∧
      Module.finrank k (F p : ModuleCat.{v} k) = ∑ j ∈ Finset.Ico p b, g j
  have hstep (p : ℤ) (hp : p < b) (h : Q (p + 1)) : Q p := by
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨h₃, h₄⟩ := finite_and_finrank_eq_of_mono (ofLE (F (p + 1)) (F p) (hF (by omega)))
      (hgr p)
    refine ⟨h₃, ?_⟩
    rw [h₄, h₂, ← Finset.insert_Ico_succ_left_eq_Ico hp, Order.succ_eq_add_one,
      Finset.sum_insert (by simp), add_comm]
  have hz : IsZero ((⊥ : Subobject H) : ModuleCat.{v} k) :=
    IsZero.of_iso (isZero_zero _) botCoeIsoZero
  have hQb : Q b := by
    refine ⟨?_, ?_⟩
    · rw [hb]
      have := ModuleCat.subsingleton_of_isZero hz
      infer_instance
    · rw [Finset.Ico_self, Finset.sum_empty, hb]
      exact HomologicalComplex.finrank_eq_zero_of_isZero hz
  have hQ : ∀ p ≤ b, Q p := by
    intro p
    induction p using Int.inductionOn' (b := b) with
    | zero => exact fun _ => hQb
    | succ n hn _ => exact fun h => absurd h (by omega)
    | pred n hn ih => exact fun _ => hstep (n - 1) (by omega) (by simpa using ih hn)
  have hzero (p : ℤ) (hp : p < a ∨ b ≤ p) : g p = 0 := by
    have := isIso_ofLE_of_eq (hF (by omega : p ≤ p + 1)) <| by
      rcases hp with hp | hp
      · exact (top_le_iff.1 (ha ▸ hF (by omega))).trans (top_le_iff.1 (ha ▸ hF (by omega))).symm
      · exact (le_bot_iff.1 (hb ▸ hF (by omega))).trans (le_bot_iff.1 (hb ▸ hF hp)).symm
    exact HomologicalComplex.finrank_eq_zero_of_isZero (isZero_cokernel_of_epi _)
  have hsupp : Function.support g ⊆ (Finset.Ico a b : Set ℤ) := by
    intro p hp
    by_contra h
    simp only [Finset.coe_Ico, Set.mem_Ico, not_and_or, not_le, not_lt] at h
    exact hp (hzero p (by omega))
  obtain ⟨h₁, h₂⟩ := hQ a hab
  rw [ha] at h₁ h₂
  let eTop := (asIso (⊤ : Subobject H).arrow).toLinearEquiv
  refine ⟨Module.Finite.equiv eTop, (Finset.Ico a b).finite_toSet.subset hsupp, ?_⟩
  rw [← eTop.finrank_eq, h₂, finsum_eq_sum_of_support_subset g hsupp]

end CategoryTheory.Subobject

namespace CategoryTheory.SpectralSequence

variable {k : Type u} [Field k] {r₀ : ℤ} (E : CohomologicalSpectralSequence (ModuleCat.{v} k) r₀)

/-- The homology of a complex of vector spaces at a finite-dimensional term is
finite-dimensional. -/
theorem _root_.HomologicalComplex.finite_homology {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} k) c) (i : ι) [Module.Finite k (K.X i)] :
    Module.Finite k (K.homology i) :=
  have : Module.Finite k (K.sc i).X₂ := ‹_›
  have : Module.Finite k (K.sc i).moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite k
      (LinearMap.ker (K.sc i).g.hom ⧸ LinearMap.range (K.sc i).moduleCatToCycles))
  Module.Finite.equiv (K.sc i).moduleCatHomologyIso.toLinearEquiv.symm

/-- **One page to the next.** If every term of the page `E_r` is finite-dimensional and only
those in a set `S` are nonzero, the same holds on the page `E_{r+1}`, and the two pages have
the same Euler characteristic. -/
theorem eulerChar_page_succ (r : ℤ) (hr : r₀ ≤ r) (S : Set (ℤ × ℤ)) (hS : S.Finite)
    (hfin : ∀ pq, Module.Finite k ((E.page r hr).X pq))
    (hsupp : ∀ pq ∉ S, IsZero ((E.page r hr).X pq)) :
    (∀ pq, Module.Finite k ((E.page (r + 1) (by omega)).X pq)) ∧
      (∀ pq ∉ S, IsZero ((E.page (r + 1) (by omega)).X pq)) ∧
      (E.page (r + 1) (by omega)).eulerChar = (E.page r hr).eulerChar := by
  have hfin' (pq : ℤ × ℤ) : Module.Finite k ((E.page (r + 1) (by omega)).X pq) :=
    have := hfin pq
    have := (E.page r hr).finite_homology pq
    Module.Finite.equiv (E.iso r (r + 1) pq).toLinearEquiv
  refine ⟨hfin', fun pq hpq => ?_, ?_⟩
  · exact IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ (hsupp pq hpq))
      (E.iso r (r + 1) pq).symm
  · rw [← HomologicalComplex.homologyEulerChar_eq_eulerChar_of_rel
      (Equiv.addRight (⟨r, 1 - r⟩ : ℤ × ℤ)) (fun _ => rfl) (E.page r) hfin
      (hS.subset fun pq hpq => by_contra fun h => hpq (hsupp pq h))]
    refine finsum_congr fun pq => ?_
    rw [(E.iso r (r + 1) pq).toLinearEquiv.finrank_eq]
    rfl

/-- **The Euler characteristic of the pages is constant.** If every term of the page `E_r` is
finite-dimensional and only those in a finite set `S` are nonzero, then the same holds on
every later page `E_{r'}`, which has the same Euler characteristic as `E_r`. -/
theorem eulerChar_page_eq (r : ℤ) (hr : r₀ ≤ r) (S : Set (ℤ × ℤ)) (hS : S.Finite)
    (hfin : ∀ pq, Module.Finite k ((E.page r).X pq))
    (hsupp : ∀ pq ∉ S, IsZero ((E.page r).X pq)) (r' : ℤ) (hr' : r ≤ r') :
    (∀ pq, Module.Finite k ((E.page r' (hr.trans hr')).X pq)) ∧
      (∀ pq ∉ S, IsZero ((E.page r' (hr.trans hr')).X pq)) ∧
      (E.page r' (hr.trans hr')).eulerChar = (E.page r hr).eulerChar := by
  revert hr'
  induction r' using Int.inductionOn' (b := r) with
  | zero => exact fun _ => ⟨hfin, hsupp, rfl⟩
  | pred n hn _ => exact fun h => absurd h (by omega)
  | succ n hn ih =>
    intro _
    obtain ⟨h₁, h₂, h₃⟩ := ih hn
    obtain ⟨h₄, h₅, h₆⟩ := E.eulerChar_page_succ n (hr.trans hn) S hS h₁ h₂
    exact ⟨h₄, h₅, h₆.trans h₃⟩

/-- If only the terms of the pages from `E_r` on in a finite set `S` are nonzero, then from some
page on every differential into and out of every position vanishes: the differentials of the
page `E_{r'}` move the first index by `r'`, more than the spread of `S` once `r'` is large. -/
theorem exists_forall_hasEdgeMonoAt_hasEdgeEpiAt (r : ℤ) (hr : r₀ ≤ r) (S : Finset (ℤ × ℤ))
    (hsupp : ∀ r' (hr' : r ≤ r'), ∀ pq ∉ S, IsZero ((E.page r' (hr.trans hr')).X pq)) :
    ∃ r' : ℤ, r ≤ r' ∧ ∀ pq, r' ∈ E.hasEdgeMonoSet pq ∧ r' ∈ E.hasEdgeEpiSet pq := by
  let B : ℤ := ∑ pq ∈ S, |pq.1|
  have hB (pq : ℤ × ℤ) (h : pq ∈ S) : -B ≤ pq.1 ∧ pq.1 ≤ B :=
    abs_le.1 (Finset.single_le_sum (f := fun pq : ℤ × ℤ => |pq.1|) (fun _ _ => abs_nonneg _) h)
  have hd (r'' : ℤ) (h : max r (2 * B + 1) ≤ r'') (pq pq' : ℤ × ℤ) :
      (E.page r'' (by omega)).d pq pq' = 0 := by
    by_cases hrel : (ComplexShape.up' (⟨r'', 1 - r''⟩ : ℤ × ℤ)).Rel pq pq'
    · by_cases h₁ : pq ∈ S
      · by_cases h₂ : pq' ∈ S
        · exfalso
          have e := congrArg _root_.Prod.fst hrel
          simp only [Prod.fst_add] at e
          have := hB pq h₁
          have := hB pq' h₂
          omega
        · exact (hsupp r'' (by omega) pq' h₂).eq_of_tgt _ _
      · exact (hsupp r'' (by omega) pq h₁).eq_of_src _ _
    · exact (E.page r'' (by omega)).shape _ _ hrel
  refine ⟨max r (2 * B + 1), le_max_left _ _, fun pq => ⟨⟨by omega, fun r'' h => ?_⟩,
    ⟨by omega, fun r'' h => ?_⟩⟩⟩
  · exact ⟨by omega, fun pq' => hd r'' h pq' pq⟩
  · exact ⟨by omega, fun pq' => hd r'' h pq pq'⟩

variable {E} in
/-- **The Euler characteristic of a convergent spectral sequence.** Let `E` be a cohomological
spectral sequence of vector spaces over a field abutting to `H`. If some page `E_r` has only
finitely many nonzero terms, each finite-dimensional, then every `Hⁿ` is finite-dimensional,
only finitely many are nonzero, and `∑ₙ (-1)ⁿ dim Hⁿ = ∑_{p,q} (-1)^{p+q} dim E_r^{p,q}`.

The Euler characteristic of the pages does not change from `E_r` on
(`CategoryTheory.SpectralSequence.eulerChar_page_eq`), the pages are eventually equal to the
infinity page (`CategoryTheory.SpectralSequence.exists_forall_hasEdgeMonoAt_hasEdgeEpiAt`), and
`Hⁿ` has a finite filtration with graded pieces `E_∞^{p,n-p}`
(`CategoryTheory.Subobject.finrank_eq_finsum_finrank_cokernel_ofLE`). -/
theorem AbutsTo.finsum_finrank_eq {H : ℤ → ModuleCat.{v} k} (hE : E.AbutsTo H) (r : ℤ)
    (hr : r₀ ≤ r) (hfin : ∀ pq, Module.Finite k ((E.page r).X pq))
    (hsupp : {pq | ¬ IsZero ((E.page r).X pq)}.Finite) :
    (∀ n, Module.Finite k (H n)) ∧ {n | ¬ IsZero (H n)}.Finite ∧
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (H n) : ℤ) =
        ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
          (Module.finrank k ((E.page r).X pq) : ℤ) := by
  classical
  let S := hsupp.toFinset
  have hS (pq : ℤ × ℤ) (h : pq ∉ S) : IsZero ((E.page r).X pq) := by
    simpa [S] using h
  have hpages := E.eulerChar_page_eq r hr S S.finite_toSet hfin hS
  obtain ⟨r', hrr', hr'⟩ := E.exists_forall_hasEdgeMonoAt_hasEdgeEpiAt r hr S
    fun r'' h => (hpages r'' h).2.1
  obtain ⟨hfin', hsupp', heuler⟩ := hpages r' hrr'
  have hinf (pq : ℤ × ℤ) : Nonempty (E.pageInfinity pq ≅ (E.page r' (hr.trans hrr')).X pq) := by
    have : E.HasPageInfinityAt pq := ⟨⟨r', (hr' pq).1⟩, ⟨r', (hr' pq).2⟩⟩
    have : E.HasEdgeMonoAtFrom pq r' := ⟨E.rToMin_LE pq r' (hr' pq).1⟩
    have : E.HasEdgeEpiAtFrom pq r' := ⟨E.rFromMin_LE pq r' (hr' pq).2⟩
    exact ⟨E.pageInfinityIso pq r'⟩
  -- the dimensions of the infinity page
  let e : ℤ × ℤ → ℕ := fun pq => Module.finrank k ((E.page r' (hr.trans hrr')).X pq)
  have he (pq : ℤ × ℤ) (h : pq ∉ S) : e pq = 0 :=
    HomologicalComplex.finrank_eq_zero_of_isZero (hsupp' pq h)
  obtain ⟨-, F, hF, hbounds, hgr⟩ := hE
  let g : ℤ → ℤ → ℕ := fun n p =>
    Module.finrank k
      (cokernel (Subobject.ofLE (F n (p + 1)) (F n p) (hF n (by omega))) : ModuleCat.{v} k)
  have hge (p q : ℤ) : g (p + q) p = e (p, q) ∧
      Module.Finite k (cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
        (hF (p + q) (by omega))) : ModuleCat.{v} k) := by
    obtain ⟨i⟩ := hgr p q
    obtain ⟨j⟩ := hinf (p, q)
    have := hfin' (p, q)
    exact ⟨(i.symm ≪≫ j).toLinearEquiv.finrank_eq,
      Module.Finite.equiv (i.symm ≪≫ j).symm.toLinearEquiv⟩
  have hH (n : ℤ) : Module.Finite k (H n) ∧ (Function.support (g n)).Finite ∧
      Module.finrank k (H n) = ∑ᶠ p, g n p := by
    obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
    refine Subobject.finrank_eq_finsum_finrank_cokernel_ofLE (F n) (hF n) hab ha hb fun p => ?_
    obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
    exact (hge p q).2
  have hgn (n p : ℤ) : g n p = e (p, n - p) := by
    rw [← (hge p (n - p)).1]
    congr 1
    omega
  -- the total degrees of the positions in `S`
  let T := S.image fun pq => pq.1 + pq.2
  have hHzero (n : ℤ) (hn : n ∉ T) : Module.finrank k (H n) = 0 := by
    rw [(hH n).2.2]
    refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
    rw [hgn, he]
    intro h
    exact hn (Finset.mem_image.2 ⟨_, h, by simp⟩)
  have hHfin (n : ℤ) := (hH n).1
  refine ⟨hHfin, T.finite_toSet.subset fun n hn => by_contra fun h => hn ?_, ?_⟩
  · have := hHfin n
    have : Subsingleton (H n) := Module.finrank_zero_iff.1 (hHzero n (by simpa using h))
    exact ModuleCat.isZero_of_subsingleton _
  · have hsuppe : (Function.support fun pq : ℤ × ℤ =>
        ((pq.1 + pq.2).negOnePow : ℤ) * (e pq : ℤ)).Finite :=
      S.finite_toSet.subset fun pq hpq => by_contra fun h => hpq (by simp [he pq h])
    let φ : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun np => (np.2, np.1 - np.2)
        invFun := fun pq => (pq.1 + pq.2, pq.1)
        left_inv := fun np => by ext <;> simp
        right_inv := fun pq => by ext <;> simp }
    have hsuppφ : (Function.support fun np : ℤ × ℤ =>
        ((np.1).negOnePow : ℤ) * (e (np.2, np.1 - np.2) : ℤ)).Finite := by
      refine (hsuppe.image φ.symm).subset fun np hnp => ⟨φ np, ?_, φ.symm_apply_apply np⟩
      simpa [φ] using hnp
    calc ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (Module.finrank k (H n) : ℤ)
        = ∑ᶠ n : ℤ, ∑ᶠ p : ℤ, (n.negOnePow : ℤ) * (e (p, n - p) : ℤ) := by
          refine finsum_congr fun n => ?_
          rw [(hH n).2.2, ← mul_finsum]
          congr 1
          refine ((Nat.castAddMonoidHom ℤ).map_finsum (hH n).2.1).trans ?_
          exact finsum_congr fun p => by simp [hgn]
      _ = ∑ᶠ np : ℤ × ℤ, ((np.1).negOnePow : ℤ) * (e (np.2, np.1 - np.2) : ℤ) :=
          (finsum_curry _ hsuppφ).symm
      _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) * (e pq : ℤ) := by
          rw [← finsum_comp_equiv φ.symm]
          refine finsum_congr fun pq => ?_
          simp [φ]
      _ = (E.page r' (hr.trans hrr')).eulerChar := rfl
      _ = _ := heuler

end CategoryTheory.SpectralSequence

end
