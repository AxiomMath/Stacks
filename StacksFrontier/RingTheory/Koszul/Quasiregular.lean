module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import StacksFrontier.RingTheory.Koszul.Functoriality
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- The comparison maps below are assembled from `ModuleCat` objects, `rTensor`s and quotient
-- wrappers, and the `change`/`rw` steps that identify their components unfold those wrappers
-- through reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false

/-!
# H₁-regular and quasi-regular sequences

Let `R` be a commutative ring, let `M` be an `R`-module and let `f₁, …, f_r ∈ R`. This file
proves that vanishing of the first Koszul homology `H₁(K(f) ⊗ M)` already forces the sequence
to be `M`-quasi-regular, and deduces from this — together with the implications assembled in
`StacksFrontier.RingTheory.Koszul.Regular` — that over a Noetherian local ring all four notions
of regularity of a sequence in the maximal ideal coincide for a nonzero finite module.

## Main results

* `Koszul.isQuasiRegular_of_isH1RegularOn` (Stacks Tag 062I, Lemma 15.30.6): an
  `M`-`H₁`-regular sequence is `M`-quasi-regular.
* `Koszul.regular_koszulRegular_h1Regular_quasiRegular_tfae` (Stacks Tag 09CC,
  Lemma 15.30.8): for a Noetherian local ring `(R, 𝔪)`, a nonzero finite `R`-module `M` and
  `f₁, …, f_r ∈ 𝔪`, the four conditions `M`-regular, `M`-Koszul-regular, `M`-`H₁`-regular and
  `M`-quasi-regular are equivalent; likewise for the four corresponding conditions on the
  sequence in `R` itself.

## Implementation notes

The Koszul-complex API represents a sequence of length `r` by a function `Fin r → R`, while
the regular- and quasi-regular-sequence API represents it by the corresponding list
`List.ofFn f`. The source's module assertion and its ring special case are recorded as two
`List.TFAE` statements.

Quasi-regularity is injectivity of the canonical map `Φ_M` of tag 061N, which is always
surjective. Injectivity is reduced degreewise (`injective_of_mem_of_sum_fpow_smul_mem`) to the
elementary statement that a relation `∑_{|e| = n} f^e · m_e ∈ J^{n+1} M` among monomials of a
fixed total degree `n` forces every coefficient `m_e` into `J M`. That statement
(`coefficients_mem_of_isH1RegularOn`) is proved from `H₁`-regularity by clearing one monomial
factor at a time (`cancel_generator`, `cancel_monomial`), which needs `H₁`-regularity to be
stable under raising the entries of the sequence to positive powers (`isH1RegularOn_pow`); the
latter comes from tag 062G together with invariance of the Koszul complex under permuting the
sequence (`isH1RegularOn_comp_perm`, via the permutation matrix and tag 0625).

## References

* [The Stacks Project, Tag 062I](https://stacks.math.columbia.edu/tag/062I)
* [The Stacks Project, Tag 09CC](https://stacks.math.columbia.edu/tag/09CC)
-/

namespace Koszul

universe u v

open CategoryTheory
open scoped TensorProduct ExteriorAlgebra

/-! ## Tag 062I: an `M`-`H₁`-regular sequence is `M`-quasi-regular -/

private lemma exact_differentials
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M) :
    LinearMap.ker (LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) 0)) ≤
      LinearMap.range (LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) 1)) := by
  rw [Koszul.IsH1RegularOn, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range] at hf
  exact hf

private lemma coordinate_mem_of_mem_relSpan
    {R : Type*} [CommRing R] {r : ℕ} {f a : Fin r → R} (i : Fin r) (I : Ideal R)
    (hI : ∀ j, j ≠ i → f j ∈ I) (ha : a ∈ Koszul.relSpan f) : a i ∈ I := by
  classical
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨⟨j, k⟩, rfl⟩ := ha
    by_cases hj : j = i <;> by_cases hk : k = i
    · subst j; subst k; simp [Koszul.trivRel]
    · subst j; simpa [Koszul.trivRel_apply, Ne.symm hk] using I.neg_mem (hI k hk)
    · subst k; simpa [Koszul.trivRel_apply, Ne.symm hj] using hI j hj
    · simp [Koszul.trivRel_apply, Ne.symm hj, Ne.symm hk]
  | zero => exact I.zero_mem
  | add a b _ _ ha hb => exact I.add_mem ha hb
  | smul c a _ ha => exact I.smul_mem c ha

private lemma relation_coefficient_mem
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M)
    (a : Fin r → M) (ha : ∑ j, f j • a j = 0) (i : Fin r) (I : Ideal R)
    (hI : ∀ j, j ≠ i → f j ∈ I) : a i ∈ I • (⊤ : Submodule R M) := by
  classical
  let e := exteriorPower.oneEquiv R (Fin r → R)
  let c : (⋀[R]^1 (Fin r → R)) ⊗[R] M →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap ∘ₗ
      LinearMap.rTensor M ((LinearMap.proj i) ∘ₗ e.toLinearMap)
  let x : (⋀[R]^1 (Fin r → R)) ⊗[R] M :=
    ∑ j, e.symm (Pi.single j 1) ⊗ₜ[R] a j
  have hx : x ∈ LinearMap.ker (LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) 0)) := by
    rw [LinearMap.mem_ker]
    apply ((exteriorPower.zeroEquiv R (Fin r → R)).rTensor M).injective
    apply (TensorProduct.lid R M).injective
    simpa [x, Koszul.zeroEquiv_d_zero, e, ← Finset.sum_smul] using ha
  obtain ⟨z, hz⟩ := exact_differentials hf hx
  have hcx : c x = a i := by
    simp [c, x, e, Pi.single_apply]
  rw [← hcx, ← hz]
  clear hz hx
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw
  | tmul z m =>
    change (e (Koszul.d (Koszul.seqDual f) 1 z)) i • m ∈ _
    apply Submodule.smul_mem_smul
    · apply coordinate_mem_of_mem_relSpan i I hI
      rw [← Koszul.map_range_d_one]
      exact ⟨_, ⟨z, rfl⟩, rfl⟩
    · exact Submodule.mem_top

private noncomputable def tensorComplexIso
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {r : ℕ} {f g : Fin r → R} (e : Koszul.seqComplex f ≅ Koszul.seqComplex g) :
    Koszul.seqComplexTensor f M ≅ Koszul.seqComplexTensor g M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (((HomologicalComplex.eval _ _ n).mapIso e).toLinearEquiv.rTensor M).toModuleIso) (by
      intro i j hij
      obtain rfl : j + 1 = i := hij
      rw [Koszul.seqComplexTensor_d, Koszul.seqComplexTensor_d]
      apply ModuleCat.hom_ext
      change (LinearMap.rTensor M (Koszul.d (Koszul.seqDual g) j)) ∘ₗ
          LinearMap.rTensor M (e.hom.f (j + 1)).hom =
        LinearMap.rTensor M (e.hom.f j).hom ∘ₗ
          LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) j)
      rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
      congr 1
      have h := congrArg ModuleCat.Hom.hom (e.hom.comm (j + 1) j)
      simpa only [Koszul.seqComplex_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom] using h)

private lemma isH1RegularOn_comp_perm
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M) (e : Equiv.Perm (Fin r)) :
    Koszul.IsH1RegularOn (f ∘ e) M := by
  have hu : IsUnit (e.permMatrix R) := by
    have := (Group.isUnit e⁻¹).map (Matrix.permMatrixHom (R := R))
    simpa [Matrix.permMatrixHom] using this
  obtain ⟨E⟩ := Koszul.seqComplex_mulVec_iso f (e.permMatrix R) hu
  rw [Matrix.permMatrix_mulVec] at E
  exact hf.of_iso ((HomologicalComplex.homologyFunctor _ _ 1).mapIso
    (tensorComplexIso M E)).symm

private lemma isH1RegularOn_update_pow
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M)
    (i : Fin r) (n : ℕ) (hn : 0 < n) :
    Koszul.IsH1RegularOn (Function.update f i (f i ^ n)) M := by
  classical
  cases r with
  | zero => exact i.elim0
  | succ r =>
    let e := Equiv.swap i (Fin.last r)
    let g := f ∘ e
    have hg := isH1RegularOn_comp_perm hf e
    have hp : ∀ n, 0 < n → Koszul.IsH1RegularOn (Fin.snoc (Fin.init g) (g (Fin.last r) ^ n)) M := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        by_cases h : n = 0
        · subst n; simpa using hg
        · have hn : 0 < n := Nat.pos_of_ne_zero h
          simpa only [pow_succ] using
            (Koszul.isH1RegularOn_and_isKoszulRegularOn_snoc_mul
              (M := M) (Fin.init g) (g (Fin.last r) ^ n) (g (Fin.last r))).1
              ⟨ih hn, by simpa using hg⟩
    have H := isH1RegularOn_comp_perm (hp n hn) e
    convert H using 1
    funext j
    by_cases hj : j = i
    · subst j
      simp [g, e]
    · have he : e j ≠ Fin.last r := by simpa [e, Equiv.swap_apply_eq_iff] using hj
      rw [Function.update_of_ne hj]
      change f j = Fin.snoc (Fin.init g) _ (e j)
      have hlt : (e j).val < r := Fin.val_lt_last he
      simp [Fin.snoc, hlt, Fin.init, g, e]

private lemma isH1RegularOn_pow
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M)
    (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) :
    Koszul.IsH1RegularOn (fun i => f i ^ n i) M := by
  classical
  have H (s : Finset (Fin r)) :
      Koszul.IsH1RegularOn (fun i => if i ∈ s then f i ^ n i else f i) M := by
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | @insert i s hi ih =>
      convert isH1RegularOn_update_pow ih i (n i) (hn i) using 1
      funext j
      by_cases hj : j = i
      · subst j
        simp [hi]
      · simp [hj]
  simpa using H Finset.univ

private lemma exists_sum_of_mem_span_smul
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {r : ℕ} (f : Fin r → R) {m : M} (hm : m ∈ Jid f • (⊤ : Submodule R M)) :
    ∃ a : Fin r → M, ∑ i, f i • a i = m := by
  classical
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha m hm
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
    refine ⟨fun i => b i • m, ?_⟩
    simpa only [← mul_smul, mul_comm, ← Finset.sum_smul] using congrArg (fun a : R => a • m) hb
  · intro m m' hm hm'
    obtain ⟨a, rfl⟩ := hm
    obtain ⟨b, rfl⟩ := hm'
    exact ⟨a + b, by simp [smul_add, Finset.sum_add_distrib]⟩

private lemma cancel_generator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M)
    (i : Fin r) (b : R) {m : M}
    (hm : f i • m ∈ Jid (Function.update f i (f i * b)) • (⊤ : Submodule R M)) :
    m ∈ Jid (Function.update f i b) • (⊤ : Submodule R M) := by
  classical
  obtain ⟨a, ha⟩ := exists_sum_of_mem_span_smul _ hm
  let c := Pi.single i m - Function.update a i (b • a i)
  have hc : ∑ j, f j • c j = 0 := by
    have h : ∑ j, f j • (Function.update a i (b • a i)) j =
        ∑ j, Function.update f i (f i * b) j • a j := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [mul_smul]
      · simp [hji]
    simp [c, smul_sub, Finset.sum_sub_distrib, h, ha, Pi.single_apply]
  have hcI := relation_coefficient_mem hf c hc i (Jid (Function.update f i b))
    fun j hj => Ideal.subset_span ⟨j, Function.update_of_ne hj _ _⟩
  have hb : b • a i ∈ Jid (Function.update f i b) • (⊤ : Submodule R M) :=
    Submodule.smul_mem_smul (Ideal.subset_span ⟨i, Function.update_self _ _ _⟩)
      Submodule.mem_top
  simpa [c] using Submodule.add_mem _ hcI hb

private lemma cancel_monomial
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M)
    (a : Fin r → ℕ) {m : M}
    (hm : (∏ i, f i ^ a i) • m ∈ Jid (fun i => f i ^ (a i + 1)) • (⊤ : Submodule R M)) :
    m ∈ Jid f • (⊤ : Submodule R M) := by
  classical
  have H (s : Finset (Fin r)) :
      ∀ m : M, (∏ i ∈ s, f i ^ a i) • m ∈
        Jid (fun i => f i ^ (if i ∈ s then a i + 1 else 1)) • (⊤ : Submodule R M) →
          m ∈ Jid f • (⊤ : Submodule R M) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      intro m hm
      apply ih m
      by_cases ha : a i = 0
      · have hgen : (fun j => f j ^ (if j ∈ insert i s then a j + 1 else 1)) =
              (fun j => f j ^ (if j ∈ s then a j + 1 else 1)) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp [hi, ha]
          · simp [hj]
        rw [hgen] at hm
        simpa [Finset.prod_insert hi, ha] using hm
      · let p : Fin r → ℕ := fun j => if j = i then a i else if j ∈ s then a j + 1 else 1
        have hp : ∀ j, 0 < p j := by intro j; dsimp [p]; split_ifs <;> omega
        have h₁ : Function.update (fun j => f j ^ p j) i ((f i ^ p i) * f i) =
            (fun j => f j ^ (if j ∈ insert i s then a j + 1 else 1)) := by
          funext j
          by_cases hj : j = i <;> simp [hj, p, pow_succ]
        have h₂ : Function.update (fun j => f j ^ p j) i (f i) =
            (fun j => f j ^ (if j ∈ s then a j + 1 else 1)) := by
          funext j
          by_cases hj : j = i <;> simp [hj, hi, p]
        have h := cancel_generator (isH1RegularOn_pow hf p hp) i (f i)
          (m := (∏ j ∈ s, f j ^ a j) • m)
        rw [h₁, h₂] at h
        apply h
        simpa [p, Finset.prod_insert hi, mul_smul] using hm
  simpa using H Finset.univ m (by simpa using hm)

private lemma exists_lt_of_sum_le_of_ne
    {ι : Type*} [Fintype ι] {a b : ι → ℕ}
    (hab : ∑ i, a i ≤ ∑ i, b i) (hne : a ≠ b) : ∃ i, a i < b i := by
  classical
  by_contra! h
  have heq : ∑ i, b i = ∑ i, a i := le_antisymm (Finset.sum_le_sum fun i _ => h i) hab
  have H := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => h i)).mp heq
  exact hne (funext fun i => (H i (Finset.mem_univ i)).symm)

private lemma fpow_mem_powerSpan
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (e d : Fin r →₀ ℕ) (h : ∃ i, e i < d i) :
    fpow f d ∈ Jid (fun i => f i ^ (e i + 1)) := by
  classical
  obtain ⟨i, hi⟩ := h
  exact Ideal.prod_mem _ (Finset.mem_univ i)
    (Ideal.mem_of_dvd _ (pow_dvd_pow _ hi) (Ideal.subset_span ⟨i, rfl⟩))

private lemma coefficients_mem_of_isH1RegularOn
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M)
    (n : ℕ) (S : Finset (Fin r →₀ ℕ)) (s : (Fin r →₀ ℕ) → M)
    (hdeg : ∀ e ∈ S, qrMdeg e = n)
    (hrel : (∑ e ∈ S, fpow f e • s e) ∈ JpowM M f (n + 1)) :
    ∀ e ∈ S, s e ∈ Jid f • (⊤ : Submodule R M) := by
  classical
  intro e he
  let I := Jid (fun i => f i ^ (e i + 1))
  have key : ∀ d, qrMdeg e ≤ qrMdeg d → d ≠ e → fpow f d ∈ I := fun d hle hne =>
    fpow_mem_powerSpan f e d (exists_lt_of_sum_le_of_ne hle fun h =>
      hne (Finsupp.ext fun i => (congrFun h i).symm))
  have hp : Jid f ^ (n + 1) ≤ I := by
    rw [Jid_pow_eq_span, Ideal.span_le]
    rintro _ ⟨d, hd, rfl⟩
    have := hdeg e he
    exact key d (by rw [hd]; omega) (by rintro rfl; omega)
  have hsum : (∑ d ∈ S.erase e, fpow f d • s d) ∈ I • (⊤ : Submodule R M) :=
    Submodule.sum_mem _ fun d hd => Submodule.smul_mem_smul
      (key d (by rw [hdeg e he, hdeg d (Finset.mem_of_mem_erase hd)]) (Finset.ne_of_mem_erase hd))
      Submodule.mem_top
  have hrel' := (Submodule.smul_mono hp le_rfl) hrel
  rw [← Finset.add_sum_erase S _ he] at hrel'
  have hm := Submodule.sub_mem _ hrel' hsum
  simp only [add_sub_cancel_right] at hm
  exact cancel_monomial hf e hm

/-- **Stacks 062I.** An `M`-`H₁`-regular sequence is `M`-quasi-regular. -/
@[stacks 062I]
public theorem isQuasiRegular_of_isH1RegularOn
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsH1RegularOn f M) :
    RingTheory.Sequence.IsQuasiRegular M (List.ofFn f) := by
  have hbij : Function.Bijective (quasiRegularCanonicalMap (M := M) f) :=
    ⟨injective_of_mem_of_sum_fpow_smul_mem (coefficients_mem_of_isH1RegularOn hf),
      quasiRegularCanonicalMap_surjective f⟩
  have hcongr {r r' : ℕ} (h : r' = r) (g : Fin r → R) (g' : Fin r' → R)
      (hg : ∀ i, g' i = g (Fin.cast h i)) :
      Function.Bijective (quasiRegularCanonicalMap (M := M) g') ↔
        Function.Bijective (quasiRegularCanonicalMap (M := M) g) := by
    subst r'
    rw [show g' = g from funext hg]
  exact (hcongr List.length_ofFn f _ (fun i => List.get_ofFn f i)).mpr hbij

/-! ## Tag 09CC: the four notions agree over a Noetherian local ring -/

/-- **Stacks 09CC.** Let `M` be a nonzero finite module over a local Noetherian ring `R`, and
let `f` be a finite sequence in the maximal ideal. Being `M`-regular, `M`-Koszul-regular,
`M`-`H₁`-regular, and `M`-quasi-regular are equivalent. In particular, the corresponding
four notions for the sequence in `R` are equivalent. -/
@[stacks 09CC,
  ega "0 15.1.11" "(1) ⇔ (4), local case",
  ega "IV 19.5.1" "a)–c), local case",
  ega "0 15.2.2" "converse: q-reg ⇒ reg",
  ega "0 15.1.10" "special case",
  ega "0 15.1.9" "special case",
  ega "IV 16.9.12" "parenthetical"]
public theorem regular_koszulRegular_h1Regular_quasiRegular_tfae
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    {r : ℕ} (f : Fin r → R) (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
        [RingTheory.Sequence.IsRegular M (List.ofFn f),
          Koszul.IsKoszulRegularOn f M,
          Koszul.IsH1RegularOn f M,
          RingTheory.Sequence.IsQuasiRegular M (List.ofFn f)] ∧
      List.TFAE
        [RingTheory.Sequence.IsRegular R (List.ofFn f),
          Koszul.IsKoszulRegular f,
          Koszul.IsH1Regular f,
          RingTheory.Sequence.IsQuasiRegular R (List.ofFn f)] := by
  have hmem : ∀ x ∈ List.ofFn f, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hf i
  constructor
  · tfae_have 1 → 2 :=
      (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (R := R) (M := M) (f := f)).2.1
    tfae_have 2 → 3 := fun h => h 1 one_ne_zero
    tfae_have 3 → 4 := isQuasiRegular_of_isH1RegularOn
    tfae_have 4 → 1 :=
      RingTheory.Sequence.IsRegular.of_isQuasiRegular_of_mem_maximalIdeal hmem
    tfae_finish
  · tfae_have 1 → 2 :=
      (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (R := R) (M := R) (f := f)).2.2
    tfae_have 2 → 3 := fun h => h 1 one_ne_zero
    tfae_have 3 → 4 := fun h =>
      isQuasiRegular_of_isH1RegularOn
        (M := R) ((Koszul.isH1RegularOn_self_iff f).2 h)
    tfae_have 4 → 1 :=
      RingTheory.Sequence.IsRegular.of_isQuasiRegular_of_mem_maximalIdeal hmem
    tfae_finish

end Koszul

end
