module

public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE
public import StacksFrontier.Algebra.Homology.SpectralSequence.Defs.FilteredComplex
public import StacksFrontier.KTheory.SerreQuotient
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Interval

/-!
# The spectral sequence of a filtered complex: the first page, graded cohomology, and `K₀`

Let `𝒜` be an abelian category and `(K^•, F)` a filtered complex of `𝒜`, with spectral sequence
`(E_r, d_r)_{r ≥ 0}` ([Stacks, Tag 012M]): writing `n = p + q`,
`E_r^{p, q} = Z_r^{p, q}/(D_r^{p, q} ∩ Z_r^{p, q})` with
`Z_r^{p, q} = F^pK^n ∩ d^{-1}(F^{p + r}K^{n + 1})` and
`D_r^{p, q} = Z_{r - 1}^{p + 1, q - 1} + d(Z_{r - 1}^{p - r + 1, q + r - 2})`, the differential
`d_r` being induced by `d`.

* **The first differential** ([Stacks, Tag 012N]). `E_1^{p, q} = H^n(gr^pK^•)`, the class of
  `x ∈ Z_1^{p, q}` going to the class of its image in `gr^pK^n`, and under this identification
  `d_1^{p, q}` is the boundary map of the long exact cohomology sequence of
  `0 → gr^{p + 1}K^• → F^pK^•/F^{p + 2}K^• → gr^pK^• → 0`. If `d(F^pK) ⊆ F^{p + 1}K` for all `p`,
  then `gr^pK^•` has zero differential, `E_1^{p, q} = gr^pK^n`, and `d_1` is the map induced
  by `d`.
* **Graded cohomology** ([Stacks, Tag 0BDT]). For the induced filtration
  `F^pH^n(K^•) = Im(H^n(F^pK^•) → H^n(K^•))`,
  `gr^pH^n(K^•) = (Ker(d) ∩ F^pK^n)/(Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n)`.
* **Euler characteristics** ([Stacks, Tag 0BDW]). If the filtration of each `K^n` is finite and
  some page `E_r` has only finitely many nonzero terms, then only finitely many `H^n(K^•)` are
  nonzero and `∑ (-1)^n [H^n(K^•)] = ∑ (-1)^{p + q} [E_r^{p, q}]` in `K₀` of any weak Serre
  subcategory containing the `E_r^{p, q}`.

## Main definitions

* `CategoryTheory.FilteredObject.grMapCompShortComplex`: for index arrows `φ : i ⟶ j` and
  `ψ : j ⟶ k`, the short complex `F^jX/F^iX → F^kX/F^iX → F^kX/F^jX` of graded pieces of a
  filtered object, short exact by
  `CategoryTheory.FilteredObject.grMapCompShortComplex_shortExact`. For `i = p + 2`,
  `j = p + 1`, `k = p` it is `0 → gr^{p + 1}X → F^pX/F^{p + 2}X → gr^pX → 0`.

## Main results

* `CochainComplex.Filtered.exists_iso_firstPage_homology_d_eq_δ`: [Stacks, Tag 012N] (1).
* `CochainComplex.Filtered.d_gr_eq_zero_and_exists_iso_firstPage_d_eq`:
  [Stacks, Tag 012N] (2).
* `CochainComplex.Filtered.exists_iso_gradedHomology`: [Stacks, Tag 0BDT].
* `CochainComplex.Filtered.finite_homology_and_sum_negOnePow_eq`: [Stacks, Tag 0BDW].
* `CochainComplex.Filtered.exists_spectralSequence_firstPage_homology_d_eq_δ`,
  `CochainComplex.Filtered.exists_spectralSequence_sum_negOnePow_eq`: [Stacks, Tag 012N] (1) and
  [Stacks, Tag 0BDW] for the spectral sequence of [Stacks, Tag 012M].

## Implementation notes

*The spectral sequence is a hypothesis.* As in [Stacks, Tag 012M], whose formalization is an
existence statement, the spectral sequence is a `CohomologicalSpectralSequence` `E` carried
together with the identification of its terms with `Z_r^{p, q}/(D_r^{p, q} ∩ Z_r^{p, q})` and,
where the differential matters, the statement that `d_r` is induced by `d`; the results about
the first page only use these data for `r = 1`. The pages are families of objects indexed by
`ℤ × ℤ` rather than direct sums, so the source's assumption that `𝒜` has countable direct sums is
not needed.

*Identifications are isomorphisms.* Each "`=`" of the source between objects that are not
literally equal is an isomorphism together with the equation that pins it down: for
`E_1^{p, q} = H^n(gr^pK^•)` its value on the class of every `x ∈ Z_1^{p, q}`, for 0BDT the
compatibility with the canonical maps out of `Ker(d) ∩ F^pK^n`, and for "the morphism induced by
`d`" its value on `F^pK^n`. Here `gr^pH^n(K^•)` is `CochainComplex.Filtered.gradedHomology`.

*`K₀` of a weak Serre subcategory.* The source works in `K₀(𝒜')` for the smallest weak Serre
subcategory `𝒜'` containing the `E_r^{p, q}`. The statement here is made for every weak Serre
subcategory `𝒫` containing them, which contains the source's statement as the case `𝒫 = 𝒜'`;
that the `H^n(K^•)` lie in `𝒫` is part of the conclusion. Sums are `finsum`s, finitely supported
by the finiteness hypotheses.

*The proof of 0BDW.* The source compares the even and odd parts of consecutive pages. Here the
same invariance `∑ (-1)^{p + q} [E_s^{p, q}] = ∑ (-1)^{p + q} [E_{s + 1}^{p, q}]` is obtained
termwise: for a complex `X` whose differentials have total degree `1`, the relation
`[H^i(X)] + [X^{i - a}] = [Ker(d^{i - a})] + [Ker(d^i)]` telescopes in the alternating sum. The
source then passes to a page with `d_r = 0` and invokes [Stacks, Tag 012W]; here, the filtration
being finite in each degree, `Z_s^{p, q} = Ker(d) ∩ F^pK^n` and
`D_s^{p, q} = Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n` for `s ≫ 0`, so that
`E_s^{p, q} = gr^pH^n(K^•)` by 0BDT, and the class of `H^n(K^•)` is the sum of the classes of
the graded pieces of its finite filtration.

## References

* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012N](https://stacks.math.columbia.edu/tag/012N)
* [Stacks Project, Tag 0BDT](https://stacks.math.columbia.edu/tag/0BDT)
* [Stacks Project, Tag 0BDW](https://stacks.math.columbia.edu/tag/0BDW)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.FilteredObject

variable {C : Type*} [Category* C] [Abelian C] {I : Type*} [Category* I]
  {i j k : I} (φ : i ⟶ j) (ψ : j ⟶ k) (X : FilteredObject C I)

/-- The inclusion `gr_φ(X) = F^jX/F^iX ⟶ F^kX/F^iX = gr_{φ ≫ ψ}(X)`. -/
noncomputable def grMapCompι : (grMap φ).obj X ⟶ (grMap (φ ≫ ψ)).obj X :=
  grMapDesc φ (X.filtration.step ψ ≫ grMapπ (φ ≫ ψ) X) (by
    rw [Filtration.step_comp_assoc]; exact step_grMapπ _ _)

/-- The projection `gr_{φ ≫ ψ}(X) = F^kX/F^iX ⟶ F^kX/F^jX = gr_ψ(X)`. -/
noncomputable def grMapCompπ : (grMap (φ ≫ ψ)).obj X ⟶ (grMap ψ).obj X :=
  grMapDesc (φ ≫ ψ) (grMapπ ψ X) (by
    rw [← Filtration.step_comp, Category.assoc, step_grMapπ, comp_zero])

/-- The composite `F^jX ⟶ F^jX/F^iX ⟶ F^kX/F^iX` is the inclusion `F^jX ⟶ F^kX` followed by the
projection to `F^kX/F^iX`. -/
@[reassoc (attr := simp)]
lemma grMapπ_grMapCompι :
    grMapπ φ X ≫ grMapCompι φ ψ X = X.filtration.step ψ ≫ grMapπ (φ ≫ ψ) X :=
  grMapπ_desc _ _ _

/-- The composite `F^kX ⟶ F^kX/F^iX ⟶ F^kX/F^jX` is the projection `F^kX ⟶ F^kX/F^jX`. -/
@[reassoc (attr := simp)]
lemma grMapπ_grMapCompπ : grMapπ (φ ≫ ψ) X ≫ grMapCompπ φ ψ X = grMapπ ψ X :=
  grMapπ_desc _ _ _

/-- The composite `F^jX/F^iX ⟶ F^kX/F^iX ⟶ F^kX/F^jX` is zero. -/
@[reassoc (attr := simp)]
lemma grMapCompι_grMapCompπ : grMapCompι φ ψ X ≫ grMapCompπ φ ψ X = 0 := by
  apply grMap_hom_ext
  simp

/-- The short complex `gr_φ(X) ⟶ gr_{φ ≫ ψ}(X) ⟶ gr_ψ(X)`, that is
`F^jX/F^iX ⟶ F^kX/F^iX ⟶ F^kX/F^jX`, for index arrows `φ : i ⟶ j` and `ψ : j ⟶ k`. -/
noncomputable abbrev grMapCompShortComplex : ShortComplex C :=
  ShortComplex.mk (grMapCompι φ ψ X) (grMapCompπ φ ψ X) (grMapCompι_grMapCompπ φ ψ X)

/-- The projection `F^kX/F^iX ⟶ F^kX/F^jX` is an epimorphism. -/
instance : Epi (grMapCompπ φ ψ X) := epi_of_epi_fac (grMapπ_grMapCompπ φ ψ X)

/-- The sequence `0 → F^jX/F^iX → F^kX/F^iX → F^kX/F^jX → 0` is short exact. -/
lemma grMapCompShortComplex_shortExact : (grMapCompShortComplex φ ψ X).ShortExact := by
  have hφψ := (stepShortComplex_shortExact (φ ≫ ψ) X).exact
  have hψ := (stepShortComplex_shortExact ψ X).exact
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hφψ hψ
  have hmono : Mono (grMapCompι φ ψ X) := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro T x hx
    obtain ⟨T₁, w₁, hw₁, x₁, fac₁⟩ := surjective_up_to_refinements_of_epi (grMapπ φ X) x
    obtain ⟨T₂, w₂, hw₂, y, fac₂⟩ := hφψ (x₁ ≫ X.filtration.step ψ) (by
      dsimp
      rw [Category.assoc, ← grMapπ_grMapCompι, ← Category.assoc, ← fac₁, Category.assoc, hx,
        comp_zero])
    have hy : y ≫ X.filtration.step φ = w₂ ≫ x₁ := by
      rw [← cancel_mono (X.filtration.step ψ), Category.assoc, Filtration.step_comp]
      exact fac₂.symm.trans (Category.assoc _ _ _).symm
    refine zero_of_epi_comp w₁ (zero_of_epi_comp w₂ ?_)
    rw [fac₁, ← Category.assoc, ← hy, Category.assoc, step_grMapπ, comp_zero]
  refine ShortComplex.ShortExact.mk' ?_ hmono inferInstance
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  obtain ⟨T₁, w₁, hw₁, x₁, fac₁⟩ := surjective_up_to_refinements_of_epi (grMapπ (φ ≫ ψ) X) x
  obtain ⟨T₂, w₂, hw₂, y, fac₂⟩ := hψ x₁ (by
    dsimp at hx ⊢
    rw [← grMapπ_grMapCompπ, ← Category.assoc, ← fac₁, Category.assoc, hx, comp_zero])
  refine ⟨T₂, w₂ ≫ w₁, epi_comp _ _, y ≫ grMapπ φ X, ?_⟩
  dsimp at fac₂ ⊢
  rw [Category.assoc, fac₁, ← Category.assoc, fac₂, Category.assoc, Category.assoc,
    grMapπ_grMapCompι]

end CategoryTheory.FilteredObject

/-! ### Alternating sums over the antidiagonals -/

/-- Regrouping a finitely supported sum over `ℤ × ℤ` along the antidiagonals `p + q = n`, with
the signs `(-1)^n`. -/
lemma finsum_negOnePow_smul_finsum_eq {M : Type*} [AddCommGroup M] (f : ℤ × ℤ → M)
    (hf : (Function.support f).Finite) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • ∑ᶠ t : ℤ, f (t, n - t) =
      ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • f pq := by
  have hsupp : (Function.support fun nt : ℤ × ℤ =>
      (nt.1.negOnePow : ℤ) • f (nt.2, nt.1 - nt.2)).Finite := by
    refine (hf.preimage (f := fun nt : ℤ × ℤ => (nt.2, nt.1 - nt.2)) ?_).subset ?_
    · intro nt _ nt' _ h
      simp only [Prod.ext_iff] at h
      exact Prod.ext (by omega) (by omega)
    · exact fun nt hnt h => hnt (by simp_all)
  let eqv : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun nt => (nt.2, nt.1 - nt.2)
      invFun := fun pq => (pq.1 + pq.2, pq.1)
      left_inv := fun nt => by simp
      right_inv := fun pq => by simp }
  calc ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • ∑ᶠ t : ℤ, f (t, n - t)
      = ∑ᶠ n : ℤ, ∑ᶠ t : ℤ, (n.negOnePow : ℤ) • f (t, n - t) :=
        finsum_congr fun n => smul_finsum' _ (hf.preimage fun t _ t' _ h => (Prod.ext_iff.1 h).1)
    _ = ∑ᶠ nt : ℤ × ℤ, (nt.1.negOnePow : ℤ) • f (nt.2, nt.1 - nt.2) :=
        (finsum_curry _ hsupp).symm
    _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • f pq :=
        (finsum_congr fun nt => by simp [eqv]).trans (finsum_comp_equiv eqv)

namespace CochainComplex.Filtered

open FilteredObject Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C] (K : Filtered C)

section GradedHomology

/-- The commutation of the inclusion `F^pK^• ⟶ K^•` with the differentials, with target `K^•`. -/
@[reassoc]
private lemma ι_f_d (p n m : ℤ) :
    (K.filtration.ι.app (op p)).f n ≫ K.X.d n m =
      (K.filtration.obj (op p)).d n m ≫ (K.filtration.ι.app (op p)).f m :=
  ((K.filtration.ι.app (op p)).comm n m)

@[reassoc]
private lemma cyclesMap_ι_iCycles (p n : ℤ) :
    HomologicalComplex.cyclesMap (K.filtration.ι.app (op p)) n ≫ K.X.iCycles n =
      (K.filtration.obj (op p)).iCycles n ≫ (K.filtration.ι.app (op p)).f n :=
  HomologicalComplex.cyclesMap_i _ _

@[reassoc]
private lemma homologyπ_homologyMap_ι (p n : ℤ) :
    (K.filtration.obj (op p)).homologyπ n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n =
      HomologicalComplex.cyclesMap (K.filtration.ι.app (op p)) n ≫ K.X.homologyπ n :=
  HomologicalComplex.homologyπ_naturality _ _

/-- A morphism to `K^n` which factors through `F^pK^n` lifts to the term `(F^pK^•)^n`. -/
private lemma exists_lift_step {p n : ℤ} {T : C} {x : T ⟶ K.X.X n}
    (hx : (K.step p n).Factors x) :
    ∃ y : T ⟶ (K.filtration.obj (op p)).X n, y ≫ (K.filtration.ι.app (op p)).f n = x :=
  ⟨(K.step p n).factorThru x hx ≫ (Subobject.underlyingIso _).hom, by
    rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.factorThru_arrow]⟩

private lemma factors_step {p n : ℤ} {T : C} (y : T ⟶ (K.filtration.obj (op p)).X n) :
    (K.step p n).Factors (y ≫ (K.filtration.ι.app (op p)).f n) :=
  (Subobject.mk_factors_iff _ _).2 ⟨y, rfl⟩

/-- A cycle of `K^•` lying in `F^pK^n` is a cycle of `F^pK^•`. -/
private lemma exists_lift_cycles {p n : ℤ} {T : C} {y : T ⟶ K.X.cycles n}
    (hy : (K.step p n).Factors (y ≫ K.X.iCycles n)) :
    ∃ c : T ⟶ (K.filtration.obj (op p)).cycles n,
      c ≫ HomologicalComplex.cyclesMap (K.filtration.ι.app (op p)) n = y := by
  obtain ⟨y₀, hy₀⟩ := K.exists_lift_step hy
  have hy₀d : y₀ ≫ (K.filtration.obj (op p)).d n (n + 1) = 0 := by
    rw [← cancel_mono ((K.filtration.ι.app (op p)).f (n + 1)), zero_comp, Category.assoc,
      ← ι_f_d, ← Category.assoc, hy₀, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  refine ⟨(K.filtration.obj (op p)).liftCycles y₀ (n + 1) (by simp) hy₀d, ?_⟩
  rw [← cancel_mono (K.X.iCycles n), Category.assoc, cyclesMap_ι_iCycles,
    HomologicalComplex.liftCycles_i_assoc, hy₀]

/-- The boundaries `Im(d^{n - 1})` lift to the cycles of `K^•`, with zero cohomology class. -/
private lemma exists_lift_imageSubobject (n : ℤ) :
    ∃ l : (imageSubobject (K.X.d (n - 1) n) : C) ⟶ K.X.cycles n,
      l ≫ K.X.iCycles n = (imageSubobject (K.X.d (n - 1) n)).arrow ∧ l ≫ K.X.homologyπ n = 0 := by
  let l := K.X.liftCycles (imageSubobject (K.X.d (n - 1) n)).arrow (n + 1) (by simp)
    (imageSubobject_arrow_comp_eq_zero (K.X.d_comp_d _ _ _))
  have hl : l ≫ K.X.iCycles n = (imageSubobject (K.X.d (n - 1) n)).arrow :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  refine ⟨l, hl, ?_⟩
  have hfac : factorThruImageSubobject (K.X.d (n - 1) n) ≫ l = K.X.toCycles (n - 1) n := by
    rw [← cancel_mono (K.X.iCycles n), Category.assoc, hl, imageSubobject_arrow_comp,
      HomologicalComplex.toCycles_i]
  rw [← cancel_epi (factorThruImageSubobject (K.X.d (n - 1) n)), comp_zero, ← Category.assoc,
    hfac, HomologicalComplex.toCycles_comp_homologyπ]

/-- `Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n ≤ Ker(d) ∩ F^pK^n` as subobjects of `K^n`. -/
lemma kernel_inf_step_succ_sup_image_inf_step_le (p n : ℤ) :
    kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n ⊔
        imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n ≤
      kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n :=
  sup_le (inf_le_inf_left _ (K.step_antitone n (by omega)))
    (inf_le_inf_right _ (image_le_kernel _ _ (K.X.d_comp_d _ _ _)))

/-- The cycles lying in `F^pK^n` surject onto
`(Ker(d) ∩ F^pK^n)/(Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n)`. -/
private lemma epi_comp_cokernel_π_of_comp_arrow_eq (p n : ℤ)
    (a : (K.cyclesInStep p n : C) ⟶
      (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n : Subobject (K.X.X n)))
    (ha : a ≫ (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n).arrow =
      (K.cyclesInStep p n).arrow ≫ K.X.iCycles n) :
    Epi (a ≫ cokernel.π
      (Subobject.ofLE _ _ (K.kernel_inf_step_succ_sup_image_inf_step_le p n))) := by
  have : Mono (a ≫ (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n).arrow) := by
    rw [ha]
    infer_instance
  have hVd : (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n).arrow ≫ K.X.d n (n + 1) = 0 :=
    Subobject.arrow_comp_eq_zero_of_le_kernelSubobject inf_le_left
  have hlift : (K.cyclesInStep p n).Factors (K.X.liftCycles _ (n + 1) (by simp) hVd) := by
    rw [pullback_factors_iff, HomologicalComplex.liftCycles_i]
    exact Subobject.factors_of_le _ inf_le_right (Subobject.factors_self _)
  refine Subobject.epi_comp_cokernel_π _ (Subobject.ofLE_arrow _) a (le_sup_of_le_left
    (Subobject.le_mk_of_comm ((K.cyclesInStep p n).factorThru _ hlift) ?_)) bot_le
  rw [ha, Subobject.factorThru_arrow_assoc, HomologicalComplex.liftCycles_i]

/-- A cycle in `Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n` has zero class in `gr^pH^n(K^•)`. -/
private lemma comp_cokernel_π_preComp_eq_zero_of_factors (p n : ℤ) {T : C}
    (g : T ⟶ (K.cyclesInStep p n : C)) (b : (K.cyclesInStep p n : C) ⟶
      image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      (K.cyclesInStep p n).arrow ≫ K.X.homologyπ n)
    (hg : (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n ⊔
        imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n).Factors
        (g ≫ (K.cyclesInStep p n).arrow ≫ K.X.iCycles n)) :
    g ≫ b ≫ cokernel.π (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) = 0 := by
  obtain ⟨T', z, hz, β, γ, fac⟩ := Subobject.exists_refinement_of_factors_sup _ hg
  obtain ⟨l, hl, hlπ⟩ := K.exists_lift_imageSubobject n
  have hβd : (β ≫ (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n).arrow) ≫
      K.X.d n (n + 1) = 0 := by
    rw [Category.assoc, Subobject.arrow_comp_eq_zero_of_le_kernelSubobject inf_le_left,
      comp_zero]
  let c := K.X.liftCycles _ (n + 1) (by simp) hβd
  have hc : c ≫ K.X.iCycles n =
      β ≫ (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n).arrow :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  obtain ⟨c', hc'⟩ := K.exists_lift_cycles (p := p + 1) (y := c) (by
    rw [hc]
    exact Subobject.factors_of_le _ inf_le_right (Subobject.factors_comp_arrow _))
  have hdecomp : z ≫ g ≫ (K.cyclesInStep p n).arrow =
      γ ≫ Subobject.ofLE _ _ (inf_le_left : imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n ≤
        imageSubobject (K.X.d (n - 1) n)) ≫ l + c := by
    rw [← cancel_mono (K.X.iCycles n), add_comp, Category.assoc, Category.assoc,
      Category.assoc, Category.assoc, hl, Subobject.ofLE_arrow, hc]
    simpa only [Category.assoc, add_comm] using fac
  let t := c' ≫ (K.filtration.obj (op (p + 1))).homologyπ n ≫
    factorThruImage (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n ≫
      HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)
  have hzt : z ≫ g ≫ b = t ≫ image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) := by
    rw [← cancel_mono (image.ι (HomologicalComplex.homologyMap
      (K.filtration.ι.app (op p)) n)), Category.assoc, Category.assoc, hb,
      ← Category.assoc g, ← Category.assoc z, hdecomp]
    simp only [t, Category.assoc, image.preComp_ι, image.fac, add_comp, hlπ, comp_zero,
      zero_add]
    rw [← HomologicalComplex.homologyMap_comp, K.filtration.diagram_map_comp_ι_app,
      homologyπ_homologyMap_ι, ← Category.assoc, hc']
  refine zero_of_epi_comp z ?_
  rw [← Category.assoc, ← Category.assoc, Category.assoc z, hzt, Category.assoc,
    cokernel.condition, comp_zero]

/-- A cycle with zero class in `gr^pH^n(K^•)` lies in
`Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n`. -/
private lemma factors_of_comp_cokernel_π_preComp_eq_zero (p n : ℤ) {T : C}
    (g : T ⟶ (K.cyclesInStep p n : C)) (b : (K.cyclesInStep p n : C) ⟶
      image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      (K.cyclesInStep p n).arrow ≫ K.X.homologyπ n)
    (hg : g ≫ b ≫ cokernel.π (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) = 0) :
    (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n ⊔
        imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n).Factors
        (g ≫ (K.cyclesInStep p n).arrow ≫ K.X.iCycles n) := by
  obtain ⟨t, ht⟩ : ∃ t, t ≫ image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) = g ≫ b :=
    ⟨Abelian.monoLift _ _ (by simpa only [Category.assoc] using hg), Abelian.monoLift_comp _ _ _⟩
  obtain ⟨T', z, hz, c', hzc⟩ := surjective_up_to_refinements_of_epi
    ((K.filtration.obj (op (p + 1))).homologyπ n ≫
      factorThruImage (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) t
  have hcls : (z ≫ g ≫ (K.cyclesInStep p n).arrow) ≫ K.X.homologyπ n =
      (c' ≫ HomologicalComplex.cyclesMap (K.filtration.ι.app (op (p + 1))) n) ≫
        K.X.homologyπ n := by
    rw [Category.assoc, Category.assoc, ← hb, ← Category.assoc g, ← ht]
    simp only [Category.assoc, image.preComp_ι]
    rw [← Category.assoc z, hzc]
    simp only [Category.assoc, image.fac]
    rw [← HomologicalComplex.homologyMap_comp, K.filtration.diagram_map_comp_ι_app,
      homologyπ_homologyMap_ι]
  obtain ⟨T'', z', hz', x₁, fac⟩ :=
    (K.X.comp_homologyπ_eq_iff_up_to_refinements (n - 1) n (by simp) _ _).1 hcls
  refine Subobject.factors_of_epi_comp z _ ?_
  refine Subobject.factors_of_epi_comp z' _ ?_
  have e : z' ≫ z ≫ g ≫ (K.cyclesInStep p n).arrow ≫ K.X.iCycles n =
      ((z' ≫ c' ≫ (K.filtration.obj (op (p + 1))).iCycles n) ≫
        (K.filtration.ι.app (op (p + 1))).f n : T'' ⟶ K.X.X n) + x₁ ≫ K.X.d (n - 1) n := by
    have := congrArg (· ≫ K.X.iCycles n) fac
    simp only [Category.assoc, add_comp, cyclesMap_ι_iCycles,
      HomologicalComplex.toCycles_i] at this
    simpa only [Category.assoc] using this
  have h₁ : (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n).Factors
      ((z' ≫ c' ≫ (K.filtration.obj (op (p + 1))).iCycles n) ≫
        (K.filtration.ι.app (op (p + 1))).f n : T'' ⟶ K.X.X n) :=
    (Subobject.inf_factors _).2 ⟨kernelSubobject_factors _ _ (by
      simp only [Category.assoc, ι_f_d, HomologicalComplex.iCycles_d_assoc, zero_comp,
        comp_zero]), K.factors_step _⟩
  have h₂ : (imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n).Factors
      (x₁ ≫ K.X.d (n - 1) n) := by
    refine (Subobject.inf_factors _).2 ⟨imageSubobject_factors_comp_self _ _, ?_⟩
    rw [show x₁ ≫ K.X.d (n - 1) n = (z' ≫ z ≫ g) ≫ (K.cyclesInStep p n).arrow ≫ K.X.iCycles n -
        ((z' ≫ c' ≫ (K.filtration.obj (op (p + 1))).iCycles n) ≫
          (K.filtration.ι.app (op (p + 1))).f n : T'' ⟶ K.X.X n) by
      rw [Category.assoc, Category.assoc, e]
      abel]
    exact Subobject.factors_sub _ _ (Subobject.factors_of_factors_right _
      ((pullback_factors_iff _ _ _).1 (Subobject.factors_self _)))
      (Subobject.factors_of_le _ (K.step_antitone n (by omega)) (K.factors_step _))
  simp only [Category.assoc] at e ⊢
  rw [e]
  exact Subobject.factors_add _ _ (Subobject.sup_factors_of_factors_left
    (by simpa only [Category.assoc] using h₁))
    (Subobject.sup_factors_of_factors_right h₂)

/-- **Stacks 0BDT.** The graded piece `gr^pH^n(K^•) = F^pH^n(K^•)/F^{p + 1}H^n(K^•)` of the
filtration induced on cohomology is
`(Ker(d) ∩ F^pK^n)/(Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n)`: there is an isomorphism between the
two compatible with the canonical maps to both from the cycles of `K^•` lying in `F^pK^n`. -/
@[stacks 0BDT]
theorem exists_iso_gradedHomology (p n : ℤ) :
    ∃ (a : (K.cyclesInStep p n : C) ⟶
        (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n : Subobject (K.X.X n)))
      (b : (K.cyclesInStep p n : C) ⟶
        image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
      (e : cokernel (Subobject.ofLE _ _ (K.kernel_inf_step_succ_sup_image_inf_step_le p n)) ≅
        K.gradedHomology p n),
      a ≫ (kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n).arrow =
        (K.cyclesInStep p n).arrow ≫ K.X.iCycles n ∧
      b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
        (K.cyclesInStep p n).arrow ≫ K.X.homologyπ n ∧
      a ≫ cokernel.π (Subobject.ofLE _ _ (K.kernel_inf_step_succ_sup_image_inf_step_le p n)) ≫
          e.hom =
        b ≫ cokernel.π (image.preComp
          (HomologicalComplex.homologyMap (K.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) := by
  set A := K.cyclesInStep p n
  set V := kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n
  set W := kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n ⊔
    imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n
  have hWV : W ≤ V := K.kernel_inf_step_succ_sup_image_inf_step_le p n
  have hAF : (K.step p n).Factors (A.arrow ≫ K.X.iCycles n) :=
    (pullback_factors_iff _ _ _).1 (Subobject.factors_self A)
  have hAV : V.Factors (A.arrow ≫ K.X.iCycles n) :=
    (Subobject.inf_factors _).2 ⟨kernelSubobject_factors _ _ (by
      rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]), hAF⟩
  let a := V.factorThru _ hAV
  have ha : a ≫ V.arrow = A.arrow ≫ K.X.iCycles n := V.factorThru_arrow _ _
  have hu : Epi (a ≫ cokernel.π (Subobject.ofLE W V hWV)) :=
    K.epi_comp_cokernel_π_of_comp_arrow_eq p n a ha
  obtain ⟨w, hw⟩ := K.exists_lift_cycles hAF
  have : Mono (HomologicalComplex.cyclesMap (K.filtration.ι.app (op p)) n) :=
    mono_of_mono_fac (K.cyclesMap_ι_iCycles p n)
  have hAu : A.Factors (HomologicalComplex.cyclesMap (K.filtration.ι.app (op p)) n) := by
    rw [pullback_factors_iff, cyclesMap_ι_iCycles]
    exact K.factors_step _
  have : IsSplitEpi w := IsSplitEpi.mk' ⟨A.factorThru _ hAu, by
    rw [← cancel_mono (HomologicalComplex.cyclesMap (K.filtration.ι.app (op p)) n),
      Category.assoc, hw, A.factorThru_arrow, Category.id_comp]⟩
  let b := w ≫ (K.filtration.obj (op p)).homologyπ n ≫
    factorThruImage (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)
  have hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n := by
    simp only [b, Category.assoc, image.fac, homologyπ_homologyMap_ι]
    rw [← Category.assoc, hw]
  have hv : Epi (b ≫ cokernel.π (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))) := by
    simp only [b]
    infer_instance
  have key : ∀ {T : C} (g : T ⟶ (A : C)),
      g ≫ a ≫ cokernel.π (Subobject.ofLE W V hWV) = 0 ↔
      g ≫ b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) = 0 := by
    intro T g
    rw [← Category.assoc, Subobject.comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow hWV),
      Category.assoc, ha]
    exact ⟨K.comp_cokernel_π_preComp_eq_zero_of_factors p n g b hb,
      K.factors_of_comp_cokernel_π_preComp_eq_zero p n g b hb⟩
  obtain ⟨e, he⟩ := Subobject.exists_iso_of_epi_of_kernel _ _
    ((key _).1 (kernel.condition _)) ((key _).2 (kernel.condition _))
  exact ⟨a, b, e, ha, hb, by simpa only [Category.assoc] using he⟩

end GradedHomology

section FirstPage

open FilteredComplexSpectralSequence

@[reassoc]
private lemma grπ_f_d (p n m : ℤ) :
    (grMapπ (succHom p) K).f n ≫ ((gr p).obj K).d n m =
      (K.filtration.obj (op p)).d n m ≫ (grMapπ (succHom p) K).f m :=
  ((grMapπ (succHom p) K).comm n m)

@[reassoc]
private lemma step_f_grπ_f (p n : ℤ) :
    (K.filtration.step (succHom p)).f n ≫ (grMapπ (succHom p) K).f n = 0 := by
  rw [← HomologicalComplex.comp_f, step_grMapπ, HomologicalComplex.zero_f]

@[reassoc]
private lemma step_f_ι_f (p n : ℤ) :
    (K.filtration.step (succHom p)).f n ≫ (K.filtration.ι.app (op p)).f n =
      (K.filtration.ι.app (op (p + 1))).f n := by
  rw [← HomologicalComplex.comp_f, Filtration.step_comp_ι_app]

/-- The sequence `0 → F^{p + 1}K^n → F^pK^n → gr^pK^n → 0` is short exact. -/
private lemma stepShortComplex_succHom_eval_shortExact (p n : ℤ) :
    ((stepShortComplex (succHom p) K).map (HomologicalComplex.eval _ _ n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (stepShortComplex_shortExact (succHom p) K) n

private lemma epi_grπ_f (p n : ℤ) : Epi ((grMapπ (succHom p) K).f n) :=
  (K.stepShortComplex_succHom_eval_shortExact p n).epi_g

private lemma exists_of_comp_grπ_f_eq_zero {p n : ℤ} {T : C}
    {x : T ⟶ (K.filtration.obj (op p)).X n} (hx : x ≫ (grMapπ (succHom p) K).f n = 0) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ (K.filtration.obj (op (p + 1))).X n),
      π ≫ x = y ≫ (K.filtration.step (succHom p)).f n :=
  (K.stepShortComplex_succHom_eval_shortExact p n).exact.exact_up_to_refinements x hx

/-- An element of `F^pK^n` whose image in `gr^pK^n` is a cycle lies in `Z_1^{p, n - p}`. -/
private lemma factors_cycles_one_of {p n : ℤ} {T : C} {x : T ⟶ (K.filtration.obj (op p)).X n}
    (hx : (x ≫ (grMapπ (succHom p) K).f n) ≫ ((gr p).obj K).d n (n + 1) = 0) :
    (cycles K.X K.step 1 p n).Factors (x ≫ (K.filtration.ι.app (op p)).f n) := by
  rw [Category.assoc, grπ_f_d, ← Category.assoc] at hx
  obtain ⟨T', π, hπ, y, hy⟩ := K.exists_of_comp_grπ_f_eq_zero hx
  rw [FilteredComplexSpectralSequence.cycles]
  refine Subobject.factors_of_epi_comp π _ ((Subobject.inf_factors _).2 ⟨?_, ?_⟩)
  · rw [← Category.assoc]; exact K.factors_step _
  · rw [pullback_factors_iff]
    have : (π ≫ x ≫ (K.filtration.ι.app (op p)).f n) ≫ K.X.d n (n + 1) =
        y ≫ (K.filtration.ι.app (op (p + 1))).f (n + 1) := by
      rw [Category.assoc, Category.assoc, ι_f_d, ← Category.assoc x, ← Category.assoc π, hy,
        Category.assoc, step_f_ι_f]
    rw [this]; exact K.factors_step _

/-- The image in `gr^pK^n` of an element of `Z_1^{p, n - p}` is a cycle. -/
private lemma comp_grπ_d_eq_zero_of_factors {p n : ℤ} {T : C}
    {x : T ⟶ (K.filtration.obj (op p)).X n}
    (hx : (cycles K.X K.step 1 p n).Factors (x ≫ (K.filtration.ι.app (op p)).f n)) :
    (x ≫ (grMapπ (succHom p) K).f n) ≫ ((gr p).obj K).d n (n + 1) = 0 := by
  rw [FilteredComplexSpectralSequence.cycles, Subobject.inf_factors, pullback_factors_iff] at hx
  obtain ⟨y, hy⟩ := K.exists_lift_step hx.2
  have h : x ≫ (K.filtration.obj (op p)).d n (n + 1) =
      y ≫ (K.filtration.step (succHom p)).f (n + 1) := by
    rw [← cancel_mono ((K.filtration.ι.app (op p)).f (n + 1)), Category.assoc, ← ι_f_d,
      Category.assoc, step_f_ι_f, hy, Category.assoc]
  rw [Category.assoc, grπ_f_d, ← Category.assoc, h, Category.assoc, step_f_grπ_f, comp_zero]

private lemma cycles_zero_eq_step (p n : ℤ) : cycles K.X K.step 0 p n = K.step p n := by
  rw [FilteredComplexSpectralSequence.cycles, add_zero, inf_eq_left, Subobject.le_pullback_iff,
    ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, ι_f_d, ← Category.assoc]
  exact K.factors_step _

private lemma boundaries_one_eq (p n : ℤ) :
    boundaries K.X K.step 1 p n =
      K.step (p + 1) n ⊔ (Subobject.exists (K.X.d (n - 1) n)).obj (K.step p (n - 1)) := by
  rw [FilteredComplexSpectralSequence.boundaries, show (1 : ℤ) - 1 = 0 by norm_num,
    show p - 1 + 1 = p by omega, K.cycles_zero_eq_step, K.cycles_zero_eq_step]

private lemma factors_exists_comp {X Y : C} (f : X ⟶ Y) {S : Subobject X} {T : C} {x : T ⟶ X}
    (h : S.Factors x) : ((Subobject.exists f).obj S).Factors (x ≫ f) := by
  rw [← S.factorThru_arrow x h, Category.assoc]
  exact Subobject.factors_of_factors_right _ (Subobject.factors_arrow_comp f S)

/-- The map from `Z_1^{p, q}` to `H^{p + q}(gr^pK^•)` taking `x` to the class of its image in
`gr^pK^{p + q}` is an epimorphism. -/
private lemma epi_liftCycles_comp_homologyπ_gr {p n : ℤ}
    {u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n}
    (hu : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow)
    (hc : (u ≫ (grMapπ (succHom p) K).f n) ≫ ((gr p).obj K).d n (n + 1) = 0) :
    Epi (((gr p).obj K).liftCycles (u ≫ (grMapπ (succHom p) K).f n) (n + 1) (by simp) hc ≫
      ((gr p).obj K).homologyπ n) := by
  have := K.epi_grπ_f p n
  rw [epi_iff_surjective_up_to_refinements]
  intro A γ
  obtain ⟨A₁, π₁, hπ₁, z₀, hz₀, fac₁⟩ :=
    ((gr p).obj K).eq_liftCycles_homologyπ_up_to_refinements γ (n + 1) (by simp)
  obtain ⟨A₂, π₂, hπ₂, x, hx⟩ :=
    surjective_up_to_refinements_of_epi ((grMapπ (succHom p) K).f n) z₀
  have hZx : (cycles K.X K.step 1 p n).Factors (x ≫ (K.filtration.ι.app (op p)).f n) :=
    K.factors_cycles_one_of (by rw [← hx, Category.assoc, hz₀, comp_zero])
  refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, (cycles K.X K.step 1 p n).factorThru _ hZx, ?_⟩
  have hs : (cycles K.X K.step 1 p n).factorThru _ hZx ≫ u = x := by
    rw [← cancel_mono ((K.filtration.ι.app (op p)).f n), Category.assoc, hu,
      Subobject.factorThru_arrow]
  rw [Category.assoc, fac₁, ← Category.assoc,
    ← Category.assoc ((cycles K.X K.step 1 p n).factorThru _ hZx)]
  congr 1
  rw [← cancel_mono (((gr p).obj K).iCycles n)]
  simp only [Category.assoc, HomologicalComplex.liftCycles_i]
  rw [hx, ← Category.assoc, hs]

/-- An element of `Z_1^{p, q}` lying in `D_1^{p, q}` maps to a boundary in `gr^pK^•`, up to
refinement. -/
private lemma exists_comp_grπ_eq_d_of_factors_boundaries {p n : ℤ}
    {u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n}
    (hu : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow) {T : C}
    (g : T ⟶ (cycles K.X K.step 1 p n : C))
    (hD : (boundaries K.X K.step 1 p n).Factors (g ≫ (cycles K.X K.step 1 p n).arrow)) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (x₁ : T' ⟶ ((gr p).obj K).X (n - 1)),
      π ≫ g ≫ u ≫ (grMapπ (succHom p) K).f n = x₁ ≫ ((gr p).obj K).d (n - 1) n := by
  rw [K.boundaries_one_eq p n] at hD
  obtain ⟨T₁, z, hz, β, γ, fac⟩ := Subobject.exists_refinement_of_factors_sup _ hD
  have hγ : (imageSubobject ((K.step p (n - 1)).arrow ≫ K.X.d (n - 1) n)).Factors
      (γ ≫ ((Subobject.exists (K.X.d (n - 1) n)).obj (K.step p (n - 1))).arrow) := by
    rw [← Subobject.exists_eq_imageSubobject]
    exact Subobject.factors_comp_arrow γ
  obtain ⟨T₂, z', hz', x, hx⟩ := (Subobject.imageSubobject_factors_iff _ _).1 hγ
  obtain ⟨b', hb'⟩ := K.exists_lift_step (p := p + 1)
    (x := β ≫ (K.step (p + 1) n).arrow) (Subobject.factors_comp_arrow _)
  obtain ⟨x', hx'⟩ := K.exists_lift_step (p := p) (n := n - 1)
    (x := x ≫ (K.step p (n - 1)).arrow) (Subobject.factors_comp_arrow _)
  have e1 : z' ≫ z ≫ g ≫ (cycles K.X K.step 1 p n).arrow = z' ≫ β ≫ (K.step (p + 1) n).arrow +
      x ≫ (K.step p (n - 1)).arrow ≫ K.X.d (n - 1) n := by
    rw [fac, Preadditive.comp_add, hx]
  refine ⟨T₂, z' ≫ z, epi_comp _ _, x' ≫ (grMapπ (succHom p) K).f (n - 1), ?_⟩
  have hdec : (z' ≫ z) ≫ g ≫ u = (z' ≫ b') ≫ (K.filtration.step (succHom p)).f n +
      x' ≫ (K.filtration.obj (op p)).d (n - 1) n := by
    rw [← cancel_mono ((K.filtration.ι.app (op p)).f n)]
    simp only [Category.assoc, add_comp, hu, step_f_ι_f, hb', ← ι_f_d]
    rw [← Category.assoc x', hx', Category.assoc, e1]
  rw [show (z' ≫ z) ≫ g ≫ u ≫ (grMapπ (succHom p) K).f n =
      ((z' ≫ z) ≫ g ≫ u) ≫ (grMapπ (succHom p) K).f n by simp only [Category.assoc],
    hdec, add_comp, Category.assoc, Category.assoc, step_f_grπ_f, comp_zero, comp_zero,
    zero_add, Category.assoc, Category.assoc, grπ_f_d]

/-- An element of `Z_1^{p, q}` mapping to a boundary in `gr^pK^•`, up to refinement, lies in
`D_1^{p, q}`. -/
private lemma factors_boundaries_of_exists_comp_grπ_eq_d {p n : ℤ}
    {u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n}
    (hu : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow) {T : C}
    (g : T ⟶ (cycles K.X K.step 1 p n : C))
    (h : ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (x₁ : T' ⟶ ((gr p).obj K).X (n - 1)),
      π ≫ g ≫ u ≫ (grMapπ (succHom p) K).f n = x₁ ≫ ((gr p).obj K).d (n - 1) n) :
    (boundaries K.X K.step 1 p n).Factors (g ≫ (cycles K.X K.step 1 p n).arrow) := by
  have := K.epi_grπ_f p (n - 1)
  obtain ⟨T₁, π, hπ, x₁, hx₁⟩ := h
  obtain ⟨T₂, π', hπ', x₁', hx₁'⟩ :=
    surjective_up_to_refinements_of_epi ((grMapπ (succHom p) K).f (n - 1)) x₁
  have h0 : (π' ≫ π ≫ g ≫ u - x₁' ≫ (K.filtration.obj (op p)).d (n - 1) n) ≫
      (grMapπ (succHom p) K).f n = 0 := by
    simp only [sub_comp, Category.assoc, ← grπ_f_d]
    rw [hx₁, ← Category.assoc x₁', ← hx₁', Category.assoc, sub_self]
  obtain ⟨T₃, π'', hπ'', y, hy⟩ := K.exists_of_comp_grπ_f_eq_zero h0
  refine Subobject.factors_of_epi_comp (π'' ≫ π' ≫ π) _ ?_
  rw [K.boundaries_one_eq p n]
  have e2 : (π'' ≫ π' ≫ π) ≫ g ≫ (cycles K.X K.step 1 p n).arrow =
      (y ≫ (K.filtration.ι.app (op (p + 1))).f n : T₃ ⟶ K.X.X n) +
        (π'' ≫ x₁' ≫ (K.filtration.ι.app (op p)).f (n - 1)) ≫ K.X.d (n - 1) n := by
    rw [← hu]
    have := congrArg (· ≫ (K.filtration.ι.app (op p)).f n) hy
    simp only [Preadditive.comp_sub, sub_comp, Category.assoc, step_f_ι_f] at this
    simp only [Category.assoc, ι_f_d]
    rw [← this]
    abel
  rw [e2]
  exact Subobject.factors_add _ _ (Subobject.sup_factors_of_factors_left (K.factors_step _))
    (Subobject.sup_factors_of_factors_right (factors_exists_comp _
      (by simpa only [Category.assoc] using K.factors_step (π'' ≫ x₁'))))

/-- Every element of `Z_1^{p, n - p}` lifts to `F^pK^n`, with image in `gr^pK^n` a cycle. -/
private lemma exists_lift_cycles_one (p n : ℤ) :
    ∃ u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n,
      u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow ∧
      (u ≫ (grMapπ (succHom p) K).f n) ≫ ((gr p).obj K).d n (n + 1) = 0 := by
  obtain ⟨u, hu⟩ := K.exists_lift_step (x := (cycles K.X K.step 1 p n).arrow)
    (Subobject.factors_of_le _ (cycles_le_F _ _ _ _ _) (Subobject.factors_self _))
  exact ⟨u, hu, K.comp_grπ_d_eq_zero_of_factors (by rw [hu]; exact Subobject.factors_self _)⟩

/-- `E_1^{p, q} = Z_1^{p, q}/(D_1^{p, q} ∩ Z_1^{p, q})` is `H^{p + q}(gr^pK^•)`, the class of `x`
going to the class of its image in `gr^pK^{p + q}`. -/
private lemma exists_iso_cokernel_homology_gr (p n : ℤ) :
    ∃ ε : cokernel (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step 1 p n ⊓
        cycles K.X K.step 1 p n ≤ cycles K.X K.step 1 p n)) ≅ ((gr p).obj K).homology n,
      ∀ (u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n)
        (_ : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow)
        (hc : (u ≫ (grMapπ (succHom p) K).f n) ≫ ((gr p).obj K).d n (n + 1) = 0),
        cokernel.π _ ≫ ε.hom =
          ((gr p).obj K).liftCycles (u ≫ (grMapπ (succHom p) K).f n) (n + 1) (by simp) hc ≫
            ((gr p).obj K).homologyπ n := by
  set Z := cycles K.X K.step 1 p n
  obtain ⟨u, hu, hc⟩ := K.exists_lift_cycles_one p n
  set v := ((gr p).obj K).liftCycles (u ≫ (grMapπ (succHom p) K).f n) (n + 1) (by simp) hc ≫
    ((gr p).obj K).homologyπ n with hvdef
  have hv : Epi v := K.epi_liftCycles_comp_homologyπ_gr hu hc
  have key : ∀ {T : C} (g : T ⟶ (Z : C)),
      g ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step 1 p n ⊓ Z ≤ Z)) =
        0 ↔ g ≫ v = 0 := by
    intro T g
    rw [Subobject.comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow _), Subobject.inf_factors]
    have hv' : g ≫ v = ((gr p).obj K).liftCycles (g ≫ u ≫ (grMapπ (succHom p) K).f n) (n + 1)
        (by simp) (by rw [Category.assoc, hc, comp_zero]) ≫ ((gr p).obj K).homologyπ n := by
      rw [hvdef, ← Category.assoc, HomologicalComplex.comp_liftCycles]
    rw [hv', ((gr p).obj K).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements (n - 1) n
      (n + 1) (by simp) (by simp)]
    exact ⟨fun ⟨hD, _⟩ => K.exists_comp_grπ_eq_d_of_factors_boundaries hu g hD, fun h =>
      ⟨K.factors_boundaries_of_exists_comp_grπ_eq_d hu g h, Subobject.factors_comp_arrow g⟩⟩
  obtain ⟨ε, hε⟩ := Subobject.exists_iso_of_epi_of_kernel (cokernel.π _) v
    ((key _).1 (kernel.condition _)) ((key _).2 (kernel.condition _))
  refine ⟨ε, fun u' hu' hc' => ?_⟩
  obtain rfl : u' = u := by rw [← cancel_mono ((K.filtration.ι.app (op p)).f n), hu, hu']
  exact hε

/-- The differential vanishes on the graded pieces `gr^pK^•` as soon as `d(F^pK) ⊆ F^{p + 1}K`
for all `p`. -/
lemma gr_d_eq_zero
    (hd : ∀ p n : ℤ, (K.step (p + 1) (n + 1)).Factors ((K.step p n).arrow ≫ K.X.d n (n + 1)))
    (p i j : ℤ) : ((gr p).obj K).d i j = 0 := by
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · obtain rfl : i + 1 = j := hij
    have := K.epi_grπ_f p i
    rw [← cancel_epi ((grMapπ (succHom p) K).f i), comp_zero, grπ_f_d]
    obtain ⟨v, hv⟩ := K.exists_lift_step (hd p i)
    have : (K.filtration.obj (op p)).d i (i + 1) =
        ((Subobject.underlyingIso ((K.filtration.ι.app (op p)).f i)).inv ≫ v) ≫
          (K.filtration.step (succHom p)).f (i + 1) := by
      rw [← cancel_mono ((K.filtration.ι.app (op p)).f (i + 1)), ← ι_f_d, Category.assoc,
        Category.assoc, step_f_ι_f, hv, ← Category.assoc, Subobject.underlyingIso_arrow]
    rw [this, Category.assoc, step_f_grπ_f, comp_zero]
  · exact ((gr p).obj K).shape _ _ hij

variable (E : CohomologicalSpectralSequence C 0)
  (e : ∀ (p q n : ℤ) (_ : n = p + q), (E.page 1).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right :
      boundaries K.X K.step 1 p n ⊓ cycles K.X K.step 1 p n ≤ cycles K.X K.step 1 p n)))
  (hδ : ∀ (p q n : ℤ) (hn : n = p + q),
    ∃ δ : (cycles K.X K.step 1 p n : C) ⟶ (cycles K.X K.step 1 (p + 1) (n + 1) : C),
      δ ≫ (cycles K.X K.step 1 (p + 1) (n + 1)).arrow =
        (cycles K.X K.step 1 p n).arrow ≫ K.X.d n (n + 1) ∧
      cokernel.π (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step 1 p n ⊓
          cycles K.X K.step 1 p n ≤ cycles K.X K.step 1 p n)) ≫
          (e p q n hn).inv ≫ (E.page 1).d (p, q) (p + 1, q) =
        δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
            boundaries K.X K.step 1 (p + 1) (n + 1) ⊓ cycles K.X K.step 1 (p + 1) (n + 1) ≤
              cycles K.X K.step 1 (p + 1) (n + 1))) ≫
          (e (p + 1) q (n + 1) (by omega)).inv)

include hδ in
/-- **Stacks 012N (1).** Let `E` be the spectral sequence of the filtered complex `K`, presented
on its first page as in [Stacks, Tag 012M]: `E_1^{p, q} = Z_1^{p, q}/(D_1^{p, q} ∩ Z_1^{p, q})`,
with `d_1` induced by `d`. Then `E_1^{p, q} = H^{p + q}(gr^pK^•)`, the class of
`x ∈ Z_1^{p, q} ⊆ F^pK^{p + q}` going to the class of its image in `gr^pK^{p + q}`, and under
these identifications `d_1^{p, q}` is the boundary map in cohomology of the short exact sequence
of complexes `0 → gr^{p + 1}K^• → F^pK^•/F^{p + 2}K^• → gr^pK^• → 0`. -/
@[stacks 012N "(1)"]
theorem exists_iso_firstPage_homology_d_eq_δ :
    ∃ ε : ∀ (p q n : ℤ) (_ : n = p + q),
        (E.page 1).X (p, q) ≅ ((gr p).obj K).homology n,
      (∀ (p q n : ℤ) (hn : n = p + q)
          (u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n)
          (_ : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow)
          (hc : (u ≫ (grMapπ (succHom p) K).f n) ≫ ((gr p).obj K).d n (n + 1) = 0),
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step 1 p n ⊓
            cycles K.X K.step 1 p n ≤ cycles K.X K.step 1 p n)) ≫
            (e p q n hn).inv ≫ (ε p q n hn).hom =
          ((gr p).obj K).liftCycles (u ≫ (grMapπ (succHom p) K).f n) (n + 1) (by simp) hc ≫
            ((gr p).obj K).homologyπ n) ∧
      ∀ (p q n : ℤ) (hn : n = p + q),
        (E.page 1).d (p, q) (p + 1, q) ≫ (ε (p + 1) q (n + 1) (by omega)).hom =
          (ε p q n hn).hom ≫
            (grMapCompShortComplex_shortExact (succHom (p + 1)) (succHom p) K).δ n (n + 1)
              (by simp) := by
  choose ε₀ hε₀ using K.exists_iso_cokernel_homology_gr
  refine ⟨fun p q n hn => e p q n hn ≪≫ ε₀ p n, fun p q n hn u hu hc => ?_,
    fun p q n hn => ?_⟩
  · simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
    exact hε₀ p n u hu hc
  · obtain ⟨δc, hδc, hδ'⟩ := hδ p q n hn
    obtain ⟨u, hu, hc⟩ := K.exists_lift_cycles_one p n
    obtain ⟨u', hu', hc'⟩ := K.exists_lift_cycles_one (p + 1) (n + 1)
    have hδu : δc ≫ u' ≫ (K.filtration.step (succHom p)).f (n + 1) =
        u ≫ (K.filtration.obj (op p)).d n (n + 1) := by
      rw [← cancel_mono ((K.filtration.ι.app (op p)).f (n + 1)), Category.assoc, Category.assoc,
        step_f_ι_f, hu', hδc, Category.assoc, ← ι_f_d, ← Category.assoc, hu]
    rw [← cancel_epi (e p q n hn).inv, ← cancel_epi (cokernel.π _)]
    simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hδ', Iso.inv_hom_id_assoc, hε₀ (p + 1) (n + 1) u' hu' hc',
      reassoc_of% (hε₀ p n u hu hc)]
    rw [(grMapCompShortComplex_shortExact (succHom (p + 1)) (succHom p) K).δ_eq n (n + 1)
      (by simp) (u ≫ (grMapπ (succHom p) K).f n) hc
      (u ≫ (grMapπ (succHom (p + 1) ≫ succHom p) K).f n) (by
        dsimp
        rw [Category.assoc, ← HomologicalComplex.comp_f, grMapπ_grMapCompπ])
      (δc ≫ u' ≫ (grMapπ (succHom (p + 1)) K).f (n + 1)) (by
        dsimp
        rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, grMapπ_grMapCompι,
          HomologicalComplex.comp_f, ← Category.assoc u', ← Category.assoc δc, hδu,
          Category.assoc, Category.assoc, (grMapπ (succHom (p + 1) ≫ succHom p) K).comm])
      (n + 1 + 1) (by simp)]
    rw [← Category.assoc, HomologicalComplex.comp_liftCycles]

include hδ in
/-- **Stacks 012N (2).** If `d(F^pK) ⊆ F^{p + 1}K` for all `p`, then `d` induces the zero
differential on every `gr^pK^•`, so that `E_1^{p, q} = gr^pK^{p + q}`, the class of
`x ∈ Z_1^{p, q} = F^pK^{p + q}` going to its image; and under these identifications `d_1^{p, q}`
is the morphism `gr^pK^{p + q} → gr^{p + 1}K^{p + q + 1}` induced by `d`. -/
@[stacks 012N "(2)"]
theorem d_gr_eq_zero_and_exists_iso_firstPage_d_eq
    (hd : ∀ p n : ℤ, (K.step (p + 1) (n + 1)).Factors ((K.step p n).arrow ≫ K.X.d n (n + 1))) :
    (∀ p i j : ℤ, ((gr p).obj K).d i j = 0) ∧
    ∃ ε : ∀ (p q n : ℤ) (_ : n = p + q), (E.page 1).X (p, q) ≅ ((gr p).obj K).X n,
      (∀ (p q n : ℤ) (hn : n = p + q)
          (u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n)
          (_ : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow),
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step 1 p n ⊓
            cycles K.X K.step 1 p n ≤ cycles K.X K.step 1 p n)) ≫
            (e p q n hn).inv ≫ (ε p q n hn).hom =
          u ≫ (grMapπ (succHom p) K).f n) ∧
      ∀ (p q n : ℤ) (hn : n = p + q), ∃ μ : ((gr p).obj K).X n ⟶ ((gr (p + 1)).obj K).X (n + 1),
        (∀ (v : (K.filtration.obj (op p)).X n ⟶ (K.filtration.obj (op (p + 1))).X (n + 1)),
          v ≫ (K.filtration.ι.app (op (p + 1))).f (n + 1) =
              (K.filtration.ι.app (op p)).f n ≫ K.X.d n (n + 1) →
            (grMapπ (succHom p) K).f n ≫ μ = v ≫ (grMapπ (succHom (p + 1)) K).f (n + 1)) ∧
        (E.page 1).d (p, q) (p + 1, q) ≫ (ε (p + 1) q (n + 1) (by omega)).hom =
          (ε p q n hn).hom ≫ μ := by
  have h0 := K.gr_d_eq_zero hd
  obtain ⟨ε, hε, -⟩ := K.exists_iso_firstPage_homology_d_eq_δ E e hδ
  let ιso : ∀ p n : ℤ, ((gr p).obj K).homology n ≅ ((gr p).obj K).X n := fun p n =>
    (((gr p).obj K).isoHomologyπ (n - 1) n (by simp) (h0 _ _ _)).symm ≪≫
      ((gr p).obj K).iCyclesIso n (n + 1) (by simp) (h0 _ _ _)
  have hpin : ∀ (p q n : ℤ) (hn : n = p + q)
      (u : (cycles K.X K.step 1 p n : C) ⟶ (K.filtration.obj (op p)).X n)
      (_ : u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X K.step 1 p n).arrow),
      cokernel.π (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step 1 p n ⊓
          cycles K.X K.step 1 p n ≤ cycles K.X K.step 1 p n)) ≫
          (e p q n hn).inv ≫ (ε p q n hn ≪≫ ιso p n).hom =
        u ≫ (grMapπ (succHom p) K).f n := by
    intro p q n hn u hu
    simp only [Iso.trans_hom, Iso.symm_hom, ιso]
    rw [reassoc_of% (hε p q n hn u hu (by rw [Category.assoc, h0, comp_zero, comp_zero]))]
    simp
  refine ⟨h0, fun p q n hn => ε p q n hn ≪≫ ιso p n, hpin, fun p q n hn => ?_⟩
  obtain ⟨v₀, hv₀⟩ := K.exists_lift_step (p := p + 1) (n := n + 1)
    (x := (K.filtration.ι.app (op p)).f n ≫ K.X.d n (n + 1)) (by
      rw [← Subobject.underlyingIso_arrow ((K.filtration.ι.app (op p)).f n), Category.assoc]
      exact Subobject.factors_of_factors_right _ (hd p n))
  have hstep : (K.filtration.step (succHom p)).f n ≫ v₀ =
      (K.filtration.obj (op (p + 1))).d n (n + 1) := by
    rw [← cancel_mono ((K.filtration.ι.app (op (p + 1))).f (n + 1)), Category.assoc, hv₀,
      ← Category.assoc, step_f_ι_f, ι_f_d]
  obtain ⟨μ, hμ⟩ :=
    Cofork.IsColimit.desc' (K.stepShortComplex_succHom_eval_shortExact p n).gIsCokernel
      (v₀ ≫ (grMapπ (succHom (p + 1)) K).f (n + 1)) (by
        dsimp
        rw [← Category.assoc, hstep, ← grπ_f_d, h0, comp_zero, zero_comp])
  have hμ' : (grMapπ (succHom p) K).f n ≫ μ = v₀ ≫ (grMapπ (succHom (p + 1)) K).f (n + 1) := hμ
  refine ⟨μ, fun v hv => ?_, ?_⟩
  · obtain rfl : v = v₀ := by
      rw [← cancel_mono ((K.filtration.ι.app (op (p + 1))).f (n + 1)), hv, hv₀]
    exact hμ'
  · obtain ⟨δc, hδc, hδ'⟩ := hδ p q n hn
    obtain ⟨u, hu, -⟩ := K.exists_lift_cycles_one p n
    obtain ⟨u', hu', -⟩ := K.exists_lift_cycles_one (p + 1) (n + 1)
    have hδu : δc ≫ u' = u ≫ v₀ := by
      rw [← cancel_mono ((K.filtration.ι.app (op (p + 1))).f (n + 1)), Category.assoc, hu', hδc,
        Category.assoc, hv₀, ← Category.assoc, hu]
    rw [← cancel_epi (e p q n hn).inv, ← cancel_epi (cokernel.π _), reassoc_of% hδ',
      hpin (p + 1) q (n + 1) (by omega) u' hu', reassoc_of% (hpin p q n hn u hu), hμ',
      ← Category.assoc, hδu, Category.assoc]

end FirstPage

section Stabilization

open FilteredComplexSpectralSequence

private lemma exists_step_eq_top_bot (hK : K.filtration.IsDegreewiseFinite) (m : ℤ) :
    (∃ a : ℤ, ∀ t ≤ a, K.step t m = ⊤) ∧ ∃ b : ℤ, ∀ t, b ≤ t → K.step t m = ⊥ := by
  obtain ⟨p₀, q₀, hiso, hzero⟩ := hK m
  refine ⟨⟨p₀, fun t ht => top_le_iff.1 ?_⟩, ⟨q₀, fun t ht => le_bot_iff.1 ?_⟩⟩
  · rw [← Subobject.mk_eq_top_of_isIso ((K.filtration.ι.app (op p₀)).f m)]
    exact K.step_antitone m ht
  · refine (K.step_antitone m ht).trans (le_of_eq ?_)
    rw [Subobject.mk_eq_bot_iff_zero]
    exact hzero.eq_of_src _ _

/-- For a filtration which is finite in each degree, `E_s^{p, q} = gr^pH^{p + q}(K^•)` for
`s ≫ 0`: the cycles `Z_s^{p, q}` and boundaries `D_s^{p, q}` become `Ker(d) ∩ F^pK^n` and
`Ker(d) ∩ F^{p + 1}K^n + Im(d) ∩ F^pK^n`, and [Stacks, Tag 0BDT] applies. -/
private lemma exists_page_iso_gradedHomology (hK : K.filtration.IsDegreewiseFinite)
    (E : CohomologicalSpectralSequence C 0)
    (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step r p n ⊓
        cycles K.X K.step r p n ≤ cycles K.X K.step r p n)))
    (p q n : ℤ) (hn : n = p + q) :
    ∃ s₀ : ℤ, ∀ (s : ℤ) (hs : 0 ≤ s), s₀ ≤ s →
      Nonempty ((E.page s hs).X (p, q) ≅ K.gradedHomology p n) := by
  obtain ⟨-, b, hb⟩ := K.exists_step_eq_top_bot hK (n + 1)
  obtain ⟨⟨a, ha⟩, -⟩ := K.exists_step_eq_top_bot hK (n - 1)
  refine ⟨max (b - p) (p + 1 - a), fun s hs hs₀ => ?_⟩
  have h₁ : K.step (p + s) (n + 1) = ⊥ := hb _ (by omega)
  have h₂ : K.step (p - s + 1) (n - 1) = ⊤ := ha _ (by omega)
  have hZ : cycles K.X K.step s p n = kernelSubobject (K.X.d n (n + 1)) ⊓ K.step p n := by
    rw [FilteredComplexSpectralSequence.cycles, h₁, Subobject.pullback_bot, inf_comm]
  have hD : boundaries K.X K.step s p n =
      kernelSubobject (K.X.d n (n + 1)) ⊓ K.step (p + 1) n ⊔
        imageSubobject (K.X.d (n - 1) n) ⊓ K.step p n := by
    rw [FilteredComplexSpectralSequence.boundaries, FilteredComplexSpectralSequence.cycles,
      FilteredComplexSpectralSequence.cycles, show p + 1 + (s - 1) = p + s by omega,
      show n - 1 + 1 = n by omega, show p - s + 1 + (s - 1) = p by omega, h₁, h₂,
      Subobject.pullback_bot, top_inf_eq, Abelian.Subobject.exists_pullback_eq_inf,
      inf_comm (K.step (p + 1) n), inf_comm (K.step p n)]
  obtain ⟨-, -, e', -, -, -⟩ := K.exists_iso_gradedHomology p n
  let φ := Subobject.cokernelOfLEIsoOfEq
    (inf_le_right : boundaries K.X K.step s p n ⊓ cycles K.X K.step s p n ≤
      cycles K.X K.step s p n) (K.kernel_inf_step_succ_sup_image_inf_step_le p n)
    (by rw [hD, hZ]; exact inf_eq_left.2 (K.kernel_inf_step_succ_sup_image_inf_step_le p n)) hZ
  exact ⟨e s p q n hs hn ≪≫ φ ≪≫ e'⟩

end Stabilization

section EulerCharacteristic

variable (P : ObjectProperty C) [P.IsWeakSerreClass]

open Classical in
/-- The class in `K₀(P)` of an object of `C`, set to zero outside of `P`. -/
private noncomputable def cl (X : C) : KZero P.FullSubcategory :=
  if h : P X then KZero.mk _ ⟨X, h⟩ else 0

private lemma cl_of_prop {X : C} (h : P X) : cl P X = KZero.mk _ ⟨X, h⟩ := by
  simp [cl, h]

private lemma cl_ι_obj (Y : P.FullSubcategory) : cl P (P.ι.obj Y) = KZero.mk _ Y :=
  cl_of_prop P Y.property

private lemma cl_eq_zero_of_isZero {X : C} (h : IsZero X) : cl P X = 0 := by
  by_cases hX : P X
  · rw [cl_of_prop P hX]
    exact KZero.mk_eq_zero_of_isZero
      ((IsZero.iff_id_eq_zero _).2 (P.ι.map_injective (h.eq_of_src _ _)))
  · simp [cl, hX]

private lemma cl_congr {X Y : C} (e : X ≅ Y) : cl P X = cl P Y := by
  by_cases hX : P X
  · have hY : P Y := P.prop_of_iso e hX
    rw [cl_of_prop P hX, cl_of_prop P hY]
    exact KZero.mk_eq_of_iso (P.isoMk e)
  · have hY : ¬ P Y := fun hY => hX (P.prop_of_iso e.symm hY)
    simp [cl, hX, hY]

/-- A short complex of `C` with terms in `P`, as a short complex of `P`. -/
private abbrev liftShortComplex (S : ShortComplex C) (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    ShortComplex P.FullSubcategory :=
  ShortComplex.mk (X₁ := ⟨S.X₁, h₁⟩) (X₂ := ⟨S.X₂, h₂⟩) (X₃ := ⟨S.X₃, h₃⟩)
    (ObjectProperty.homMk S.f) (ObjectProperty.homMk S.g) (by ext; exact S.zero)

private lemma cl_shortExact {S : ShortComplex C} (hS : S.ShortExact) (h₁ : P S.X₁)
    (h₂ : P S.X₂) (h₃ : P S.X₃) : cl P S.X₂ = cl P S.X₁ + cl P S.X₃ := by
  have := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  have := hS.mono_f
  have := hS.epi_g
  have hS' : (liftShortComplex P S h₁ h₂ h₃).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [← ShortComplex.exact_map_iff_of_faithful _ P.ι]
      exact hS.exact
    · exact P.ι.mono_of_mono_map (show Mono S.f from inferInstance)
    · exact P.ι.epi_of_epi_map (show Epi S.g from inferInstance)
  rw [cl_of_prop P h₁, cl_of_prop P h₂, cl_of_prop P h₃]
  exact KZero.mk_of_shortExact _ hS'

private lemma cl_homology_add (S : ShortComplex C) (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) :
    cl P S.homology + cl P S.X₁ = cl P (kernel S.f) + cl P (kernel S.g) := by
  have := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  set S' := liftShortComplex P S h₁ h₂ h₃
  have e : S'.map P.ι ≅ S := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [S']) (by simp [S'])
  have eH : P.ι.obj S'.homology ≅ S.homology :=
    (S'.mapHomologyIso P.ι).symm ≪≫ ShortComplex.homologyMapIso e
  have ek₁ : P.ι.obj (kernel S'.f) ≅ kernel S.f :=
    PreservesKernel.iso P.ι S'.f ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp [S'])
  have ek₂ : P.ι.obj (kernel S'.g) ≅ kernel S.g :=
    PreservesKernel.iso P.ι S'.g ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp [S'])
  rw [← cl_congr P eH, ← cl_congr P ek₁, ← cl_congr P ek₂, cl_ι_obj, cl_ι_obj, cl_ι_obj,
    cl_of_prop P h₁]
  exact KZero.mk_homology_add_mk_X₁ S'

private lemma prop_homology_of_prop (S : ShortComplex C) (h₁ : P S.X₁) (h₂ : P S.X₂)
    (h₃ : P S.X₃) : P S.homology := by
  have hc : P S.cycles :=
    P.prop_of_iso (S.cyclesIsKernel.conePointUniqueUpToIso (limit.isLimit _)).symm
      (P.prop_kernel _ h₂ h₃)
  exact P.prop_of_iso ((cokernelIsCokernel _).coconePointUniqueUpToIso S.homologyIsCokernel)
    (P.prop_cokernel _ h₁ hc)

/-- **The Euler characteristic of a complex is that of its cohomology.** For a complex `X`
indexed by `ℤ × ℤ`, with differentials of total degree `1` and only finitely many nonzero terms,
all in `P`, `∑ (-1)^{p + q} [X^{p, q}] = ∑ (-1)^{p + q} [H^{p, q}(X)]` in `K₀(P)`. -/
private lemma finsum_cl_eq_finsum_cl_homology (a : ℤ × ℤ) (ha : a.1 + a.2 = 1)
    (X : HomologicalComplex C (ComplexShape.up' a)) (hP : ∀ i, P (X.X i))
    (hfin : {i | ¬ IsZero (X.X i)}.Finite) :
    ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) • cl P (X.X i) =
      ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) • cl P (X.homology i) := by
  set ε : ℤ × ℤ → ℤ := fun i => ((i.1 + i.2).negOnePow : ℤ) with hεdef
  have hε : ∀ i, ε (i - a) = - ε i := by
    intro i
    simp only [hεdef, Prod.fst_sub, Prod.snd_sub]
    rw [show i.1 + i.2 = (i.1 - a.1 + (i.2 - a.2)) + 1 by omega, Int.negOnePow_succ]
    simp
  set k : ℤ × ℤ → KZero P.FullSubcategory := fun i => cl P (kernel (X.d i (i + a)))
  set g : ℤ × ℤ → KZero P.FullSubcategory := fun i => ε i • (k i - cl P (X.X i)) with hgdef
  have hprev : ∀ i, (ComplexShape.up' a).prev i = i - a := fun i =>
    (ComplexShape.up' a).prev_eq' (show i - a + a = i from sub_add_cancel i a)
  have hnext : ∀ i, (ComplexShape.up' a).next i = i + a := fun i =>
    (ComplexShape.up' a).next_eq' rfl
  have key : ∀ i, ε i • cl P (X.homology i) - ε i • cl P (X.X i) = g i - g (i - a) := by
    intro i
    have h := cl_homology_add P (X.sc' (i - a) i (i + a)) (hP _) (hP _) (hP _)
    rw [← cl_congr P (X.homologyIsoSc' (i - a) i (i + a) (hprev i) (hnext i))] at h
    have hk : cl P (kernel (X.sc' (i - a) i (i + a)).f) = k (i - a) := by
      change cl P (kernel (X.d (i - a) i)) = cl P (kernel (X.d (i - a) (i - a + a)))
      rw [sub_add_cancel]
    change cl P (X.homology i) + cl P (X.X (i - a)) = cl P (kernel (X.sc' (i - a) i (i + a)).f) +
      k i at h
    rw [hk] at h
    have hh : cl P (X.homology i) = k (i - a) + k i - cl P (X.X (i - a)) := eq_sub_of_add_eq h
    simp only [hgdef, hε, hh, smul_sub, smul_add, neg_smul]
    abel
  have hzero : ∀ i, IsZero (X.X i) → g i = 0 ∧ cl P (X.X i) = 0 ∧ cl P (X.homology i) = 0 := by
    intro i hi
    have hx := cl_eq_zero_of_isZero P hi
    refine ⟨?_, hx, cl_eq_zero_of_isZero P (ShortComplex.isZero_homology_of_isZero_X₂ _ hi)⟩
    simp only [hgdef, k, hx, cl_eq_zero_of_isZero P (IsZero.of_mono (kernel.ι _) hi), sub_zero,
      smul_zero]
  have hg : (Function.support g).Finite :=
    hfin.subset fun i hi hz => hi (hzero i hz).1
  have hg' : (Function.support fun i => g (i - a)).Finite :=
    (hg.image fun j => j + a).subset fun i hi => ⟨i - a, hi, sub_add_cancel i a⟩
  have h₁ : (Function.support fun i => ε i • cl P (X.homology i)).Finite :=
    hfin.subset fun i hi hz => hi (by simp only [(hzero i hz).2.2, smul_zero])
  have h₂ : (Function.support fun i => ε i • cl P (X.X i)).Finite :=
    hfin.subset fun i hi hz => hi (by simp only [(hzero i hz).2.1, smul_zero])
  have hsum : ∑ᶠ i, (g i - g (i - a)) = 0 := by
    rw [finsum_sub_distrib hg hg', sub_eq_zero]
    exact (finsum_comp_equiv (Equiv.subRight a) (f := g)).symm
  refine (sub_eq_zero.1 ?_).symm
  change ∑ᶠ i, ε i • cl P (X.homology i) - ∑ᶠ i, ε i • cl P (X.X i) = 0
  rw [← finsum_sub_distrib h₁ h₂, ← hsum]
  exact finsum_congr key

/-- Along the pages `E_s`, `s ≥ r`, of a spectral sequence whose page `E_r` has only finitely many
nonzero terms, all in `P`: the terms stay in `P`, vanishing terms stay zero, and the Euler
characteristic `∑ (-1)^{p + q} [E_s^{p, q}]` does not change. -/
private lemma page_induction (E : CohomologicalSpectralSequence C 0) (r : ℤ) (hr : 0 ≤ r)
    (hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite)
    (hP : ∀ pq, P ((E.page r hr).X pq)) :
    ∀ s : ℤ, r ≤ s → ∀ hs : 0 ≤ s, (∀ pq, P ((E.page s hs).X pq)) ∧
      {pq : ℤ × ℤ | ¬ IsZero ((E.page s hs).X pq)} ⊆
        {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)} ∧
      ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • cl P ((E.page s hs).X pq) =
        ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • cl P ((E.page r hr).X pq) := by
  intro s hle
  induction s, hle using Int.leInduction with
  | base => exact fun _ => ⟨hP, subset_rfl, rfl⟩
  | succ m hm ih =>
    intro _
    have hm0 : 0 ≤ m := hr.trans hm
    obtain ⟨hPm, hsub, hsum⟩ := ih hm0
    refine ⟨fun pq => P.prop_of_iso (E.iso m (m + 1) pq rfl hm0)
      (prop_homology_of_prop P ((E.page m hm0).sc pq) (hPm _) (hPm _) (hPm _)),
      fun pq hpq => hsub fun hz => hpq ?_, ?_⟩
    · exact IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ hz)
        (E.iso m (m + 1) pq rfl hm0).symm
    · rw [← hsum, finsum_cl_eq_finsum_cl_homology P _ (by simp) (E.page m hm0) hPm
        (hfin.subset hsub)]
      exact finsum_congr fun pq => by rw [cl_congr P (E.iso m (m + 1) pq rfl hm0)]

/-- If `F^{t + 1}H^n(K^•)` lies in `P`, its class is the sum of the classes of the
`gr^uH^n(K^•)`, `t + 1 ≤ u < b`, and it vanishes when they all do, then the same holds for
`F^tH^n(K^•)` and `t ≤ u < b`. -/
private lemma cl_image_homologyMap_eq_sum_of_succ {n t b : ℤ} (htb : t < b)
    (hPgr : ∀ t, P (K.gradedHomology t n))
    (hQ : P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op (t + 1))) n)) ∧
        cl P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op (t + 1))) n)) =
          ∑ u ∈ Finset.Ico (t + 1) b, cl P (K.gradedHomology u n) ∧
        ((∀ u ∈ Finset.Ico (t + 1) b, IsZero (K.gradedHomology u n)) →
          IsZero (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op (t + 1))) n)))) :
    P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) ∧
      cl P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) =
        ∑ u ∈ Finset.Ico t b, cl P (K.gradedHomology u n) ∧
      ((∀ u ∈ Finset.Ico t b, IsZero (K.gradedHomology u n)) →
        IsZero (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n))) := by
  have hφ : HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (t : ℤ) ⟶ t + 1).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n =
      HomologicalComplex.homologyMap (K.filtration.ι.app (op (t + 1))) n := by
    rw [← HomologicalComplex.homologyMap_comp, K.filtration.diagram_map_comp_ι_app]
  have hS : (ShortComplex.mk _ _ (cokernel.condition (image.preComp
      (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (t : ℤ) ⟶ t + 1).op) n)
      (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)))).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      (show Mono (image.preComp _ _) from inferInstance)
      (show Epi (cokernel.π _) from inferInstance)
  have h₁ : P (image (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (t : ℤ) ⟶ t + 1).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) := by
    rw [hφ]; exact hQ.1
  have h₂ : P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) :=
    P.prop_X₂_of_shortExact hS h₁ (hPgr t)
  have hIco : insert t (Finset.Ico (t + 1) b) = Finset.Ico t b := by
    ext u; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
  have hcl₁ : cl P (image (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (t : ℤ) ⟶ t + 1).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) =
      cl P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op (t + 1))) n)) := by
    rw [hφ]
  refine ⟨h₂, ?_, fun hz => ?_⟩
  · rw [cl_shortExact P hS h₁ h₂ (hPgr t)]
    change cl P (image (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (t : ℤ) ⟶ t + 1).op) n ≫
        HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) +
      cl P (K.gradedHomology t n) = _
    rw [hcl₁, hQ.2.1, ← hIco, Finset.sum_insert (by simp), add_comm]
  · refine hS.exact.isZero_X₂ (IsZero.eq_of_src ?_ _ _) (IsZero.eq_of_tgt ?_ _ _)
    · change IsZero (image (HomologicalComplex.homologyMap (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (t : ℤ) ⟶ t + 1).op) n ≫
          HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n))
      rw [hφ]
      exact hQ.2.2 fun u hu => hz u (by rw [← hIco]; exact Finset.mem_insert_of_mem hu)
    · exact hz t (by rw [← hIco]; exact Finset.mem_insert_self _ _)

/-- **A finite filtration of `H^n(K^•)`.** If the induced filtration of `H^n(K^•)` is `⊤` at `a`
and `⊥` at `b ≥ a`, and its graded pieces are in `P`, then `H^n(K^•)` is in `P`, its class is the
sum of those of the graded pieces `gr^tH^n(K^•)`, `a ≤ t < b`, and it vanishes if they all do. -/
private lemma cl_homology_eq_sum (n a b : ℤ) (hab : a ≤ b)
    (ha : K.inducedFiltrationStep n a = ⊤) (hb : K.inducedFiltrationStep n b = ⊥)
    (hPgr : ∀ t, P (K.gradedHomology t n)) :
    P (K.X.homology n) ∧
      cl P (K.X.homology n) = ∑ t ∈ Finset.Ico a b, cl P (K.gradedHomology t n) ∧
      ((∀ t ∈ Finset.Ico a b, IsZero (K.gradedHomology t n)) → IsZero (K.X.homology n)) := by
  let Q : ℤ → Prop := fun t =>
    P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) ∧
      cl P (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)) =
        ∑ u ∈ Finset.Ico t b, cl P (K.gradedHomology u n) ∧
      ((∀ u ∈ Finset.Ico t b, IsZero (K.gradedHomology u n)) →
        IsZero (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op t)) n)))
  have hbase : Q b := by
    have hz : IsZero (image (HomologicalComplex.homologyMap (K.filtration.ι.app (op b)) n)) :=
      (isZero_zero C).of_iso ((imageSubobjectIso _).symm ≪≫ Subobject.isoOfEq _ _ hb ≪≫
        Subobject.botCoeIsoZero)
    exact ⟨P.prop_of_isZero hz, by rw [cl_eq_zero_of_isZero P hz, Finset.Ico_self,
      Finset.sum_empty], fun _ => hz⟩
  have hQ : ∀ t, t ≤ b → Q t := by
    intro t ht
    induction t, ht using Int.leInductionDown with
    | base => exact hbase
    | pred u hu ih =>
      exact cl_image_homologyMap_eq_sum_of_succ K P (by omega) hPgr (by rwa [sub_add_cancel])
  have eH : image (HomologicalComplex.homologyMap (K.filtration.ι.app (op a)) n) ≅
      K.X.homology n :=
    (imageSubobjectIso _).symm ≪≫ Subobject.isoOfEq _ _ ha ≪≫
      asIso (⊤ : Subobject (K.X.homology n)).arrow
  obtain ⟨h₁, h₂, h₃⟩ := hQ a hab
  exact ⟨P.prop_of_iso eH h₁, by rw [← cl_congr P eH, h₂], fun hz => (h₃ hz).of_iso eH.symm⟩

/-- If the induced filtration of `H^n(K^•)` is `⊤` at `a₀` and `⊥` at `b₀ ≥ a₀`, and each graded
piece `gr^tH^n(K^•)` is isomorphic to `G (t, n - t)` and vanishes off a finite set `S`, then the
class of `H^n(K^•)` is the sum of those of the `G (t, n - t)`, and `H^n(K^•)` vanishes unless `S`
meets the antidiagonal of `n`. -/
private lemma cl_homology_eq_finsum (n a₀ b₀ : ℤ) (hab₀ : a₀ ≤ b₀)
    (ha₀ : K.inducedFiltrationStep n a₀ = ⊤) (hb₀ : K.inducedFiltrationStep n b₀ = ⊥)
    (G : ℤ × ℤ → C) {S : Set (ℤ × ℤ)} (hS : S.Finite)
    (hiso : ∀ t, Nonempty (G (t, n - t) ≅ K.gradedHomology t n))
    (hzero : ∀ t, (t, n - t) ∉ S → IsZero (K.gradedHomology t n))
    (hPgr : ∀ t, P (K.gradedHomology t n)) :
    cl P (K.X.homology n) = ∑ᶠ t : ℤ, cl P (G (t, n - t)) ∧
      (IsZero (K.X.homology n) ∨ ∃ t, (t, n - t) ∈ S) := by
  have hT : {t : ℤ | (t, n - t) ∈ S}.Finite :=
    hS.preimage fun t _ t' _ h => (Prod.ext_iff.1 h).1
  obtain ⟨lo, hlo⟩ := hT.bddBelow
  obtain ⟨hi, hhi⟩ := hT.bddAbove
  have ha : K.inducedFiltrationStep n (min a₀ lo) = ⊤ :=
    top_le_iff.1 (ha₀ ▸ K.inducedFiltrationStep_antitone n (min_le_left _ _))
  have hb : K.inducedFiltrationStep n (max b₀ (hi + 1)) = ⊥ :=
    le_bot_iff.1 (hb₀ ▸ K.inducedFiltrationStep_antitone n (le_max_left _ _))
  have hIco : ∀ t, (t, n - t) ∈ S → t ∈ Finset.Ico (min a₀ lo) (max b₀ (hi + 1)) := by
    intro t ht
    have h₁ := hlo ht
    have h₂ := hhi ht
    simp only [Finset.mem_Ico]
    omega
  obtain ⟨-, hcl, hz⟩ := cl_homology_eq_sum K P n _ _
    ((min_le_left _ _).trans (hab₀.trans (le_max_left _ _))) ha hb hPgr
  refine ⟨?_, ?_⟩
  · rw [hcl, finsum_eq_sum_of_support_subset _ (s := Finset.Ico (min a₀ lo) (max b₀ (hi + 1)))]
    · exact Finset.sum_congr rfl fun t _ => cl_congr P (hiso t).some.symm
    · intro t ht
      by_contra h
      exact ht (cl_eq_zero_of_isZero P ((hzero t fun h' => h (hIco t h')).of_iso
        (hiso t).some))
  · refine (em (IsZero (K.X.homology n))).elim Or.inl fun hH0 => Or.inr ?_
    by_contra h'
    exact hH0 (hz fun t _ => hzero t fun ht => h' ⟨t, ht⟩)

end EulerCharacteristic

open FilteredComplexSpectralSequence in
/-- **Stacks 0BDW.** Let `(K^•, F)` be a filtered complex of `C` whose filtration is finite in
each degree, and let `E` be its spectral sequence, presented by the identification of its pages
with `Z_s^{p, q}/(D_s^{p, q} ∩ Z_s^{p, q})` of [Stacks, Tag 012M]. If some page `E_r` has only
finitely many nonzero terms, then only finitely many `H^n(K^•)` are nonzero, and for every weak
Serre subcategory `P` of `C` containing the terms of `E_r` (for instance the smallest one) the
`H^n(K^•)` lie in `P` and `∑ (-1)^n [H^n(K^•)] = ∑ (-1)^{p + q} [E_r^{p, q}]` in `K₀(P)`. -/
@[stacks 0BDW]
theorem finite_homology_and_sum_negOnePow_eq (hK : K.filtration.IsDegreewiseFinite)
    (E : CohomologicalSpectralSequence C 0)
    (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : boundaries K.X K.step r p n ⊓
        cycles K.X K.step r p n ≤ cycles K.X K.step r p n)))
    (r : ℤ) (hr : 0 ≤ r) (hfin : {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite)
    (P : ObjectProperty C) [P.IsWeakSerreClass] (hP : ∀ pq : ℤ × ℤ, P ((E.page r hr).X pq)) :
    {n : ℤ | ¬ IsZero (K.X.homology n)}.Finite ∧
    ∃ hH : ∀ n : ℤ, P (K.X.homology n),
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • KZero.mk P.FullSubcategory ⟨K.X.homology n, hH n⟩ =
        ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
          KZero.mk P.FullSubcategory ⟨(E.page r hr).X pq, hP pq⟩ := by
  obtain ⟨-, hFH, -, -, hSerre⟩ := isBounded_and_converges_of_isDegreewiseFinite K hK K.step
    (fun _ _ => rfl) (cycles K.X K.step) (fun _ _ _ => rfl) (boundaries K.X K.step)
    (fun _ _ _ => rfl) (fun n p => K.inducedFiltrationStep n p) (fun _ _ => rfl) E e
  have hH : ∀ n, P (K.X.homology n) := hSerre P r hr fun p q => hP (p, q)
  set S := {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}
  choose s₀ hs₀ using fun pq : ℤ × ℤ =>
    K.exists_page_iso_gradedHomology hK E e pq.1 pq.2 (pq.1 + pq.2) rfl
  obtain ⟨M, hM⟩ := (hfin.image s₀).bddAbove
  have hrs : r ≤ max r M := le_max_left _ _
  have hs : 0 ≤ max r M := hr.trans hrs
  obtain ⟨hPs, hsub, hsum⟩ := page_induction P E r hr hfin hP (max r M) hrs hs
  have hiso : ∀ p q : ℤ,
      Nonempty ((E.page (max r M) hs).X (p, q) ≅ K.gradedHomology p (p + q)) := by
    intro p q
    by_cases hpq : IsZero ((E.page r hr).X (p, q))
    · obtain ⟨φ⟩ := hs₀ (p, q) (max (max r M) (s₀ (p, q))) (hs.trans (le_max_left _ _))
        (le_max_right _ _)
      have h₁ := E.isZero_page_of_le hr (p, q) hpq (max r M) hrs hs
      have h₂ := E.isZero_page_of_le hr (p, q) hpq (max (max r M) (s₀ (p, q)))
        (hrs.trans (le_max_left _ _)) (hs.trans (le_max_left _ _))
      exact ⟨h₁.iso (h₂.of_iso φ.symm)⟩
    · exact hs₀ (p, q) (max r M) hs ((hM ⟨(p, q), hpq, rfl⟩).trans (le_max_right _ _))
  have hiso' : ∀ t n : ℤ,
      Nonempty ((E.page (max r M) hs).X (t, n - t) ≅ K.gradedHomology t n) := fun t n =>
    by simpa only [add_sub_cancel] using hiso t (n - t)
  have hPgr : ∀ t n, P (K.gradedHomology t n) := fun t n =>
    P.prop_of_iso (hiso' t n).some (hPs _)
  have hzero : ∀ t n, (t, n - t) ∉ S → IsZero (K.gradedHomology t n) := fun t n h =>
    (Classical.not_not.1 fun h' => h (hsub h')).of_iso (hiso' t n).some.symm
  have hHn : ∀ n : ℤ, cl P (K.X.homology n) =
      ∑ᶠ t : ℤ, cl P ((E.page (max r M) hs).X (t, n - t)) ∧
      (IsZero (K.X.homology n) ∨ ∃ t, (t, n - t) ∈ S) := by
    intro n
    obtain ⟨a₀, b₀, hab₀, ha₀, hb₀⟩ := hFH n
    exact cl_homology_eq_finsum K P n a₀ b₀ hab₀ ha₀ hb₀ _ hfin (fun t => hiso' t n)
      (fun t => hzero t n) fun t => hPgr t n
  refine ⟨?_, hH, ?_⟩
  · refine ((hfin.image fun pq => pq.1 + pq.2)).subset fun n hn => ?_
    obtain h | ⟨t, ht⟩ := (hHn n).2
    · exact absurd h hn
    · exact ⟨(t, n - t), ht, by simp⟩
  · calc ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • KZero.mk P.FullSubcategory ⟨K.X.homology n, hH n⟩
        = ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • ∑ᶠ t : ℤ,
            cl P ((E.page (max r M) hs).X (t, n - t)) :=
          finsum_congr fun n => by rw [← cl_of_prop P (hH n), (hHn n).1]
      _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • cl P ((E.page (max r M) hs).X pq) :=
          finsum_negOnePow_smul_finsum_eq _ (hfin.subset fun pq h h' =>
            h (cl_eq_zero_of_isZero P (Classical.not_not.1 fun h'' => (hsub h'') h')))
      _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) • cl P ((E.page r hr).X pq) := hsum
      _ = _ := finsum_congr fun pq => by rw [cl_of_prop P (hP pq)]

open FilteredComplexSpectralSequence in
/-- [Stacks, Tag 012N] (1) for the spectral sequence of [Stacks, Tag 012M]: it has
`E_1^{p, q} = H^{p + q}(gr^pK^•)`, and `d_1^{p, q}` is the boundary map of
`0 → gr^{p + 1}K^• → F^pK^•/F^{p + 2}K^• → gr^pK^• → 0`. -/
theorem exists_spectralSequence_firstPage_homology_d_eq_δ :
    ∃ (E : CohomologicalSpectralSequence C 0)
      (ε : ∀ (p q n : ℤ) (_ : n = p + q), (E.page 1).X (p, q) ≅ ((gr p).obj K).homology n),
      ∀ (p q n : ℤ) (hn : n = p + q),
        (E.page 1).d (p, q) (p + 1, q) ≫ (ε (p + 1) q (n + 1) (by omega)).hom =
          (ε p q n hn).hom ≫
            (grMapCompShortComplex_shortExact (succHom (p + 1)) (succHom p) K).δ n (n + 1)
              (by simp) := by
  obtain ⟨E, e, -, hδ, -⟩ := exists_cohomologicalSpectralSequence K K.step (fun _ _ => rfl)
    (cycles K.X K.step) (fun _ _ _ => rfl) (boundaries K.X K.step) (fun _ _ _ => rfl)
  obtain ⟨ε, -, hε⟩ := K.exists_iso_firstPage_homology_d_eq_δ E
    (fun p q n hn => e 1 p q n zero_le_one hn)
    (fun p q n hn => by
      obtain ⟨δ, h₁, h₂⟩ := hδ 1 p q n zero_le_one hn
      refine ⟨δ, h₁, ?_⟩
      convert h₂ using 3 <;> congr! <;> omega)
  exact ⟨E, ε, hε⟩

open FilteredComplexSpectralSequence in
/-- [Stacks, Tag 0BDW] for the spectral sequence of [Stacks, Tag 012M]: if the filtration is
finite in each degree and `E_r` has finitely many nonzero terms, all lying in the weak Serre
subcategory `P`, then finitely many `H^n(K^•)` are nonzero, they lie in `P`, and
`∑ (-1)^n [H^n(K^•)] = ∑ (-1)^{p + q} [E_r^{p, q}]` in `K₀(P)`. -/
theorem exists_spectralSequence_sum_negOnePow_eq (hK : K.filtration.IsDegreewiseFinite)
    (r : ℤ) (hr : 0 ≤ r) (P : ObjectProperty C) [P.IsWeakSerreClass] :
    ∃ E : CohomologicalSpectralSequence C 0,
      {pq : ℤ × ℤ | ¬ IsZero ((E.page r hr).X pq)}.Finite →
      ∀ hP : ∀ pq : ℤ × ℤ, P ((E.page r hr).X pq),
        {n : ℤ | ¬ IsZero (K.X.homology n)}.Finite ∧
        ∃ hH : ∀ n : ℤ, P (K.X.homology n),
          ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • KZero.mk P.FullSubcategory ⟨K.X.homology n, hH n⟩ =
            ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) •
              KZero.mk P.FullSubcategory ⟨(E.page r hr).X pq, hP pq⟩ := by
  obtain ⟨E, e, -⟩ := exists_cohomologicalSpectralSequence K K.step (fun _ _ => rfl)
    (cycles K.X K.step) (fun _ _ _ => rfl) (boundaries K.X K.step) (fun _ _ _ => rfl)
  exact ⟨E, fun hfin hP => K.finite_homology_and_sum_negOnePow_eq hK E e r hr hfin P hP⟩

end CochainComplex.Filtered
