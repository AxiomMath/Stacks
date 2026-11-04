module

public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.FilteredCompletionSpectralSequence
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.CategoryTheory.Subobject.Butterfly
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles

/-!
# The derived-completion spectral sequence of an object of the derived category

Let `I` be a finitely generated ideal of a commutative ring `A`. The canonical truncation
(Postnikov) filtration `F^pC = τ^{≤-p}C` of a representative of an object `K` of `D(A)` is finite
in each degree, so the derived-completion spectral sequence of
`StacksFrontier.Homology.DerivedComplete.FilteredCompletionSpectralSequence` applied to it is bounded
and converges. Its first page consists of the derived completions of the cohomology modules of
`K`; after the reindexing `p = -j`, `q = i + 2j` and a shift of the page number by one it becomes
the spectral sequence with `E₂^{i,j} ≅ H^i(H^j(K)^∧)` converging to `H^{i+j}(K^∧)`.

## Main definitions

* `AdicFilteredCompletion.postnikovFiltered`: the strict Postnikov filtration `F^pC = τ^{≤-p}C`
  of a cochain complex `C`, with underlying object `C` itself.
* `AdicFilteredCompletion.truncLEInclusion`: the inclusion `τ^{≤a}C ⟶ τ^{≤b}C` of canonical
  truncations.
* `AdicFilteredCompletion.reindexEquiv`: the lattice bijection `(i, j) ↦ (-j, i + 2j)`.

## Main results

* `AdicFilteredCompletion.postnikovStepIso_hom_ιTruncLE`,
  `AdicFilteredCompletion.postnikovFinite` and `AdicFilteredCompletion.postnikovGraded`: the steps
  of the Postnikov filtration are the truncations compatibly with the inclusions, the filtration
  is finite in each degree, and its graded pieces are `H^{-p}(C)[p]` in the derived category.
* `AdicFilteredCompletion.reindex_target` and `AdicFilteredCompletion.reindex_source`: the
  bidegree equations for the reindexed differentials.
* `AdicFilteredCompletion.exists_spectralSequence_derivedCompletion_homology`:
  [Stacks, Tag 0BKE], giving both the truncation-filtered first-page spectral sequence and its
  reindexing as a second-page spectral sequence.

## Implementation notes

Derived completion is represented by a left adjoint to the inclusion of the derived-complete
objects, whose existence ([Stacks, Tag 0920]) is part of the result. The chosen filtered complex
is identified at every step with the canonical truncation `τ^{≤-p}` of a representative of `K`,
compatibly with the inclusions into that representative. The first spectral sequence is literally
the filtered-complex spectral sequence used in [Stacks, Tag 0BKD], namely
`CochainComplex.Filtered.spectralSequenceFunctor` applied to a filtered model of the completion.
Convergence is recorded by the induced finite decreasing filtration on cohomology
(`CochainComplex.Filtered.inducedFiltrationStep`) and eventual identifications with its associated
graded objects. The isomorphisms `reindex` identify page `r` of the reindexed sequence with page
`r - 1` of the first sequence at `p = -j`, `q = i + 2j`, and commute with the differentials.

## References

* [The Stacks Project, Tag 0BKE](https://stacks.math.columbia.edu/tag/0BKE)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AdicFilteredCompletion

attribute [local instance 2000] HasDerivedCategory.standard

section Postnikov

variable {A : Type u} [CommRing A]

/-- The canonical inclusion `τ≤n C ⟶ C` is a monomorphism. -/
instance mono_ιTruncLE (complex : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℤ) :
    Mono (complex.ιTruncLE n) :=
  inferInstanceAs (Mono (HomologicalComplex.ιTruncLE complex _))

/-- The canonical inclusion `τ≤n C ⟶ C` is a monomorphism in each degree. -/
instance mono_ιTruncLE_f (complex : CochainComplex (ModuleCat.{v} A) ℤ) (n i : ℤ) :
    Mono ((complex.ιTruncLE n).f i) :=
  inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE complex _).f i))

/-- The inclusion `τ≤a C ⟶ τ≤b C` of canonical truncations for `a ≤ b`, the unique map over `C`. -/
def truncLEInclusion (complex : CochainComplex (ModuleCat.{v} A) ℤ) {a b : ℤ} (hab : a ≤ b) :
    complex.truncLE a ⟶ complex.truncLE b :=
  have : (complex.truncLE a).IsStrictlyLE b := (complex.truncLE a).isStrictlyLE_of_le a b hab
  inv ((complex.truncLE a).ιTruncLE b) ≫ CochainComplex.truncLEMap (complex.ιTruncLE a) b

/-- The inclusion `τ^{≤a}C ⟶ τ^{≤b}C` is compatible with the inclusions of both truncations
into `C`. -/
@[reassoc (attr := simp)]
theorem truncLEInclusion_ι (complex : CochainComplex (ModuleCat.{v} A) ℤ) {a b : ℤ}
    (hab : a ≤ b) :
    truncLEInclusion complex hab ≫ complex.ιTruncLE b = complex.ιTruncLE a := by
  simp [truncLEInclusion, CochainComplex.ιTruncLE_naturality]

/-- The strict Postnikov (canonical truncation) filtration `F^p C = τ≤-p C` of a cochain complex
`C`, a decreasing filtration of `C` by subcomplexes whose underlying object is `C` itself. -/
def postnikovFiltered (complex : CochainComplex (ModuleCat.{v} A) ℤ) :
    FilteredObject (CochainComplex (ModuleCat.{v} A) ℤ) ℤᵒᵖ where
  X := complex
  filtration :=
    { toMonoOver :=
        { obj p := MonoOver.mk (complex.ιTruncLE (-p.unop))
          map {p p'} f := MonoOver.homMk
            (truncLEInclusion complex (neg_le_neg (leOfHom f.unop))) (by simp)
          map_id _ := Subsingleton.elim _ _
          map_comp _ _ := Subsingleton.elim _ _ } }

/-- Unfolding lemma for the Postnikov filtration. -/
theorem postnikovFiltered_X (complex : CochainComplex (ModuleCat.{v} A) ℤ) :
    (postnikovFiltered complex).X = complex := rfl

/-- Unfolding lemma for the Postnikov filtration. -/
theorem postnikovFiltered_obj (complex : CochainComplex (ModuleCat.{v} A) ℤ) (index : ℤ) :
    (postnikovFiltered complex).filtration.obj (op index) = complex.truncLE (-index) := rfl

/-- Unfolding lemma for the Postnikov filtration. -/
theorem postnikovFiltered_ι_app (complex : CochainComplex (ModuleCat.{v} A) ℤ) (index : ℤ) :
    (postnikovFiltered complex).filtration.ι.app (op index) = complex.ιTruncLE (-index) := rfl

/-- Unfolding lemma for the Postnikov filtration. -/
theorem postnikovFiltered_map (complex : CochainComplex (ModuleCat.{v} A) ℤ) {a b : ℤ}
    (hab : a ≤ b) :
    (postnikovFiltered complex).filtration.diagram.map (homOfLE hab).op =
      truncLEInclusion complex (neg_le_neg hab) := rfl

/-- The underlying complex of the Postnikov filtration is the given complex. -/
def postnikovUnderlyingIso (complex : CochainComplex (ModuleCat.{v} A) ℤ) :
    (postnikovFiltered complex).X ≅ complex :=
  Iso.refl _

/-- The `p`-th step of the Postnikov filtration is the canonical truncation `τ≤-p`. -/
def postnikovStepIso (complex : CochainComplex (ModuleCat.{v} A) ℤ) (index : ℤ) :
    (postnikovFiltered complex).filtration.obj (op index) ≅ complex.truncLE (-index) :=
  Iso.refl _

/-- The steps of the Postnikov filtration are compatible with the canonical inclusions
`τ≤-p C ⟶ C`. -/
theorem postnikovStepIso_hom_ιTruncLE (complex : CochainComplex (ModuleCat.{v} A) ℤ)
    (index : ℤ) :
    (postnikovStepIso complex index).hom ≫ complex.ιTruncLE (-index) =
      (postnikovFiltered complex).filtration.ι.app (op index) ≫
        (postnikovUnderlyingIso complex).hom := by
  simp only [postnikovStepIso, postnikovUnderlyingIso, Iso.refl_hom]
  rfl

/-- The `p`-th step of the Postnikov filtration is `τ≤-p C`. -/
theorem postnikovStep (complex : CochainComplex (ModuleCat.{v} A) ℤ) (index : ℤ) :
    Nonempty ((postnikovFiltered complex).filtration.obj (op index) ≅
      complex.truncLE (-index)) :=
  ⟨postnikovStepIso complex index⟩

/-- In degrees `n < m` the inclusion `τ≤m C ⟶ C` is an isomorphism. -/
theorem isIso_ιTruncLE_f (complex : CochainComplex (ModuleCat.{v} A) ℤ) {m n : ℤ}
    (h : n < m) : IsIso ((complex.ιTruncLE m).f n) := by
  let e := ComplexShape.embeddingUpIntLE m
  have hi : e.f (m - n).natAbs = n := by
    simp only [e, ComplexShape.embeddingUpIntLE_f, Int.natCast_natAbs, abs_of_pos (sub_pos.2 h)]
    omega
  have hb : ¬ e.op.BoundaryGE (m - n).natAbs := by
    rw [ComplexShape.Embedding.op_boundaryGE_iff, ComplexShape.boundaryLE_embeddingUpIntLE_iff,
      Int.natAbs_eq_zero]
    omega
  have : IsIso ((complex.op.πTruncGE e.op).f n) := by
    show IsIso ((e.op.liftExtend _ _).f n)
    rw [e.op.isIso_liftExtend_f_iff _ _ hi]
    exact complex.op.isIso_restrictionToTruncGE' e.op _ hb
  exact inferInstanceAs (IsIso ((complex.op.πTruncGE e.op).f n).unop)

/-- The Postnikov filtration is finite in each degree: `F^p C^n = C^n` for `p < -n` and
`F^p C^n = 0` for `p > -n`. No boundedness of `C` is needed. -/
theorem postnikovFinite (complex : CochainComplex (ModuleCat.{v} A) ℤ) :
    (postnikovFiltered complex).filtration.IsDegreewiseFinite := by
  intro n
  refine ⟨-(n + 1), -(n - 1), ?_, ?_⟩
  · rw [postnikovFiltered_ι_app]
    exact isIso_ιTruncLE_f complex (by omega)
  · rw [postnikovFiltered_obj]
    exact (complex.truncLE (-(-(n - 1)))).isZero_of_isStrictlyLE (-(-(n - 1))) n (by omega)

/-- `τ≤m C` has no homology above degree `m`. -/
theorem isZero_homology_truncLE (complex : CochainComplex (ModuleCat.{v} A) ℤ) {m n : ℤ}
    (h : m < n) : IsZero ((complex.truncLE m).homology n) :=
  ((complex.truncLE m).exactAt_of_isLE m n h).isZero_homology

/-- The inclusion `τ≤a C ⟶ τ≤b C` induces isomorphisms on homology in degrees `≤ a`. -/
theorem isIso_homologyMap_truncLEInclusion (complex : CochainComplex (ModuleCat.{v} A) ℤ)
    {a b : ℤ} (hab : a ≤ b) {n : ℤ} (hn : n ≤ a) :
    IsIso (HomologicalComplex.homologyMap (truncLEInclusion complex hab) n) := by
  have := complex.quasiIsoAt_ιTruncLE a n hn
  have := complex.quasiIsoAt_ιTruncLE b n (hn.trans hab)
  have : IsIso (HomologicalComplex.homologyMap (truncLEInclusion complex hab) n ≫
      HomologicalComplex.homologyMap (complex.ιTruncLE b) n) := by
    rw [← HomologicalComplex.homologyMap_comp, truncLEInclusion_ι]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap (complex.ιTruncLE b) n)

/-- The short exact sequence `0 ⟶ τ≤a C ⟶ τ≤b C ⟶ τ≤b C / τ≤a C ⟶ 0`. -/
abbrev truncLEShortComplex (complex : CochainComplex (ModuleCat.{v} A) ℤ) {a b : ℤ}
    (hab : a ≤ b) : ShortComplex (CochainComplex (ModuleCat.{v} A) ℤ) :=
  ShortComplex.mk (truncLEInclusion complex hab) (cokernel.π _) (cokernel.condition _)

/-- The sequence `0 ⟶ τ≤a C ⟶ τ≤b C ⟶ τ≤b C / τ≤a C ⟶ 0` is short exact. -/
theorem truncLEShortComplex_shortExact (complex : CochainComplex (ModuleCat.{v} A) ℤ)
    {a b : ℤ} (hab : a ≤ b) : (truncLEShortComplex complex hab).ShortExact := by
  have : Mono (truncLEInclusion complex hab) :=
    mono_of_mono_fac (truncLEInclusion_ι complex hab)
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance

/-- The adjacent quotient `τ≤a+1 C / τ≤a C` has no homology outside degree `a + 1`. -/
theorem isZero_homology_truncLEQuotient (complex : CochainComplex (ModuleCat.{v} A) ℤ)
    {a b : ℤ} (hab : a + 1 = b) {n : ℤ} (hn : n ≠ b) :
    IsZero ((cokernel (truncLEInclusion complex (show a ≤ b by omega))).homology n) := by
  have hab' : a ≤ b := by omega
  have hS := truncLEShortComplex_shortExact complex hab'
  rcases lt_or_gt_of_ne hn with hn | hn
  · have hf : HomologicalComplex.homologyMap (truncLEShortComplex complex hab').g n = 0 := by
      have := isIso_homologyMap_truncLEInclusion complex (show a ≤ b by omega)
        (show n ≤ a by omega)
      exact (hS.homology_exact₂ n).epi_f_iff.1 (by dsimp; infer_instance)
    have hg : hS.δ n (n + 1) rfl = 0 := by
      by_cases hn' : n + 1 = b
      · exact (isZero_homology_truncLE complex (show a < n + 1 by omega)).eq_of_tgt _ _
      · have := isIso_homologyMap_truncLEInclusion complex (show a ≤ b by omega)
          (show n + 1 ≤ a by omega)
        exact (hS.homology_exact₁ n (n + 1) rfl).mono_g_iff.1 (by dsimp; infer_instance)
    exact (hS.homology_exact₃ n (n + 1) rfl).isZero_of_both_zeros hf hg
  · exact (hS.homology_exact₃ n (n + 1) rfl).isZero_of_both_isZero
      (isZero_homology_truncLE complex hn)
      (isZero_homology_truncLE complex (show a < n + 1 by omega))

/-- The projection `τ≤a+1 C ⟶ τ≤a+1 C / τ≤a C` is an isomorphism on homology in degree `a + 1`. -/
theorem isIso_homologyMap_truncLEQuotient (complex : CochainComplex (ModuleCat.{v} A) ℤ)
    {a b : ℤ} (hab : a + 1 = b) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.π (truncLEInclusion complex (show a ≤ b by omega))) b) := by
  have hab' : a ≤ b := by omega
  have hS := truncLEShortComplex_shortExact complex hab'
  have : Mono (HomologicalComplex.homologyMap (truncLEShortComplex complex hab').g b) :=
    (hS.homology_exact₂ b).mono_g
      ((isZero_homology_truncLE complex (show a < b by omega)).eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap (truncLEShortComplex complex hab').g b) :=
    (hS.homology_exact₃ b (b + 1) rfl).epi_f
      ((isZero_homology_truncLE complex (show a < b + 1 by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The homology of `τ≤b C / τ≤a C` in degree `b = a + 1` is `H^b(C)`. -/
def truncLEQuotientHomologyIso (complex : CochainComplex (ModuleCat.{v} A) ℤ)
    {a b : ℤ} (hab : a + 1 = b) :
    (cokernel (truncLEInclusion complex (show a ≤ b by omega))).homology b ≅
      complex.homology b :=
  have := isIso_homologyMap_truncLEQuotient complex hab
  (asIso (HomologicalComplex.homologyMap
      (cokernel.π (truncLEInclusion complex (show a ≤ b by omega))) b)).symm ≪≫
    asIso (HomologicalComplex.homologyMap (complex.ιTruncLE b) b)

/-- The graded piece `gr^p C = τ≤-p C / τ≤-p-1 C` is isomorphic in the derived category, through
the quasi-isomorphisms computing its homology, to `H^(-p)(C)[p]`. -/
theorem postnikovGraded (complex : CochainComplex (ModuleCat.{v} A) ℤ) (index : ℤ) :
    Nonempty (DerivedCategory.Q.obj
        ((FilteredObject.gr index).obj (postnikovFiltered complex)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
        (complex.homology (-index)))⟦index⟧) := by
  let G := cokernel (truncLEInclusion complex
    (show -(index + 1) ≤ -index by omega))
  show Nonempty (DerivedCategory.Q.obj G ≅ _)
  have hG : ∀ n, n ≠ -index → IsZero (G.homology n) := fun n hn ↦
    isZero_homology_truncLEQuotient complex (show -(index + 1) + 1 = -index by omega) hn
  have : G.IsGE (-index) := by
    rw [CochainComplex.isGE_iff]
    exact fun n hn ↦ (G.exactAt_iff_isZero_homology n).2 (hG n (by omega))
  have : G.IsLE (-index) := by
    rw [CochainComplex.isLE_iff]
    exact fun n hn ↦ (G.exactAt_iff_isZero_homology n).2 (hG n (by omega))
  have : (DerivedCategory.Q.obj G).IsGE (-index) :=
    (DerivedCategory.isGE_Q_obj_iff G _).2 inferInstance
  have : (DerivedCategory.Q.obj G).IsLE (-index) :=
    (DerivedCategory.isLE_Q_obj_iff G _).2 inferInstance
  obtain ⟨Y, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (DerivedCategory.Q.obj G)
      (-index)
  have eY : Y ≅ complex.homology (-index) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-index)).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor _ (-index)).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ (-index)).app G ≪≫
      truncLEQuotientHomologyIso complex (show -(index + 1) + 1 = -index by omega)
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ (-index)).mapIso eY ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{v} A)).shiftIso index (-index) 0
      (by omega)).symm.app _⟩

end Postnikov

/-- The affine lattice bijection `(i, j) ↦ (p, q) = (-j, i + 2j)` identifying the positions of
the reindexed spectral sequence with those of the truncation spectral sequence. -/
def reindexEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (-x.2, x.1 + 2 * x.2)
  invFun y := (y.2 + 2 * y.1, -y.1)
  left_inv x := by ext <;> dsimp <;> omega
  right_inv y := by ext <;> dsimp <;> omega

/-- `reindexEquiv` sends `(i, j)` to `(-j, i + 2j)`. -/
@[simp]
theorem reindexEquiv_apply (i j : ℤ) : reindexEquiv (i, j) = (-j, i + 2 * j) := rfl

/-- The inverse of `reindexEquiv` sends `(p, q)` to `(q + 2p, -p)`. -/
@[simp]
theorem reindexEquiv_symm_apply (p q : ℤ) : reindexEquiv.symm (p, q) = (q + 2 * p, -p) := rfl

/-- `reindexEquiv` preserves the total degree: `p + q = i + j`. -/
theorem reindexEquiv_diagonal (i j : ℤ) :
    (reindexEquiv (i, j)).1 + (reindexEquiv (i, j)).2 = i + j := by
  simp only [reindexEquiv_apply]
  omega

/-- The target of the reindexed differential `(i, j) ⟶ (i + r, j - r + 1)` corresponds to the
target of the differential of page `r - 1` of the truncation spectral sequence. -/
theorem reindex_target (page first second : ℤ) :
    (-(second - page + 1), (first + page) + 2 * (second - page + 1)) =
      (-second + (page - 1), first + 2 * second - (page - 1) + 1) := by
  ext <;> dsimp <;> omega

/-- The source of the reindexed differential `(i - r, j + r - 1) ⟶ (i, j)` corresponds to the
source of the differential of page `r - 1` of the truncation spectral sequence. -/
theorem reindex_source (page first second : ℤ) :
    (-(second + page - 1), (first - page) + 2 * (second + page - 1)) =
      (-second - (page - 1), first + 2 * second + (page - 1) - 1) := by
  ext <;> dsimp <;> omega


section Completion

variable {A : Type u} [CommRing A]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]

/-- The inclusion of the derived-complete objects into `D(A)` has a left adjoint when `I` is
finitely generated ([Stacks, Tag 0920]). -/
private theorem exists_completion (I : Ideal A) (hI : I.FG) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L => IsDerivedComplete I L
    ∃ L : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory, Nonempty (L ⊣ P.ι) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  subst I
  obtain ⟨L, hL, _⟩ := AdicKoszulAdjunction.koszulPowerDerivedLimit_isLeftAdjoint A f
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} A))
  exact ⟨L, hL⟩

private def postnikovGradedIso (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (K : DerivedCategory (ModuleCat.{v} A)) (eK : DerivedCategory.Q.obj C ≅ K)
    (p : ℤ) : DerivedCategory.Q.obj
      ((FilteredObject.gr p).obj (postnikovFiltered C)) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ (-p)).obj K))⟦p⟧ :=
  (postnikovGraded C p).some ≪≫ (shiftFunctor _ p).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      (((DerivedCategory.homologyFunctorFactors _ (-p)).app C).symm ≪≫
        (DerivedCategory.homologyFunctor _ (-p)).mapIso eK))

private def completionShiftIso (I : Ideal A) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun K => IsDerivedComplete I K
    -- `_adj` is consumed by the proof, which needs the adjunction to transport the shift,
    -- but does not appear in the type; `intro` below names it positionally.
    ∀ (L : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory) (_adj : L ⊣ P.ι)
      (K : DerivedCategory (ModuleCat.{v} A)) (p : ℤ),
      (L ⋙ P.ι).obj (K⟦p⟧) ≅ ((L ⋙ P.ι).obj K)⟦p⟧ := by
  intro P L adj K p
  let Q : ObjectProperty (ModuleCat.{v} A) := fun M => IsDerivedCompleteModule I M
  have h := AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff A I
  have : Q.IsWeakSerreClass := h.1
  have : P.IsStableUnderShift ℤ := ⟨fun a => ⟨fun X hX => (h.2 _).1 fun n => Q.prop_of_iso
    (((DerivedCategory.homologyFunctor _ 0).shiftIso a n (a + n) rfl).app X).symm
    ((h.2 _).2 hX (a + n))⟩⟩
  letI : L.CommShift ℤ := adj.leftAdjointCommShift ℤ
  exact ((L ⋙ P.ι).commShiftIso p).app K

end Completion

section Reindex

variable {C : Type u} [Category.{v} C] [Abelian C]

private def reindexedPage (S : CohomologicalSpectralSequence C 0) (r : ℤ) (hr : 2 ≤ r) :
    HomologicalComplex C (ComplexShape.up' (r, 1 - r)) where
  X x := (S.page (r - 1) (by omega)).X (reindexEquiv x)
  d x y := (S.page (r - 1) (by omega)).d (reindexEquiv x) (reindexEquiv y)
  shape x y h := by
    apply (S.page (r - 1) (by omega)).shape
    intro hh
    apply h
    change reindexEquiv x + (r - 1, 1 - (r - 1)) = reindexEquiv y at hh
    change x + (r, 1 - r) = y
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    dsimp [reindexEquiv] at h1 h2
    ext <;> dsimp <;> omega
  d_comp_d' x y z _ _ := (S.page (r - 1) (by omega)).d_comp_d _ _ _

private def reindexedHomologyIso (S : CohomologicalSpectralSequence C 0) (r : ℤ) (hr : 2 ≤ r)
    (x : ℤ × ℤ) :
    (reindexedPage S r hr).homology x ≅ (S.page (r - 1) (by omega)).homology (reindexEquiv x) := by
  let a := x - (r, 1 - r)
  let b := x + (r, 1 - r)
  have ha : (ComplexShape.up' (r, 1 - r)).prev x = a :=
    ComplexShape.prev_eq' _ (by change a + (r, 1 - r) = x; simp [a])
  have hb : (ComplexShape.up' (r, 1 - r)).next x = b :=
    ComplexShape.next_eq' _ rfl
  have ha' : (ComplexShape.up' (r - 1, 1 - (r - 1))).prev (reindexEquiv x) = reindexEquiv a := by
    apply ComplexShape.prev_eq'
    change reindexEquiv a + (r - 1, 1 - (r - 1)) = reindexEquiv x
    ext <;> dsimp [reindexEquiv, a] <;> omega
  have hb' : (ComplexShape.up' (r - 1, 1 - (r - 1))).next (reindexEquiv x) = reindexEquiv b := by
    apply ComplexShape.next_eq'
    change reindexEquiv x + (r - 1, 1 - (r - 1)) = reindexEquiv b
    ext <;> dsimp [reindexEquiv, b] <;> omega
  exact (reindexedPage S r hr).homologyIsoSc' a x b ha hb ≪≫
    ShortComplex.homologyMapIso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, HomologicalComplex.sc', Category.id_comp,
        Category.comp_id])
      (by simp only [Iso.refl_hom, HomologicalComplex.sc', Category.id_comp,
        Category.comp_id])) ≪≫
    ((S.page (r - 1) (by omega)).homologyIsoSc' (reindexEquiv a) (reindexEquiv x)
      (reindexEquiv b) ha' hb').symm

private def reindexedSpectralSequence (S : CohomologicalSpectralSequence C 0) :
    E₂CohomologicalSpectralSequence C where
  page := reindexedPage S
  iso r r' x h hr := reindexedHomologyIso S r hr x ≪≫
    S.iso (r - 1) (r'-1) (reindexEquiv x) (by omega) (by omega)

private theorem finite_diagonal_of_reindex
    (S : CohomologicalSpectralSequence C 0) (E : E₂CohomologicalSpectralSequence C)
    (e : ∀ i j, (E.page 2).X (i, j) ≅ (S.page 1).X (-j, i + 2 * j))
    (h : ∀ n, {p | ¬ IsZero ((S.page 1).X (p, n - p))}.Finite) :
    ∀ n, {i | ¬ IsZero ((E.page 2).X (i, n - i))}.Finite := by
  intro n
  apply ((h n).preimage (f := fun i : ℤ => i - n) (by
    intro a ha b hb hab
    dsimp at hab
    omega)).subset
  intro i hi
  show ¬ IsZero ((S.page 1).X (i - n, n - (i - n)))
  intro hs
  apply hi
  apply hs.of_iso
  exact e i (n - i) ≪≫ eqToIso (by congr 1; ext <;> dsimp <;> omega)

end Reindex

section Convergence

open CochainComplex FilteredComplexSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem le_of_isZero_cokernel {X : C} {U V : Subobject X}
    (h : U ≤ V) (hz : IsZero (cokernel (Subobject.ofLE U V h))) : V ≤ U := by
  let j := Subobject.ofLE U V h
  have : Epi j := Abelian.epi_of_cokernel_π_eq_zero j (hz.eq_of_tgt _ _)
  have : IsIso j := isIso_of_mono_of_epi j
  apply Subobject.le_of_comm (inv j)
  rw [← Subobject.ofLE_arrow h]
  show inv j ≫ (j ≫ V.arrow) = V.arrow
  simp

private theorem cycles_le_boundaries_of_isZero (M : Filtered C)
    (r p n : ℤ) (hr : 0 ≤ r)
    (h : IsZero ((Filtered.spectralSequenceFunctor.obj M).page r hr |>.X (p, n - p))) :
    cycles M.X (filtrationSubobject M) r p n ≤
      boundaries M.X (filtrationSubobject M) r p n := by
  generalize hq : n - p = q at h
  obtain rfl : n = p + q := by omega
  have hz := h.of_iso (Filtered.pageIso M r p q hr).symm
  exact (le_of_isZero_cokernel inf_le_right hz).trans inf_le_left

private theorem exists_inf_pullback {X Y : C} (f : X ⟶ Y) (U : Subobject X) (V : Subobject Y) :
    (Subobject.exists f).obj (U ⊓ (Subobject.pullback f).obj V) =
      (Subobject.exists f).obj U ⊓ V := by
  apply le_antisymm
  · exact le_inf ((Subobject.exists f).monotone inf_le_left)
      ((Subobject.exists_le_iff_le_pullback f _ _).2 inf_le_right)
  · let W := (Subobject.exists f).obj U ⊓ V
    obtain ⟨T, e, he, b, hb⟩ := (Subobject.exists_factors_iff f U W.arrow).1
      (Subobject.inf_arrow_factors_left _ _)
    apply Subobject.le_of_factors
    apply Subobject.factors_of_epi_comp e
    rw [hb, ← Category.assoc]
    apply (Subobject.exists_factors_iff f _ _).2
    have hv : V.Factors (b ≫ U.arrow ≫ f) := by
      rw [← hb]
      exact Subobject.factors_of_factors_right _ (Subobject.inf_arrow_factors_right _ _)
    have hu : (U ⊓ (Subobject.pullback f).obj V).Factors (b ≫ U.arrow) :=
      (Subobject.inf_factors _).2 ⟨Subobject.factors_comp_arrow _,
        (pullback_factors_iff _ _ _).2 (by simpa [Category.assoc] using hv)⟩
    exact ⟨_, 𝟙 _, inferInstance,
      (U ⊓ (Subobject.pullback f).obj V).factorThru _ hu, by
        simp [Category.assoc]⟩

/-- The image under `d` of the `s`-th cycles of `F^k` is `F^p ⊓ d (F^k)` when `k + s = p`. -/
private theorem exists_cycles_eq_inf (M : Filtered C) (n s k p : ℤ) (hk : k + s = p) :
    (Subobject.exists (M.X.d (n - 1) n)).obj (cycles M.X (filtrationSubobject M) s k (n - 1)) =
      filtrationSubobject M p n ⊓
        (Subobject.exists (M.X.d (n - 1) n)).obj (filtrationSubobject M k (n - 1)) := by
  unfold cycles
  rw [show n - 1 + 1 = n by omega, hk, exists_inf_pullback, inf_comm]

private theorem cycleNumerator_eq_succ_of_isZero (M : Filtered C)
    (r p n : ℤ) (hr : 1 ≤ r)
    (h : IsZero ((Filtered.spectralSequenceFunctor.obj M).page r
      (by omega) |>.X (p + r, n + 1 - (p + r)))) :
    cycles M.X (filtrationSubobject M) r p n ⊔ filtrationSubobject M (p + 1) n =
      cycles M.X (filtrationSubobject M) (r + 1) p n ⊔ filtrationSubobject M (p + 1) n := by
  let F := filtrationSubobject M
  let Z := cycles M.X F
  let D := boundaries M.X F
  have hz : Z r (p + r) (n + 1) ≤ D r (p + r) (n + 1) :=
    cycles_le_boundaries_of_isZero M r (p + r) (n + 1) (by omega) h
  have hk : Z r p n ≤ kernelNumerator M.X F r p n :=
    le_inf le_rfl <| (Subobject.exists_le_iff_le_pullback _ _ _).1 <|
      le_inf ((exists_cycles_le M.X F r p n).trans hz) (exists_cycles_le M.X F r p n)
  rw [kernelNumerator_eq M.X F
    (filtrationSubobject_antitone M)] at hk
  have hd : D r p n ≤ Z (r + 1) p n ⊔ F (p + 1) n := by
    refine sup_le ((cycles_le_F M.X F (r - 1) (p + 1) n).trans le_sup_right) ?_
    apply le_trans _ le_sup_left
    apply le_inf
    · apply (Subobject.exists_le_iff_le_pullback _ _ _).2
      show F _ _ ⊓ _ ≤ _
      rw [show n - 1 + 1 = n by omega, show p - r + 1 + (r - 1) = p by omega]
      exact inf_le_right
    · exact Subobject.exists_le_pullback_of_comp_eq_zero (M.X.d_comp_d _ _ _) _ _
  exact le_antisymm (sup_le (hk.trans (sup_le le_sup_left (inf_le_left.trans hd))) le_sup_right)
    (sup_le_sup_right (cycles_succ_le M.X F (filtrationSubobject_antitone M) r p n) _)

private theorem boundaryNumerator_eq_pred_of_isZero (M : Filtered C)
    (r p n : ℤ) (hr : 1 ≤ r)
    (h : IsZero ((Filtered.spectralSequenceFunctor.obj M).page r
      (by omega) |>.X (p - r, n - 1 - (p - r)))) :
    filtrationSubobject M p n ⊓ (Subobject.exists (M.X.d (n - 1) n)).obj
        (filtrationSubobject M (p - r) (n - 1)) ⊔ filtrationSubobject M (p + 1) n =
      filtrationSubobject M p n ⊓ (Subobject.exists (M.X.d (n - 1) n)).obj
        (filtrationSubobject M (p - (r - 1)) (n - 1)) ⊔ filtrationSubobject M (p + 1) n := by
  let F := filtrationSubobject M
  let Z := cycles M.X F
  let D := boundaries M.X F
  have hz : Z r (p - r) (n - 1) ≤ D r (p - r) (n - 1) :=
    cycles_le_boundaries_of_isZero M r (p - r) (n - 1) (by omega) h
  apply le_antisymm
  · apply sup_le _ le_sup_right
    rw [← exists_cycles_eq_inf M n r (p - r) p (by omega)]
    refine ((Subobject.exists _).monotone hz).trans ?_
    dsimp only [D, boundaries]
    rw [(Subobject.existsPullbackAdj (M.X.d (n - 1) n)).gc.l_sup]
    apply sup_le
    · rw [exists_cycles_eq_inf M n (r - 1) (p - r + 1) p (by omega),
        show p - r + 1 = p - (r - 1) by omega]
      exact le_sup_left
    · apply (Subobject.exists_le_iff_le_pullback _ _ _).2
      exact Subobject.exists_le_pullback_of_comp_eq_zero (M.X.d_comp_d _ _ _) _ _
  · exact sup_le_sup_right (inf_le_inf_left _ ((Subobject.exists _).monotone
      (filtrationSubobject_antitone M _ _ _ (by omega)))) _

private theorem exists_cokernelIso_sup {X : C} (D U W : Subobject X)
    (hD : D ≤ U) (hW : W ⊓ U ≤ D) :
    Nonempty (cokernel (Subobject.ofLE D U hD) ≅
      cokernel (Subobject.ofLE (D ⊔ W) (U ⊔ W) (sup_le_sup_right hD W))) := by
  let j := Subobject.ofLE D U hD
  let j' := Subobject.ofLE (D ⊔ W) (U ⊔ W) (sup_le_sup_right hD W)
  let v := Subobject.ofLE U (U ⊔ W) le_sup_left
  have hv : v ≫ (U ⊔ W).arrow = U.arrow := Subobject.ofLE_arrow _
  have : Mono (v ≫ (U ⊔ W).arrow) := by
    rw [hv]
    infer_instance
  have : Epi (v ≫ cokernel.π j') :=
    Subobject.epi_comp_cokernel_π (Y := W) j' (Subobject.ofLE_arrow _) v
      (by simp only [hv, Subobject.mk_arrow]; exact le_rfl) le_sup_right
  have hi : (D ⊔ W) ⊓ U = D := (sup_inf_assoc_of_le _ hD).trans (sup_eq_left.2 hW)
  obtain ⟨e, _⟩ := Subobject.exists_iso_cokernel_of_factors_iff j
    (Subobject.ofLE_arrow _) j' (Subobject.ofLE_arrow _) (𝟙 _) v
    (fun {T} g => by
      simp only [Category.id_comp, hv]
      exact ⟨Subobject.factors_of_le _ le_sup_left, fun h => by
        simpa only [hi] using
          (Subobject.inf_factors (g ≫ U.arrow)).2 ⟨h, Subobject.factors_comp_arrow _⟩⟩)
  exact ⟨e⟩

private def cokernelOfLEIso {X : C} {D U D' U' : Subobject X}
    (h : D ≤ U) (h' : D' ≤ U') (eD : D = D') (eU : U = U') :
    cokernel (Subobject.ofLE D U h) ≅ cokernel (Subobject.ofLE D' U' h') := by
  subst D'
  subst U'
  exact Iso.refl _

private theorem pageObject_iso_normalized (M : Filtered C)
    (r p n : ℤ) :
    Nonempty (pageObj M.X (filtrationSubobject M) r p n ≅
      cokernel (Subobject.ofLE
        ((filtrationSubobject M p n ⊓ (Subobject.exists (M.X.d (n - 1) n)).obj
          (filtrationSubobject M (p - r + 1) (n - 1)) ⊔ filtrationSubobject M (p + 1) n) ⊓
          (cycles M.X (filtrationSubobject M) r p n ⊔ filtrationSubobject M (p + 1) n))
        (cycles M.X (filtrationSubobject M) r p n ⊔ filtrationSubobject M (p + 1) n)
        inf_le_right)) := by
  let F := filtrationSubobject M
  let Z := cycles M.X F r p n
  let D := boundaries M.X F r p n
  let W := F (p + 1) n
  have he := exists_cycles_eq_inf M n (r - 1) (p - r + 1) p (by omega)
  have hD : D ≤ Z := by
    refine sup_le (cycles_pred_succ_le M.X F
      (filtrationSubobject_antitone M) r p n) ?_
    refine le_inf ?_ ?_
    · rw [he]
      exact inf_le_left
    · exact Subobject.exists_le_pullback_of_comp_eq_zero (M.X.d_comp_d _ _ _) _ _
  have hW : W ⊓ Z ≤ D := by
    apply le_trans _ le_sup_left
    show F (p + 1) n ⊓ (F p n ⊓ _) ≤ F (p + 1) n ⊓ _
    rw [← inf_assoc, inf_eq_left.2 (filtrationSubobject_antitone M _ _ n (by omega)),
      show p + 1 + (r - 1) = p + r by omega]
  have hDW : D ⊔ W =
      F p n ⊓ (Subobject.exists (M.X.d (n - 1) n)).obj (F (p - r + 1) (n - 1)) ⊔ W := by
    dsimp only [D, boundaries]
    rw [he]
    have hz : cycles M.X F (r - 1) (p + 1) n ≤ W := inf_le_left
    exact le_antisymm
      (sup_le (sup_le (hz.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
  have hle : D ⊔ W ≤ Z ⊔ W := sup_le_sup_right hD W
  obtain ⟨e⟩ := exists_cokernelIso_sup D Z W hD hW
  refine ⟨cokernelOfLEIso inf_le_right hD (inf_eq_left.2 hD) rfl ≪≫ e ≪≫
    cokernelOfLEIso hle inf_le_right ?_ rfl⟩
  rw [← hDW]
  exact (inf_eq_left.2 hle).symm

private theorem eq_of_isGLB_of_eventually_eq {α : Type*} [PartialOrder α]
    (f : ℤ → α) (hf : Antitone f) (a : α)
    (ha : IsGLB (Set.range fun i : ℕ => f i) a) (k : ℤ) (hk : 0 ≤ k)
    (h : ∀ m, k ≤ m → f m = f k) : f k = a := by
  apply le_antisymm
  · apply ha.2
    rintro _ ⟨i, rfl⟩
    rcases le_total (i : ℤ) k with hi | hi
    · exact hf hi
    · exact (h i hi).ge
  · exact ha.1 ⟨k.toNat, congrArg f (Int.toNat_of_nonneg hk)⟩

private theorem eq_of_isLUB_of_eventually_eq {α : Type*} [PartialOrder α]
    (f : ℤ → α) (hf : Monotone f) (a : α)
    (ha : IsLUB (Set.range fun i : ℕ => f i) a) (k : ℤ) (hk : 0 ≤ k)
    (h : ∀ m, k ≤ m → f m = f k) : f k = a :=
  eq_of_isGLB_of_eventually_eq (α := OrderDual α) f hf a ha k hk h

private theorem eq_of_ge_of_eq_succ {α : Type*} (f : ℤ → α) (k : ℤ)
    (h : ∀ m, k ≤ m → f (m + 1) = f m) (m : ℤ) (hm : k ≤ m) : f m = f k := by
  induction m, hm using Int.leInduction with
  | base => rfl
  | succ m hm ih => exact (h m hm).trans ih

private theorem exists_stable_page (M : Filtered C)
    (hfinite : ∀ n : ℤ, {p : ℤ | ¬ IsZero
      ((Filtered.spectralSequenceFunctor.obj M).page 1 |>.X (p, n - p))}.Finite)
    (hbounds : ∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ => filtrationSubobject M p n ⊓
        (Subobject.pullback (M.X.d n (n + 1))).obj (filtrationSubobject M (p + r) (n + 1)) ⊔
          filtrationSubobject M (p + 1) n)
        (kernelSubobject (M.X.d n (n + 1)) ⊓ filtrationSubobject M p n ⊔
          filtrationSubobject M (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ => filtrationSubobject M p n ⊓
        (Subobject.exists (M.X.d (n - 1) n)).obj (filtrationSubobject M (p - r) (n - 1)) ⊔
          filtrationSubobject M (p + 1) n)
        (imageSubobject (M.X.d (n - 1) n) ⊓ filtrationSubobject M p n ⊔
          filtrationSubobject M (p + 1) n)) :
    ∀ p q : ℤ, ∃ (r₀ : ℤ) (hr₀ : 1 ≤ r₀), ∀ r : ℤ, ∀ hr : r₀ ≤ r,
      ((Filtered.spectralSequenceFunctor.obj M).page r (by omega)).d
        (p, q) (p + r, q - r + 1) = 0 ∧
      ((Filtered.spectralSequenceFunctor.obj M).page r (by omega)).d
        (p - r, q + r - 1) (p, q) = 0 ∧
      Nonempty (((Filtered.spectralSequenceFunctor.obj M).page r
        (by omega)).X (p, q) ≅
        cokernel (Subobject.ofLE
          ((imageSubobject (M.X.d (p + q - 1) (p + q)) ⊓ filtrationSubobject M p (p + q) ⊔
            filtrationSubobject M (p + 1) (p + q)) ⊓
            (kernelSubobject (M.X.d (p + q) (p + q + 1)) ⊓ filtrationSubobject M p (p + q) ⊔
              filtrationSubobject M (p + 1) (p + q)))
          (kernelSubobject (M.X.d (p + q) (p + q + 1)) ⊓ filtrationSubobject M p (p + q) ⊔
            filtrationSubobject M (p + 1) (p + q)) inf_le_right)) := by
  intro p q
  let S := Filtered.spectralSequenceFunctor.obj M
  let n := p + q
  obtain ⟨a, ha⟩ := (hfinite (n - 1)).bddBelow
  obtain ⟨b, hb⟩ := (hfinite (n + 1)).bddAbove
  let R := max 1 (max (b - p + 1) (p - a + 1))
  have hR : 1 ≤ R := le_max_left _ _
  have hout (r : ℤ) (hr : R ≤ r) : IsZero ((S.page r (by omega)).X (p + r, n + 1 - (p + r))) := by
    apply S.isZero_page_of_le (r := 1) (by omega) _ _ r (by omega)
    by_contra hz
    have hh := hb hz
    dsimp [R] at hr
    omega
  have hin (r : ℤ) (hr : R ≤ r) : IsZero ((S.page r (by omega)).X (p - r, n - 1 - (p - r))) := by
    apply S.isZero_page_of_le (r := 1) (by omega) _ _ r (by omega)
    by_contra hz
    have hh := ha hz
    dsimp [R] at hr
    omega
  let N (r : ℤ) := cycles M.X (filtrationSubobject M) r p n ⊔ filtrationSubobject M (p + 1) n
  let B (r : ℤ) := filtrationSubobject M p n ⊓ (Subobject.exists (M.X.d (n - 1) n)).obj
    (filtrationSubobject M (p - r) (n - 1)) ⊔ filtrationSubobject M (p + 1) n
  have hNanti : Antitone N := fun i j hij =>
    sup_le_sup_right (cycles_mono M.X (filtrationSubobject M)
      (filtrationSubobject_antitone M) n le_rfl (by omega)) _
  have hBmono : Monotone B := fun i j hij =>
    sup_le_sup_right (inf_le_inf_left _ ((Subobject.exists _).monotone
      (filtrationSubobject_antitone M _ _ _ (by omega)))) _
  have hNs (m : ℤ) (hm : R ≤ m) : N m = N R :=
    eq_of_ge_of_eq_succ N R (fun r hr =>
      (cycleNumerator_eq_succ_of_isZero M r p n (by omega) (hout r hr)).symm) m hm
  have hBs (m : ℤ) (hm : R ≤ m) : B m = B R := by
    apply eq_of_ge_of_eq_succ B R _ m hm
    intro r hr
    simpa only [show r + 1 - 1 = r by omega] using
      boundaryNumerator_eq_pred_of_isZero M (r + 1) p n (by omega) (hin (r + 1) (by omega))
  have hNeq : N R = kernelSubobject (M.X.d n (n + 1)) ⊓ filtrationSubobject M p n ⊔
      filtrationSubobject M (p + 1) n :=
    eq_of_isGLB_of_eventually_eq N hNanti _ (hbounds p n).1 R (by omega) hNs
  have hBeq : B R = imageSubobject (M.X.d (n - 1) n) ⊓ filtrationSubobject M p n ⊔
      filtrationSubobject M (p + 1) n :=
    eq_of_isLUB_of_eventually_eq B hBmono _ (hbounds p n).2 R (by omega) hBs
  refine ⟨R + 1, by omega, fun r hr => ?_⟩
  have ho : IsZero ((S.page r (by omega)).X (p + r, q - r + 1)) := by
    have he : n + 1 - (p + r) = q - r + 1 := by
      dsimp [n]
      omega
    simpa only [he] using hout r (by omega)
  have hi : IsZero ((S.page r (by omega)).X (p - r, q + r - 1)) := by
    have he : n - 1 - (p - r) = q + r - 1 := by
      dsimp [n]
      omega
    simpa only [he] using hin r (by omega)
  refine ⟨ho.eq_of_tgt _ _, hi.eq_of_src _ _, ?_⟩
  have hn : N r = _ := (hNs r (by omega)).trans hNeq
  have hb : B (r - 1) = _ := (hBs (r - 1) (by omega)).trans hBeq
  obtain ⟨e⟩ := pageObject_iso_normalized M r p n
  refine ⟨Filtered.pageIso M r p q (by omega) ≪≫
    e ≪≫ cokernelOfLEIso inf_le_right inf_le_right ?_ hn⟩
  rw [show p - r + 1 = p - (r - 1) by omega]
  show (B (r - 1) ⊓ N r) = _
  rw [hb, hn]

end Convergence

-- The existential package names each component it binds; several are pinned only by the
-- equations that follow, so the unused-variable linter is silenced rather than the names lost.
set_option linter.unusedVariables false in
/-- **Stacks 0BKE.** For a finitely generated ideal `I` and `K ∈ D(A)`, the truncation
filtration gives a bounded cohomological spectral sequence `S₁^{p,q} ≅ H^{2p+q}(H^{-p}(K)^∧)`
converging to `H^{p+q}(K^∧)`. After the reindexing `p = -j`, `q = i + 2j` and a shift of the page
number by one it is a bounded spectral sequence of derived-complete modules with
`E₂^{i,j} ≅ H^i(H^j(K)^∧)` converging to `H^{i+j}(K^∧)`. -/
@[stacks 0BKE]
theorem exists_spectralSequence_derivedCompletion_homology
    (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (K : DerivedCategory (ModuleCat.{v} A)) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∃ (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
      (adj : completion ⊣ P.ι)
      (C : CochainComplex (ModuleCat.{v} A) ℤ)
      (eK : DerivedCategory.Q.obj C ≅ K)
      (T : FilteredObject (CochainComplex (ModuleCat.{v} A) ℤ) ℤᵒᵖ)
      (eUnderlying : T.X ≅ C)
      (eStep : ∀ p : ℤ, T.filtration.obj (op p) ≅ C.truncLE (-p))
      (eStep_ι : ∀ p : ℤ,
        (eStep p).hom ≫ C.ιTruncLE (-p) =
          T.filtration.ι.app (op p) ≫ eUnderlying.hom)
      (hT : T.filtration.IsDegreewiseFinite)
      (M : CochainComplex.Filtered (ModuleCat.{v} A))
      (eTotal : DerivedCategory.Q.obj M.X ≅ (completion ⋙ P.ι).obj K)
      (eCohomology : ∀ n : ℤ, M.X.homology n ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj
          ((completion ⋙ P.ι).obj K)),
      let S := CochainComplex.Filtered.spectralSequenceFunctor.obj M
      ∃ (E : E₂CohomologicalSpectralSequence (ModuleCat.{v} A))
      (eGr : ∀ p : ℤ,
        DerivedCategory.Q.obj ((FilteredObject.gr p).obj T) ≅
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) (-p)).obj K))⟦p⟧)
      (e₁Filtered : ∀ p q : ℤ, (S.page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).obj
          ((completion ⋙ P.ι).obj
            (DerivedCategory.Q.obj ((FilteredObject.gr p).obj T))))
      (e₁ : ∀ p q : ℤ, (S.page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (2 * p + q)).obj
          ((completion ⋙ P.ι).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
              ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) (-p)).obj K))))
      (e₂ : ∀ i j : ℤ, (E.page 2).X (i, j) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
          ((completion ⋙ P.ι).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
              ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj K))))
      (reindex : ∀ (r i j : ℤ) (hr : 2 ≤ r),
        (E.page r hr).X (i, j) ≅ (S.page (r - 1) (by omega)).X (-j, i + 2 * j))
      (hF : ∀ n : ℤ, Antitone (M.inducedFiltrationStep n)),
      (∀ (r p q : ℤ) (hr : 1 ≤ r),
        IsDerivedCompleteModule I ((S.page r (by omega)).X (p, q))) ∧
      (∀ (r i j : ℤ) (hr : 2 ≤ r),
        IsDerivedCompleteModule I ((E.page r hr).X (i, j))) ∧
      (∀ (r i j : ℤ) (hr : 2 ≤ r),
        (reindex r i j hr).hom ≫ (S.page (r - 1) (by omega)).d
              (-j, i + 2 * j) (-(j - r + 1), (i + r) + 2 * (j - r + 1)) =
          (E.page r hr).d (i, j) (i + r, j - r + 1) ≫
            (reindex r (i + r) (j - r + 1) hr).hom) ∧
      (∀ n : ℤ, {p : ℤ | ¬ IsZero ((S.page 1 (by omega)).X (p, n - p))}.Finite) ∧
      (∀ n : ℤ, {i : ℤ | ¬ IsZero ((E.page 2).X (i, n - i))}.Finite) ∧
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ M.inducedFiltrationStep n a = ⊤ ∧
        M.inducedFiltrationStep n b = ⊥) ∧
      (∀ p q : ℤ, ∃ (r₀ : ℤ) (hr₀ : 1 ≤ r₀), ∀ (r : ℤ) (hr : r₀ ≤ r),
        (S.page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
        (S.page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 ∧
        Nonempty ((S.page r (by omega)).X (p, q) ≅
          cokernel (Subobject.ofLE (M.inducedFiltrationStep (p + q) (p + 1))
            (M.inducedFiltrationStep (p + q) p) (hF (p + q) (by omega))))) ∧
      ∀ i j : ℤ, ∃ (r₀ : ℤ) (hr₀ : 2 ≤ r₀), ∀ (r : ℤ) (hr : r₀ ≤ r),
        (E.page r (by omega)).d (i, j) (i + r, j - r + 1) = 0 ∧
        (E.page r (by omega)).d (i - r, j + r - 1) (i, j) = 0 ∧
        Nonempty ((E.page r (by omega)).X (i, j) ≅
          cokernel (Subobject.ofLE (M.inducedFiltrationStep (i + j) (-j + 1))
            (M.inducedFiltrationStep (i + j) (-j)) (hF (i + j) (by omega)))) := by
  classical
  let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
    fun L => IsDerivedComplete I L
  obtain ⟨completion, ⟨adj⟩⟩ := exists_completion (A := A) I hI
  let C := (DerivedCategory.Q (C := ModuleCat.{v} A)).objPreimage K
  let eK : DerivedCategory.Q.obj C ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let T := postnikovFiltered C
  obtain ⟨M, eTotal₀, eCohomology₀, hcomplete, e₁Filtered₀, hdata⟩ :=
    exists_derivedCompletion_spectralSequence A I hI T completion adj
  let eTotal := eTotal₀ ≪≫ (completion ⋙ P.ι).mapIso eK
  let eCohomology (n : ℤ) := eCohomology₀ n ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).mapIso
      ((completion ⋙ P.ι).mapIso eK)
  refine ⟨completion, adj, C, eK, T, postnikovUnderlyingIso C, postnikovStepIso C,
    postnikovStepIso_hom_ιTruncLE C, postnikovFinite C, M, eTotal, eCohomology, ?_⟩
  let S := CochainComplex.Filtered.spectralSequenceFunctor.obj M
  let E := reindexedSpectralSequence S
  let eGr := postnikovGradedIso C K eK
  let e₁Filtered (p q : ℤ) := (e₁Filtered₀ p q).some
  let e₁ (p q : ℤ) := e₁Filtered p q ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).mapIso
      ((completion ⋙ P.ι).mapIso (eGr p) ≪≫
        completionShiftIso I completion adj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) (-p)).obj K)) p) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).shiftIso p (p + q)
      (2 * p + q) (by omega)).app _
  have e₂ (i j : ℤ) : (E.page 2).X (i, j) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
        ((completion ⋙ P.ι).obj ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).obj K))) := by
    show (S.page 1).X (-j, i + 2 * j) ≅ _
    simpa only [DerivedCategory.shift_homologyFunctor, neg_neg,
      show 2 * -j + (i + 2 * j) = i by omega] using e₁ (-j) (i + 2 * j)
  let reindex (r i j : ℤ) (hr : 2 ≤ r) :
      (E.page r hr).X (i, j) ≅ (S.page (r - 1) (by omega)).X (-j, i + 2 * j) := Iso.refl _
  let hF : ∀ n : ℤ, Antitone (M.inducedFiltrationStep n) := M.inducedFiltrationStep_antitone
  obtain ⟨hfinite, hbounded, _, hlimits, hcomparison⟩ := hdata (postnikovFinite C)
  have hstable : ∀ p q : ℤ, ∃ (r₀ : ℤ) (hr₀ : 1 ≤ r₀), ∀ (r : ℤ) (hr : r₀ ≤ r),
      (S.page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
      (S.page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 ∧
      Nonempty ((S.page r (by omega)).X (p, q) ≅
        cokernel (Subobject.ofLE (M.inducedFiltrationStep (p + q) (p + 1))
          (M.inducedFiltrationStep (p + q) p) (hF (p + q) (by omega)))) := by
    intro p q
    obtain ⟨r₀, hr₀, h⟩ := exists_stable_page M hfinite hlimits p q
    obtain ⟨a, b, hFH, e, _⟩ := hcomparison p (p + q)
    exact ⟨r₀, hr₀, fun r hr => ⟨(h r hr).1, (h r hr).2.1, (h r hr).2.2.map (· ≪≫ e)⟩⟩
  refine ⟨E, eGr, e₁Filtered, e₁, e₂, reindex, hF, hcomplete,
    fun r i j hr => hcomplete (r - 1) (-j) (i + 2 * j) (by omega), ?_, hfinite,
    finite_diagonal_of_reindex S E (fun i j => reindex 2 i j (by omega)) hfinite,
    hbounded, hstable, ?_⟩
  · intro r i j hr
    dsimp only [reindex, E, reindexedSpectralSequence, reindexedPage, Iso.refl_hom,
      reindexEquiv_apply]
    simp only [Category.id_comp, Category.comp_id]
    rfl
  · intro i j
    obtain ⟨r₀, hr₀, h⟩ := hstable (-j) (i + 2 * j)
    refine ⟨r₀ + 1, by omega, fun r hr => ?_⟩
    obtain ⟨ho, hi, ⟨e⟩⟩ := h (r - 1) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (S.page (r - 1) (by omega)).d (-j, i + 2 * j)
        (-(j - r + 1), (i + r) + 2 * (j - r + 1)) = 0
      rwa [reindex_target]
    · show (S.page (r - 1) (by omega)).d (-(j + r - 1), (i - r) + 2 * (j + r - 1))
        (-j, i + 2 * j) = 0
      rwa [reindex_source]
    · let gr (n : ℤ) := cokernel (Subobject.ofLE
        (M.inducedFiltrationStep n (-j + 1)) (M.inducedFiltrationStep n (-j))
        (hF n (by omega)))
      exact ⟨e ≪≫ eqToIso (congrArg gr (show -j + (i + 2 * j) = i + j by omega))⟩

end AdicFilteredCompletion

end
