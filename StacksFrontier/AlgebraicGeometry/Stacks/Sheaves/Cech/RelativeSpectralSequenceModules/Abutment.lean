module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedTensor
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.TwoFibreProductEqualizers
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechRows
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechSections
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechRows

/-!
# Existence of the relative Čech spectral sequence for sheaves of modules

Spectral sequences of first-quadrant double complexes indexed by `ℕ × ℕ` and their abutment when
the rows are resolutions, and the resulting relative Čech-to-cohomology spectral sequence
`exists_moduleSpectralSequenceData` (Stacks, Tag 06XG).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.RelativeCech

universe u vᵤ vₓ wᵤ wₓ a v₁ w₁ v₂ w₂ r

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰] {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (τ : AlgebraicGeometry.SiteKind)

attribute [local instance] siteHasSheafifyAt siteWEqualsLocallyBijectiveAt

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

section DoubleComplex

open HomologicalComplex Opposite

universe v

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A double complex indexed by `ℕ × ℕ`, extended by zero to one indexed by `ℤ × ℤ`. -/
private abbrev extendDoubleComplex (K : HomologicalComplex₂ A (ComplexShape.up ℕ)
    (ComplexShape.up ℕ)) :
    HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((ComplexShape.embeddingUpNat.extendFunctor A).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).extend ComplexShape.embeddingUpNat

/-- In a nonnegative degree, the column of the extended double complex is the extension of the
corresponding column. -/
private def extendDoubleComplexColumnIso
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (i : ℕ) :
    (extendDoubleComplex K).X (i : ℤ) ≅ (K.X i).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendXIso _ _ rfl

/-- In a nonnegative degree, the row of the extended double complex is the extension of the
corresponding row. -/
private def extendDoubleComplexRowIso
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (j : ℕ) :
    (extendDoubleComplex K).flip.X (j : ℤ) ≅
      (K.flip.X j).extend ComplexShape.embeddingUpNat :=
  Stacks.DerivedIndexing.mapExtendIsoSymm (HomologicalComplex.eval A (ComplexShape.up ℤ) (j : ℤ))
    ComplexShape.embeddingUpNat _ ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor A).mapIso
        ((NatIso.mapHomologicalComplex
          (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso A (show (j : ℤ) = j from rfl))
          (ComplexShape.up ℕ)).app K)

/-- The extension by zero of a complex indexed by `ℕ` vanishes in negative degrees. -/
private lemma isZero_extend_X_of_neg (T : HomologicalComplex A (ComplexShape.up ℕ))
    (i : ℤ) (hi : i < 0) : IsZero ((T.extend ComplexShape.embeddingUpNat).X i) :=
  HomologicalComplex.isZero_extend_X _ _ i (fun n h => by change (n : ℤ) = i at h; omega)

/-- The columns of the extended double complex in negative degrees vanish. -/
private lemma extendDoubleComplex_isZero₁
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (i : ℤ) (hi : i < 0) : IsZero ((extendDoubleComplex K).X i) :=
  isZero_extend_X_of_neg _ i hi

/-- The terms of the extended double complex outside the first quadrant vanish. -/
private lemma extendDoubleComplex_isZero₂
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (i j : ℤ) (hj : j < 0) : IsZero (((extendDoubleComplex K).X i).X j) := by
  by_cases hi : i < 0
  · exact (HomologicalComplex.eval _ _ j).map_isZero (extendDoubleComplex_isZero₁ K i hi)
  · lift i to ℕ using (by omega : 0 ≤ i)
    apply IsZero.of_iso _ ((HomologicalComplex.eval _ _ j).mapIso
      (extendDoubleComplexColumnIso K i))
    exact isZero_extend_X_of_neg _ j hj

/-- Being supported in the first quadrant, the extended double complex has a total complex. -/
private lemma extendDoubleComplex_hasTotal
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    (extendDoubleComplex K).HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded (extendDoubleComplex K) 0
    (extendDoubleComplex_isZero₂ K) (extendDoubleComplex_isZero₁ K)

attribute [local instance] extendDoubleComplex_hasTotal

/-- The map of extended double complexes induced by a map of double complexes indexed by
`ℕ × ℕ`. -/
private abbrev extendDoubleComplexMap
    {K L : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (g : K ⟶ L) :=
  HomologicalComplex.extendMap
    (((ComplexShape.embeddingUpNat.extendFunctor A).mapHomologicalComplex
      (ComplexShape.up ℕ)).map g) ComplexShape.embeddingUpNat

/-- A map of double complexes that is a quasi-isomorphism in each column induces a
quasi-isomorphism of the total complexes of the extensions. -/
private lemma extendDoubleComplexMap_quasiIso
    {K L : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (g : K ⟶ L) (hg : ∀ i, QuasiIso (g.f i)) :
    QuasiIso (HomologicalComplex₂.total.map (extendDoubleComplexMap g) (ComplexShape.up ℤ)) := by
  apply StacksDraft.TotalComplexQuasiIso.quasiIso_total_map _ 0
    (extendDoubleComplex_isZero₂ K) (extendDoubleComplex_isZero₁ K)
    (extendDoubleComplex_isZero₂ L) (extendDoubleComplex_isZero₁ L)
  intro i
  by_cases hi : i < 0
  · constructor
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((HomologicalComplex.homologyFunctor _ _ j).map_isZero
      (extendDoubleComplex_isZero₁ K i hi)).isIso
      ((HomologicalComplex.homologyFunctor _ _ j).map_isZero
        (extendDoubleComplex_isZero₁ L i hi)) _
  · lift i to ℕ using (by omega : 0 ≤ i)
    show QuasiIso ((HomologicalComplex.extendMap _ ComplexShape.embeddingUpNat).f (i : ℤ))
    rw [HomologicalComplex.extendMap_f _ _ (show (i : ℤ) = i from rfl)]
    have : QuasiIso (g.f i) := hg i
    have : QuasiIso (HomologicalComplex.extendMap (g.f i) ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
    have : QuasiIso
        ((((ComplexShape.embeddingUpNat.extendFunctor A).mapHomologicalComplex
          (ComplexShape.up ℕ)).map g).f i) := by
      show QuasiIso (HomologicalComplex.extendMap (g.f i) ComplexShape.embeddingUpNat)
      infer_instance
    infer_instance

/-- Extending the complex concentrated in degree `0 : ℕ` gives the complex concentrated in
degree `0 : ℤ`, naturally in the object. -/
private def extendSingleNatIso :
    HomologicalComplex.single A (ComplexShape.up ℕ) 0 ⋙
      ComplexShape.embeddingUpNat.extendFunctor A ≅
      HomologicalComplex.single A (ComplexShape.up ℤ) 0 :=
  NatIso.ofComponents (fun X => HomologicalComplex.extendSingleIso
    ComplexShape.embeddingUpNat X 0 0 ComplexShape.embeddingUpNat_f_zero) (by
      intro X Y g
      apply HomologicalComplex.Hom.ext
      funext j
      by_cases hj : j = 0
      · subst j
        change (HomologicalComplex.extendMap
                ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).map g)
                ComplexShape.embeddingUpNat ≫
              (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat Y 0 0
                ComplexShape.embeddingUpNat_f_zero).hom).f 0 =
            ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 0
                ComplexShape.embeddingUpNat_f_zero).hom ≫
              (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map g).f 0
        rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
          HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
            ComplexShape.embeddingUpNat_f_zero,
          HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingUpNat Y 0 0
            ComplexShape.embeddingUpNat_f_zero,
          HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingUpNat X 0 0
            ComplexShape.embeddingUpNat_f_zero,
          HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj).eq_of_tgt _ _)

/-- Extending the double complex of a cochain complex concentrated in row zero gives the row-zero
double complex of its extension. -/
private def extendDoubleSingleIso (T : CochainComplex A ℕ) :
    extendDoubleComplex
      (((HomologicalComplex.single A (ComplexShape.up ℕ) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj T) ≅
      StacksDraft.TotalComplexQuasiIso.singleRowZero (T.extend ComplexShape.embeddingUpNat) :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
    ((NatIso.mapHomologicalComplex extendSingleNatIso (ComplexShape.up ℕ)).app T) ≪≫
      (Stacks.DerivedIndexing.mapExtendIsoSymm (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
        ComplexShape.embeddingUpNat T).symm

/-- The total complex of a cochain complex concentrated in row zero computes the cohomology of that
complex. -/
private def totalSingleNatHomologyIso (T : CochainComplex A ℕ) (n : ℤ) :
    ((extendDoubleComplex
      (((HomologicalComplex.single A (ComplexShape.up ℕ) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj T)).total (ComplexShape.up ℤ)).homology n ≅
      (T.extend ComplexShape.embeddingUpNat).homology n := by
  let Q := StacksDraft.TotalComplexQuasiIso.singleRowZero (T.extend ComplexShape.embeddingUpNat)
  letI : Q.HasTotal (ComplexShape.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded Q 0
      (StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X_X _)
      (fun i hi => (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map_isZero
        (isZero_extend_X_of_neg T i hi))
  let e := extendDoubleSingleIso T
  let eTotal := HomologicalComplex₂.total.mapIso e (ComplexShape.up ℤ)
  let e' := StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit
      (T.extend ComplexShape.embeddingUpNat)
  have : IsIso e' := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleRowZeroUnit _
  exact (HomologicalComplex.homologyFunctor _ _ n).mapIso (eTotal ≪≫ (asIso e').symm)

/-- A cohomological spectral sequence whose first page vanishes outside the first quadrant has an
infinity page at every position. -/
private lemma firstQuadrant_hasPageInfinity
    (E : CohomologicalSpectralSequence A 1)
    (hE : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((E.page 1).X (i, j)))
    (p q : ℤ) : E.HasPageInfinityAt (p, q) := by
  refine ⟨⟨max 1 (p + 1), ?_⟩, ⟨max 1 (q + 2), ?_⟩⟩
  · refine ⟨le_max_left _ _, fun r hr => ⟨by omega, ?_⟩⟩
    intro ij
    by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel ij (p, q)
    · have hp : ij.1 + r = p := congrArg Prod.fst hrel
      exact (E.isZero_page_of_le le_rfl ij
        (hE ij.1 ij.2 (Or.inl (by omega))) r (by omega) (by omega)).eq_of_src _ _
    · exact (E.page r (by omega)).shape _ _ hrel
  · refine ⟨le_max_left _ _, fun r hr => ⟨by omega, ?_⟩⟩
    intro ij
    by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel (p, q) ij
    · have hq : q + (1 - r) = ij.2 := congrArg Prod.snd hrel
      exact (E.isZero_page_of_le le_rfl ij
        (hE ij.1 ij.2 (Or.inr (by omega))) r (by omega) (by omega)).eq_of_tgt _ _
    · exact (E.page r (by omega)).shape _ _ hrel

/-- The filtration of the total complex of a double complex supported in the first quadrant is
finite in every degree. -/
private lemma totalFiltration_finite_of_firstQuadrant
    (L : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [L.HasTotal (ComplexShape.up ℤ)]
    (hL : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((L.X i).X j)) :
    ∀ n : ℤ, ∃ lo hi : ℤ,
      Subobject.mk ((L.totalFiltration₁.filtration.ι.app (op lo)).f n) = ⊤ ∧
      Subobject.mk ((L.totalFiltration₁.filtration.ι.app (op hi)).f n) = ⊥ := by
  intro n
  refine ⟨0, n + 1, ?_, ?_⟩
  · rw [L.mk_totalFiltration_ι_f]
    have hid : L.totalProjector (fun i _ => 0 ≤ i) n = 𝟙 _ := by
      apply HomologicalComplex₂.total.hom_ext
      intro i j hij
      rw [L.ι_totalProjector]
      split_ifs with hi
      · simp
      · exact (hL i j (Or.inl (by omega))).eq_of_src _ _
    rw [hid]
    exact Subobject.imageSubobject_eq_top_of_epi _
  · rw [L.mk_totalFiltration_ι_f]
    have hzero : L.totalProjector (fun i _ => n + 1 ≤ i) n = 0 := by
      apply HomologicalComplex₂.total.hom_ext
      intro i j hij
      change i + j = n at hij
      rw [L.ι_totalProjector]
      split_ifs with hi
      · exact (hL i j (Or.inr (by omega))).eq_of_src _ _
      · simp
    rw [hzero]
    simp

open CochainComplex.DerivedTensorSpectralSequence in
/-- A cohomological spectral sequence whose pages are those of a finite filtration of a cochain
complex abuts to the cohomology of that complex. -/
private lemma finiteFiltration_abutsTo
    (T : CochainComplex A ℤ) (F : ∀ _ n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n)
    (hd : ∀ p n, (Subobject.exists (T.d n (n + 1))).obj (F p n) ≤ F p (n + 1))
    (hfinite : ∀ n, ∃ lo hi : ℤ, F lo n = ⊤ ∧ F hi n = ⊥)
    (E : CohomologicalSpectralSequence A 1)
    (e : ∀ (r p q : ℤ) (hr : 1 ≤ r),
      (E.page r hr).X (p, q) ≅ filteredPageObject T F r p q)
    (hE : ∀ p q : ℤ, E.HasPageInfinityAt (p, q)) :
    E.AbutsTo (fun n => T.homology n) := by
  let S := associatedSpectralSequenceOfFiniteFiltration T F hF hd hfinite
  let G := fun n p => inducedHomologyFiltration T F p n
  have hG : ∀ n : ℤ, Antitone (G n) := fun n p p' hp =>
    (Subobject.exists (T.homologyπ n)).monotone
      ((Subobject.pullback (T.iCycles n)).monotone (hF p p' n hp))
  refine ⟨hE, G, hG, ?_, ?_⟩
  · intro n
    obtain ⟨lo, hi, hlo, hhi⟩ := hfinite n
    refine ⟨lo, max lo hi, le_max_left _ _, ?_, ?_⟩
    · simp [G, inducedHomologyFiltration, hlo, Subobject.pullback_top,
        Subobject.exists_obj_top, Subobject.imageSubobject_eq_top_of_epi]
    · have hhi' : F (max lo hi) n = ⊥ :=
        le_bot_iff.mp (hhi ▸ hF hi (max lo hi) n (le_max_right _ _))
      simp only [G, inducedHomologyFiltration, hhi', Subobject.pullback_bot,
        Subobject.kernelSubobject_eq_bot_of_mono]
      rw [Subobject.exists_eq_imageSubobject, Subobject.bot_arrow, zero_comp,
        imageSubobject_zero]
  · intro p q
    let := hE p q
    obtain ⟨r₀, hr₀, htail⟩ := S.abuts p q
    let r := max r₀ (E.rMin (p, q))
    have hr : 2 ≤ r := hr₀.trans (le_max_left _ _)
    let : E.HasEdgeMonoAtFrom (p, q) r :=
      E.hasEdgeMonoAtFrom_of_GE (p, q) (E.rMin (p, q)) r (le_max_right _ _)
    let : E.HasEdgeEpiAtFrom (p, q) r :=
      E.hasEdgeEpiAtFrom_of_GE (p, q) (E.rMin (p, q)) r (le_max_right _ _)
    obtain ⟨_, _, comparison, _, _, hcmp, _, _⟩ := htail r hr (le_max_left _ _)
    let : IsIso comparison := hcmp
    exact ⟨E.pageInfinityIso (p, q) r ≪≫ e r p q (by omega) ≪≫
      (S.pageIso r p q hr).symm ≪≫ (asIso comparison).symm⟩

/-- A double complex supported in the first quadrant has a cohomological spectral sequence with
first page the cohomology of its columns, abutting to the cohomology of its total complex. -/
private theorem exists_doubleComplex_spectralSequence
    (L : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [L.HasTotal (ComplexShape.up ℤ)]
    (hL : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((L.X i).X j)) :
    ∃ E : CohomologicalSpectralSequence A 1,
      (∀ i j : ℤ, Nonempty ((E.page 1).X (i, j) ≅ (L.X i).homology j)) ∧
      (∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((E.page 1).X (i, j))) ∧
      E.AbutsTo (fun n => (L.total (ComplexShape.up ℤ)).homology n) := by
  let F := fun p n => Subobject.mk ((L.totalFiltration₁.filtration.ι.app (op p)).f n)
  let Z := FilteredComplexSpectralSequence.cycles L.totalFiltration₁.X F
  let D := FilteredComplexSpectralSequence.boundaries L.totalFiltration₁.X F
  obtain ⟨E, e, α, hδ, _⟩ := CochainComplex.exists_cohomologicalSpectralSequence
    L.totalFiltration₁ F (fun _ _ => rfl) Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl)
  obtain ⟨β, hβ⟩ := (L.exists_iso_pages_totalFiltration₁ F (fun _ _ => rfl)
    Z (fun _ _ _ => rfl) D (fun _ _ _ => rfl) E e hδ).2.1
  let E' : CohomologicalSpectralSequence A 1 :=
    { page := fun r hr => E.page r (by omega)
      iso := fun r r' pq h hr => E.iso r r' pq h (by omega) }
  have hquadrant (i j : ℤ) (h : i < 0 ∨ j < 0) : IsZero ((E'.page 1).X (i, j)) :=
    IsZero.of_iso ((HomologicalComplex.ExactAt.of_isZero (hL i j h)).isZero_homology)
      (β i j)
  refine ⟨E', fun i j => ⟨β i j⟩, hquadrant, ?_⟩
  apply finiteFiltration_abutsTo L.totalFiltration₁.X F
    (L.isLeast_totalFiltration₁ F (fun _ _ => rfl)).2.2
    (fun p n => CochainComplex.exists_mk_le_mk _ _ _
      ((L.totalFiltration₁.filtration.obj (op p)).d n (n + 1))
      ((L.totalFiltration₁.filtration.ι.app (op p)).comm n (n + 1)).symm)
    (totalFiltration_finite_of_firstQuadrant L hL) E'
    (fun r p q hr => e r p q (p + q) (by omega) rfl)
    (firstQuadrant_hasPageInfinity E' hquadrant)

/-- A double complex indexed by `ℕ × ℕ` has a first-quadrant cohomological spectral sequence with
first page the cohomology of its columns, abutting to the cohomology of the total complex of
its extension. -/
private theorem exists_firstQuadrant_spectralSequence
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ E : CohomologicalSpectralSequence A 1,
      (∀ i j : ℕ, Nonempty ((E.page 1).X ((i : ℤ), (j : ℤ)) ≅ (K.X i).homology j)) ∧
      (∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((E.page 1).X (i, j))) ∧
      E.AbutsTo (fun n => ((extendDoubleComplex K.flip).flip.total
          (ComplexShape.up ℤ)).homology n) := by
  let L := (extendDoubleComplex K.flip).flip
  have hL (i j : ℤ) (h : i < 0 ∨ j < 0) : IsZero ((L.X i).X j) := by
    rcases h with hi | hj
    · exact extendDoubleComplex_isZero₂ K.flip j i hi
    · exact (HomologicalComplex.eval _ _ i).map_isZero
        (extendDoubleComplex_isZero₁ K.flip j hj)
  obtain ⟨E, hE, hquadrant, habuts⟩ := exists_doubleComplex_spectralSequence L hL
  refine ⟨E, ?_, hquadrant, habuts⟩
  intro i j
  exact ⟨(hE i j).some ≪≫
      (HomologicalComplex.homologyFunctor _ _ (j : ℤ)).mapIso
        (extendDoubleComplexRowIso K.flip i) ≪≫
      (K.X i).extendHomologyIso ComplexShape.embeddingUpNat rfl⟩

/-- If a double complex is a degreewise resolution of a cochain complex concentrated in row zero,
its total complex computes the cohomology of that complex. -/
private def totalHomologyIsoOfRowResolution (T : CochainComplex A ℕ)
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (α : ((HomologicalComplex.single A (ComplexShape.up ℕ) 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj T ⟶ K.flip)
    (hα : ∀ n, QuasiIso (α.f n)) (n : ℤ) :
    ((extendDoubleComplex K.flip).flip.total (ComplexShape.up ℤ)).homology n ≅
      (T.extend ComplexShape.embeddingUpNat).homology n := by
  let g := HomologicalComplex₂.total.map (extendDoubleComplexMap α) (ComplexShape.up ℤ)
  letI : QuasiIso g := extendDoubleComplexMap_quasiIso α hα
  exact (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((extendDoubleComplex K.flip).totalFlipIso (ComplexShape.up ℤ)) ≪≫
    (asIso (HomologicalComplex.homologyMap g n)).symm ≪≫ totalSingleNatHomologyIso T n

/-- Abutment of a spectral sequence transfers along a degreewise isomorphism of the objects it
abuts to. -/
private lemma abutsTo_of_iso
    {C : Type*} [Category C] [Abelian C]
    {r₀ : ℤ} (E : CohomologicalSpectralSequence C r₀)
    {H H' : ℤ → C} (e : ∀ n, H n ≅ H' n)
    (h : SpectralSequence.AbutsTo E H) : SpectralSequence.AbutsTo E H' := by
  rcases h with ⟨hInf, ⟨F, hF, hfinite, hgraded⟩⟩
  let φ (n : ℤ) := Subobject.mapIsoToOrderIso (e n)
  let F' (n : ℤ) (p : ℤ) := φ n (F n p)
  have hF' : ∀ n : ℤ, Antitone (F' n) :=
    fun n _ _ hpq => (φ n).map_rel_iff'.2 (hF n hpq)
  refine ⟨hInf, F', hF', ?_, ?_⟩
  · intro n
    obtain ⟨a, b, hab, ha, hb⟩ := hfinite n
    refine ⟨a, b, hab, ?_, ?_⟩
    · show (φ n) (F n a) = ⊤; simp [ha]
    · show (φ n) (F n b) = ⊥; simp [hb]
  · intro p q
    obtain ⟨i⟩ := hgraded p q
    exact ⟨i.trans (Subobject.cokernelMapIso (e (p + q))
      (F (p + q) (p + 1)) (F (p + q) p) (hF (p + q) (by omega)) )⟩

end DoubleComplex

section Abutment

/-- A spectral sequence abutting to the cohomology of the total complex of the relative Čech double
complex of an injective resolution of `𝓕` abuts to the module cohomology of `𝓕` on `𝒳_τ`. -/
private lemma cechModuleDoubleComplex_abutsTo
    (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    (𝓕 : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)))
    (I : InjectiveResolution 𝓕)
    (hrows : ∀ n, QuasiIso
      ((cechSectionsAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq h).app (I.cocomplex.X n)))
    (E : CohomologicalSpectralSequence
      (ModuleCat.{max u vᵤ vₓ wᵤ wₓ a}
        (Stacks.Cohomology.SiteModules.GlobalSectionRing
          (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)))) 1)
    (hE : E.AbutsTo (fun n =>
      ((extendDoubleComplex
        (cechModuleDoubleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
          B S hS q f τ hq h I.cocomplex).flip).flip.total
            (ComplexShape.up ℤ)).homology n)) :
    E.AbutsTo (fun n : ℤ => if n < 0 then 0 else
      (Stacks.Cohomology.SiteModules.globalModuleCohomology.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
        (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) n.toNat).obj 𝓕) := by
  let G := Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))
  let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let K := cechModuleDoubleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
    B S hS q f τ hq h I.cocomplex
  let := cechSectionsComplexFunctor_additive.{u, vᵤ, vₓ, wᵤ, wₓ, a}
    B S hS q f τ hq h
  let : (cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq h).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let α : ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj T ⟶ K.flip :=
    (NatTrans.mapHomologicalComplex
      (cechSectionsAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq h) (ComplexShape.up ℕ)).app I.cocomplex
  apply abutsTo_of_iso E (fun n => ?_) hE
  refine totalHomologyIsoOfRowResolution T K α hrows n ≪≫ ?_
  split_ifs with hn
  · exact (HomologicalComplex.ExactAt.of_isZero
      (isZero_extend_X_of_neg T n hn)).isZero_homology.iso (isZero_zero _)
  · exact T.extendHomologyIso ComplexShape.embeddingUpNat (by simp; omega) ≪≫
      (Stacks.Cohomology.SiteModules.globalModuleCohomologyIso.{vₓ, wₓ, u,
        max u vᵤ vₓ wᵤ wₓ a} _ 𝓕 I n.toNat).symm

end Abutment

/-- For a faithful 1-morphism `f : 𝒰 ⥤ 𝒳` of categories fibred in groupoids over `(Sch/S)_fppf`
with equalizers in `𝒰`, whose image covers `𝒳` locally in the `τ`-topology, every sheaf of
`𝒪_𝒳`-modules `𝓕` has a first-quadrant spectral sequence of `Γ(𝒪_𝒳)`-modules
`E₁^{i,j} = Hʲ((𝒰ᵢ)_τ, fᵢ^*𝓕) ⇒ Hⁱ⁺ʲ(𝒳_τ, 𝓕)`. -/
@[stacks 06XG]
public theorem exists_moduleSpectralSequenceData
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f) [f.Faithful] [HasEqualizers 𝒰]
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g →
          ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    (𝓕 : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) :
    Nonempty (ModuleSpectralSequenceData.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq 𝓕) := by
  have hpU : (f ⋙ q).IsFiberedInGroupoids := by
    rw [hf.comp_eq]
    exact hp
  have hlevels := fun n => tuple_isFiberedInGroupoids q f hpU hq n
  have hequalizers := cech_hasEqualizers q f hq hpU hlevels
  have hfaithful := tuple_projection_faithful q f
  have : EnoughInjectives (SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) :=
    Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{vₓ, wₓ, u,
      max u vᵤ vₓ wᵤ wₓ a} _
  let I := injectiveResolution 𝓕
  let K := cechModuleDoubleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
    B S hS q f τ hq hlevels I.cocomplex
  obtain ⟨E, hE, hquadrant, habuts⟩ := exists_firstQuadrant_spectralSequence K
  refine ⟨{
    fiberedInGroupoids := hlevels
    sequence := E
    pageOneIso i j := (hE i j).some ≪≫
      cechColumnCohomologyIso B S hS q f τ hq hlevels hequalizers 𝓕 I i j
    firstQuadrant := hquadrant
    abutment := ?_ }⟩
  exact cechModuleDoubleComplex_abutsTo.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq hlevels 𝓕 I
    (fun n => cechSectionsAugmentation_quasiIso.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS p q f τ hq hlevels (I.cocomplex.X n) hp hf hcover hequalizers) E habuts

end Stacks.RelativeCech

end
