module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafSpectralSequence.SecondPage

/-!
# The functorial filtered abutment of the spectral sequence of a hypercovering of a presheaf

The filtered complex underlying the spectral sequence of a hypercovering `K` of a presheaf `G`,
functorial in the coefficient sheaf, and its functorial first-quadrant abutment.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe q w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### The functorial filtered abutment -/

section Abutment

open CochainComplex FilteredComplexSpectralSequence Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

/-- **The double complex of a sheaf vanishes outside the first quadrant.**  The inner index is
extended by zero from `ℕ` by `SemiRepresentable.sectionsComplexIntFunctor` and the outer one by
the extension of the chosen injective resolution, so each negative index kills the term on its
own. -/
lemma isZero_hypercoverPresheafDouble_X_X
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (i j : ℤ)
    (h : i < 0 ∨ j < 0) :
    IsZero (((hypercoverPresheafDouble J G K F).X i).X j) := by
  rcases h with hi | hj
  · exact Functor.map_isZero
      (HomologicalComplex.eval AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ) j)
      (isZero_hypercoverPresheafDoubleFunctor_X J G K _ i
        (isZero_injectiveResolutionExtend_X F i hi))
  · exact isZero_hypercoverPresheafDoubleFunctor_X_X_of_inner_neg J G K _ i j hj

/-- **The total complex of the double complex, filtered by the hypercovering degree.**  This is
the filtered complex whose spectral sequence is the spectral sequence of `K` and whose cohomology
with its induced filtration is the abutment. -/
abbrev hypercoverPresheafFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    CochainComplex.Filtered AddCommGrpCat.{max (max u v) (max q w)} :=
  (hypercoverPresheafDouble J G K F).totalFiltration₂

/-- **`htop` for the filtered complex of `K`**: the zeroth step of the filtration by the
hypercovering degree is the whole total complex. -/
lemma isIso_hypercoverPresheafFiltered_ι_f
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (n : ℤ) :
    IsIso (((hypercoverPresheafFiltered J G K F).filtration.ι.app (op (0 : ℤ))).f n) :=
  HomologicalComplex₂.isIso_totalFiltration₂_ι_f _
    (fun i j hj => isZero_hypercoverPresheafDouble_X_X J G K F i j (Or.inr hj)) n

/-- **`hbot` for the filtered complex of `K`**: the `p`-th step of the filtration by the
hypercovering degree vanishes in total degrees below `p`. -/
lemma isZero_hypercoverPresheafFiltered_obj_X
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p n : ℤ)
    (hnp : n < p) :
    IsZero (((hypercoverPresheafFiltered J G K F).filtration.obj (op p)).X n) :=
  HomologicalComplex₂.isZero_totalFiltration₂_obj_X _
    (fun i j hi => isZero_hypercoverPresheafDouble_X_X J G K F i j (Or.inl hi)) p n hnp

/-- **The second spectral sequence of the double complex vanishes outside the first quadrant,
before the start-page shift.**  This unshifted form is what
`CategoryTheory.SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant` and its companion need, and
it is obtained from `CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration` applied
to the `HomologicalComplex₂.stepSubobject` presentation of the filtration -- the presentation
`HomologicalComplex₂.spectralSequence₂` is built on -- so that no transport is involved. -/
lemma isFirstQuadrant_hypercoverPresheafSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)) :=
  CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration
    (hypercoverPresheafFiltered J G K F)
    ((hypercoverPresheafDouble J G K F).stepSubobject fun (_ : ℤ) j => j)
    (fun p n => HomologicalComplex₂.stepSubobject_eq _ _ (fun _ _ => le_rfl)
      (fun _ _ => by omega) p n)
    (HomologicalComplex₂.cycles₂ (hypercoverPresheafDouble J G K F)) (fun _ _ _ => rfl)
    (HomologicalComplex₂.boundaries₂ (hypercoverPresheafDouble J G K F)) (fun _ _ _ => rfl)
    _ (fun rr p₁ q₁ n₁ hr hn => HomologicalComplex₂.pageIso₂ _ rr p₁ q₁ n₁ hr hn)
    (isIso_hypercoverPresheafFiltered_ι_f J G K F)
    (isZero_hypercoverPresheafFiltered_obj_X J G K F)

open CochainComplex.Filtered in
/-- The second spectral sequence of the double complex has an infinity page at every bidegree of
`ℤ × ℤ`. -/
lemma hasPageInfinityAt_hypercoverPresheafSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (x : ℤ × ℤ) :
    (HomologicalComplex₂.spectralSequence₂
      (hypercoverPresheafDouble J G K F)).HasPageInfinityAt x :=
  CategoryTheory.SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q')` have vanished for good from `stablePage p q'` on**, for the
unshifted second spectral sequence of the double complex. -/
lemma hasEdgeMonoAtFrom_hypercoverPresheafSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ)
    [(HomologicalComplex₂.spectralSequence₂
      (hypercoverPresheafDouble J G K F)).HasPageInfinityAt (ComplexShape.natEmb (p, q'))] :
    (HomologicalComplex₂.spectralSequence₂
      (hypercoverPresheafDouble J G K F)).HasEdgeMonoAtFrom
        (ComplexShape.natEmb (p, q')) (stablePage p q') :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F)
    (ComplexShape.natEmb (p, q')) (stablePage p q')
    (by have := two_le_stablePage p q'; omega) (natEmb_fst_lt_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q')` have vanished for good from `stablePage p q'` on**, for
the unshifted second spectral sequence of the double complex. -/
lemma hasEdgeEpiAtFrom_hypercoverPresheafSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ)
    [(HomologicalComplex₂.spectralSequence₂
      (hypercoverPresheafDouble J G K F)).HasPageInfinityAt (ComplexShape.natEmb (p, q'))] :
    (HomologicalComplex₂.spectralSequence₂
      (hypercoverPresheafDouble J G K F)).HasEdgeEpiAtFrom
        (ComplexShape.natEmb (p, q')) (stablePage p q') :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F)
    (ComplexShape.natEmb (p, q')) (stablePage p q')
    (by have := two_le_stablePage p q'; omega) (natEmb_snd_add_one_lt_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeMonoAtFrom_hypercoverPresheafSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeMonoAtFrom_hypercoverPresheafShiftStart
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q'))] :
    ((HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeMonoAtFrom
        (ComplexShape.natEmb (p, q')) (stablePage p q') :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F))
    (ComplexShape.natEmb (p, q')) (stablePage p q') (two_le_stablePage p q')
    (natEmb_fst_lt_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeEpiAtFrom_hypercoverPresheafSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeEpiAtFrom_hypercoverPresheafShiftStart
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q'))] :
    ((HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeEpiAtFrom
        (ComplexShape.natEmb (p, q')) (stablePage p q') :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F))
    (ComplexShape.natEmb (p, q')) (stablePage p q') (two_le_stablePage p q')
    (natEmb_snd_add_one_lt_stablePage p q')

open CochainComplex.Filtered in
/-- `hasEdgeMonoAtFrom_hypercoverPresheafShiftStart` after the first-quadrant reindexing.

Stated in the `CategoryTheory.SpectralSequence.natRestrict`-of-`shiftStart` spelling rather than
as `(hypercoverPresheafSpectralSequenceFunctor J G K).obj F`, because that is the spelling
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt` asks for: the two are equal
by definition, but instance search is keyed on the head symbol and would not look through
`hypercoverPresheafSpectralSequenceFunctor`. -/
lemma hasEdgeMonoAtFrom_hypercoverPresheafNatRestrict
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F))).HasEdgeMonoAtFrom
          (p, q') (stablePage p q') :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ (p, q')
    (stablePage p q') (add_one_le_stablePage p q') (two_le_stablePage p q')

open CochainComplex.Filtered in
/-- The companion of `hasEdgeMonoAtFrom_hypercoverPresheafNatRestrict`, in the same spelling and
for the same reason. -/
lemma hasEdgeEpiAtFrom_hypercoverPresheafNatRestrict
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F))).HasEdgeEpiAtFrom
          (p, q') (stablePage p q') :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ (p, q')
    (stablePage p q') (add_two_le_stablePage p q') (two_le_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The infinity page of the spectral sequence of `K` at `(p, q')` is the infinity page of the
second spectral sequence of the double complex at `ComplexShape.natEmb (p, q')`**, read at the
uniform stable page `CochainComplex.Filtered.stablePage p q'`.  This is
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt`. -/
def hypercoverPresheafPageInfinityIso
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    ((hypercoverPresheafSpectralSequenceFunctor J G K).obj F).pageInfinity (p, q') ≅
      (HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).pageInfinity
        (ComplexShape.natEmb (p, q')) :=
  haveI := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G K F
    (ComplexShape.natEmb (p, q'))
  haveI := hasEdgeMonoAtFrom_hypercoverPresheafSpectralSequence₂ J G K F p q'
  haveI := hasEdgeEpiAtFrom_hypercoverPresheafSpectralSequence₂ J G K F p q'
  haveI := hasEdgeMonoAtFrom_hypercoverPresheafShiftStart J G K F p q'
  haveI := hasEdgeEpiAtFrom_hypercoverPresheafShiftStart J G K F p q'
  haveI := hasEdgeMonoAtFrom_hypercoverPresheafNatRestrict J G K F p q'
  haveI := hasEdgeEpiAtFrom_hypercoverPresheafNatRestrict J G K F p q'
  shiftNatRestrict_pageInfinityIsoAt (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F)) (p, q') (stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPresheafPageInfinityIso` is natural in the sheaf.**  Both transports -- the
start-page shift and the first-quadrant reindexing -- are read at the page
`CochainComplex.Filtered.stablePage p q'`, which is admissible for every sheaf at once, and there
the two induced maps on the infinity pages are the *same* morphism of pages. -/
theorem hypercoverPresheafPageInfinityIso_naturality
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (p q' : ℕ) :
    Hom.mapPageInfinity ((hypercoverPresheafSpectralSequenceFunctor J G K).map f) (p, q') ≫
        (hypercoverPresheafPageInfinityIso J G K F' p q').hom =
      (hypercoverPresheafPageInfinityIso J G K F p q').hom ≫
        Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverPresheafDoubleMap J G K f))
          (ComplexShape.natEmb (p, q')) := by
  have := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G K
  have := hasEdgeMonoAtFrom_hypercoverPresheafSpectralSequence₂ J G K
  have := hasEdgeEpiAtFrom_hypercoverPresheafSpectralSequence₂ J G K
  have := hasEdgeMonoAtFrom_hypercoverPresheafShiftStart J G K
  have := hasEdgeEpiAtFrom_hypercoverPresheafShiftStart J G K
  have := hasEdgeMonoAtFrom_hypercoverPresheafNatRestrict J G K
  have := hasEdgeEpiAtFrom_hypercoverPresheafNatRestrict J G K
  exact shiftNatRestrict_pageInfinityIsoAt_naturality (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F))
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverPresheafSpectralSequence₂ J G K F'))
    (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverPresheafDoubleMap J G K f)) (p, q')
    (stablePage p q') (two_le_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The canonical spectral sequence of the filtered complex of `K` vanishes outside the first
quadrant.**  The same statement as `isFirstQuadrant_hypercoverPresheafSpectralSequence₂` for the
other presentation of the same filtration, the one `CochainComplex.filteredSpectralSequence` is
built on. -/
lemma isFirstQuadrant_hypercoverPresheafFilteredSpectralSequence
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (CochainComplex.filteredSpectralSequence (hypercoverPresheafFiltered J G K F)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (hypercoverPresheafFiltered J G K F)
    (filtrationSubobject (hypercoverPresheafFiltered J G K F)) (fun _ _ => rfl)
    (cycles (hypercoverPresheafFiltered J G K F).X
      (filtrationSubobject (hypercoverPresheafFiltered J G K F))) (fun _ _ _ => rfl)
    (boundaries (hypercoverPresheafFiltered J G K F).X
      (filtrationSubobject (hypercoverPresheafFiltered J G K F))) (fun _ _ _ => rfl)
    _ (fun rr p₁ q₁ n₁ hr hn₁ => by
        subst hn₁; exact pageIso (hypercoverPresheafFiltered J G K F) rr p₁ q₁ hr)
    (isIso_hypercoverPresheafFiltered_ι_f J G K F)
    (isZero_hypercoverPresheafFiltered_obj_X J G K F)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- The canonical spectral sequence of the filtered complex of `K` has an infinity page at every
bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_hypercoverPresheafFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (x : ℤ × ℤ) :
    (CochainComplex.filteredSpectralSequence
      (hypercoverPresheafFiltered J G K F)).HasPageInfinityAt x :=
  hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverPresheafFilteredSpectralSequence J G K F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q')` have vanished for good from `stablePage p q'` on**, for the
canonical spectral sequence of the filtered complex of `K`. -/
lemma hasEdgeMonoAtFrom_hypercoverPresheafFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (hypercoverPresheafFiltered J G K F)).HasPageInfinityAt ((p : ℤ), (q' : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (hypercoverPresheafFiltered J G K F)).HasEdgeMonoAtFrom ((p : ℤ), (q' : ℤ))
        (stablePage p q') :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverPresheafFilteredSpectralSequence J G K F) ((p : ℤ), (q' : ℤ))
    (stablePage p q') (by have := two_le_stablePage p q'; omega) (add_one_le_stablePage p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q')` have vanished for good from `stablePage p q'` on**, for
the canonical spectral sequence of the filtered complex of `K`. -/
lemma hasEdgeEpiAtFrom_hypercoverPresheafFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (hypercoverPresheafFiltered J G K F)).HasPageInfinityAt ((p : ℤ), (q' : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (hypercoverPresheafFiltered J G K F)).HasEdgeEpiAtFrom ((p : ℤ), (q' : ℤ))
        (stablePage p q') :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverPresheafFilteredSpectralSequence J G K F) ((p : ℤ), (q' : ℤ))
    (stablePage p q') (by have := two_le_stablePage p q'; omega)
    (by have := add_two_le_stablePage p q'; omega)

open CochainComplex.Filtered in
/-- The filtration of the total complex by the hypercovering degree is degreewise finite, so the
convergence identification of [Stacks, Tag 012W] applies to it. -/
lemma isDegreewiseFinite_hypercoverPresheafFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (hypercoverPresheafFiltered J G K F).filtration.IsDegreewiseFinite :=
  isDegreewiseFinite_of_firstQuadrant (hypercoverPresheafFiltered J G K F)
    (isIso_hypercoverPresheafFiltered_ι_f J G K F)
    (isZero_hypercoverPresheafFiltered_obj_X J G K F)

open CochainComplex.Filtered in
/-- **`CochainComplex.Filtered.stablePage p q'` is a stable page at `(p, q')` for the filtered
complex of every sheaf simultaneously**, which is what the naturality of the convergence
identification needs. -/
lemma isStableFrom_hypercoverPresheafFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    IsStableFrom (hypercoverPresheafFiltered J G K F)
      (filtrationSubobject (hypercoverPresheafFiltered J G K F)) (p : ℤ) (q' : ℤ)
      (stablePage p q') :=
  isStableFrom_of_firstQuadrant (hypercoverPresheafFiltered J G K F)
    (isIso_hypercoverPresheafFiltered_ι_f J G K F)
    (isZero_hypercoverPresheafFiltered_obj_X J G K F)
    (p : ℤ) (q' : ℤ) (stablePage p q') (one_le_stablePage p q') (add_two_le_stablePage p q')
    (add_one_le_stablePage p q')

/-- **The morphism of filtered complexes attached to a morphism of sheaves**: the total complex of
`hypercoverPresheafDoubleMap` with its filtration by the hypercovering degree.  Like
`hypercoverPresheafDoubleMap` it is functorial only up to homotopy; what *is* functorial is the
cohomology it induces, which is `hypercoverPresheafFiltrationFunctor`. -/
def hypercoverPresheafFilteredMap
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    hypercoverPresheafFiltered J G K F ⟶ hypercoverPresheafFiltered J G K F' :=
  Stacks.Cohomology.CechSpectral.totalFiltrationMap (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
    (fun _ _ => by omega) (hypercoverPresheafDoubleMap J G K f)

/-- The underlying morphism of complexes of `hypercoverPresheafFilteredMap f` is
`Tot(A^{•,•}(f))`. -/
@[simp]
lemma hypercoverPresheafFilteredMap_hom
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    (hypercoverPresheafFilteredMap J G K f).hom =
      HomologicalComplex₂.total.map (hypercoverPresheafDoubleMap J G K f)
        (ComplexShape.up ℤ) :=
  rfl

/-- **`H^n` of the total complex sends an identity to an identity.**
`hypercoverPresheafDoubleMap (𝟙 F)` is only filtered homotopic to the identity, but the homotopy
carried inside `HomologicalComplex₂.FilteredHomotopy₂` is a homotopy of the *total* complexes, and
homology is homotopy invariant. -/
lemma homologyMap_hypercoverPresheafFilteredMap_id
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (n : ℤ) :
    HomologicalComplex.homologyMap (hypercoverPresheafFilteredMap J G K (𝟙 F)).hom n = 𝟙 _ := by
  rw [hypercoverPresheafFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_hypercoverPresheafDoubleMap_id J G K F) |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_id, HomologicalComplex.homologyMap_id]

/-- **`H^n` of the total complex is multiplicative.**  As with
`homologyMap_hypercoverPresheafFilteredMap_id`, from the homotopy carried inside
`HomologicalComplex₂.FilteredHomotopy₂`. -/
lemma homologyMap_hypercoverPresheafFilteredMap_comp
    {F F' F'' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (g : F' ⟶ F'') (n : ℤ) :
    HomologicalComplex.homologyMap (hypercoverPresheafFilteredMap J G K (f ≫ g)).hom n =
      HomologicalComplex.homologyMap (hypercoverPresheafFilteredMap J G K f).hom n ≫
        HomologicalComplex.homologyMap (hypercoverPresheafFilteredMap J G K g).hom n := by
  rw [hypercoverPresheafFilteredMap_hom, hypercoverPresheafFilteredMap_hom,
    hypercoverPresheafFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_hypercoverPresheafDoubleMap_comp J G K f g)
      |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

open CochainComplex.Filtered in
/-- **The `filtration` field**: `H^n(Tot(s(I^•(K))))` with its induced filtration, as a
functor. -/
def hypercoverPresheafFiltrationFunctor (n : ℤ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      FilteredObject AddCommGrpCat.{max (max u v) (max q w)} ℤᵒᵖ where
  obj F := (hypercoverPresheafFiltered J G K F).inducedFilteredObject n
  map f := inducedFilteredObjectMap (hypercoverPresheafFilteredMap J G K f) n
  map_id F := FilteredObject.hom_ext (homologyMap_hypercoverPresheafFilteredMap_id J G K F n)
  map_comp f g :=
    FilteredObject.hom_ext (homologyMap_hypercoverPresheafFilteredMap_comp J G K f g n)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport of the infinity page across the two presentations of the filtration of the
total complex by the hypercovering degree**: `HomologicalComplex₂.stepSubobject`, which
`HomologicalComplex₂.spectralSequence₂` uses, and `CochainComplex.filtrationSubobject` of
`HomologicalComplex₂.totalFiltration₂`, which `CochainComplex.filteredSpectralSequence` uses. -/
def hypercoverPresheafPageInfinityTransportIso
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverPresheafDouble J G K F)).pageInfinity
        (ComplexShape.natEmb (p, q')) ≅
      (CochainComplex.filteredSpectralSequence
        (hypercoverPresheafFiltered J G K F)).pageInfinity (ComplexShape.natEmb (p, q')) :=
  haveI := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G K F
    (ComplexShape.natEmb (p, q'))
  haveI := hasPageInfinityAt_hypercoverPresheafFiltered J G K F (ComplexShape.natEmb (p, q'))
  pageInfinityEqToIso
    (HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence
      (hypercoverPresheafDouble J G K F)) (ComplexShape.natEmb (p, q'))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport is natural in the sheaf.**  This is
`CategoryTheory.SpectralSequence.mapPageInfinity_pageInfinityEqToIso` at the conjugation square
`HomologicalComplex₂.spectralSequenceMap₂_eqToHom`. -/
theorem hypercoverPresheafPageInfinityTransportIso_naturality
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (p q' : ℕ) :
    Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverPresheafDoubleMap J G K f))
          (ComplexShape.natEmb (p, q')) ≫
        (hypercoverPresheafPageInfinityTransportIso J G K F' p q').hom =
      (hypercoverPresheafPageInfinityTransportIso J G K F p q').hom ≫
        Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (hypercoverPresheafFilteredMap J G K f)) (ComplexShape.natEmb (p, q')) := by
  have := hasPageInfinityAt_hypercoverPresheafSpectralSequence₂ J G K
  have := hasPageInfinityAt_hypercoverPresheafFiltered J G K
  exact mapPageInfinity_pageInfinityEqToIso _ _ _ _
    (HomologicalComplex₂.spectralSequenceMap₂_eqToHom (hypercoverPresheafDoubleMap J G K f))
    (ComplexShape.natEmb (p, q'))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`E_∞^{p,q'} ≅ gr^pH^{p+q'}(Tot(A^{•,•}(F)))` for the canonical spectral sequence of the
filtered complex of `K`**, with the stable page supplied uniformly by
`CochainComplex.Filtered.stablePage`.  This is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr`. -/
def hypercoverPresheafCanonicalGradedIso
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    (CochainComplex.filteredSpectralSequence
        (hypercoverPresheafFiltered J G K F)).pageInfinity (ComplexShape.natEmb (p, q')) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((hypercoverPresheafFiltrationFunctor J G K ((p + q' : ℕ) : ℤ)).obj F) :=
  haveI := hasPageInfinityAt_hypercoverPresheafFiltered J G K F ((p : ℤ), (q' : ℤ))
  haveI := hasEdgeMonoAtFrom_hypercoverPresheafFiltered J G K F p q'
  haveI := hasEdgeEpiAtFrom_hypercoverPresheafFiltered J G K F p q'
  canonicalPageInfinityIsoGr (hypercoverPresheafFiltered J G K F)
    (isDegreewiseFinite_hypercoverPresheafFiltered J G K F) (p : ℤ) (q' : ℤ) (stablePage p q')
    (isStableFrom_hypercoverPresheafFiltered J G K F p q')

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPresheafCanonicalGradedIso` is natural in the sheaf.**  This is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr_naturality` at the page
`CochainComplex.Filtered.stablePage p q'`, which
`isStableFrom_hypercoverPresheafFiltered` makes stable for every sheaf at once. -/
theorem hypercoverPresheafCanonicalGradedIso_naturality
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (p q' : ℕ) :
    Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (hypercoverPresheafFilteredMap J G K f)) (ComplexShape.natEmb (p, q')) ≫
        (hypercoverPresheafCanonicalGradedIso J G K F' p q').hom =
      (hypercoverPresheafCanonicalGradedIso J G K F p q').hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((hypercoverPresheafFiltrationFunctor J G K ((p + q' : ℕ) : ℤ)).map f) := by
  have := hasPageInfinityAt_hypercoverPresheafFiltered J G K
  have := hasEdgeMonoAtFrom_hypercoverPresheafFiltered J G K
  have := hasEdgeEpiAtFrom_hypercoverPresheafFiltered J G K
  exact canonicalPageInfinityIsoGr_naturality (hypercoverPresheafFilteredMap J G K f)
    (isDegreewiseFinite_hypercoverPresheafFiltered J G K F)
    (isDegreewiseFinite_hypercoverPresheafFiltered J G K F') (p : ℤ) (q' : ℤ)
    (stablePage p q')
    (isStableFrom_hypercoverPresheafFiltered J G K F p q')
    (isStableFrom_hypercoverPresheafFiltered J G K F' p q')
    (inducedFilteredObjectMap (hypercoverPresheafFilteredMap J G K f) ((p + q' : ℕ) : ℤ)) rfl

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso` field**: `E_∞^{p,q'} ≅ gr^pH^{p+q'}`. -/
def hypercoverPresheafGradedIso
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p q' : ℕ) :
    ((hypercoverPresheafSpectralSequenceFunctor J G K).obj F).pageInfinity (p, q') ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((hypercoverPresheafFiltrationFunctor J G K ((p + q' : ℕ) : ℤ)).obj F) :=
  hypercoverPresheafPageInfinityIso J G K F p q' ≪≫
    hypercoverPresheafPageInfinityTransportIso J G K F p q' ≪≫
      hypercoverPresheafCanonicalGradedIso J G K F p q'

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso_naturality` field**: the three squares, pasted. -/
theorem hypercoverPresheafGradedIso_naturality
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (p q' : ℕ) :
    Hom.mapPageInfinity ((hypercoverPresheafSpectralSequenceFunctor J G K).map f) (p, q') ≫
        (hypercoverPresheafGradedIso J G K F' p q').hom =
      (hypercoverPresheafGradedIso J G K F p q').hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((hypercoverPresheafFiltrationFunctor J G K ((p + q' : ℕ) : ℤ)).map f) := by
  rw [hypercoverPresheafGradedIso, hypercoverPresheafGradedIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% hypercoverPresheafPageInfinityIso_naturality J G K f p q',
    reassoc_of% hypercoverPresheafPageInfinityTransportIso_naturality J G K f p q',
    hypercoverPresheafCanonicalGradedIso_naturality J G K f p q']

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The functorial filtered abutment of the spectral sequence of `K`, abutting to the cohomology
of the total complex.** -/
def hypercoverPresheafFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (hypercoverPresheafSpectralSequenceFunctor J G K)
      (fun n => hypercoverPresheafFiltrationFunctor J G K (n : ℤ) ⋙
        FilteredObject.forget) where
  filtration n := hypercoverPresheafFiltrationFunctor J G K (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite F n := (Filtration.isFinite_iff_subobject _).2
    ⟨⟨op (0 : ℤ), inducedFilteredObject_subobject_zero (hypercoverPresheafFiltered J G K F)
        (isIso_hypercoverPresheafFiltered_ι_f J G K F) (n : ℤ)⟩,
      ⟨op ((n : ℤ) + 1), inducedFilteredObject_subobject_succ
        (hypercoverPresheafFiltered J G K F)
        (isZero_hypercoverPresheafFiltered_obj_X J G K F) (n : ℤ)⟩⟩
  isTop F n := inducedFilteredObject_subobject_zero (hypercoverPresheafFiltered J G K F)
    (isIso_hypercoverPresheafFiltered_ι_f J G K F) (n : ℤ)
  isBot F n := inducedFilteredObject_subobject_succ (hypercoverPresheafFiltered J G K F)
    (isZero_hypercoverPresheafFiltered_obj_X J G K F) (n : ℤ)
  gradedIso F p q' := hypercoverPresheafGradedIso J G K F p q'
  gradedIso_naturality f p q' := hypercoverPresheafGradedIso_naturality J G K f p q'

end Abutment

end Stacks.CategoryTheory.Hypercovering

end
