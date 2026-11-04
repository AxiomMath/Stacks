module

public import StacksFrontier.Algebra.Homology.SpectralSequence.ConvergenceTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFilteredAbutment
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexAsAFilteredComplex

/-!
# The functorial filtered abutment of the Čech-to-cohomology spectral sequence

The Čech-to-cohomology spectral sequence of [Stacks, Tag 01ES], as a functor of the sheaf of
modules (`Stacks.Cohomology.CechSpectral.cechSpectralSequenceFunctor`), has a functorial filtered
abutment in the shape `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` of
[Stacks, Tag 01F6]: the cohomology of the total complex `Tot(Č^•(𝒰, I^•(F)))`, with the filtration
[Stacks, Tag 012P] induces on it, functorially in `F`, together with the identification
`E_∞^{p,q} ≅ gr^pH^{p+q}` and its naturality.

The morphism of Čech double complexes attached to a morphism of sheaves is functorial only up to
`HomologicalComplex₂.FilteredHomotopy₂`, which is a homotopy of the total complexes; so
`H^n(Tot(K^{•,•}(-)))` is a functor although `Tot(K^{•,•}(-))` is not.

## Main definitions

* `Stacks.Cohomology.CechSpectral.cechFiltered`: `Tot(Č^•(𝒰, I^•(F)))` filtered by the Čech
  degree.
* `Stacks.Cohomology.CechSpectral.cechFiltrationFunctor`: its cohomology with the induced
  filtration, as a functor to `CategoryTheory.FilteredObject` -- the `filtration` field.
* `Stacks.Cohomology.CechSpectral.cechGradedIso`: the identification
  `E_∞^{p,q} ≅ gr^pH^{p+q}` -- the `gradedIso` field.
* `Stacks.Cohomology.CechSpectral.cechFunctorialAbutment`: the two assembled into a
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`.

## Main results

* `Stacks.Cohomology.CechSpectral.isFirstQuadrant_cechSpectralSequence₂` and
  `Stacks.Cohomology.CechSpectral.isFirstQuadrant_cechFilteredSpectralSequence`: first-quadrant
  vanishing for the two presentations of the Čech spectral sequence.
* `Stacks.Cohomology.CechSpectral.homologyMap_cechFilteredMap_id` and
  `Stacks.Cohomology.CechSpectral.homologyMap_cechFilteredMap_comp`: the cohomology of the Čech
  total complex is a functor, although the total complex itself is not.
* `Stacks.Cohomology.CechSpectral.cechGradedIso_naturality`: the naturality of the identification
  `E_∞^{p,q} ≅ gr^pH^{p+q}` in the sheaf.

## References

* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex FilteredComplexSpectralSequence Stacks.Cohomology.Leray

namespace Stacks.Cohomology.CechSpectral

universe u r v w

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

section Resolution

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r v w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u r v w}]
  [EnoughInjectives (SheafOfModules.{max u r v w} O)]

/-- **The total complex of the Čech double complex, filtered by the Čech degree.** -/
abbrev cechFiltered (F : SheafOfModules.{max u r v w} O) :
    CochainComplex.Filtered (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) :=
  (cechDouble.{u, r, v, w} O 𝒰 F).totalFiltration₂

/-- The zeroth step of the filtration of the Čech total complex by the Čech degree is the whole
total complex. -/
lemma isIso_cechFiltered_ι_f (F : SheafOfModules.{max u r v w} O) (n : ℤ) :
    IsIso (((cechFiltered.{u, r, v, w} O 𝒰 F).filtration.ι.app (op (0 : ℤ))).f n) :=
  isIso_cechDouble_totalFiltration₂_ι_f.{u, r, v, w} O 𝒰 F n

/-- The `p`-th step of the filtration of the Čech total complex by the Čech degree vanishes in
total degrees below `p`. -/
lemma isZero_cechFiltered_obj_X (F : SheafOfModules.{max u r v w} O) (p n : ℤ) (hnp : n < p) :
    IsZero (((cechFiltered.{u, r, v, w} O 𝒰 F).filtration.obj (op p)).X n) :=
  isZero_cechDouble_totalFiltration₂_obj_X.{u, r, v, w} O 𝒰 F p n hnp

/-- **The second spectral sequence of the Čech double complex vanishes outside the first
quadrant, before the start-page shift.** -/
lemma isFirstQuadrant_cechSpectralSequence₂ (F : SheafOfModules.{max u r v w} O) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)) :=
  CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration
    (cechFiltered.{u, r, v, w} O 𝒰 F)
    ((cechDouble.{u, r, v, w} O 𝒰 F).stepSubobject fun (_ : ℤ) j => j)
    (fun p n => HomologicalComplex₂.stepSubobject_eq _ _ (fun _ _ => le_rfl)
      (fun _ _ => by omega) p n)
    (HomologicalComplex₂.cycles₂ (cechDouble.{u, r, v, w} O 𝒰 F)) (fun _ _ _ => rfl)
    (HomologicalComplex₂.boundaries₂ (cechDouble.{u, r, v, w} O 𝒰 F)) (fun _ _ _ => rfl)
    _ (fun rr p q n hr hn => HomologicalComplex₂.pageIso₂ _ rr p q n hr hn)
    (isIso_cechFiltered_ι_f.{u, r, v, w} O 𝒰 F)
    (isZero_cechFiltered_obj_X.{u, r, v, w} O 𝒰 F)

open CochainComplex.Filtered in
/-- The second spectral sequence of the Čech double complex has an infinity page at every
bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_cechSpectralSequence₂ (F : SheafOfModules.{max u r v w} O) (x : ℤ × ℤ) :
    (HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).HasPageInfinityAt x :=
  CategoryTheory.SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F) x

/-- The start-page shift of the second spectral sequence of the Čech double complex vanishes
outside the first quadrant. -/
private theorem isFirstQuadrant_cechShiftStart (F : SheafOfModules.{max u r v w} O) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant ((HomologicalComplex₂.spectralSequence₂
      (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart (show (0 : ℤ) ≤ 2 by omega)) :=
  CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (by omega)
    (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F)

open CochainComplex.Filtered in
/-- The start-page shift of the second spectral sequence of the Čech double complex has an
infinity page at every bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_cechShiftStart (F : SheafOfModules.{max u r v w} O) (x : ℤ × ℤ) :
    ((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt x :=
  CategoryTheory.SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_cechShiftStart.{u, r, v, w} O 𝒰 F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the Čech double complex. -/
lemma hasEdgeMonoAtFrom_cechSpectralSequence₂ (F : SheafOfModules.{max u r v w} O) (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).HasPageInfinityAt
      (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).HasEdgeMonoAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the Čech double complex. -/
lemma hasEdgeEpiAtFrom_cechSpectralSequence₂ (F : SheafOfModules.{max u r v w} O) (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).HasPageInfinityAt
      (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).HasEdgeEpiAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeMonoAtFrom_cechSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeMonoAtFrom_cechShiftStart (F : SheafOfModules.{max u r v w} O) (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeMonoAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_cechShiftStart.{u, r, v, w} O 𝒰 F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeEpiAtFrom_cechSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeEpiAtFrom_cechShiftStart (F : SheafOfModules.{max u r v w} O) (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeEpiAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_cechShiftStart.{u, r, v, w} O 𝒰 F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered in
/-- `hasEdgeMonoAtFrom_cechShiftStart` after the first-quadrant reindexing. -/
lemma hasEdgeMonoAtFrom_cechNatRestrict (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F))).HasEdgeMonoAtFrom (p, q)
      (stablePage p q) :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ (p, q)
    (stablePage p q) (add_one_le_stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered in
/-- `hasEdgeEpiAtFrom_cechShiftStart` after the first-quadrant reindexing. -/
lemma hasEdgeEpiAtFrom_cechNatRestrict (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F))).HasEdgeEpiAtFrom (p, q)
      (stablePage p q) :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ (p, q)
    (stablePage p q) (add_two_le_stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The infinity page of the Čech spectral sequence at `(p, q)` is the infinity page of the
second spectral sequence of the Čech double complex at `ComplexShape.natEmb (p, q)`**, read at the
uniform stable page `CochainComplex.Filtered.stablePage p q`. -/
def cechPageInfinityIso (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    ((cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰).obj F).pageInfinity (p, q) ≅
      (HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).pageInfinity
        (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F (ComplexShape.natEmb (p, q))
  haveI := hasEdgeMonoAtFrom_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F p q
  haveI := hasEdgeEpiAtFrom_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F p q
  haveI := hasEdgeMonoAtFrom_cechShiftStart.{u, r, v, w} O 𝒰 F p q
  haveI := hasEdgeEpiAtFrom_cechShiftStart.{u, r, v, w} O 𝒰 F p q
  haveI := hasEdgeMonoAtFrom_cechNatRestrict.{u, r, v, w} O 𝒰 F p q
  haveI := hasEdgeEpiAtFrom_cechNatRestrict.{u, r, v, w} O 𝒰 F p q
  shiftNatRestrict_pageInfinityIsoAt (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F)) (p, q) (stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`cechPageInfinityIso` is natural in the sheaf.** -/
theorem cechPageInfinityIso_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G)
    (p q : ℕ) :
    Hom.mapPageInfinity ((cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰).map f) (p, q) ≫
        (cechPageInfinityIso.{u, r, v, w} O 𝒰 G p q).hom =
      (cechPageInfinityIso.{u, r, v, w} O 𝒰 F p q).hom ≫
        Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (cechDoubleMap.{u, r, v, w} O 𝒰 f))
          (ComplexShape.natEmb (p, q)) := by
  have := hasPageInfinityAt_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_cechSpectralSequence₂.{u, r, v, w} O 𝒰 G (ComplexShape.natEmb (p, q))
  have := hasEdgeMonoAtFrom_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeEpiAtFrom_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeMonoAtFrom_cechSpectralSequence₂.{u, r, v, w} O 𝒰 G p q
  have := hasEdgeEpiAtFrom_cechSpectralSequence₂.{u, r, v, w} O 𝒰 G p q
  have := hasEdgeMonoAtFrom_cechShiftStart.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeEpiAtFrom_cechShiftStart.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeMonoAtFrom_cechShiftStart.{u, r, v, w} O 𝒰 G p q
  have := hasEdgeEpiAtFrom_cechShiftStart.{u, r, v, w} O 𝒰 G p q
  have := hasEdgeMonoAtFrom_cechNatRestrict.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeEpiAtFrom_cechNatRestrict.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeMonoAtFrom_cechNatRestrict.{u, r, v, w} O 𝒰 G p q
  have := hasEdgeEpiAtFrom_cechNatRestrict.{u, r, v, w} O 𝒰 G p q
  exact shiftNatRestrict_pageInfinityIsoAt_naturality (show (0 : ℤ) ≤ 2 by omega)
    (isFirstQuadrant_cechShiftStart.{u, r, v, w} O 𝒰 F)
    (isFirstQuadrant_cechShiftStart.{u, r, v, w} O 𝒰 G)
    (HomologicalComplex₂.spectralSequenceMap₂ (cechDoubleMap.{u, r, v, w} O 𝒰 f)) (p, q)
    (stablePage p q) (two_le_stablePage p q)

/-! #### The filtered side -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The canonical spectral sequence of the Čech filtered complex vanishes outside the first
quadrant.** -/
lemma isFirstQuadrant_cechFilteredSpectralSequence (F : SheafOfModules.{max u r v w} O) :
    IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (CochainComplex.filteredSpectralSequence (cechFiltered.{u, r, v, w} O 𝒰 F)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (cechFiltered.{u, r, v, w} O 𝒰 F)
    (filtrationSubobject (cechFiltered.{u, r, v, w} O 𝒰 F)) (fun _ _ => rfl)
    (cycles (cechFiltered.{u, r, v, w} O 𝒰 F).X
      (filtrationSubobject (cechFiltered.{u, r, v, w} O 𝒰 F))) (fun _ _ _ => rfl)
    (boundaries (cechFiltered.{u, r, v, w} O 𝒰 F).X
      (filtrationSubobject (cechFiltered.{u, r, v, w} O 𝒰 F))) (fun _ _ _ => rfl)
    _ (fun rr p' q' n' hr hn' => by
        subst hn'; exact pageIso (cechFiltered.{u, r, v, w} O 𝒰 F) rr p' q' hr)
    (isIso_cechFiltered_ι_f.{u, r, v, w} O 𝒰 F)
    (isZero_cechFiltered_obj_X.{u, r, v, w} O 𝒰 F)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- The canonical spectral sequence of the Čech filtered complex has an infinity page at every
bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_cechFiltered (F : SheafOfModules.{max u r v w} O) (x : ℤ × ℤ) :
    (CochainComplex.filteredSpectralSequence
      (cechFiltered.{u, r, v, w} O 𝒰 F)).HasPageInfinityAt x :=
  hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_cechFilteredSpectralSequence.{u, r, v, w} O 𝒰 F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the Čech filtered complex. -/
lemma hasEdgeMonoAtFrom_cechFiltered (F : SheafOfModules.{max u r v w} O) (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (cechFiltered.{u, r, v, w} O 𝒰 F)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (cechFiltered.{u, r, v, w} O 𝒰 F)).HasEdgeMonoAtFrom ((p : ℤ), (q : ℤ))
        (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_cechFilteredSpectralSequence.{u, r, v, w} O 𝒰 F) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the Čech filtered complex. -/
lemma hasEdgeEpiAtFrom_cechFiltered (F : SheafOfModules.{max u r v w} O) (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (cechFiltered.{u, r, v, w} O 𝒰 F)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (cechFiltered.{u, r, v, w} O 𝒰 F)).HasEdgeEpiAtFrom ((p : ℤ), (q : ℤ))
        (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_cechFilteredSpectralSequence.{u, r, v, w} O 𝒰 F) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)

open CochainComplex.Filtered in
/-- The filtration of the Čech total complex by the Čech degree is degreewise finite. -/
lemma isDegreewiseFinite_cechFiltered (F : SheafOfModules.{max u r v w} O) :
    (cechFiltered.{u, r, v, w} O 𝒰 F).filtration.IsDegreewiseFinite :=
  isDegreewiseFinite_of_firstQuadrant (cechFiltered.{u, r, v, w} O 𝒰 F)
    (isIso_cechFiltered_ι_f.{u, r, v, w} O 𝒰 F) (isZero_cechFiltered_obj_X.{u, r, v, w} O 𝒰 F)

open CochainComplex.Filtered in
/-- **`CochainComplex.Filtered.stablePage p q` is a stable page at `(p, q)` for the Čech filtered
complex of every sheaf.** -/
lemma isStableFrom_cechFiltered (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    IsStableFrom (cechFiltered.{u, r, v, w} O 𝒰 F)
      (filtrationSubobject (cechFiltered.{u, r, v, w} O 𝒰 F)) (p : ℤ) (q : ℤ) (stablePage p q) :=
  isStableFrom_of_firstQuadrant (cechFiltered.{u, r, v, w} O 𝒰 F)
    (isIso_cechFiltered_ι_f.{u, r, v, w} O 𝒰 F) (isZero_cechFiltered_obj_X.{u, r, v, w} O 𝒰 F)
    (p : ℤ) (q : ℤ) (stablePage p q) (one_le_stablePage p q) (add_two_le_stablePage p q)
    (add_one_le_stablePage p q)

/-! #### The filtration functor -/

/-- **The morphism of Čech filtered complexes attached to a morphism of sheaves**: the total
complex of `cechDoubleMap` with its filtration by the Čech degree. -/
def cechFilteredMap {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    cechFiltered.{u, r, v, w} O 𝒰 F ⟶ cechFiltered.{u, r, v, w} O 𝒰 G :=
  totalFiltrationMap (fun (_ : ℤ) j => j) (fun _ _ => le_rfl) (fun _ _ => by omega)
    (cechDoubleMap.{u, r, v, w} O 𝒰 f)

/-- The underlying morphism of complexes of `cechFilteredMap f` is `Tot(K^{•,•}(f))`. -/
@[simp]
lemma cechFilteredMap_hom {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    (cechFilteredMap.{u, r, v, w} O 𝒰 f).hom =
      HomologicalComplex₂.total.map (cechDoubleMap.{u, r, v, w} O 𝒰 f) (ComplexShape.up ℤ) :=
  rfl

/-- **`H^n` of the Čech total complex sends an identity to an identity.** -/
lemma homologyMap_cechFilteredMap_id (F : SheafOfModules.{max u r v w} O) (n : ℤ) :
    HomologicalComplex.homologyMap (cechFilteredMap.{u, r, v, w} O 𝒰 (𝟙 F)).hom n = 𝟙 _ := by
  rw [cechFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_cechDoubleMap_id.{u, r, v, w} O 𝒰 F)
      |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_id, HomologicalComplex.homologyMap_id]

/-- **`H^n` of the Čech total complex is multiplicative.** -/
lemma homologyMap_cechFilteredMap_comp {F G H : SheafOfModules.{max u r v w} O} (f : F ⟶ G)
    (g : G ⟶ H) (n : ℤ) :
    HomologicalComplex.homologyMap (cechFilteredMap.{u, r, v, w} O 𝒰 (f ≫ g)).hom n =
      HomologicalComplex.homologyMap (cechFilteredMap.{u, r, v, w} O 𝒰 f).hom n ≫
        HomologicalComplex.homologyMap (cechFilteredMap.{u, r, v, w} O 𝒰 g).hom n := by
  rw [cechFilteredMap_hom, cechFilteredMap_hom, cechFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_cechDoubleMap_comp.{u, r, v, w} O 𝒰 f g)
      |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

open CochainComplex.Filtered in
/-- **`H^n(Tot(Č(𝒰, I^•(-))))` with its induced filtration**, as a functor. -/
def cechFiltrationFunctor (n : ℤ) :
    SheafOfModules.{max u r v w} O ⥤
      FilteredObject (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℤᵒᵖ where
  obj F := (cechFiltered.{u, r, v, w} O 𝒰 F).inducedFilteredObject n
  map f := inducedFilteredObjectMap (cechFilteredMap.{u, r, v, w} O 𝒰 f) n
  map_id F := FilteredObject.hom_ext (homologyMap_cechFilteredMap_id.{u, r, v, w} O 𝒰 F n)
  map_comp f g :=
    FilteredObject.hom_ext (homologyMap_cechFilteredMap_comp.{u, r, v, w} O 𝒰 f g n)

/-! #### The graded identification -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport of the infinity page across the two presentations of the filtration of the
Čech total complex by the Čech degree**: `HomologicalComplex₂.stepSubobject`, which
`HomologicalComplex₂.spectralSequence₂` uses, and `CochainComplex.filtrationSubobject` of
`HomologicalComplex₂.totalFiltration₂`, which `CochainComplex.filteredSpectralSequence` uses. -/
def cechPageInfinityTransportIso (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    (HomologicalComplex₂.spectralSequence₂ (cechDouble.{u, r, v, w} O 𝒰 F)).pageInfinity
        (ComplexShape.natEmb (p, q)) ≅
      (CochainComplex.filteredSpectralSequence (cechFiltered.{u, r, v, w} O 𝒰 F)).pageInfinity
        (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F (ComplexShape.natEmb (p, q))
  haveI := hasPageInfinityAt_cechFiltered.{u, r, v, w} O 𝒰 F (ComplexShape.natEmb (p, q))
  pageInfinityEqToIso
    (HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence
      (cechDouble.{u, r, v, w} O 𝒰 F)) (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`cechPageInfinityTransportIso` is natural in the sheaf.** -/
theorem cechPageInfinityTransportIso_naturality {F G : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (cechDoubleMap.{u, r, v, w} O 𝒰 f))
          (ComplexShape.natEmb (p, q)) ≫
        (cechPageInfinityTransportIso.{u, r, v, w} O 𝒰 G p q).hom =
      (cechPageInfinityTransportIso.{u, r, v, w} O 𝒰 F p q).hom ≫
        Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (cechFilteredMap.{u, r, v, w} O 𝒰 f)) (ComplexShape.natEmb (p, q)) := by
  have := hasPageInfinityAt_cechSpectralSequence₂.{u, r, v, w} O 𝒰 F (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_cechSpectralSequence₂.{u, r, v, w} O 𝒰 G (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_cechFiltered.{u, r, v, w} O 𝒰 F (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_cechFiltered.{u, r, v, w} O 𝒰 G (ComplexShape.natEmb (p, q))
  exact mapPageInfinity_pageInfinityEqToIso _ _ _ _
    (HomologicalComplex₂.spectralSequenceMap₂_eqToHom (cechDoubleMap.{u, r, v, w} O 𝒰 f))
    (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(Tot(K^{•,•}(F)))` for the canonical spectral sequence of the Čech
filtered complex**, at the stable page `CochainComplex.Filtered.stablePage p q`. -/
def cechCanonicalGradedIso (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    (CochainComplex.filteredSpectralSequence (cechFiltered.{u, r, v, w} O 𝒰 F)).pageInfinity
        (ComplexShape.natEmb (p, q)) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((cechFiltrationFunctor.{u, r, v, w} O 𝒰 ((p + q : ℕ) : ℤ)).obj F) :=
  haveI := hasPageInfinityAt_cechFiltered.{u, r, v, w} O 𝒰 F ((p : ℤ), (q : ℤ))
  haveI := hasEdgeMonoAtFrom_cechFiltered.{u, r, v, w} O 𝒰 F p q
  haveI := hasEdgeEpiAtFrom_cechFiltered.{u, r, v, w} O 𝒰 F p q
  canonicalPageInfinityIsoGr (cechFiltered.{u, r, v, w} O 𝒰 F)
    (isDegreewiseFinite_cechFiltered.{u, r, v, w} O 𝒰 F) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_cechFiltered.{u, r, v, w} O 𝒰 F p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`cechCanonicalGradedIso` is natural in the sheaf.** -/
theorem cechCanonicalGradedIso_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G)
    (p q : ℕ) :
    Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (cechFilteredMap.{u, r, v, w} O 𝒰 f)) (ComplexShape.natEmb (p, q)) ≫
        (cechCanonicalGradedIso.{u, r, v, w} O 𝒰 G p q).hom =
      (cechCanonicalGradedIso.{u, r, v, w} O 𝒰 F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((cechFiltrationFunctor.{u, r, v, w} O 𝒰 ((p + q : ℕ) : ℤ)).map f) := by
  have := hasPageInfinityAt_cechFiltered.{u, r, v, w} O 𝒰 F ((p : ℤ), (q : ℤ))
  have := hasPageInfinityAt_cechFiltered.{u, r, v, w} O 𝒰 G ((p : ℤ), (q : ℤ))
  have := hasEdgeMonoAtFrom_cechFiltered.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeEpiAtFrom_cechFiltered.{u, r, v, w} O 𝒰 F p q
  have := hasEdgeMonoAtFrom_cechFiltered.{u, r, v, w} O 𝒰 G p q
  have := hasEdgeEpiAtFrom_cechFiltered.{u, r, v, w} O 𝒰 G p q
  exact canonicalPageInfinityIsoGr_naturality (cechFilteredMap.{u, r, v, w} O 𝒰 f)
    (isDegreewiseFinite_cechFiltered.{u, r, v, w} O 𝒰 F)
    (isDegreewiseFinite_cechFiltered.{u, r, v, w} O 𝒰 G) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_cechFiltered.{u, r, v, w} O 𝒰 F p q)
    (isStableFrom_cechFiltered.{u, r, v, w} O 𝒰 G p q)
    (inducedFilteredObjectMap (cechFilteredMap.{u, r, v, w} O 𝒰 f) ((p + q : ℕ) : ℤ)) rfl

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}` for the Čech spectral sequence.** -/
def cechGradedIso (F : SheafOfModules.{max u r v w} O) (p q : ℕ) :
    ((cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰).obj F).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((cechFiltrationFunctor.{u, r, v, w} O 𝒰 ((p + q : ℕ) : ℤ)).obj F) :=
  cechPageInfinityIso.{u, r, v, w} O 𝒰 F p q ≪≫
    cechPageInfinityTransportIso.{u, r, v, w} O 𝒰 F p q ≪≫
      cechCanonicalGradedIso.{u, r, v, w} O 𝒰 F p q

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`cechGradedIso` is natural in the sheaf.** -/
theorem cechGradedIso_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity ((cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰).map f) (p, q) ≫
        (cechGradedIso.{u, r, v, w} O 𝒰 G p q).hom =
      (cechGradedIso.{u, r, v, w} O 𝒰 F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((cechFiltrationFunctor.{u, r, v, w} O 𝒰 ((p + q : ℕ) : ℤ)).map f) := by
  simp only [cechGradedIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% cechPageInfinityIso_naturality.{u, r, v, w} O 𝒰 f p q,
    reassoc_of% cechPageInfinityTransportIso_naturality.{u, r, v, w} O 𝒰 f p q,
    cechCanonicalGradedIso_naturality.{u, r, v, w} O 𝒰 f p q]

/-! #### The functorial abutment -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The functorial filtered abutment of the Čech spectral sequence, abutting to the cohomology
of the total complex.** -/
def cechFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰)
      (fun n => cechFiltrationFunctor.{u, r, v, w} O 𝒰 (n : ℤ) ⋙ FilteredObject.forget) where
  filtration n := cechFiltrationFunctor.{u, r, v, w} O 𝒰 (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite F n := (Filtration.isFinite_iff_subobject _).2
    ⟨⟨op (0 : ℤ), inducedFilteredObject_subobject_zero (cechFiltered.{u, r, v, w} O 𝒰 F)
        (isIso_cechFiltered_ι_f.{u, r, v, w} O 𝒰 F) (n : ℤ)⟩,
      ⟨op ((n : ℤ) + 1), inducedFilteredObject_subobject_succ
        (cechFiltered.{u, r, v, w} O 𝒰 F) (isZero_cechFiltered_obj_X.{u, r, v, w} O 𝒰 F) (n : ℤ)⟩⟩
  isTop F n := inducedFilteredObject_subobject_zero (cechFiltered.{u, r, v, w} O 𝒰 F)
    (isIso_cechFiltered_ι_f.{u, r, v, w} O 𝒰 F) (n : ℤ)
  isBot F n := inducedFilteredObject_subobject_succ (cechFiltered.{u, r, v, w} O 𝒰 F)
    (isZero_cechFiltered_obj_X.{u, r, v, w} O 𝒰 F) (n : ℤ)
  gradedIso F p q := cechGradedIso.{u, r, v, w} O 𝒰 F p q
  gradedIso_naturality f p q := cechGradedIso_naturality.{u, r, v, w} O 𝒰 f p q

end Resolution

end Stacks.Cohomology.CechSpectral

end
