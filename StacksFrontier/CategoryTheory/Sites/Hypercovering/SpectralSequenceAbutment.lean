module

public import StacksFrontier.Algebra.Homology.SpectralSequence.ConvergenceTransport
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSecondPage
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFilteredAbutment
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexAsAFilteredComplex

/-!
# The filtered abutment of the hypercovering spectral sequence of a small site

The **functorial filtered abutment** of the hypercovering spectral sequence of [Stacks, Tag 01GY],
in the shape `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` of [Stacks, Tag 01F6]: the
cohomology of the total complex `Tot(Č^•(K, I^•(F)))` with the filtration [Stacks, Tag 012P]
induces on it, functorially in the simplicial semi-representable object **and** in the
coefficient sheaf, together with the identification `E_∞^{p,q} ≅ gr^pH^{p+q}` and its naturality.
The abutment is the cohomology of the total complex itself, so the field `abutmentIso` is the
identity.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFiltered`: `Tot(Č^•(K, I^•(F)))`
  filtered by the Čech degree.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFiltrationFunctor`: its cohomology
  with the induced filtration, as a functor to `CategoryTheory.FilteredObject` -- the `filtration`
  field.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverGradedIso`: the identification
  `E_∞^{p,q} ≅ gr^pH^{p+q}` -- the `gradedIso` field.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverFunctorialAbutment`: the two assembled
  into a `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` for
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverSpectralSequenceFunctor`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringFunctorialAbutment`: the same
  restricted to the full subcategory of hypercoverings.

## Main results

* `Stacks.CategoryTheory.Hypercovering.Functorial.isZero_cechDoubleBifunctor_X_X`: the Čech double
  complex of a complex of presheaves of abelian groups vanishes outside the first quadrant.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isIso_hypercoverFiltered_ι_f` and
  `Stacks.CategoryTheory.Hypercovering.Functorial.isZero_hypercoverFiltered_obj_X`: the hypotheses
  `htop` and `hbot` for the filtration of the total complex by the Čech degree.
* `Stacks.CategoryTheory.Hypercovering.Functorial.homologyMap_hypercoverFilteredMap_id` and
  `Stacks.CategoryTheory.Hypercovering.Functorial.homologyMap_hypercoverFilteredMap_comp`: the
  cohomology of the total complex is a functor, although the total complex itself is not.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverGradedIso_naturality`: the
  `gradedIso_naturality` field.

## Implementation notes

`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverDoubleMap` is functorial only up to
`HomologicalComplex₂.FilteredHomotopy₂`, so there is no functor `D ⥤ CochainComplex.Filtered 𝒜`
and `CochainComplex.Filtered.functorialFirstQuadrantAbutment` does not apply. The homotopy is one
of the *total* complexes and homology is homotopy invariant, so `H^n(Tot(A^{•,•}(-)))` is
nevertheless a functor, and the abutment is built from the objectwise results
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt` and
`CochainComplex.Filtered.canonicalPageInfinityIsoGr` and their naturality squares, at the uniform
page `CochainComplex.Filtered.stablePage p q`.

`hypercoverSpectralSequenceFunctor` is built on `HomologicalComplex₂.spectralSequence₂`, whose
filtration is presented as `HomologicalComplex₂.stepSubobject`, while
`CochainComplex.Filtered.canonicalPageInfinityIsoGr` is stated for
`CochainComplex.filteredSpectralSequence`, whose filtration is presented as
`CochainComplex.filtrationSubobject` of `HomologicalComplex₂.totalFiltration₂`. The two
presentations describe the same family of subobjects, but
`HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence` is a propositional and not a
definitional equality; `hypercoverPageInfinityTransportIso` crosses it once, at the infinity page.

## References

* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex FilteredComplexSpectralSequence Stacks.Cohomology.Leray

universe v

namespace Stacks.CategoryTheory.Hypercovering.Functorial

section SmallSite

variable {C : Type v} [SmallCategory C] (X : C) (J : GrothendieckTopology C)

/-! ### First-quadrant vanishing of the double complex -/

/-- **The Čech double complex of a complex of presheaves of abelian groups vanishes outside the
first quadrant.** Both indices are extended by zero from `ℕ`, the outer one by
`cechDoubleOuterBifunctor` and the inner one by `cechDoubleBifunctor`, so each negative index
kills the term on its own. -/
lemma isZero_cechDoubleBifunctor_X_X
    (K : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ)
    (Y : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ) (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero ((((cechDoubleBifunctor X).obj K).obj Y).X i |>.X j) := by
  rcases h with hi | hj
  · refine Functor.map_isZero
      (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) j)
      (Functor.map_isZero
        (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}) ?_)
    exact HomologicalComplex.isZero_extend_X
      (((cechDoubleNatBifunctor X).obj K).obj Y) ComplexShape.embeddingUpNat i
      fun k => by show ((k : ℕ) : ℤ) ≠ i; omega
  · exact HomologicalComplex.isZero_extend_X
      ((((cechDoubleOuterBifunctor X).obj K).obj Y).X i) ComplexShape.embeddingUpNat j
      fun k => by show ((k : ℕ) : ℤ) ≠ j; omega

section Resolution

/-- **The Čech double complex of the chosen injective resolution of a sheaf vanishes outside the
first quadrant.** -/
lemma isZero_hypercoverDouble_X_X
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((hypercoverDouble X J KF).X i).X j) :=
  isZero_cechDoubleBifunctor_X_X X KF.1 _ i j h

/-! ### The filtered complex -/

/-- **The total complex of the Čech double complex, filtered by the Čech degree.** -/
abbrev hypercoverFiltered
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    CochainComplex.Filtered AddCommGrpCat.{v} :=
  (hypercoverDouble X J KF).totalFiltration₂

/-- **`htop` for the hypercovering filtered complex**: the zeroth step of the filtration by the
Čech degree is the whole total complex. -/
lemma isIso_hypercoverFiltered_ι_f
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (n : ℤ) :
    IsIso (((hypercoverFiltered X J KF).filtration.ι.app (op (0 : ℤ))).f n) :=
  HomologicalComplex₂.isIso_totalFiltration₂_ι_f _
    (fun i j hj => isZero_hypercoverDouble_X_X X J KF i j (Or.inr hj)) n

/-- **`hbot` for the hypercovering filtered complex**: the `p`-th step of the filtration by the
Čech degree vanishes in total degrees below `p`. -/
lemma isZero_hypercoverFiltered_obj_X
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p n : ℤ) (hnp : n < p) :
    IsZero (((hypercoverFiltered X J KF).filtration.obj (op p)).X n) :=
  HomologicalComplex₂.isZero_totalFiltration₂_obj_X _
    (fun i j hi => isZero_hypercoverDouble_X_X X J KF i j (Or.inl hi)) p n hnp

/-! ### The infinity page before the transport -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The second spectral sequence of the Čech double complex vanishes outside the first quadrant,
before the start-page shift.** -/
lemma isFirstQuadrant_hypercoverSpectralSequence₂
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (hypercoverFiltered X J KF)
    ((hypercoverDouble X J KF).stepSubobject fun (_ : ℤ) j => j)
    (fun p n => HomologicalComplex₂.stepSubobject_eq _ _ (fun _ _ => le_rfl)
      (fun _ _ => by omega) p n)
    (HomologicalComplex₂.cycles₂ (hypercoverDouble X J KF)) (fun _ _ _ => rfl)
    (HomologicalComplex₂.boundaries₂ (hypercoverDouble X J KF)) (fun _ _ _ => rfl)
    _ (fun rr p q n hr hn => HomologicalComplex₂.pageIso₂ _ rr p q n hr hn)
    (isIso_hypercoverFiltered_ι_f X J KF)
    (isZero_hypercoverFiltered_obj_X X J KF)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- The second spectral sequence of the Čech double complex has an infinity page at every bidegree
of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_hypercoverSpectralSequence₂
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (x : ℤ × ℤ) :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).HasPageInfinityAt x :=
  hasPageInfinityAt_of_isFirstQuadrant _ (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the Čech double complex. -/
lemma hasEdgeMonoAtFrom_hypercoverSpectralSequence₂
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).HasPageInfinityAt
      (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).HasEdgeMonoAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _ (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF)
    (ComplexShape.natEmb (p, q)) (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the Čech double complex. -/
lemma hasEdgeEpiAtFrom_hypercoverSpectralSequence₂
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).HasPageInfinityAt
      (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).HasEdgeEpiAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _ (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF)
    (ComplexShape.natEmb (p, q)) (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeMonoAtFrom_hypercoverSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeMonoAtFrom_hypercoverShiftStart
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeMonoAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeEpiAtFrom_hypercoverSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeEpiAtFrom_hypercoverShiftStart
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeEpiAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered in
/-- `hasEdgeMonoAtFrom_hypercoverShiftStart` after the first-quadrant reindexing. -/
lemma hasEdgeMonoAtFrom_hypercoverNatRestrict
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF))).HasEdgeMonoAtFrom (p, q)
      (stablePage p q) :=
  CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ (p, q)
    (stablePage p q) (add_one_le_stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered in
/-- `hasEdgeEpiAtFrom_hypercoverShiftStart` after the first-quadrant reindexing. -/
lemma hasEdgeEpiAtFrom_hypercoverNatRestrict
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF))).HasEdgeEpiAtFrom (p, q)
      (stablePage p q) :=
  CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ (p, q)
    (stablePage p q) (add_two_le_stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The infinity page of the hypercovering spectral sequence at `(p, q)` is the infinity page of
the second spectral sequence of the Čech double complex at `ComplexShape.natEmb (p, q)`**, read at
the uniform stable page `CochainComplex.Filtered.stablePage p q`. -/
def hypercoverPageInfinityIso
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    ((hypercoverSpectralSequenceFunctor X J).obj KF).pageInfinity (p, q) ≅
      (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).pageInfinity
        (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_hypercoverSpectralSequence₂ X J KF (ComplexShape.natEmb (p, q))
  haveI := hasEdgeMonoAtFrom_hypercoverSpectralSequence₂ X J KF p q
  haveI := hasEdgeEpiAtFrom_hypercoverSpectralSequence₂ X J KF p q
  haveI := hasEdgeMonoAtFrom_hypercoverShiftStart X J KF p q
  haveI := hasEdgeEpiAtFrom_hypercoverShiftStart X J KF p q
  haveI := hasEdgeMonoAtFrom_hypercoverNatRestrict X J KF p q
  haveI := hasEdgeEpiAtFrom_hypercoverNatRestrict X J KF p q
  shiftNatRestrict_pageInfinityIsoAt (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF)) (p, q) (stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPageInfinityIso` is natural in the pair.** -/
theorem hypercoverPageInfinityIso_naturality
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (p q : ℕ) :
    Hom.mapPageInfinity ((hypercoverSpectralSequenceFunctor X J).map fg) (p, q) ≫
        (hypercoverPageInfinityIso X J LG p q).hom =
      (hypercoverPageInfinityIso X J KF p q).hom ≫
        Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverDoubleMap X J fg))
          (ComplexShape.natEmb (p, q)) := by
  have := fun M => hasPageInfinityAt_hypercoverSpectralSequence₂ X J M (ComplexShape.natEmb (p, q))
  have := fun M => hasEdgeMonoAtFrom_hypercoverSpectralSequence₂ X J M p q
  have := fun M => hasEdgeEpiAtFrom_hypercoverSpectralSequence₂ X J M p q
  have := fun M => hasEdgeMonoAtFrom_hypercoverShiftStart X J M p q
  have := fun M => hasEdgeEpiAtFrom_hypercoverShiftStart X J M p q
  have := fun M => hasEdgeMonoAtFrom_hypercoverNatRestrict X J M p q
  have := fun M => hasEdgeEpiAtFrom_hypercoverNatRestrict X J M p q
  exact shiftNatRestrict_pageInfinityIsoAt_naturality (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂ X J KF))
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂ X J LG))
    (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverDoubleMap X J fg)) (p, q)
    (stablePage p q) (two_le_stablePage p q)

/-! ### The filtered side -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The canonical spectral sequence of the hypercovering filtered complex vanishes outside the
first quadrant.** -/
lemma isFirstQuadrant_hypercoverFilteredSpectralSequence
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (CochainComplex.filteredSpectralSequence (hypercoverFiltered X J KF)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (hypercoverFiltered X J KF)
    (filtrationSubobject (hypercoverFiltered X J KF)) (fun _ _ => rfl)
    (cycles (hypercoverFiltered X J KF).X
      (filtrationSubobject (hypercoverFiltered X J KF))) (fun _ _ _ => rfl)
    (boundaries (hypercoverFiltered X J KF).X
      (filtrationSubobject (hypercoverFiltered X J KF))) (fun _ _ _ => rfl)
    _ (fun rr p' q' n' hr hn' => by
        subst hn'; exact pageIso (hypercoverFiltered X J KF) rr p' q' hr)
    (isIso_hypercoverFiltered_ι_f X J KF)
    (isZero_hypercoverFiltered_obj_X X J KF)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- The canonical spectral sequence of the hypercovering filtered complex has an infinity page at
every bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_hypercoverFiltered
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (x : ℤ × ℤ) :
    (CochainComplex.filteredSpectralSequence (hypercoverFiltered X J KF)).HasPageInfinityAt x :=
  hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverFilteredSpectralSequence X J KF) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the hypercovering filtered complex. -/
lemma hasEdgeMonoAtFrom_hypercoverFiltered
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (hypercoverFiltered X J KF)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (hypercoverFiltered X J KF)).HasEdgeMonoAtFrom ((p : ℤ), (q : ℤ)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverFilteredSpectralSequence X J KF) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the hypercovering filtered complex. -/
lemma hasEdgeEpiAtFrom_hypercoverFiltered
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (hypercoverFiltered X J KF)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (hypercoverFiltered X J KF)).HasEdgeEpiAtFrom ((p : ℤ), (q : ℤ)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverFilteredSpectralSequence X J KF) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)

open CochainComplex.Filtered in
/-- The filtration of the total complex by the Čech degree is degreewise finite. -/
lemma isDegreewiseFinite_hypercoverFiltered
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}) :
    (hypercoverFiltered X J KF).filtration.IsDegreewiseFinite :=
  isDegreewiseFinite_of_firstQuadrant (hypercoverFiltered X J KF)
    (isIso_hypercoverFiltered_ι_f X J KF) (isZero_hypercoverFiltered_obj_X X J KF)

open CochainComplex.Filtered in
/-- **`CochainComplex.Filtered.stablePage p q` is a stable page at `(p, q)` for the filtered
complex of every pair `(K, F)` simultaneously.** -/
lemma isStableFrom_hypercoverFiltered
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    IsStableFrom (hypercoverFiltered X J KF)
      (filtrationSubobject (hypercoverFiltered X J KF)) (p : ℤ) (q : ℤ) (stablePage p q) :=
  isStableFrom_of_firstQuadrant (hypercoverFiltered X J KF)
    (isIso_hypercoverFiltered_ι_f X J KF) (isZero_hypercoverFiltered_obj_X X J KF)
    (p : ℤ) (q : ℤ) (stablePage p q) (one_le_stablePage p q) (add_two_le_stablePage p q)
    (add_one_le_stablePage p q)

/-! ### The filtration functor -/

/-- **The morphism of filtered complexes attached to a morphism of pairs**: the total complex of
`hypercoverDoubleMap` with its filtration by the Čech degree. -/
def hypercoverFilteredMap
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) : hypercoverFiltered X J KF ⟶ hypercoverFiltered X J LG :=
  Stacks.Cohomology.CechSpectral.totalFiltrationMap (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
    (fun _ _ => by omega) (hypercoverDoubleMap X J fg)

/-- The underlying morphism of complexes of `hypercoverFilteredMap fg` is `Tot(A^{•,•}(fg))`. -/
@[simp]
lemma hypercoverFilteredMap_hom
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) :
    (hypercoverFilteredMap X J fg).hom =
      HomologicalComplex₂.total.map (hypercoverDoubleMap X J fg) (ComplexShape.up ℤ) :=
  rfl

/-- **`H^n` of the total complex sends an identity to an identity.** -/
lemma homologyMap_hypercoverFilteredMap_id
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (n : ℤ) :
    HomologicalComplex.homologyMap (hypercoverFilteredMap X J (𝟙 KF)).hom n = 𝟙 _ := by
  rw [hypercoverFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_hypercoverDoubleMap_id X J KF) |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_id, HomologicalComplex.homologyMap_id]

/-- **`H^n` of the total complex is multiplicative.** -/
lemma homologyMap_hypercoverFilteredMap_comp
    {KF LG MH : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (f'g' : LG ⟶ MH) (n : ℤ) :
    HomologicalComplex.homologyMap (hypercoverFilteredMap X J (fg ≫ f'g')).hom n =
      HomologicalComplex.homologyMap (hypercoverFilteredMap X J fg).hom n ≫
        HomologicalComplex.homologyMap (hypercoverFilteredMap X J f'g').hom n := by
  rw [hypercoverFilteredMap_hom, hypercoverFilteredMap_hom, hypercoverFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_hypercoverDoubleMap_comp X J fg f'g')
      |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

open CochainComplex.Filtered in
/-- **The `filtration` field**: `H^n(Tot(Č^•(K, I^•(F))))` with its induced filtration, as a
functor of the pair `(K, F)`. -/
def hypercoverFiltrationFunctor (n : ℤ) :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      FilteredObject AddCommGrpCat.{v} ℤᵒᵖ where
  obj KF := (hypercoverFiltered X J KF).inducedFilteredObject n
  map fg := inducedFilteredObjectMap (hypercoverFilteredMap X J fg) n
  map_id KF := FilteredObject.hom_ext (homologyMap_hypercoverFilteredMap_id X J KF n)
  map_comp fg f'g' :=
    FilteredObject.hom_ext (homologyMap_hypercoverFilteredMap_comp X J fg f'g' n)

/-! ### The graded identification -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport of the infinity page across the two presentations of the filtration of the
total complex by the Čech degree**: `HomologicalComplex₂.stepSubobject`, which
`HomologicalComplex₂.spectralSequence₂` uses, and `CochainComplex.filtrationSubobject` of
`HomologicalComplex₂.totalFiltration₂`, which `CochainComplex.filteredSpectralSequence` uses. -/
def hypercoverPageInfinityTransportIso
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble X J KF)).pageInfinity
        (ComplexShape.natEmb (p, q)) ≅
      (CochainComplex.filteredSpectralSequence (hypercoverFiltered X J KF)).pageInfinity
        (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_hypercoverSpectralSequence₂ X J KF (ComplexShape.natEmb (p, q))
  haveI := hasPageInfinityAt_hypercoverFiltered X J KF (ComplexShape.natEmb (p, q))
  pageInfinityEqToIso
    (HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence
      (hypercoverDouble X J KF)) (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPageInfinityTransportIso` is natural in the pair.** -/
theorem hypercoverPageInfinityTransportIso_naturality
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (p q : ℕ) :
    Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverDoubleMap X J fg))
          (ComplexShape.natEmb (p, q)) ≫
        (hypercoverPageInfinityTransportIso X J LG p q).hom =
      (hypercoverPageInfinityTransportIso X J KF p q).hom ≫
        Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (hypercoverFilteredMap X J fg)) (ComplexShape.natEmb (p, q)) := by
  have := fun M => hasPageInfinityAt_hypercoverSpectralSequence₂ X J M (ComplexShape.natEmb (p, q))
  have := fun M => hasPageInfinityAt_hypercoverFiltered X J M (ComplexShape.natEmb (p, q))
  exact mapPageInfinity_pageInfinityEqToIso _ _ _ _
    (HomologicalComplex₂.spectralSequenceMap₂_eqToHom (hypercoverDoubleMap X J fg))
    (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(Tot(A^{•,•}(K, F)))` for the canonical spectral sequence of the
hypercovering filtered complex**, read at the uniform stable page
`CochainComplex.Filtered.stablePage p q`. -/
def hypercoverCanonicalGradedIso
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    (CochainComplex.filteredSpectralSequence (hypercoverFiltered X J KF)).pageInfinity
        (ComplexShape.natEmb (p, q)) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((hypercoverFiltrationFunctor X J ((p + q : ℕ) : ℤ)).obj KF) :=
  haveI := hasPageInfinityAt_hypercoverFiltered X J KF ((p : ℤ), (q : ℤ))
  haveI := hasEdgeMonoAtFrom_hypercoverFiltered X J KF p q
  haveI := hasEdgeEpiAtFrom_hypercoverFiltered X J KF p q
  canonicalPageInfinityIsoGr (hypercoverFiltered X J KF)
    (isDegreewiseFinite_hypercoverFiltered X J KF) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_hypercoverFiltered X J KF p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverCanonicalGradedIso` is natural in the pair.** -/
theorem hypercoverCanonicalGradedIso_naturality
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (p q : ℕ) :
    Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (hypercoverFilteredMap X J fg)) (ComplexShape.natEmb (p, q)) ≫
        (hypercoverCanonicalGradedIso X J LG p q).hom =
      (hypercoverCanonicalGradedIso X J KF p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((hypercoverFiltrationFunctor X J ((p + q : ℕ) : ℤ)).map fg) := by
  have := fun M => hasPageInfinityAt_hypercoverFiltered X J M ((p : ℤ), (q : ℤ))
  have := fun M => hasEdgeMonoAtFrom_hypercoverFiltered X J M p q
  have := fun M => hasEdgeEpiAtFrom_hypercoverFiltered X J M p q
  exact canonicalPageInfinityIsoGr_naturality (hypercoverFilteredMap X J fg)
    (isDegreewiseFinite_hypercoverFiltered X J KF)
    (isDegreewiseFinite_hypercoverFiltered X J LG) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_hypercoverFiltered X J KF p q)
    (isStableFrom_hypercoverFiltered X J LG p q)
    (inducedFilteredObjectMap (hypercoverFilteredMap X J fg) ((p + q : ℕ) : ℤ)) rfl

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso` field**: `E_∞^{p,q} ≅ gr^pH^{p+q}`. -/
def hypercoverGradedIso
    (KF : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v})
    (p q : ℕ) :
    ((hypercoverSpectralSequenceFunctor X J).obj KF).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((hypercoverFiltrationFunctor X J ((p + q : ℕ) : ℤ)).obj KF) :=
  hypercoverPageInfinityIso X J KF p q ≪≫
    hypercoverPageInfinityTransportIso X J KF p q ≪≫
      hypercoverCanonicalGradedIso X J KF p q

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso_naturality` field**: `hypercoverGradedIso` is natural in the pair. -/
theorem hypercoverGradedIso_naturality
    {KF LG : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (p q : ℕ) :
    Hom.mapPageInfinity ((hypercoverSpectralSequenceFunctor X J).map fg) (p, q) ≫
        (hypercoverGradedIso X J LG p q).hom =
      (hypercoverGradedIso X J KF p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((hypercoverFiltrationFunctor X J ((p + q : ℕ) : ℤ)).map fg) := by
  rw [hypercoverGradedIso, hypercoverGradedIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% hypercoverPageInfinityIso_naturality X J fg p q,
    reassoc_of% hypercoverPageInfinityTransportIso_naturality X J fg p q,
    hypercoverCanonicalGradedIso_naturality X J fg p q]

/-! ### The functorial abutment -/

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The functorial filtered abutment of the hypercovering spectral sequence for an arbitrary
simplicial semi-representable object**, abutting to the cohomology of the total complex
`Tot(Č^•(K, I^•(F)))`. -/
def hypercoverFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (hypercoverSpectralSequenceFunctor X J)
      (fun n => hypercoverFiltrationFunctor X J (n : ℤ) ⋙ FilteredObject.forget) where
  filtration n := hypercoverFiltrationFunctor X J (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite KF n := (Filtration.isFinite_iff_subobject _).2
    ⟨⟨op (0 : ℤ), inducedFilteredObject_subobject_zero (hypercoverFiltered X J KF)
        (isIso_hypercoverFiltered_ι_f X J KF) (n : ℤ)⟩,
      ⟨op ((n : ℤ) + 1), inducedFilteredObject_subobject_succ (hypercoverFiltered X J KF)
        (isZero_hypercoverFiltered_obj_X X J KF) (n : ℤ)⟩⟩
  isTop KF n := inducedFilteredObject_subobject_zero (hypercoverFiltered X J KF)
    (isIso_hypercoverFiltered_ι_f X J KF) (n : ℤ)
  isBot KF n := inducedFilteredObject_subobject_succ (hypercoverFiltered X J KF)
    (isZero_hypercoverFiltered_obj_X X J KF) (n : ℤ)
  gradedIso KF p q := hypercoverGradedIso X J KF p q
  gradedIso_naturality fg p q := hypercoverGradedIso_naturality X J fg p q

end Resolution

end SmallSite

section Hypercoverings

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)

/-- **The filtered abutment of clause (3) of [Stacks, Tag 01GY]**, abutting to the cohomology of
the total complex: `hypercoverFunctorialAbutment` restricted along the inclusion of the full
subcategory of hypercoverings, the category
`Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringSpectralSequence` is a functor on. -/
def hypercoveringFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (hypercoveringSpectralSequence X J)
      (fun n => (ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
        hypercoverFiltrationFunctor X J.toGrothendieck (n : ℤ) ⋙ FilteredObject.forget) where
  filtration n := (ObjectProperty.ι _).op.prod
      (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
    hypercoverFiltrationFunctor X J.toGrothendieck (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite _ n := (hypercoverFunctorialAbutment X J.toGrothendieck).isFinite _ n
  isTop _ n := (hypercoverFunctorialAbutment X J.toGrothendieck).isTop _ n
  isBot _ n := (hypercoverFunctorialAbutment X J.toGrothendieck).isBot _ n
  gradedIso _ p q := (hypercoverFunctorialAbutment X J.toGrothendieck).gradedIso _ p q
  gradedIso_naturality _ p q :=
    (hypercoverFunctorialAbutment X J.toGrothendieck).gradedIso_naturality _ p q

end Hypercoverings

end Stacks.CategoryTheory.Hypercovering.Functorial

end
