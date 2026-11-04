module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectAcyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.AbutmentIsCohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.SequenceAndSecondPage

/-!
# The abutment of the hypercovering spectral sequence

Let `C` be a site with fibre products, `X` an object of `C`, `K` a hypercovering of `X` and `F` a
sheaf of abelian groups on `C`.  The spectral sequence of [Stacks, Tag 01GY], constructed in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.SequenceAndSecondPage` from the
double complex `A^{p,q}(F) = s(I^p(K))^q` of a chosen injective resolution `F ⟶ I^•`, converges to
`H^{p+q}(X, F)`.  This file supplies that abutment.

The abutment is the cohomology of the total complex, filtered by the hypercovering degree, which
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex` turns into a
functorial filtered abutment; `hypercoverAbutmentIso` then identifies it with `R^nΓ(X, -)` through
[Stacks, Tag 0133], the four hypotheses of which are `hypotheses_sectionsAug` -- the
positive-degree acyclicity of the sections complex of an injective sheaf is [Stacks, Tag 01GW] and
the degree-zero clause is [Stacks, Tag 01GV] in canonical-map form.  The open-covering analogue is
`StacksFrontier/Topology/Sheaves/Cohomology/CechSpectralSequence/AbutmentIsCohomology.lean`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.hypercoverFiltrationFunctor`: the cohomology of the total
  complex with the filtration by the hypercovering degree, as a functor.
* `Stacks.CategoryTheory.Hypercovering.hypercoverFunctorialAbutment` and
  `Stacks.CategoryTheory.Hypercovering.hypercoverAbutment`: its functorial filtered abutment,
  abutting to the cohomology of the total complex and then to `R^nΓ(X, -)`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.hypotheses_sectionsAug`: the four hypotheses of
  [Stacks, Tag 0133] for the double complex.
* `Stacks.CategoryTheory.Hypercovering.hypercoverAbutmentIso`: the abutment is `R^nΓ(X, -)`,
  naturally in `F`.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GW](https://stacks.math.columbia.edu/tag/01GW)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### The functorial filtered abutment -/

section Abutment

open CochainComplex FilteredComplexSpectralSequence Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

attribute [local instance] enoughInjectives_sheafAddCommGrpCat

/-- **The double complex of a sheaf vanishes outside the first quadrant.**  The inner index is
extended by zero from `ℕ` by `hypercoverCochainIntFunctor` and the outer one by the extension of
the chosen injective resolution, so each negative index kills the term on its own. -/
lemma isZero_hypercoverDouble_X_X (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((hypercoverDouble.{w} J X K F).X i).X j) := by
  rcases h with hi | hj
  · exact Functor.map_isZero
      (HomologicalComplex.eval AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) j)
      (isZero_hypercoverDoubleFunctor_X.{w} J X K _ i (isZero_resolutionExtend_X J F i hi))
  · exact isZero_hypercoverDoubleFunctor_X_X_of_inner_neg.{w} J X K _ i j hj

/-- **The total complex of the double complex, filtered by the hypercovering degree.**  This is
the filtered complex whose spectral sequence is the hypercovering spectral sequence and whose
cohomology with its induced filtration is the abutment. -/
abbrev hypercoverFiltered (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    CochainComplex.Filtered AddCommGrpCat.{max u v w} :=
  (hypercoverDouble.{w} J X K F).totalFiltration₂

/-- **`htop` for the hypercovering filtered complex**: the zeroth step of the filtration by the
hypercovering degree is the whole total complex. -/
lemma isIso_hypercoverFiltered_ι_f
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℤ) :
    IsIso (((hypercoverFiltered.{w} J X K F).filtration.ι.app (op (0 : ℤ))).f n) :=
  HomologicalComplex₂.isIso_totalFiltration₂_ι_f _
    (fun i j hj => isZero_hypercoverDouble_X_X.{w} J X K F i j (Or.inr hj)) n

/-- **`hbot` for the hypercovering filtered complex**: the `p`-th step of the filtration by the
hypercovering degree vanishes in total degrees below `p`. -/
lemma isZero_hypercoverFiltered_obj_X
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p n : ℤ) (hnp : n < p) :
    IsZero (((hypercoverFiltered.{w} J X K F).filtration.obj (op p)).X n) :=
  HomologicalComplex₂.isZero_totalFiltration₂_obj_X _
    (fun i j hi => isZero_hypercoverDouble_X_X.{w} J X K F i j (Or.inl hi)) p n hnp

/-- **The second spectral sequence of the double complex vanishes outside the first quadrant,
before the start-page shift.**  This unshifted form is what
`CategoryTheory.SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant` and its companion need, and
it is obtained from `CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration` applied to
the `HomologicalComplex₂.stepSubobject` presentation of the filtration -- the presentation
`HomologicalComplex₂.spectralSequence₂` is built on -- so that no transport is involved. -/
lemma isFirstQuadrant_hypercoverSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)) :=
  CochainComplex.Filtered.isFirstQuadrant_of_firstQuadrantFiltration
    (hypercoverFiltered.{w} J X K F)
    ((hypercoverDouble.{w} J X K F).stepSubobject fun (_ : ℤ) j => j)
    (fun p n => HomologicalComplex₂.stepSubobject_eq _ _ (fun _ _ => le_rfl)
      (fun _ _ => by omega) p n)
    (HomologicalComplex₂.cycles₂ (hypercoverDouble.{w} J X K F)) (fun _ _ _ => rfl)
    (HomologicalComplex₂.boundaries₂ (hypercoverDouble.{w} J X K F)) (fun _ _ _ => rfl)
    _ (fun rr p q n hr hn => HomologicalComplex₂.pageIso₂ _ rr p q n hr hn)
    (isIso_hypercoverFiltered_ι_f.{w} J X K F)
    (isZero_hypercoverFiltered_obj_X.{w} J X K F)

open CochainComplex.Filtered in
/-- The second spectral sequence of the double complex has an infinity page at every bidegree of
`ℤ × ℤ`. -/
lemma hasPageInfinityAt_hypercoverSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (x : ℤ × ℤ) :
    (HomologicalComplex₂.spectralSequence₂
      (hypercoverDouble.{w} J X K F)).HasPageInfinityAt x :=
  CategoryTheory.SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the double complex. -/
lemma hasEdgeMonoAtFrom_hypercoverSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂
      (hypercoverDouble.{w} J X K F)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).HasEdgeMonoAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
unshifted second spectral sequence of the double complex. -/
lemma hasEdgeEpiAtFrom_hypercoverSpectralSequence₂
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ)
    [(HomologicalComplex₂.spectralSequence₂
      (hypercoverDouble.{w} J X K F)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).HasEdgeEpiAtFrom
      (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeMonoAtFrom_hypercoverSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeMonoAtFrom_hypercoverShiftStart
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeMonoAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_fst_lt_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- `hasEdgeEpiAtFrom_hypercoverSpectralSequence₂` after the start-page shift. -/
lemma hasEdgeEpiAtFrom_hypercoverShiftStart
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ)
    [((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt (ComplexShape.natEmb (p, q))] :
    ((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).shiftStart
      (show (0 : ℤ) ≤ 2 by omega)).HasEdgeEpiAtFrom
        (ComplexShape.natEmb (p, q)) (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)

open CochainComplex.Filtered in
/-- `hasEdgeMonoAtFrom_hypercoverShiftStart` after the first-quadrant reindexing.

Stated in the `CategoryTheory.SpectralSequence.natRestrict`-of-`shiftStart` spelling rather than as
`(hypercoverSpectralSequenceFunctor J X K).obj F`, because that is the spelling
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt` asks for: the two are equal by
definition, but instance search is keyed on the head symbol and would not look through
`hypercoverSpectralSequenceFunctor`. -/
lemma hasEdgeMonoAtFrom_hypercoverNatRestrict
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F))).HasEdgeMonoAtFrom (p, q)
      (stablePage p q) :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ (p, q)
    (stablePage p q) (add_one_le_stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered in
/-- The companion of `hasEdgeMonoAtFrom_hypercoverNatRestrict`, in the same spelling and for the
same reason. -/
lemma hasEdgeEpiAtFrom_hypercoverNatRestrict
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    (((HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).shiftStart
        (show (0 : ℤ) ≤ 2 by omega)).natRestrict
      (CategoryTheory.SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
        (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F))).HasEdgeEpiAtFrom (p, q)
      (stablePage p q) :=
  CategoryTheory.CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ (p, q)
    (stablePage p q) (add_two_le_stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The infinity page of the hypercovering spectral sequence at `(p, q)` is the infinity page of
the second spectral sequence of the double complex at `ComplexShape.natEmb (p, q)`**, read at the
uniform stable page `CochainComplex.Filtered.stablePage p q`.  This is
`CategoryTheory.SpectralSequence.shiftNatRestrict_pageInfinityIsoAt`. -/
def hypercoverPageInfinityIso (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    ((hypercoverSpectralSequenceFunctor.{w} J X K).obj F).pageInfinity (p, q) ≅
      (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).pageInfinity
        (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_hypercoverSpectralSequence₂.{w} J X K F
    (ComplexShape.natEmb (p, q))
  haveI := hasEdgeMonoAtFrom_hypercoverSpectralSequence₂.{w} J X K F p q
  haveI := hasEdgeEpiAtFrom_hypercoverSpectralSequence₂.{w} J X K F p q
  haveI := hasEdgeMonoAtFrom_hypercoverShiftStart.{w} J X K F p q
  haveI := hasEdgeEpiAtFrom_hypercoverShiftStart.{w} J X K F p q
  haveI := hasEdgeMonoAtFrom_hypercoverNatRestrict.{w} J X K F p q
  haveI := hasEdgeEpiAtFrom_hypercoverNatRestrict.{w} J X K F p q
  shiftNatRestrict_pageInfinityIsoAt (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F)) (p, q) (stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverPageInfinityIso` is natural in the sheaf.**  Both transports -- the start-page
shift and the first-quadrant reindexing -- are read at the page
`CochainComplex.Filtered.stablePage p q`, which is admissible for every sheaf at once, and there
the two induced maps on the infinity pages are the *same* morphism of pages. -/
theorem hypercoverPageInfinityIso_naturality
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity ((hypercoverSpectralSequenceFunctor.{w} J X K).map f) (p, q) ≫
        (hypercoverPageInfinityIso.{w} J X K G p q).hom =
      (hypercoverPageInfinityIso.{w} J X K F p q).hom ≫
        Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverDoubleMap.{w} J X K f))
          (ComplexShape.natEmb (p, q)) := by
  have := fun H => hasPageInfinityAt_hypercoverSpectralSequence₂.{w} J X K H
    (ComplexShape.natEmb (p, q))
  have := fun H => hasEdgeMonoAtFrom_hypercoverSpectralSequence₂.{w} J X K H p q
  have := fun H => hasEdgeEpiAtFrom_hypercoverSpectralSequence₂.{w} J X K H p q
  have := fun H => hasEdgeMonoAtFrom_hypercoverShiftStart.{w} J X K H p q
  have := fun H => hasEdgeEpiAtFrom_hypercoverShiftStart.{w} J X K H p q
  have := fun H => hasEdgeMonoAtFrom_hypercoverNatRestrict.{w} J X K H p q
  have := fun H => hasEdgeEpiAtFrom_hypercoverNatRestrict.{w} J X K H p q
  exact shiftNatRestrict_pageInfinityIsoAt_naturality (show (0 : ℤ) ≤ 2 by omega)
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K F))
    (shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_hypercoverSpectralSequence₂.{w} J X K G))
    (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverDoubleMap.{w} J X K f)) (p, q)
    (stablePage p q) (two_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The canonical spectral sequence of the hypercovering filtered complex vanishes outside the
first quadrant.**  The same statement as `isFirstQuadrant_hypercoverSpectralSequence₂` for the
other presentation of the same filtration, the one `CochainComplex.filteredSpectralSequence` is
built on. -/
lemma isFirstQuadrant_hypercoverFilteredSpectralSequence
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (CochainComplex.filteredSpectralSequence (hypercoverFiltered.{w} J X K F)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (hypercoverFiltered.{w} J X K F)
    (filtrationSubobject (hypercoverFiltered.{w} J X K F)) (fun _ _ => rfl)
    (cycles (hypercoverFiltered.{w} J X K F).X
      (filtrationSubobject (hypercoverFiltered.{w} J X K F))) (fun _ _ _ => rfl)
    (boundaries (hypercoverFiltered.{w} J X K F).X
      (filtrationSubobject (hypercoverFiltered.{w} J X K F))) (fun _ _ _ => rfl)
    _ (fun rr p' q' n' hr hn' => by
        subst hn'; exact pageIso (hypercoverFiltered.{w} J X K F) rr p' q' hr)
    (isIso_hypercoverFiltered_ι_f.{w} J X K F)
    (isZero_hypercoverFiltered_obj_X.{w} J X K F)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- The canonical spectral sequence of the hypercovering filtered complex has an infinity page at
every bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_hypercoverFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (x : ℤ × ℤ) :
    (CochainComplex.filteredSpectralSequence
      (hypercoverFiltered.{w} J X K F)).HasPageInfinityAt x :=
  hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverFilteredSpectralSequence.{w} J X K F) x

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials into `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the hypercovering filtered complex. -/
lemma hasEdgeMonoAtFrom_hypercoverFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (hypercoverFiltered.{w} J X K F)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (hypercoverFiltered.{w} J X K F)).HasEdgeMonoAtFrom ((p : ℤ), (q : ℤ))
        (stablePage p q) :=
  hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverFilteredSpectralSequence.{w} J X K F) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The differentials out of `(p, q)` have vanished for good from `stablePage p q` on**, for the
canonical spectral sequence of the hypercovering filtered complex. -/
lemma hasEdgeEpiAtFrom_hypercoverFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ)
    [(CochainComplex.filteredSpectralSequence
      (hypercoverFiltered.{w} J X K F)).HasPageInfinityAt ((p : ℤ), (q : ℤ))] :
    (CochainComplex.filteredSpectralSequence
      (hypercoverFiltered.{w} J X K F)).HasEdgeEpiAtFrom ((p : ℤ), (q : ℤ))
        (stablePage p q) :=
  hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_hypercoverFilteredSpectralSequence.{w} J X K F) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)

open CochainComplex.Filtered in
/-- The filtration of the total complex by the hypercovering degree is degreewise finite, so the
convergence identification of [Stacks, Tag 012W] applies to it. -/
lemma isDegreewiseFinite_hypercoverFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (hypercoverFiltered.{w} J X K F).filtration.IsDegreewiseFinite :=
  isDegreewiseFinite_of_firstQuadrant (hypercoverFiltered.{w} J X K F)
    (isIso_hypercoverFiltered_ι_f.{w} J X K F)
    (isZero_hypercoverFiltered_obj_X.{w} J X K F)

open CochainComplex.Filtered in
/-- **`CochainComplex.Filtered.stablePage p q` is a stable page at `(p, q)` for the filtered
complex of every sheaf simultaneously**, which is what the naturality of the convergence
identification needs. -/
lemma isStableFrom_hypercoverFiltered
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    IsStableFrom (hypercoverFiltered.{w} J X K F)
      (filtrationSubobject (hypercoverFiltered.{w} J X K F)) (p : ℤ) (q : ℤ)
      (stablePage p q) :=
  isStableFrom_of_firstQuadrant (hypercoverFiltered.{w} J X K F)
    (isIso_hypercoverFiltered_ι_f.{w} J X K F)
    (isZero_hypercoverFiltered_obj_X.{w} J X K F)
    (p : ℤ) (q : ℤ) (stablePage p q) (one_le_stablePage p q) (add_two_le_stablePage p q)
    (add_one_le_stablePage p q)

/-- **The morphism of filtered complexes attached to a morphism of sheaves**: the total complex of
`hypercoverDoubleMap` with its filtration by the hypercovering degree.  Like
`hypercoverDoubleMap` it is functorial only up to homotopy; what *is* functorial is the cohomology
it induces, which is `hypercoverFiltrationFunctor`. -/
def hypercoverFilteredMap {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    hypercoverFiltered.{w} J X K F ⟶ hypercoverFiltered.{w} J X K G :=
  Stacks.Cohomology.CechSpectral.totalFiltrationMap (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
    (fun _ _ => by omega) (hypercoverDoubleMap.{w} J X K f)

/-- The underlying morphism of complexes of `hypercoverFilteredMap f` is `Tot(A^{•,•}(f))`. -/
@[simp]
lemma hypercoverFilteredMap_hom
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    (hypercoverFilteredMap.{w} J X K f).hom =
      HomologicalComplex₂.total.map (hypercoverDoubleMap.{w} J X K f) (ComplexShape.up ℤ) :=
  rfl

/-- **`H^n` of the total complex sends an identity to an identity.**
`hypercoverDoubleMap (𝟙 F)` is only filtered homotopic to the identity, but the homotopy carried
inside `HomologicalComplex₂.FilteredHomotopy₂` is a homotopy of the *total* complexes, and
homology is homotopy invariant. -/
lemma homologyMap_hypercoverFilteredMap_id
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℤ) :
    HomologicalComplex.homologyMap (hypercoverFilteredMap.{w} J X K (𝟙 F)).hom n = 𝟙 _ := by
  rw [hypercoverFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_hypercoverDoubleMap_id.{w} J X K F) |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_id, HomologicalComplex.homologyMap_id]

/-- **`H^n` of the total complex is multiplicative.**  As with
`homologyMap_hypercoverFilteredMap_id`, from the homotopy carried inside
`HomologicalComplex₂.FilteredHomotopy₂`. -/
lemma homologyMap_hypercoverFilteredMap_comp
    {F G H : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
    HomologicalComplex.homologyMap (hypercoverFilteredMap.{w} J X K (f ≫ g)).hom n =
      HomologicalComplex.homologyMap (hypercoverFilteredMap.{w} J X K f).hom n ≫
        HomologicalComplex.homologyMap (hypercoverFilteredMap.{w} J X K g).hom n := by
  rw [hypercoverFilteredMap_hom, hypercoverFilteredMap_hom, hypercoverFilteredMap_hom,
    Exists.choose (filteredHomotopy₂_hypercoverDoubleMap_comp.{w} J X K f g) |>.homologyMap_eq n,
    HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

open CochainComplex.Filtered in
/-- **The `filtration` field**: `H^n(Tot(s(I^•(K))))` with its induced filtration, as a
functor. -/
def hypercoverFiltrationFunctor (n : ℤ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      FilteredObject AddCommGrpCat.{max u v w} ℤᵒᵖ where
  obj F := (hypercoverFiltered.{w} J X K F).inducedFilteredObject n
  map f := inducedFilteredObjectMap (hypercoverFilteredMap.{w} J X K f) n
  map_id F := FilteredObject.hom_ext (homologyMap_hypercoverFilteredMap_id.{w} J X K F n)
  map_comp f g :=
    FilteredObject.hom_ext (homologyMap_hypercoverFilteredMap_comp.{w} J X K f g n)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport of the infinity page across the two presentations of the filtration of the
total complex by the hypercovering degree**: `HomologicalComplex₂.stepSubobject`, which
`HomologicalComplex₂.spectralSequence₂` uses, and `CochainComplex.filtrationSubobject` of
`HomologicalComplex₂.totalFiltration₂`, which `CochainComplex.filteredSpectralSequence` uses. -/
def hypercoverPageInfinityTransportIso
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    (HomologicalComplex₂.spectralSequence₂ (hypercoverDouble.{w} J X K F)).pageInfinity
        (ComplexShape.natEmb (p, q)) ≅
      (CochainComplex.filteredSpectralSequence
        (hypercoverFiltered.{w} J X K F)).pageInfinity (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_hypercoverSpectralSequence₂.{w} J X K F
    (ComplexShape.natEmb (p, q))
  haveI := hasPageInfinityAt_hypercoverFiltered.{w} J X K F (ComplexShape.natEmb (p, q))
  pageInfinityEqToIso
    (HomologicalComplex₂.spectralSequence₂_eq_filteredSpectralSequence
      (hypercoverDouble.{w} J X K F)) (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The transport is natural in the sheaf.**  This is
`CategoryTheory.SpectralSequence.mapPageInfinity_pageInfinityEqToIso` at the conjugation square
`HomologicalComplex₂.spectralSequenceMap₂_eqToHom`. -/
theorem hypercoverPageInfinityTransportIso_naturality
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity
          (HomologicalComplex₂.spectralSequenceMap₂ (hypercoverDoubleMap.{w} J X K f))
          (ComplexShape.natEmb (p, q)) ≫
        (hypercoverPageInfinityTransportIso.{w} J X K G p q).hom =
      (hypercoverPageInfinityTransportIso.{w} J X K F p q).hom ≫
        Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (hypercoverFilteredMap.{w} J X K f)) (ComplexShape.natEmb (p, q)) := by
  have := fun H => hasPageInfinityAt_hypercoverSpectralSequence₂.{w} J X K H
    (ComplexShape.natEmb (p, q))
  have := fun H => hasPageInfinityAt_hypercoverFiltered.{w} J X K H (ComplexShape.natEmb (p, q))
  exact mapPageInfinity_pageInfinityEqToIso _ _ _ _
    (HomologicalComplex₂.spectralSequenceMap₂_eqToHom (hypercoverDoubleMap.{w} J X K f))
    (ComplexShape.natEmb (p, q))

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`E_∞^{p,q} ≅ gr^pH^{p+q}(Tot(A^{•,•}(F)))` for the canonical spectral sequence of the
hypercovering filtered complex**, with the stable page supplied uniformly by
`CochainComplex.Filtered.stablePage`.  This is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr`. -/
def hypercoverCanonicalGradedIso
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    (CochainComplex.filteredSpectralSequence
        (hypercoverFiltered.{w} J X K F)).pageInfinity (ComplexShape.natEmb (p, q)) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((hypercoverFiltrationFunctor.{w} J X K ((p + q : ℕ) : ℤ)).obj F) :=
  haveI := hasPageInfinityAt_hypercoverFiltered.{w} J X K F ((p : ℤ), (q : ℤ))
  haveI := hasEdgeMonoAtFrom_hypercoverFiltered.{w} J X K F p q
  haveI := hasEdgeEpiAtFrom_hypercoverFiltered.{w} J X K F p q
  canonicalPageInfinityIsoGr (hypercoverFiltered.{w} J X K F)
    (isDegreewiseFinite_hypercoverFiltered.{w} J X K F) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_hypercoverFiltered.{w} J X K F p q)

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **`hypercoverCanonicalGradedIso` is natural in the sheaf.**  This is
`CochainComplex.Filtered.canonicalPageInfinityIsoGr_naturality` at the page
`CochainComplex.Filtered.stablePage p q`, which `isStableFrom_hypercoverFiltered` makes stable for
every sheaf at once. -/
theorem hypercoverCanonicalGradedIso_naturality
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity (CochainComplex.filteredSpectralSequenceMap
          (hypercoverFilteredMap.{w} J X K f)) (ComplexShape.natEmb (p, q)) ≫
        (hypercoverCanonicalGradedIso.{w} J X K G p q).hom =
      (hypercoverCanonicalGradedIso.{w} J X K F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((hypercoverFiltrationFunctor.{w} J X K ((p + q : ℕ) : ℤ)).map f) := by
  have := fun H => hasPageInfinityAt_hypercoverFiltered.{w} J X K H ((p : ℤ), (q : ℤ))
  have := fun H => hasEdgeMonoAtFrom_hypercoverFiltered.{w} J X K H p q
  have := fun H => hasEdgeEpiAtFrom_hypercoverFiltered.{w} J X K H p q
  exact canonicalPageInfinityIsoGr_naturality (hypercoverFilteredMap.{w} J X K f)
    (isDegreewiseFinite_hypercoverFiltered.{w} J X K F)
    (isDegreewiseFinite_hypercoverFiltered.{w} J X K G) (p : ℤ) (q : ℤ) (stablePage p q)
    (isStableFrom_hypercoverFiltered.{w} J X K F p q)
    (isStableFrom_hypercoverFiltered.{w} J X K G p q)
    (inducedFilteredObjectMap (hypercoverFilteredMap.{w} J X K f) ((p + q : ℕ) : ℤ)) rfl

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso` field**: `E_∞^{p,q} ≅ gr^pH^{p+q}`. -/
def hypercoverGradedIso (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p q : ℕ) :
    ((hypercoverSpectralSequenceFunctor.{w} J X K).obj F).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((hypercoverFiltrationFunctor.{w} J X K ((p + q : ℕ) : ℤ)).obj F) :=
  hypercoverPageInfinityIso.{w} J X K F p q ≪≫
    hypercoverPageInfinityTransportIso.{w} J X K F p q ≪≫
      hypercoverCanonicalGradedIso.{w} J X K F p q

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The `gradedIso_naturality` field**: the three squares, pasted. -/
theorem hypercoverGradedIso_naturality
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (p q : ℕ) :
    Hom.mapPageInfinity ((hypercoverSpectralSequenceFunctor.{w} J X K).map f) (p, q) ≫
        (hypercoverGradedIso.{w} J X K G p q).hom =
      (hypercoverGradedIso.{w} J X K F p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((hypercoverFiltrationFunctor.{w} J X K ((p + q : ℕ) : ℤ)).map f) := by
  rw [hypercoverGradedIso, hypercoverGradedIso]
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% hypercoverPageInfinityIso_naturality.{w} J X K f p q,
    reassoc_of% hypercoverPageInfinityTransportIso_naturality.{w} J X K f p q,
    hypercoverCanonicalGradedIso_naturality.{w} J X K f p q]

open CochainComplex.Filtered CategoryTheory.SpectralSequence in
/-- **The functorial filtered abutment of the hypercovering spectral sequence, abutting to the
cohomology of the total complex.** -/
def hypercoverFunctorialAbutment :
    FunctorialFirstQuadrantAbutsTo (hypercoverSpectralSequenceFunctor.{w} J X K)
      (fun n => hypercoverFiltrationFunctor.{w} J X K (n : ℤ) ⋙ FilteredObject.forget) where
  filtration n := hypercoverFiltrationFunctor.{w} J X K (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite F n := (Filtration.isFinite_iff_subobject _).2
    ⟨⟨op (0 : ℤ), inducedFilteredObject_subobject_zero (hypercoverFiltered.{w} J X K F)
        (isIso_hypercoverFiltered_ι_f.{w} J X K F) (n : ℤ)⟩,
      ⟨op ((n : ℤ) + 1), inducedFilteredObject_subobject_succ
        (hypercoverFiltered.{w} J X K F)
        (isZero_hypercoverFiltered_obj_X.{w} J X K F) (n : ℤ)⟩⟩
  isTop F n := inducedFilteredObject_subobject_zero (hypercoverFiltered.{w} J X K F)
    (isIso_hypercoverFiltered_ι_f.{w} J X K F) (n : ℤ)
  isBot F n := inducedFilteredObject_subobject_succ (hypercoverFiltered.{w} J X K F)
    (isZero_hypercoverFiltered_obj_X.{w} J X K F) (n : ℤ)
  gradedIso F p q := hypercoverGradedIso.{w} J X K F p q
  gradedIso_naturality f p q := hypercoverGradedIso_naturality.{w} J X K f p q

end Abutment

/-! ### The abutment is cohomology on `X` -/

section AbutmentIsCohomology

open CochainComplex StacksDraft.DerivedSectionsComparison Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

attribute [local instance] enoughInjectives_sheafAddCommGrpCat

/-- **The augmentation of the double complex of a complex of abelian sheaves**: in outer degree
`q` the degree-zero part of `sectionsEps` at the `q`-th term.  Its target is the zeroth row of the
double complex on the nose, which is what makes the index bookkeeping of [Stacks, Tag 0133]
disappear: the inner extension by zero is already inside `hypercoverCochainIntFunctor`. -/
def sectionsAug (Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) :
    ((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶
      rowZero ((hypercoverDoubleFunctor.{w} J X K).obj Z) where
  f q := augZero ((sheafSectionsFunctor.{w} J X).obj (Z.X q))
    ((hypercoverCochainIntFunctor.{w} J X K).obj (Z.X q)) (sectionsEps J X K (Z.X q))
  comm' q q' _ := (augZero_nat (sheafSectionsFunctor.{w} J X)
    (hypercoverCochainIntFunctor.{w} J X K) (sectionsEps J X K)
    (fun {_ _} φ => sectionsEps_naturality J X K φ) (Z.d q q')).symm

/-- **The augmentation is natural in the complex of abelian sheaves.** -/
lemma sectionsAug_naturality
    {Z Z' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ} (φ : Z ⟶ Z') :
    sectionsAug J X K Z ≫ rowZeroMap ((hypercoverDoubleFunctor.{w} J X K).map φ) =
      ((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫
        sectionsAug J X K Z' := by
  refine HomologicalComplex.hom_ext _ _ fun q => ?_
  exact (augZero_nat (sheafSectionsFunctor.{w} J X) (hypercoverCochainIntFunctor.{w} J X K)
    (sectionsEps J X K) (fun {_ _} ψ => sectionsEps_naturality J X K ψ) (φ.f q)).symm

/-- **All four hypotheses of [Stacks, Tag 0133] for the double complex of a bounded below complex
of injective abelian sheaves.**  Finiteness of the antidiagonals comes from the lower bound on the
complex together with the vanishing of the sections complex in negative degrees; exactness of the
columns away from degree `0` and the degree-zero kernel clause are the two halves of
`quasiIso_sectionsEps`, i.e. of [Stacks, Tag 01GW] and [Stacks, Tag 01GV]. -/
theorem hypotheses_sectionsAug (hK : IsHypercovering J K)
    (Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ)
    (hZ : ∃ n : ℤ, Z.IsStrictlyGE n) (hinj : ∀ n : ℤ, Injective (Z.X n)) :
    Hypotheses (((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      ((hypercoverDoubleFunctor.{w} J X K).obj Z) (sectionsAug J X K Z) where
  diagonalFinite := by
    obtain ⟨n₀, hn₀⟩ := hZ
    have := hn₀
    intro n
    refine (Set.finite_Icc n₀ n).subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    refine Set.mem_Icc.2 ⟨?_, ?_⟩
    · by_contra h
      exact hp ((HomologicalComplex.eval AddCommGrpCat.{max u v w}
        (ComplexShape.up ℤ) (n - p)).map_isZero
          ((hypercoverCochainIntFunctor.{w} J X K).map_isZero
            (Z.isZero_of_isStrictlyGE n₀ p (by omega))))
    · by_contra h
      exact hp (isZero_hypercoverCochainIntFunctor_obj_X J X K (Z.X p) (n - p) (by omega))
  zero_of_neg p q hq := isZero_hypercoverCochainIntFunctor_obj_X J X K (Z.X p) q hq
  exactAt_of_ne_zero p q hq := by
    have := hinj p
    have := quasiIso_sectionsEps J X K hK (Z.X p)
    exact exactAt_of_quasiIso_single _ _ (sectionsEps J X K (Z.X p)) q hq
  inducesIsoKernel p := by
    have := hinj p
    have := quasiIso_sectionsEps J X K hK (Z.X p)
    exact ⟨augZero_comp_d _ _ _, isIso_kernelLift_augZero _ _
      (isZero_hypercoverCochainIntFunctor_obj_X J X K (Z.X p) (-1) (by omega)) _⟩

/-- The chosen injective resolution of a sheaf, extended by zero, is bounded below. -/
lemma exists_isStrictlyGE_resolutionExtend
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    ∃ n : ℤ, CochainComplex.IsStrictlyGE
      ((ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).obj
          (injectiveResolution F).cocomplex) n :=
  ⟨0, inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)⟩

/-- The terms of the chosen injective resolution, extended by zero, are injective. -/
lemma injective_resolutionExtend_X
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℤ) :
    Injective (((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).obj
        (injectiveResolution F).cocomplex).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

/-- **The hypotheses of [Stacks, Tag 0133] at the chosen injective resolution of a sheaf.** -/
theorem hypotheses_sectionsAug_resolution (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    Hypotheses (((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).obj
            (injectiveResolution F).cocomplex))
      (hypercoverDouble.{w} J X K F)
      (sectionsAug J X K ((ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).obj
          (injectiveResolution F).cocomplex)) :=
  hypotheses_sectionsAug J X K hK _ (exists_isStrictlyGE_resolutionExtend J F)
    (injective_resolutionExtend_X J F)

/-- `Γ(X, -)` applied to the chosen injective resolution of a sheaf, extended by zero. -/
abbrev sectionsResZ (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  ((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).obj
        (injectiveResolution F).cocomplex)

/-- The morphism of `Γ`-applied resolutions attached to a morphism of sheaves, via the chosen
descent to the chosen injective resolutions.  Functorial only up to homotopy. -/
def sectionsResZMap {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    sectionsResZ.{w} J X F ⟶ sectionsResZ.{w} J X G :=
  ((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).map
        (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)))

/-- A homotopy between two descents to the chosen injective resolutions induces a homotopy of the
induced morphisms of `Γ`-applied extended resolutions: sections are additive and extension by zero
carries homotopies to homotopies. -/
def sectionsResZHomotopy {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}}
    {φ ψ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex}
    (H : Homotopy φ ψ) :
    Homotopy
      (((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).map φ))
      (((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).map ψ)) :=
  (sheafSectionsFunctor.{w} J X).mapHomotopy (H.extend ComplexShape.embeddingUpNat)

/-- `sectionsResZMap` sends an identity to the identity in cohomology. -/
lemma homologyMap_sectionsResZMap_id
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (n : ℤ) :
    HomologicalComplex.homologyMap (sectionsResZMap.{w} J X (𝟙 F)) n = 𝟙 _ := by
  have h := (sectionsResZHomotopy.{w} J X
    (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).homologyMap_eq n
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id] at h
  exact h

/-- `sectionsResZMap` is multiplicative in cohomology. -/
lemma homologyMap_sectionsResZMap_comp
    {F G H : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
    HomologicalComplex.homologyMap (sectionsResZMap.{w} J X (f ≫ g)) n =
      HomologicalComplex.homologyMap (sectionsResZMap.{w} J X f) n ≫
        HomologicalComplex.homologyMap (sectionsResZMap.{w} J X g) n := by
  have h := (sectionsResZHomotopy.{w} J X
    (InjectiveResolution.descCompHomotopy f g (injectiveResolution F) (injectiveResolution G)
      (injectiveResolution H))).homologyMap_eq n
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

/-- **`H^n(Γ(X, I^•(-)))`, as a functor of the sheaf.**  The `Γ`-applied chosen resolution is
functorial only up to homotopy, but cohomology is homotopy invariant. -/
def sectionsResZHomologyFunctor (n : ℕ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w} where
  obj F := (sectionsResZ.{w} J X F).homology (n : ℤ)
  map f := HomologicalComplex.homologyMap (sectionsResZMap.{w} J X f) (n : ℤ)
  map_id F := homologyMap_sectionsResZMap_id.{w} J X F (n : ℤ)
  map_comp f g := homologyMap_sectionsResZMap_comp.{w} J X f g (n : ℤ)

/-- **[Stacks, Tag 0133] at a sheaf**: `H^n(Γ(X, I^•(F))) ≅ H^n(Tot(A^{•,•}(F)))`, the
isomorphism the comparison map `comparisonMapP` induces on cohomology. -/
def hypercoverTotalComparisonIso (hK : IsHypercovering J K) (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (sectionsResZ.{w} J X F).homology (n : ℤ) ≅
      ((hypercoverDouble.{w} J X K F).total (ComplexShape.up ℤ)).homology (n : ℤ) :=
  comparisonHomologyIso _ _ _ (hypotheses_sectionsAug_resolution J X K hK F) (n : ℤ)

/-- **`H^n(Γ(X, I^•(-))) ≅ H^n(Tot(A^{•,•}(-)))`, naturally in the sheaf.**  At each sheaf this is
`comparisonHomologyIso`, the isomorphism the comparison map of [Stacks, Tag 0133] induces on
cohomology; its naturality is `comparisonMapP_naturality` with cohomology applied to it.  Both are
available because that comparison map is *data* and not a chosen witness of an existential. -/
def hypercoverTotalComparisonNatIso (hK : IsHypercovering J K) (n : ℕ) :
    sectionsResZHomologyFunctor.{w} J X n ≅
      hypercoverFiltrationFunctor.{w} J X K (n : ℤ) ⋙ CategoryTheory.FilteredObject.forget :=
  NatIso.ofComponents (fun F => hypercoverTotalComparisonIso J X K hK n F)
    (fun {F G} f => by
      have hsq := congrArg (fun z => HomologicalComplex.homologyMap z (n : ℤ))
        (comparisonMapP_naturality _ _ _ (hypotheses_sectionsAug_resolution J X K hK F)
          (hypotheses_sectionsAug_resolution J X K hK G) (sectionsResZMap.{w} J X f)
          (hypercoverDoubleMap.{w} J X K f) (sectionsAug_naturality J X K _))
      simp only [HomologicalComplex.homologyMap_comp] at hsq
      exact hsq.symm)

/-- `Γ(X, -)` applied to the chosen injective resolution of a sheaf, indexed by `ℕ`. -/
abbrev sectionsResNat (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  ((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- The morphism of `ℕ`-indexed `Γ`-applied resolutions attached to a morphism of sheaves. -/
def sectionsResNatMap {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    sectionsResNat.{w} J X F ⟶ sectionsResNat.{w} J X G :=
  ((sheafSectionsFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- Piece (a) of the comparison: in the degrees coming from `ℕ`, the cohomology of the
`ℤ`-extension is the cohomology of the original complex. -/
def sectionsResExtendIso (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (sectionsResZ.{w} J X F).homology (n : ℤ) ≅ (sectionsResNat.{w} J X F).homology n :=
  (extendUpNatMapHomologyNatIso (sheafSectionsFunctor.{w} J X) n).app
    (injectiveResolution F).cocomplex

/-- `sectionsResExtendIso` is natural in the sheaf, for the chosen descent. -/
lemma sectionsResExtendIso_hom_naturality (n : ℕ)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    HomologicalComplex.homologyMap (sectionsResZMap.{w} J X f) (n : ℤ) ≫
        (sectionsResExtendIso.{w} J X n G).hom =
      (sectionsResExtendIso.{w} J X n F).hom ≫
        HomologicalComplex.homologyMap (sectionsResNatMap.{w} J X f) n :=
  (extendUpNatMapHomologyNatIso (sheafSectionsFunctor.{w} J X) n).hom.naturality
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- Piece (b) of the comparison: the right derived functor of sections on `X` computed by the
chosen injective resolution. -/
def sectionsResRightDerivedIso (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (sectionsResNat.{w} J X F).homology n ≅
      ((sheafSectionsFunctor.{w} J X).rightDerived n).obj F :=
  ((injectiveResolution F).isoRightDerivedObj (sheafSectionsFunctor.{w} J X) n).symm

/-- `sectionsResRightDerivedIso` is natural in the sheaf, for the chosen descent. -/
lemma sectionsResRightDerivedIso_hom_naturality (n : ℕ)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    HomologicalComplex.homologyMap (sectionsResNatMap.{w} J X f) n ≫
        (sectionsResRightDerivedIso.{w} J X n G).hom =
      (sectionsResRightDerivedIso.{w} J X n F).hom ≫
        ((sheafSectionsFunctor.{w} J X).rightDerived n).map f :=
  (InjectiveResolution.isoRightDerivedObj_inv_naturality f (injectiveResolution F)
    (injectiveResolution G) _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
      (injectiveResolution F)) (sheafSectionsFunctor.{w} J X) n).symm

/-- **`H^n(Γ(X, I^•(-))) ≅ R^nΓ(X, -)`, naturally in the sheaf.** -/
def sectionsRightDerivedNatIso (n : ℕ) :
    sectionsResZHomologyFunctor.{w} J X n ≅ (sheafSectionsFunctor.{w} J X).rightDerived n :=
  NatIso.ofComponents
    (fun F => sectionsResExtendIso.{w} J X n F ≪≫ sectionsResRightDerivedIso.{w} J X n F)
    (fun {F G} f => by
      dsimp only [sectionsResZHomologyFunctor, Iso.trans_hom]
      rw [← Category.assoc, sectionsResExtendIso_hom_naturality.{w} J X n f, Category.assoc,
        sectionsResRightDerivedIso_hom_naturality.{w} J X n f, Category.assoc])

/-- **The convergence half of the third clause of [Stacks, Tag 01GY]**: the cohomology of the
total complex, which is what `hypercoverFunctorialAbutment` abuts to, is `R^nΓ(X, -)`, naturally
in the sheaf. -/
def hypercoverAbutmentIso (hK : IsHypercovering J K) (n : ℕ) :
    hypercoverFiltrationFunctor.{w} J X K (n : ℤ) ⋙ CategoryTheory.FilteredObject.forget ≅
      (sheafSectionsFunctor.{w} J X).rightDerived n :=
  (hypercoverTotalComparisonNatIso J X K hK n).symm ≪≫ sectionsRightDerivedNatIso.{w} J X n

/-- **The functorial filtered abutment of the hypercovering spectral sequence, abutting to
cohomology on `X`.**  This is the `abutment` field of the third clause of [Stacks, Tag 01GY]:
`hypercoverFunctorialAbutment` with its abutment transported along `hypercoverAbutmentIso`. -/
def hypercoverAbutment (hK : IsHypercovering J K) :
    FunctorialFirstQuadrantAbutsTo (hypercoverSpectralSequenceFunctor.{w} J X K)
      (fun n => (sheafSectionsFunctor.{w} J X).rightDerived n) :=
  (hypercoverFunctorialAbutment.{w} J X K).ofIsoAbutment (hypercoverAbutmentIso J X K hK)

end AbutmentIsCohomology

end Stacks.CategoryTheory.Hypercovering

end
