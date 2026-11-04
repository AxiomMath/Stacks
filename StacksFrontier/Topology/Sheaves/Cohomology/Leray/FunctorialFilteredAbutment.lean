module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexSpectralSequences
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFirstQuadrantAbutment
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbutmentOfAFilteredComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functorial filtered abutment of a functorial first-quadrant filtered complex

For a functor `G : D ⥤ CochainComplex.Filtered 𝒜` whose filtrations are all first quadrant, this
file constructs the filtration induced on `H^n(G(-)^•)` as a functor `D ⥤ Fil(𝒜)`, the
first-quadrant `E₂` spectral sequence of `G` as a functor, and the isomorphism
`E_∞^{p,q} ≅ gr^pH^{p+q}` with its naturality in the object of `D`. Together these form a
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` whose only hypotheses are `htop` and
`hbot`, the two halves of the first-quadrant condition on the filtration of `G(X)^•`.

## Main definitions

* `CochainComplex.Filtered.inducedFilteredObjectMap`: the morphism of filtered cohomologies
  induced by a morphism of filtered complexes.
* `CochainComplex.Filtered.inducedFilteredObjectFunctor`: `H^n` with its induced filtration, as a
  functor to `Fil(𝒜)`.
* `CochainComplex.Filtered.stablePage`: the page `p + q + 2`, stable at `(p, q)` for every
  first-quadrant filtered complex.
* `CochainComplex.Filtered.natE₂SequenceFunctor`: the first-quadrant `E₂` spectral sequence of a
  functorial first-quadrant filtered complex, as a functor.
* `CochainComplex.Filtered.natE₂SequenceFunctor_pageInfinityIsoGr`: the isomorphism
  `E_∞^{p,q} ≅ gr^pH^{p+q}` for that functor, at each object.
* `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex`: the
  functorial abutment to `H^n(G(-)^•)` given a graded identification and its naturality.
* `CochainComplex.Filtered.functorialFirstQuadrantAbutment`: the functorial abutment of
  `natE₂SequenceFunctor` to `H^n(G(-)^•)`.

## Main results

* `CochainComplex.Filtered.exists_inducedFiltrationStep_le`: a morphism of filtered complexes
  carries each step of the induced filtration of cohomology into the corresponding step.
* `CochainComplex.Filtered.natE₂SequenceFunctor_obj`: the value of `natE₂SequenceFunctor` at `X`
  is `CochainComplex.Filtered.natE₂SequenceOfFiltered` of `G(X)`.
* `CochainComplex.Filtered.natE₂SequenceFunctor_pageInfinityIsoGr_naturality`: the isomorphism
  `E_∞^{p,q} ≅ gr^pH^{p+q}` is natural in the object of `D`.

## References

* [Stacks Project, Tag 0121](https://stacks.math.columbia.edu/tag/0121)
* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
## References

* [Stacks Project, Tag 0121](https://stacks.math.columbia.edu/tag/0121)
* [Stacks Project, Tag 012P](https://stacks.math.columbia.edu/tag/012P)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex FilteredComplexSpectralSequence Stacks.Cohomology.Leray

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Functoriality of the filtration induced on cohomology -/

/-- The image subobject of a morphism `f` factors `f`. -/
lemma imageSubobject_factors_self {X Y : C} (f : X ⟶ Y) : (imageSubobject f).Factors f :=
  (Subobject.mk_factors_iff (image.ι f) f).2 ⟨factorThruImage f, image.fac f⟩

/-- The inclusion of the `p`-th step of the filtration of `K.inducedFilteredObject n` is the arrow
of the subobject `K.inducedFiltrationStep n p`. -/
lemma inducedFilteredObject_ι_app (K : Filtered C) (n p : ℤ) :
    (K.inducedFilteredObject n).filtration.ι.app (op p) = (K.inducedFiltrationStep n p).arrow :=
  rfl

/-- A morphism of filtered complexes carries each step of the induced filtration of cohomology into
the corresponding step: `H^n(φ)(F^pH^n(K^•)) ⊆ F^pH^n(L^•)`. -/
@[stacks 0121 "(3) for the filtrations induced on cohomology by a morphism of filtered complexes"]
lemma exists_inducedFiltrationStep_le {K L : Filtered C} (φ : K ⟶ L) (n p : ℤ) :
    (Subobject.«exists» (HomologicalComplex.homologyMap φ.hom n)).obj
        (K.inducedFiltrationStep n p) ≤ L.inducedFiltrationStep n p := by
  rw [← Subobject.imageSubobject_comp_eq_exists, ← HomologicalComplex.homologyMap_comp,
    ← FilteredObject.Hom.comm, HomologicalComplex.homologyMap_comp]
  exact imageSubobject_comp_le _ _

/-- The morphism of filtered cohomologies `H^n(K^•) ⟶ H^n(L^•)` induced by a morphism of filtered
complexes `φ`; its underlying morphism is `H^n(φ)`. -/
def inducedFilteredObjectMap {K L : Filtered C} (φ : K ⟶ L) (n : ℤ) :
    K.inducedFilteredObject n ⟶ L.inducedFilteredObject n :=
  FilteredObject.homMk' (HomologicalComplex.homologyMap φ.hom n) (fun i => by
    obtain ⟨p⟩ := i
    rw [show (L.inducedFilteredObject n).subobject (op p) = L.inducedFiltrationStep n p from
        inducedFilteredObject_subobject L n p, inducedFilteredObject_ι_app K n p]
    refine Subobject.factors_of_le
      (P := (Subobject.«exists» (HomologicalComplex.homologyMap φ.hom n)).obj
        (K.inducedFiltrationStep n p)) _ (exists_inducedFiltrationStep_le φ n p) ?_
    rw [Subobject.exists_eq_imageSubobject]
    exact imageSubobject_factors_self _)

/-- The underlying morphism of `inducedFilteredObjectMap φ n` is `H^n(φ)`. -/
@[simp]
lemma inducedFilteredObjectMap_hom {K L : Filtered C} (φ : K ⟶ L) (n : ℤ) :
    (inducedFilteredObjectMap φ n).hom = HomologicalComplex.homologyMap φ.hom n :=
  rfl

variable {D : Type*} [Category* D]

/-- The cohomology `H^n` of a functorial filtered complex, with its induced filtration, as a
functor to `Fil(𝒜)`. -/
@[stacks 012P "the induced filtration of `H^n`, functorially in the filtered complex"]
def inducedFilteredObjectFunctor (G : D ⥤ Filtered C) (n : ℤ) : D ⥤ FilteredObject C ℤᵒᵖ where
  obj X := (G.obj X).inducedFilteredObject n
  map f := inducedFilteredObjectMap (G.map f) n
  map_id X := FilteredObject.hom_ext (by
    change HomologicalComplex.homologyMap (G.map (𝟙 X)).hom n = 𝟙 _
    rw [G.map_id]
    exact HomologicalComplex.homologyMap_id _ _)
  map_comp f g := FilteredObject.hom_ext (by
    change HomologicalComplex.homologyMap (G.map (f ≫ g)).hom n = _
    rw [G.map_comp]
    exact HomologicalComplex.homologyMap_comp _ _ _)

/-! ### The spectral sequence of a functorial first-quadrant filtered complex -/

section Sequence

variable (G : D ⥤ Filtered C)
  (htop : ∀ (X : D) (n : ℤ), IsIso (((G.obj X).filtration.ι.app (op (0 : ℤ))).f n))
  (hbot : ∀ (X : D) (p n : ℤ), n < p → IsZero (((G.obj X).filtration.obj (op p)).X n))

/-- The canonical spectral sequence of a functorial filtered complex, read from the second page, as
a functor `D ⥤ E₂CohomologicalSpectralSequence 𝒜`. -/
abbrev e₂SequenceFunctorAux : D ⥤ E₂CohomologicalSpectralSequence C :=
  G ⋙ spectralSequenceFunctor ⋙
    Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 2 by omega)

/-! #### The stable page and the edge instances -/

/-- The page `p + q + 2`, which is stable at `(p, q)` for every first-quadrant filtered complex. -/
def stablePage (p q : ℕ) : ℤ := (p : ℤ) + (q : ℤ) + 2

/-- `1 ≤ stablePage p q`. -/
lemma one_le_stablePage (p q : ℕ) : 1 ≤ stablePage p q := by
  simp only [stablePage]; omega

/-- `q + 2 ≤ stablePage p q`. -/
lemma add_two_le_stablePage (p q : ℕ) : (q : ℤ) + 2 ≤ stablePage p q := by
  simp only [stablePage]; omega

/-- `p + 1 ≤ stablePage p q`. -/
lemma add_one_le_stablePage (p q : ℕ) : (p : ℤ) + 1 ≤ stablePage p q := by
  simp only [stablePage]; omega

/-- `2 ≤ stablePage p q`. -/
lemma two_le_stablePage (p q : ℕ) : (2 : ℤ) ≤ stablePage p q := by
  simp only [stablePage]; omega

/-- The first coordinate of `ComplexShape.natEmb (p, q)` is less than `stablePage p q`. -/
lemma natEmb_fst_lt_stablePage (p q : ℕ) :
    (ComplexShape.natEmb (p, q)).1 < stablePage p q := by
  simp only [ComplexShape.natEmb_fst, stablePage]; omega

/-- The second coordinate of `ComplexShape.natEmb (p, q)`, plus one, is less than
`stablePage p q`. -/
lemma natEmb_snd_add_one_lt_stablePage (p q : ℕ) :
    (ComplexShape.natEmb (p, q)).2 + 1 < stablePage p q := by
  simp only [ComplexShape.natEmb_snd, stablePage]; omega

include htop hbot

/-- At every object `X`, the spectral sequence `(e₂SequenceFunctorAux G).obj X` vanishes outside
the first quadrant. -/
lemma isFirstQuadrant_e₂SequenceFunctorAux (X : D) :
    SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      ((e₂SequenceFunctorAux G).obj X) :=
  SpectralSequence.shiftStart_isFirstQuadrant _ (by omega)
    (isFirstQuadrant_of_firstQuadrantFiltration (G.obj X) (filtrationSubobject (G.obj X))
      (fun _ _ => rfl) (cycles (G.obj X).X (filtrationSubobject (G.obj X))) (fun _ _ _ => rfl)
      (boundaries (G.obj X).X (filtrationSubobject (G.obj X))) (fun _ _ _ => rfl) _
      (fun r p' q' n' hr hn' => by subst hn'; exact pageIso (G.obj X) r p' q' hr)
      (htop X) (hbot X))

/-- The first-quadrant `E₂` spectral sequence of a functorial first-quadrant filtered complex, as a
functor: the canonical spectral sequence of `G(X)`, read from the second page and reindexed from
`ℤ × ℤ` to `ℕ × ℕ`. -/
def natE₂SequenceFunctor : D ⥤ E₂CohomologicalSpectralSequenceNat C :=
  SpectralSequence.natRestrictE₂Comp _ (isFirstQuadrant_e₂SequenceFunctorAux G htop hbot)

/-- The value of `natE₂SequenceFunctor` at `X` is
`CochainComplex.Filtered.natE₂SequenceOfFiltered` of `G(X)`, definitionally. -/
lemma natE₂SequenceFunctor_obj (X : D) :
    (natE₂SequenceFunctor G htop hbot).obj X =
      natE₂SequenceOfFiltered (G.obj X) (htop X) (hbot X) :=
  rfl

/-- At every object `X`, the canonical spectral sequence of `G(X)` vanishes outside the first
quadrant. -/
lemma isFirstQuadrant_filteredSpectralSequence (X : D) :
    SpectralSequence.IsFirstQuadrant (u := fun r => ((r, 1 - r) : ℤ × ℤ))
      (filteredSpectralSequence (G.obj X)) :=
  isFirstQuadrant_of_firstQuadrantFiltration (G.obj X) (filtrationSubobject (G.obj X))
    (fun _ _ => rfl) (cycles (G.obj X).X (filtrationSubobject (G.obj X))) (fun _ _ _ => rfl)
    (boundaries (G.obj X).X (filtrationSubobject (G.obj X))) (fun _ _ _ => rfl) _
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso (G.obj X) r p' q' hr)
    (htop X) (hbot X)

/-- The canonical spectral sequence of a first-quadrant filtered complex has an infinity page at
every bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_filteredSpectralSequence (X : D) (x : ℤ × ℤ) :
    (filteredSpectralSequence (G.obj X)).HasPageInfinityAt x :=
  SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) x

/-- The shifted canonical spectral sequence has an infinity page at every bidegree of `ℤ × ℤ`. -/
lemma hasPageInfinityAt_shiftStart (X : D) (x : ℤ × ℤ) :
    ((filteredSpectralSequence (G.obj X)).shiftStart (show (0 : ℤ) ≤ 2 by omega)).HasPageInfinityAt
      x :=
  SpectralSequence.hasPageInfinityAt_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X)) x

/-- The filtration of `G(X)` is degreewise finite. -/
lemma isDegreewiseFinite_filtration (X : D) : (G.obj X).filtration.IsDegreewiseFinite :=
  isDegreewiseFinite_of_firstQuadrant (G.obj X) (htop X) (hbot X)

/-- `stablePage p q` is a stable page at `(p, q)` for the filtration of `G(X)^•`, at every object
`X`. -/
lemma isStableFrom_stablePage (X : D) (p q : ℕ) :
    IsStableFrom (G.obj X) (filtrationSubobject (G.obj X)) (p : ℤ) (q : ℤ) (stablePage p q) :=
  isStableFrom_of_firstQuadrant (G.obj X) (htop X) (hbot X) (p : ℤ) (q : ℤ) (stablePage p q)
    (one_le_stablePage p q) (add_two_le_stablePage p q) (add_one_le_stablePage p q)

/-- The differentials of the shifted and reindexed canonical spectral sequence of `G(X)` into
`(p, q)` vanish from the page `stablePage p q` on. -/
lemma hasEdgeMonoAtFrom_natRestrict (X : D) (p q : ℕ) :
    (((filteredSpectralSequence (G.obj X)).shiftStart (show (0 : ℤ) ≤ 2 by omega)).natRestrict
        (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
          (isFirstQuadrant_filteredSpectralSequence G htop hbot X))).HasEdgeMonoAtFrom (p, q)
      (stablePage p q) :=
  CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ (p, q) (stablePage p q)
    (add_one_le_stablePage p q) (two_le_stablePage p q)

/-- The differentials of the shifted and reindexed canonical spectral sequence of `G(X)` out of
`(p, q)` vanish from the page `stablePage p q` on. -/
lemma hasEdgeEpiAtFrom_natRestrict (X : D) (p q : ℕ) :
    (((filteredSpectralSequence (G.obj X)).shiftStart (show (0 : ℤ) ≤ 2 by omega)).natRestrict
        (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
          (isFirstQuadrant_filteredSpectralSequence G htop hbot X))).HasEdgeEpiAtFrom (p, q)
      (stablePage p q) :=
  CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ (p, q) (stablePage p q)
    (add_two_le_stablePage p q) (two_le_stablePage p q)

/-! #### The convergence identification and its naturality -/

/-- The infinity page of `natE₂SequenceFunctor` at `(p, q)` is isomorphic to the infinity page of
the canonical spectral sequence of `G(X)` at `ComplexShape.natEmb (p, q)`, both read at the page
`stablePage p q`. -/
def natE₂SequenceFunctor_pageInfinityIso (X : D) (p q : ℕ) :
    ((natE₂SequenceFunctor G htop hbot).obj X).pageInfinity (p, q) ≅
      (filteredSpectralSequence (G.obj X)).pageInfinity (ComplexShape.natEmb (p, q)) :=
  haveI := hasPageInfinityAt_filteredSpectralSequence G htop hbot X (ComplexShape.natEmb (p, q))
  haveI := hasPageInfinityAt_shiftStart G htop hbot X (ComplexShape.natEmb (p, q))
  haveI := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (natEmb_fst_lt_stablePage p q)
  haveI := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)
  haveI := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_fst_lt_stablePage p q)
  haveI := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)
  haveI := hasEdgeMonoAtFrom_natRestrict G htop hbot X p q
  haveI := hasEdgeEpiAtFrom_natRestrict G htop hbot X p q
  SpectralSequence.shiftNatRestrict_pageInfinityIsoAt (show (0 : ℤ) ≤ 2 by omega)
    (SpectralSequence.shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X)) (p, q) (stablePage p q)

/-- The isomorphism `natE₂SequenceFunctor_pageInfinityIso` is natural in the object of `D`. -/
theorem natE₂SequenceFunctor_pageInfinityIso_naturality {X Y : D} (φ : X ⟶ Y) (p q : ℕ) :
    SpectralSequence.Hom.mapPageInfinity ((natE₂SequenceFunctor G htop hbot).map φ) (p, q) ≫
        (natE₂SequenceFunctor_pageInfinityIso G htop hbot Y p q).hom =
      (natE₂SequenceFunctor_pageInfinityIso G htop hbot X p q).hom ≫
        SpectralSequence.Hom.mapPageInfinity (filteredSpectralSequenceMap (G.map φ))
          (ComplexShape.natEmb (p, q)) := by
  have := hasPageInfinityAt_filteredSpectralSequence G htop hbot X (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_filteredSpectralSequence G htop hbot Y (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_shiftStart G htop hbot X (ComplexShape.natEmb (p, q))
  have := hasPageInfinityAt_shiftStart G htop hbot Y (ComplexShape.natEmb (p, q))
  have := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (natEmb_fst_lt_stablePage p q)
  have := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)
  have := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot Y) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (natEmb_fst_lt_stablePage p q)
  have := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot Y) (ComplexShape.natEmb (p, q))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (natEmb_snd_add_one_lt_stablePage p q)
  have := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_fst_lt_stablePage p q)
  have := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)
  have := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot Y)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_fst_lt_stablePage p q)
  have := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (SpectralSequence.shiftStart_isFirstQuadrant _ (show (0 : ℤ) ≤ 2 by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot Y)) (ComplexShape.natEmb (p, q))
    (stablePage p q) (two_le_stablePage p q) (natEmb_snd_add_one_lt_stablePage p q)
  have := hasEdgeMonoAtFrom_natRestrict G htop hbot X p q
  have := hasEdgeEpiAtFrom_natRestrict G htop hbot X p q
  have := hasEdgeMonoAtFrom_natRestrict G htop hbot Y p q
  have := hasEdgeEpiAtFrom_natRestrict G htop hbot Y p q
  exact SpectralSequence.shiftNatRestrict_pageInfinityIsoAt_naturality
    (show (0 : ℤ) ≤ 2 by omega)
    (SpectralSequence.shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot X))
    (SpectralSequence.shiftStart_isFirstQuadrant _ (by omega)
      (isFirstQuadrant_filteredSpectralSequence G htop hbot Y))
    (filteredSpectralSequenceMap (G.map φ)) (p, q) (stablePage p q) (two_le_stablePage p q)

/-- The isomorphism `E_∞^{p,q} ≅ gr^pH^{p+q}(G(X)^•)` for the canonical spectral sequence of
`G(X)`, read at the page `stablePage p q`. -/
def canonicalGradedIso (X : D) (p q : ℕ) :
    (filteredSpectralSequence (G.obj X)).pageInfinity (ComplexShape.natEmb (p, q)) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((inducedFilteredObjectFunctor G ((p + q : ℕ) : ℤ)).obj X) :=
  haveI := hasPageInfinityAt_filteredSpectralSequence G htop hbot X ((p : ℤ), (q : ℤ))
  haveI := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)
  haveI := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)
  canonicalPageInfinityIsoGr (G.obj X) (isDegreewiseFinite_filtration G htop hbot X)
    (p : ℤ) (q : ℤ) (stablePage p q) (isStableFrom_stablePage G htop hbot X p q)

/-- The isomorphism `canonicalGradedIso` is natural in the object of `D`. -/
theorem canonicalGradedIso_naturality {X Y : D} (φ : X ⟶ Y) (p q : ℕ) :
    SpectralSequence.Hom.mapPageInfinity (filteredSpectralSequenceMap (G.map φ))
          (ComplexShape.natEmb (p, q)) ≫ (canonicalGradedIso G htop hbot Y p q).hom =
      (canonicalGradedIso G htop hbot X p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((inducedFilteredObjectFunctor G ((p + q : ℕ) : ℤ)).map φ) := by
  have := hasPageInfinityAt_filteredSpectralSequence G htop hbot X ((p : ℤ), (q : ℤ))
  have := hasPageInfinityAt_filteredSpectralSequence G htop hbot Y ((p : ℤ), (q : ℤ))
  have := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)
  have := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot X) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)
  have := SpectralSequence.hasEdgeMonoAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot Y) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega) (add_one_le_stablePage p q)
  have := SpectralSequence.hasEdgeEpiAtFrom_of_isFirstQuadrant _
    (isFirstQuadrant_filteredSpectralSequence G htop hbot Y) ((p : ℤ), (q : ℤ))
    (stablePage p q) (by have := two_le_stablePage p q; omega)
    (by have := add_two_le_stablePage p q; omega)
  exact canonicalPageInfinityIsoGr_naturality (G.map φ)
    (isDegreewiseFinite_filtration G htop hbot X) (isDegreewiseFinite_filtration G htop hbot Y)
    (p : ℤ) (q : ℤ) (stablePage p q) (isStableFrom_stablePage G htop hbot X p q)
    (isStableFrom_stablePage G htop hbot Y p q)
    (inducedFilteredObjectMap (G.map φ) ((p + q : ℕ) : ℤ)) rfl

/-- The isomorphism `E_∞^{p,q} ≅ gr^pH^{p+q}(G(X)^•)` for `natE₂SequenceFunctor`, at each object
`X`: the composite of `natE₂SequenceFunctor_pageInfinityIso` and `canonicalGradedIso`. -/
@[sga "4 Vbis 2.5.2" "partial"]
def natE₂SequenceFunctor_pageInfinityIsoGr (X : D) (p q : ℕ) :
    ((natE₂SequenceFunctor G htop hbot).obj X).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((inducedFilteredObjectFunctor G ((p + q : ℕ) : ℤ)).obj X) :=
  natE₂SequenceFunctor_pageInfinityIso G htop hbot X p q ≪≫
    canonicalGradedIso G htop hbot X p q

/-- The isomorphism `natE₂SequenceFunctor_pageInfinityIsoGr` is natural in the object of `D`. -/
theorem natE₂SequenceFunctor_pageInfinityIsoGr_naturality {X Y : D} (φ : X ⟶ Y) (p q : ℕ) :
    SpectralSequence.Hom.mapPageInfinity ((natE₂SequenceFunctor G htop hbot).map φ) (p, q) ≫
        (natE₂SequenceFunctor_pageInfinityIsoGr G htop hbot Y p q).hom =
      (natE₂SequenceFunctor_pageInfinityIsoGr G htop hbot X p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map
          ((inducedFilteredObjectFunctor G ((p + q : ℕ) : ℤ)).map φ) := by
  rw [natE₂SequenceFunctor_pageInfinityIsoGr, natE₂SequenceFunctor_pageInfinityIsoGr,
    Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
    natE₂SequenceFunctor_pageInfinityIso_naturality, Category.assoc,
    canonicalGradedIso_naturality, ← Category.assoc]

end Sequence

end CochainComplex.Filtered

namespace Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category* D]

/-- A functorial filtered abutment of `E` to the cohomology `H^n(G(-)^•)` of a functorial
first-quadrant filtered complex `G`, given an isomorphism `gradedIso` of the infinity pages of `E`
with the graded pieces of the filtration induced on `H^{p+q}(G(-)^•)` and its naturality `hnat`.
The filtration is `CochainComplex.Filtered.inducedFilteredObjectFunctor G` and the abutment
isomorphism is the identity. -/
def FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex
    (G : D ⥤ CochainComplex.Filtered C)
    (htop : ∀ (X : D) (n : ℤ), IsIso (((G.obj X).filtration.ι.app (op (0 : ℤ))).f n))
    (hbot : ∀ (X : D) (p n : ℤ), n < p → IsZero (((G.obj X).filtration.obj (op p)).X n))
    (E : D ⥤ E₂CohomologicalSpectralSequenceNat C)
    (gradedIso : ∀ (X : D) (p q : ℕ), (E.obj X).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj
        ((CochainComplex.Filtered.inducedFilteredObjectFunctor G ((p + q : ℕ) : ℤ)).obj X))
    (hnat : ∀ {X Y : D} (φ : X ⟶ Y) (p q : ℕ),
      SpectralSequence.Hom.mapPageInfinity (E.map φ) (p, q) ≫ (gradedIso Y p q).hom =
        (gradedIso X p q).hom ≫ (FilteredObject.gr (p : ℤ)).map
          ((CochainComplex.Filtered.inducedFilteredObjectFunctor G ((p + q : ℕ) : ℤ)).map φ)) :
    FunctorialFirstQuadrantAbutsTo E
      (fun n => G ⋙ FilteredObject.forget ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)) where
  filtration n := CochainComplex.Filtered.inducedFilteredObjectFunctor G (n : ℤ)
  abutmentIso _ := Iso.refl _
  isFinite X n := (Filtration.isFinite_iff_subobject _).2
    ⟨⟨op (0 : ℤ),
      CochainComplex.Filtered.inducedFilteredObject_subobject_zero (G.obj X) (htop X) (n : ℤ)⟩,
      ⟨op ((n : ℤ) + 1),
        CochainComplex.Filtered.inducedFilteredObject_subobject_succ (G.obj X) (hbot X) (n : ℤ)⟩⟩
  isTop X n :=
    CochainComplex.Filtered.inducedFilteredObject_subobject_zero (G.obj X) (htop X) (n : ℤ)
  isBot X n :=
    CochainComplex.Filtered.inducedFilteredObject_subobject_succ (G.obj X) (hbot X) (n : ℤ)
  gradedIso X p q := gradedIso X p q
  gradedIso_naturality φ p q := hnat φ p q

end Stacks.Cohomology.Leray

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category* D]

/-- The functorial filtered abutment of `natE₂SequenceFunctor G htop hbot` to the cohomology
`H^n(G(-)^•)` of a functorial filtered complex `G`. Its only hypotheses are `htop` and `hbot`: the
filtration of each `G(X)^•` is the whole complex at the index `0`, and `F^p G(X)^n = 0` for
`n < p`. -/
def functorialFirstQuadrantAbutment (G : D ⥤ Filtered C)
    (htop : ∀ (X : D) (n : ℤ), IsIso (((G.obj X).filtration.ι.app (op (0 : ℤ))).f n))
    (hbot : ∀ (X : D) (p n : ℤ), n < p → IsZero (((G.obj X).filtration.obj (op p)).X n)) :
    FunctorialFirstQuadrantAbutsTo (natE₂SequenceFunctor G htop hbot)
      (fun n => G ⋙ FilteredObject.forget ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)) :=
  FunctorialFirstQuadrantAbutsTo.ofFunctorialFilteredComplex G htop hbot _
    (natE₂SequenceFunctor_pageInfinityIsoGr G htop hbot)
    (fun φ p q => natE₂SequenceFunctor_pageInfinityIsoGr_naturality G htop hbot φ p q)

end CochainComplex.Filtered

end
