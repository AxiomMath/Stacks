module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality

/-!
# The total complex of a double complex with acyclic rows or columns is acyclic

Let `𝒜` be an abelian category and `K^{•,•}` a double complex of `𝒜` whose total complex exists
and whose antidiagonals carry only finitely many nonzero terms.  If every column `K^{p,•}` is
acyclic, then `Tot(K^{•,•})` is acyclic; likewise if every row `K^{•,p}` is acyclic.  This is the
*acyclic assembly lemma*, the degeneration of the two spectral sequences of
[Stacks, Tag 0130] in the case where the first page already vanishes.

The route is the one [Stacks, Tag 05S3] provides.  A filtered complex whose graded pieces are all
acyclic, and whose filtration is finite in each degree, has acyclic underlying complex — this is
`CochainComplex.acyclic_of_filteredAcyclic` below, obtained from
`CochainComplex.quasiIso_hom_of_filteredQuasiIso` applied to the morphism from the trivially
filtered zero complex.  The two filtrations of the total complex,
`HomologicalComplex₂.totalFiltration₁` and `...₂`, are finite in each degree exactly when the
antidiagonals are finite (`HomologicalComplex₂.isDegreewiseFinite_totalFiltration₁` and `...₂`),
and their graded pieces have the cohomology of the columns, resp. of the rows: this is the first
page of [Stacks, Tag 0130], which `HomologicalComplex₂.exists_iso_pages_totalFiltration₁` and
`...₂` identify, composed with the generic identification of the first page of the spectral
sequence of a filtered complex with the cohomology of its graded pieces,
`FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage`.

## Main results

* `CochainComplex.acyclic_of_filteredAcyclic` — a filtered complex with degreewise finite
  filtration and acyclic graded pieces has acyclic underlying complex.
* `HomologicalComplex₂.isZero_homology_gradedPiece_totalFiltration₁` and `...₂` — the cohomology
  of the `p`-th graded piece of the first, resp. second, filtration of `Tot(K^{•,•})` vanishes
  where the cohomology of the column `K^{p,•}`, resp. of the row `K^{•,p}`, vanishes.
* `HomologicalComplex₂.acyclic_total_of_acyclic_column` — **the acyclic assembly lemma for
  columns**: a diagonally finite double complex all of whose columns are acyclic has acyclic
  total complex.
* `HomologicalComplex₂.acyclic_total_of_acyclic_row` — the same for rows.

## Why this is wanted

The proof of [Stacks, Proposition 60.21.3, Tag 07LG] runs over the double complex
`K^{a,b} = M ⊗̂_D Ω^a_{D(b)}`, of which [Stacks, Tag 07LA] says that every column with `a > 0` is
acyclic; the first of the two spectral sequences the source invokes is exactly the statement that
the total complex of the part with `a > 0` is then acyclic.  The completed clause of
[Stacks, Tag 07LD] needs the same lemma for the rows of the filtration of a completed de Rham
complex.  No tag attribute is placed here: the lemma is a degeneration of [Stacks, Tag 0130] and
is not itself the content of a tag.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Any morphism between two zero objects is an isomorphism. -/
private theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] {X Y : C} (hX : IsZero X)
    (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  ⟨hY.to_ X, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/-- A functor preserving zero morphisms sends a zero object to a zero object. -/
private theorem isZero_obj_of_isZero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {X : C}
    (h : IsZero X) : IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, (IsZero.iff_id_eq_zero _).1 h, F.map_zero]

/-- A morphism of acyclic cochain complexes is a quasi-isomorphism: in each degree both
cohomology objects vanish, so the induced map is an isomorphism. -/
private theorem quasiIso_of_acyclic_of_acyclic {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) (hL : L.Acyclic) : QuasiIso f where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_of_isZero_of_isZero ((K.exactAt_iff_isZero_homology n).1 (hK n))
      ((L.exactAt_iff_isZero_homology n).1 (hL n)) _

/-- If the first page of the spectral sequence of a filtered complex vanishes at `(p, n - p)`,
then the cohomology of `gr^p` vanishes in degree `n`. -/
private theorem isZero_homology_gr_of_isZero_page_one
    (T : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ)
    (h : ∀ (F : ℤ → ∀ n : ℤ, Subobject (T.X.X n))
      (_ : ∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
      (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n),
      IsZero (((FilteredComplexSpectralSequence.spectralSequence T.X F hanti).page 1
        zero_le_one).X (p, n - p))) :
    IsZero (((FilteredObject.gr p).obj T).homology n) := by
  set F : ℤ → ∀ n : ℤ, Subobject (T.X.X n) := fun p n =>
    CochainComplex.filtrationSubobject T p n with hFdef
  have hF (p n : ℤ) : F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n) := rfl
  have hanti := CochainComplex.antitone_of_eq T F hF
  obtain ⟨-, -, -, hgr⟩ :=
    FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage T F hF hanti
  obtain ⟨g⟩ := hgr p (n - p) n (by omega)
  exact IsZero.of_iso (h F hF hanti) g.symm

/-- **A filtered complex with degreewise finite filtration and acyclic graded pieces has acyclic
underlying complex.**

This is the second clause of [Stacks, Tag 05S3] read at the morphism from the trivially filtered
zero complex: that morphism is a filtered quasi-isomorphism precisely because every `gr^p K^•` is
acyclic, both filtrations are finite in each degree, and so the underlying morphism
`0 ⟶ K^•` is a quasi-isomorphism.  Finiteness cannot be dropped, for the reason recorded at
`CochainComplex.quasiIso_hom_of_filteredQuasiIso`. -/
public theorem acyclic_of_filteredAcyclic (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hfin : K.filtration.IsDegreewiseFinite) (hgr : CochainComplex.filteredAcyclic 𝒜 K) :
    K.X.Acyclic := by
  set Z : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ :=
    FilteredObject.ofTop (0 : CochainComplex 𝒜 ℤ) with hZdef
  have hZobj (q : ℤ) : IsZero (Z.filtration.obj (op q)) := isZero_zero _
  have hZX : IsZero Z.X := isZero_zero _
  have hZgr (p : ℤ) : IsZero ((FilteredObject.gr p).obj Z) :=
    FilteredObject.isZero_gr_obj_of_isZero Z le_rfl (hZobj p)
  have hZfin : Z.filtration.IsDegreewiseFinite := fun n =>
    ⟨0, 0, isIso_of_isZero_of_isZero
      (isZero_obj_of_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) (hZobj 0))
      (isZero_obj_of_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) hZX) _,
      isZero_obj_of_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n) (hZobj 0)⟩
  -- the unique morphism `K^• ⟶ 0` of filtered complexes
  set α : K ⟶ Z := FilteredObject.homMk (hZX.from_ K.X) (fun i => (hZobj i.unop).from_ _)
    (fun _ => hZX.eq_of_tgt _ _) with hα
  have hqi : QuasiIso α.hom :=
    CochainComplex.quasiIso_hom_of_filteredQuasiIso α (fun p =>
      quasiIso_of_acyclic_of_acyclic ((FilteredObject.gr p).map α) (hgr p)
        (fun n => ((((FilteredObject.gr p).obj Z).exactAt_iff_isZero_homology n)).2
          (isZero_obj_of_isZero
            (HomologicalComplex.homologyFunctor 𝒜 (ComplexShape.up ℤ) n) (hZgr p)))) hfin hZfin
  intro n
  rw [K.X.exactAt_iff_isZero_homology n]
  have hiso := (quasiIsoAt_iff_isIso_homologyMap α.hom n).1 (hqi.quasiIsoAt n)
  exact IsZero.of_iso
    (isZero_obj_of_isZero (HomologicalComplex.homologyFunctor 𝒜 (ComplexShape.up ℤ) n) hZX)
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap α.hom n) hiso)

end CochainComplex

namespace HomologicalComplex₂

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  (K : HomologicalComplex₂ 𝒜 (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- **The cohomology of the `p`-th graded piece of the first filtration of `Tot(K^{•,•})`
vanishes where the cohomology of the column `K^{p,•}` vanishes.**

The `p`-th graded piece of `F_I` is the `p`-th column placed in total degree, so its cohomology
in degree `n` is `H^{n - p}(K^{p,•})`.  Both identifications are read off the first page of the
spectral sequence of the filtered complex: generically by
`FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage`, and for the first filtration of
a double complex by `HomologicalComplex₂.exists_iso_pages_totalFiltration₁`. -/
public theorem isZero_homology_gradedPiece_totalFiltration₁ (p n : ℤ)
    (hzero : IsZero ((K.X p).homology (n - p))) :
    IsZero (((FilteredObject.gr p).obj K.totalFiltration₁).homology n) := by
  refine CochainComplex.isZero_homology_gr_of_isZero_page_one _ p n fun F hF hanti => ?_
  obtain ⟨-, ⟨β, -⟩, -⟩ := K.exists_iso_pages_totalFiltration₁ F hF
    (fun r p n => FilteredComplexSpectralSequence.cycles _ F r p n) (fun _ _ _ => rfl)
    (fun r p n => FilteredComplexSpectralSequence.boundaries _ F r p n) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.spectralSequence _ F hanti)
    (fun r p q n hr hn => FilteredComplexSpectralSequence.eIso _ F hanti r p q n hr hn)
    (fun r p q n _ hn => ⟨FilteredComplexSpectralSequence.deltaCycles _ F r p n,
      FilteredComplexSpectralSequence.deltaCycles_arrow _ F r p n, by
      subst hn
      rw [FilteredComplexSpectralSequence.spectralSequence_d,
        FilteredComplexSpectralSequence.eIso_inv_rfl, Category.id_comp,
        ← Category.assoc, FilteredComplexSpectralSequence.π_comp_pageMap, Category.assoc]⟩)
  exact IsZero.of_iso hzero (β p (n - p))

/-- **The cohomology of the `p`-th graded piece of the second filtration of `Tot(K^{•,•})`
vanishes where the cohomology of the row `K^{•,p}` vanishes.**

The companion of `HomologicalComplex₂.isZero_homology_gradedPiece_totalFiltration₁` for the
filtration by the second coordinate, whose `p`-th graded piece is the `p`-th row. -/
public theorem isZero_homology_gradedPiece_totalFiltration₂ (p n : ℤ)
    (hzero : IsZero ((K.homology (n - p)).X p)) :
    IsZero (((FilteredObject.gr p).obj K.totalFiltration₂).homology n) := by
  refine CochainComplex.isZero_homology_gr_of_isZero_page_one _ p n fun F hF hanti => ?_
  obtain ⟨-, ⟨β, -⟩, -⟩ := K.exists_iso_pages_totalFiltration₂ F hF
    (fun r p n => FilteredComplexSpectralSequence.cycles _ F r p n) (fun _ _ _ => rfl)
    (fun r p n => FilteredComplexSpectralSequence.boundaries _ F r p n) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.spectralSequence _ F hanti)
    (fun r p q n hr hn => FilteredComplexSpectralSequence.eIso _ F hanti r p q n hr hn)
    (fun r p q n _ hn => ⟨FilteredComplexSpectralSequence.deltaCycles _ F r p n,
      FilteredComplexSpectralSequence.deltaCycles_arrow _ F r p n, by
      subst hn
      rw [FilteredComplexSpectralSequence.spectralSequence_d,
        FilteredComplexSpectralSequence.eIso_inv_rfl, Category.id_comp,
        ← Category.assoc, FilteredComplexSpectralSequence.π_comp_pageMap, Category.assoc]⟩)
  exact IsZero.of_iso hzero (β p (n - p))

/-- **The acyclic assembly lemma, for columns.**  If every antidiagonal of the double complex
`K^{•,•}` carries only finitely many nonzero terms and every column `K^{p,•}` is acyclic, then
`Tot(K^{•,•})` is acyclic.

This is the degeneration of the first spectral sequence of [Stacks, Tag 0130]: its first page is
`H^q(K^{p,•})`, which vanishes identically, so every graded piece of the first filtration of the
total complex is acyclic and `CochainComplex.acyclic_of_filteredAcyclic` applies. -/
public theorem acyclic_total_of_acyclic_column
    (hfin : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hcol : ∀ p : ℤ, (K.X p).Acyclic) : (K.total (ComplexShape.up ℤ)).Acyclic :=
  CochainComplex.acyclic_of_filteredAcyclic K.totalFiltration₁
    (K.isDegreewiseFinite_totalFiltration₁ hfin) fun p n =>
    ((((FilteredObject.gr p).obj K.totalFiltration₁).exactAt_iff_isZero_homology n)).2
      (K.isZero_homology_gradedPiece_totalFiltration₁ p n
        (((K.X p).exactAt_iff_isZero_homology (n - p)).1 (hcol p (n - p))))

/-- **The acyclic assembly lemma, for rows.**  If every antidiagonal of the double complex
`K^{•,•}` carries only finitely many nonzero terms and every row `K^{•,p}` is acyclic, then
`Tot(K^{•,•})` is acyclic.

The companion of `HomologicalComplex₂.acyclic_total_of_acyclic_column`, through the second
spectral sequence of [Stacks, Tag 0130].  The hypothesis is phrased with
`HomologicalComplex₂.row`, the row as a cochain complex with differential `d_1`. -/
public theorem acyclic_total_of_acyclic_row
    (hfin : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hrow : ∀ p : ℤ, (K.row p).Acyclic) : (K.total (ComplexShape.up ℤ)).Acyclic :=
  CochainComplex.acyclic_of_filteredAcyclic K.totalFiltration₂
    (K.isDegreewiseFinite_totalFiltration₂ hfin) fun p n =>
    ((((FilteredObject.gr p).obj K.totalFiltration₂).exactAt_iff_isZero_homology n)).2
      (K.isZero_homology_gradedPiece_totalFiltration₂ p n
        (IsZero.of_iso (((K.row p).exactAt_iff_isZero_homology (n - p)).1 (hrow p (n - p)))
          (K.rowHomologyIso p (n - p)).symm))

end HomologicalComplex₂

end
