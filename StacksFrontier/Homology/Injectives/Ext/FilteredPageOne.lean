module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality

/-!
# The first page of the spectral sequence of a filtered complex, and filtered quasi-isomorphisms

Let `A` be an abelian category and let `f : F ⟶ G` be a morphism of filtered cochain complexes
of `A`.  The zeroth page of the spectral sequence of a filtered complex is, in bidegree `(p, q)`,
the term `(gr^pF)^{p + q}` of the `p`-th graded piece, with differential in the `q` direction the
differential of that graded piece; so the first page is the cohomology of the graded pieces, and
a morphism which is a quasi-isomorphism on every graded piece induces an isomorphism on the whole
of the first page.

These statements are about an arbitrary filtered complex of an arbitrary abelian category.  They
are used by the Ext spectral sequences of Tags 0G1X, 0G1Y, 0G1Z and 0G20 to pass from a
comparison of graded pieces, which is where the mathematical input lives, to a comparison of
spectral sequences.

## Main definitions

* `FilteredComplexSpectralSequence.zeroPageGrIso` and
  `FilteredComplexSpectralSequence.zeroPageGrIsoAt`: the identification of the zeroth page at
  `(p, q)` with the degree `p + q` term of the `p`-th graded piece, the latter with the degree as
  an argument constrained by an equation.
* `FilteredComplexSpectralSequence.zeroPageCyclesLift`: the factorization of the zeroth-page
  cycles through the corresponding filtration step.
* `FilteredComplexSpectralSequence.zeroPageScIso`: the same identification for the short complex
  around a bidegree, which is what the first page is the homology of.

## Main results

* `FilteredComplexSpectralSequence.zeroPageGrIso_naturality` and
  `FilteredComplexSpectralSequence.zeroPageGrIsoAt_naturality`: that identification is natural in
  the filtered complex.
* `FilteredComplexSpectralSequence.isIso_pageHom_one_f`: a morphism of filtered complexes which
  is a quasi-isomorphism on every graded piece is an isomorphism in every bidegree of the first
  page.
* `FilteredComplexSpectralSequence.isIso_filteredSpectralSequenceMap_hom_one`: the same
  conclusion for the induced morphism of spectral sequences on its first page.
* `FilteredComplexSpectralSequence.quasiIso_gr_map`: a morphism of filtered complexes which is a
  quasi-isomorphism on two consecutive filtration steps is a quasi-isomorphism on the graded
  piece between them.

## Implementation notes

The page objects are the subquotients `FilteredComplexSpectralSequence.pageObj` of the terms of
the underlying complex, and the degreewise filtration they are formed from is
`CochainComplex.filtrationSubobject`; both are reused rather than respelled.

The contravariant Ext spectral sequence of Tag 0G20 establishes the same first-page comparison
through declarations private to its own module; the statements here are those statements, for an
arbitrary filtered complex of an arbitrary abelian category and with no Ext groups in sight.

The identification of the zeroth page with the graded pieces is only available as an existential
statement,
`FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage`, whose first two clauses pin it
down on cycle representatives and against the differential; `zeroPageGrIso` is a chosen witness
and its naturality is proved from those two clauses.  The first-page clause of that existential
is a bare `Nonempty`, so it cannot be used for a naturality argument and is not used here.

## References

* [Stacks Project, Lemma 012O](https://stacks.math.columbia.edu/tag/012O)
* [Stacks Project, Tag 0G1Y](https://stacks.math.columbia.edu/tag/0G1Y)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory Limits Opposite

namespace FilteredComplexSpectralSequence

/-- The zeroth page of the spectral sequence of a filtered complex, in bidegree `(p, q)`, is the
degree `p + q` term of the `p`-th graded piece. -/
def zeroPageGrIso
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : CochainComplex.Filtered A) (p q : ℤ) :
    ((FilteredComplexSpectralSequence.spectralSequence F.X
      (CochainComplex.filtrationSubobject F)
      (CochainComplex.filtrationSubobject_antitone F)).page 0 le_rfl).X (p, q) ≅
      ((FilteredObject.gr p).obj F).X (p + q) := by
  let hF : ∀ i n : ℤ,
      CochainComplex.filtrationSubobject F i n =
        Subobject.mk ((F.filtration.ι.app (op i)).f n) := fun _ _ => rfl
  let h := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage F
    (CochainComplex.filtrationSubobject F) hF
    (CochainComplex.filtrationSubobject_antitone F)
  exact (Classical.choose h) p q (p + q) rfl

/-- The same identification as `zeroPageGrIso`, stated for an arbitrary index `n = p + q`. -/
def zeroPageGrIsoAt
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : CochainComplex.Filtered A) (p q n : ℤ) (hn : n = p + q) :
    ((FilteredComplexSpectralSequence.spectralSequence F.X
      (CochainComplex.filtrationSubobject F)
      (CochainComplex.filtrationSubobject_antitone F)).page 0 le_rfl).X (p, q) ≅
      ((FilteredObject.gr p).obj F).X n := by
  let hF : ∀ i n : ℤ,
      CochainComplex.filtrationSubobject F i n =
        Subobject.mk ((F.filtration.ι.app (op i)).f n) := fun _ _ => rfl
  let h := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage F
    (CochainComplex.filtrationSubobject F) hF
    (CochainComplex.filtrationSubobject_antitone F)
  exact (Classical.choose h) p q n hn

/-- The cycles of the zeroth page sit inside the corresponding filtration step. -/
def zeroPageCyclesLift
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : CochainComplex.Filtered A) (p n : ℤ) :
    ((FilteredComplexSpectralSequence.cycles F.X
      (CochainComplex.filtrationSubobject F) 0 p n : Subobject (F.X.X n)) : A) ⟶
      (F.filtration.obj (op p)).X n :=
  Subobject.ofLE _ _ (by
    change FilteredComplexSpectralSequence.cycles F.X
      (CochainComplex.filtrationSubobject F) 0 p n ≤
        CochainComplex.filtrationSubobject F p n
    rw [FilteredComplexSpectralSequence.cycles_zero_eq F
      (CochainComplex.filtrationSubobject F) (fun _ _ => rfl) p n]) ≫
      (Subobject.underlyingIso ((F.filtration.ι.app (op p)).f n)).hom

/-- The lift `zeroPageCyclesLift` composed with the inclusion of the filtration step is the
inclusion of the cycles. -/
private lemma zeroPageCyclesLift_comp_ι
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : CochainComplex.Filtered A) (p n : ℤ) :
    zeroPageCyclesLift F p n ≫ (F.filtration.ι.app (op p)).f n =
      (FilteredComplexSpectralSequence.cycles F.X
        (CochainComplex.filtrationSubobject F) 0 p n).arrow := by
  dsimp [zeroPageCyclesLift]
  rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

/-- The quotient map onto the zeroth page, followed by `zeroPageGrIso`, is the lift of the cycles
followed by the projection to the graded piece. -/
private lemma π_comp_zeroPageGrIso
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : CochainComplex.Filtered A) (p q : ℤ) :
    Limits.cokernel.π
      (FilteredComplexSpectralSequence.den F.X
        (CochainComplex.filtrationSubobject F) 0 p (p + q)) ≫
      (zeroPageGrIso F p q).hom =
      zeroPageCyclesLift F p (p + q) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom p) F).f (p + q) := by
  let hF : ∀ i n : ℤ,
      CochainComplex.filtrationSubobject F i n =
        Subobject.mk ((F.filtration.ι.app (op i)).f n) := fun _ _ => rfl
  let dF := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage F
    (CochainComplex.filtrationSubobject F) hF
    (CochainComplex.filtrationSubobject_antitone F)
  simpa [zeroPageGrIso, FilteredComplexSpectralSequence.eIso_inv_rfl] using
    (Classical.choose_spec dF).1 p q (p + q) rfl (zeroPageCyclesLift F p (p + q))
      (zeroPageCyclesLift_comp_ι F p (p + q))

/-- `zeroPageGrIso` is natural in the filtered complex. -/
lemma zeroPageGrIso_naturality
    {A : Type u} [Category.{v} A] [Abelian A]
    {F G : CochainComplex.Filtered A} (f : F ⟶ G) (p q : ℤ) :
    FilteredComplexSpectralSequence.pageObjMap f.hom
        (CochainComplex.exists_filtrationSubobject_le f) 0 p (p + q) ≫
      (zeroPageGrIso G p q).hom =
    (zeroPageGrIso F p q).hom ≫ ((FilteredObject.gr p).map f).f (p + q) := by
  have hstep : FilteredComplexSpectralSequence.cyclesMap f.hom
      (CochainComplex.exists_filtrationSubobject_le f) 0 p (p + q) ≫
      zeroPageCyclesLift G p (p + q) =
    zeroPageCyclesLift F p (p + q) ≫ (f.natTrans.app (op p)).f (p + q) := by
    apply (cancel_mono ((G.filtration.ι.app (op p)).f (p + q))).1
    have hcomm := HomologicalComplex.congr_hom (f.comm (op p)) (p + q)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hcomm
    rw [Category.assoc, zeroPageCyclesLift_comp_ι, Category.assoc, hcomm,
      FilteredComplexSpectralSequence.cyclesMap_arrow, ← zeroPageCyclesLift_comp_ι F,
      Category.assoc]
  have hgrπ := HomologicalComplex.congr_hom
    (FilteredObject.grMapπ_map (FilteredObject.succHom p) f) (p + q)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hgrπ
  apply (cancel_epi (Limits.cokernel.π
    (FilteredComplexSpectralSequence.den F.X
      (CochainComplex.filtrationSubobject F) 0 p (p + q)))).1
  rw [← Category.assoc, FilteredComplexSpectralSequence.π_pageObjMap, Category.assoc,
    π_comp_zeroPageGrIso, ← Category.assoc, hstep, ← Category.assoc,
    π_comp_zeroPageGrIso, Category.assoc, Category.assoc]
  exact congrArg _ hgrπ.symm

/-- `zeroPageGrIsoAt` is natural in the filtered complex. -/
lemma zeroPageGrIsoAt_naturality
    {A : Type u} [Category.{v} A] [Abelian A]
    {F G : CochainComplex.Filtered A} (f : F ⟶ G) (p q n : ℤ) (hn : n = p + q) :
    FilteredComplexSpectralSequence.pageObjMap f.hom
        (CochainComplex.exists_filtrationSubobject_le f) 0 p (p + q) ≫
      (zeroPageGrIsoAt G p q n hn).hom =
    (zeroPageGrIsoAt F p q n hn).hom ≫ ((FilteredObject.gr p).map f).f n := by
  subst n
  simpa [zeroPageGrIsoAt, zeroPageGrIso] using zeroPageGrIso_naturality f p q

/-- The short complex of the zeroth page around bidegree `(p, q)` is the short complex of the
`p`-th graded piece around degree `p + q`. -/
def zeroPageScIso
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : CochainComplex.Filtered A) (p q : ℤ) :
    ((FilteredComplexSpectralSequence.spectralSequence F.X
      (CochainComplex.filtrationSubobject F)
      (CochainComplex.filtrationSubobject_antitone F)).page 0 le_rfl).sc'
        (p, q - 1) (p, q) (p, q + 1) ≅
      ((FilteredObject.gr p).obj F).sc' (p + q - 1) (p + q) (p + q + 1) := by
  let hF : ∀ i n : ℤ,
      CochainComplex.filtrationSubobject F i n =
        Subobject.mk ((F.filtration.ι.app (op i)).f n) := fun _ _ => rfl
  let dF := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage F
    (CochainComplex.filtrationSubobject F) hF
    (CochainComplex.filtrationSubobject_antitone F)
  have key : ∀ (p q n q' n' : ℤ) (hn : n = p + q) (hn' : n' = p + q')
      (hq' : q' = q + 1),
      ((FilteredComplexSpectralSequence.spectralSequence F.X
        (CochainComplex.filtrationSubobject F)
        (CochainComplex.filtrationSubobject_antitone F)).page 0 le_rfl).d
          (p, q) (p, q') ≫ (zeroPageGrIsoAt F p q' n' hn').hom =
        (zeroPageGrIsoAt F p q n hn).hom ≫ ((FilteredObject.gr p).obj F).d n n' := by
    intro p q n q' n' hn hn' hq'
    subst q'
    subst n
    obtain rfl : n' = p + q + 1 := by omega
    have h := (Classical.choose_spec dF).2.1 p q (p + q) rfl
    simpa [Int.add_assoc, zeroPageGrIsoAt] using h
  have hkey₁ := key p (q - 1) (p + q - 1) q (p + q) (by omega) (by omega) (by omega)
  have hkey₂ := key p q (p + q) (q + 1) (p + q + 1) rfl (by omega) rfl
  let e₁ := zeroPageGrIsoAt F p (q - 1) (p + q - 1) (by omega)
  let e₂ := zeroPageGrIsoAt F p q (p + q) rfl
  let e₃ := zeroPageGrIsoAt F p (q + 1) (p + q + 1) (by omega)
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · dsimp [e₁, e₂, zeroPageGrIsoAt, FilteredComplexSpectralSequence.eIso_inv_rfl]
    exact hkey₁.symm
  · dsimp [e₂, e₃, zeroPageGrIsoAt, FilteredComplexSpectralSequence.eIso_inv_rfl]
    exact hkey₂.symm

/-- A morphism of filtered complexes which is a quasi-isomorphism on every graded piece is an
isomorphism in every bidegree of the first page. -/
lemma isIso_pageHom_one_f
    {A : Type u} [Category.{v} A] [Abelian A]
    {F G : CochainComplex.Filtered A} (f : F ⟶ G)
    (hf : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map f)) (p q : ℤ) :
    IsIso ((FilteredComplexSpectralSequence.pageHom f.hom
    (CochainComplex.exists_filtrationSubobject_le f) 1).f (p, q)) := by
  let hφ := CochainComplex.exists_filtrationSubobject_le f
  let hantiF := CochainComplex.filtrationSubobject_antitone F
  let hantiG := CochainComplex.filtrationSubobject_antitone G
  let pageF := FilteredComplexSpectralSequence.spectralSequence F.X
    (CochainComplex.filtrationSubobject F) hantiF
  let pageG := FilteredComplexSpectralSequence.spectralSequence G.X
    (CochainComplex.filtrationSubobject G) hantiG
  let φ₀ := FilteredComplexSpectralSequence.pageHom f.hom hφ 0
  let m₀ := (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up' ((0, 1) : ℤ × ℤ))
    (p, q - 1) (p, q) (p, q + 1)).map φ₀
  let mGr := (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ)
    (p + q - 1) (p + q) (p + q + 1)).map ((FilteredObject.gr p).map f)
  let eF := zeroPageScIso F p q
  let eG := zeroPageScIso G p q
  have hdiag : m₀ ≫ eG.hom = eF.hom ≫ mGr := by
    apply ShortComplex.hom_ext
    · dsimp only [m₀, mGr, φ₀, eF, eG, zeroPageScIso,
        HomologicalComplex.shortComplexFunctor', ShortComplex.isoMk]
      exact zeroPageGrIsoAt_naturality f p (q - 1) (p + q - 1) (by omega)
    · dsimp only [m₀, mGr, φ₀, eF, eG, zeroPageScIso,
        HomologicalComplex.shortComplexFunctor', ShortComplex.isoMk]
      exact zeroPageGrIsoAt_naturality f p q (p + q) rfl
    · dsimp only [m₀, mGr, φ₀, eF, eG, zeroPageScIso,
        HomologicalComplex.shortComplexFunctor', ShortComplex.isoMk]
      exact zeroPageGrIsoAt_naturality f p (q + 1) (p + q + 1) (by omega)
  have hgr : ShortComplex.QuasiIso mGr :=
    (quasiIsoAt_iff' _ _ _ _ (CochainComplex.prev ℤ (p + q))
      (CochainComplex.next ℤ (p + q))).1 ((hf p).quasiIsoAt (p + q))
  have hm₀ : ShortComplex.QuasiIso m₀ := by
    have : ShortComplex.QuasiIso (m₀ ≫ eG.hom) := by
      rw [hdiag]
      infer_instance
    exact ShortComplex.quasiIso_of_comp_right m₀ eG.hom
  have hp : IsIso (HomologicalComplex.homologyMap φ₀ (p, q)) := by
    have hprev : (ComplexShape.up' ((0, 1) : ℤ × ℤ)).prev (p, q) = (p, q - 1) :=
      (ComplexShape.up' (0, 1)).prev_eq' (by ext <;> simp)
    have hnext : (ComplexShape.up' ((0, 1) : ℤ × ℤ)).next (p, q) = (p, q + 1) :=
      (ComplexShape.up' (0, 1)).next_eq' (by ext <;> simp)
    have := (quasiIsoAt_iff' φ₀ _ _ _ hprev hnext).2 hm₀
    infer_instance
  have hturn := FilteredComplexSpectralSequence.homologyMap_pageHom_comp_pageHomologyIso
    f.hom hφ hantiF hantiG 0 (p, q)
  have : IsIso (HomologicalComplex.homologyMap φ₀ (p, q) ≫
      (FilteredComplexSpectralSequence.pageHomologyIso G.X
        (CochainComplex.filtrationSubobject G) hantiG 0 (p, q)).hom) := inferInstance
  have hturn' : HomologicalComplex.homologyMap φ₀ (p, q) ≫
      (FilteredComplexSpectralSequence.pageHomologyIso G.X
        (CochainComplex.filtrationSubobject G) hantiG 0 (p, q)).hom =
      (FilteredComplexSpectralSequence.pageHomologyIso F.X
          (CochainComplex.filtrationSubobject F) hantiF 0 (p, q)).hom ≫
        FilteredComplexSpectralSequence.pageObjMap f.hom hφ 1 p (p + q) := by
    simpa using hturn
  rw [hturn'] at this
  exact IsIso.of_isIso_comp_left
    (FilteredComplexSpectralSequence.pageHomologyIso F.X
      (CochainComplex.filtrationSubobject F) hantiF 0 (p, q)).hom
    (FilteredComplexSpectralSequence.pageObjMap f.hom hφ 1 p (p + q))


/-- A morphism of filtered complexes which is a quasi-isomorphism on every graded piece is an
isomorphism on the first page of the induced morphism of spectral sequences. -/
lemma isIso_filteredSpectralSequenceMap_hom_one
    {A : Type u} [Category.{v} A] [Abelian A]
    {F G : CochainComplex.Filtered A} (f : F ⟶ G)
    (hf : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map f)) :
    IsIso ((CochainComplex.filteredSpectralSequenceMap f).hom 1 (by omega)) := by
  let ψ := (CochainComplex.filteredSpectralSequenceMap f).hom 1 (show (0 : ℤ) ≤ 1 by omega)
  have hc (pq : ℤ × ℤ) : IsIso (ψ.f pq) := by
    show IsIso ((FilteredComplexSpectralSequence.pageHom f.hom
      (CochainComplex.exists_filtrationSubobject_le f) 1).f pq)
    exact isIso_pageHom_one_f f hf pq.1 pq.2
  let : ∀ pq : ℤ × ℤ, IsIso (ψ.f pq) := hc
  exact HomologicalComplex.Hom.isIso_of_components ψ

/-- A morphism of filtered complexes which is a quasi-isomorphism on two consecutive filtration
steps is a quasi-isomorphism on the graded piece between them. -/
lemma quasiIso_gr_map
    {A : Type u} [Category.{v} A] [Abelian A]
    {F G : CochainComplex.Filtered A} (f : F ⟶ G) (p : ℤ)
    (h : QuasiIso (f.natTrans.app (op p)))
    (h' : QuasiIso (f.natTrans.app (op (p + 1)))) :
    QuasiIso ((FilteredObject.gr p).map f) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (FilteredObject.stepShortComplexMap (FilteredObject.succHom p) f)
    (FilteredObject.stepShortComplex_shortExact _ F)
    (FilteredObject.stepShortComplex_shortExact _ G) h' h

end FilteredComplexSpectralSequence

end
