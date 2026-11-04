module

import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Homology.Ext.DerivedCoyoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# The hyper-Ext spectral sequences of a complex

Let `M` be an object of an abelian category. For a bounded below cochain complex `K`, the Ext
groups from `M` to the terms of `K` form the first page of a spectral sequence converging to the
Ext groups from `M` to the derived object represented by `K`. For a bounded below derived object
`K`, the Ext groups from `M` to the cohomology objects of `K` form the second page of a spectral
sequence converging to the Ext groups from `M` to `K`.

## Main results

* `StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence`: the spectral sequence
  with `E₁ⁱʲ = Extʲ(M, Kⁱ)` and its finite filtration on the abutment.
* `StacksDraft.ExtSpectralSequence.exists_ext_homology_spectralSequence`: the spectral sequence
  with `E₂ⁱʲ = Extⁱ(M, Hʲ(K))` and its finite filtration on the abutment.

## Implementation notes

The `E₁` spectral sequence is produced from the spectral object obtained by applying derived Hom
out of `M` to the tower of stupid truncations `σ^{≥ -i} K`. Its first page is expressed using
Mathlib's cohomological spectral-sequence type, beginning on page `1`. Convergence is recorded by
a finite decreasing filtration of each abutment group: in every bidegree, all sufficiently late
pages are identified with the corresponding associated graded piece, and both the incoming and
outgoing differentials vanish.

The `E₂` spectral sequence is the second spectral sequence of the double complex `Hom(M, I)`, for
`I` a Cartan-Eilenberg resolution ([Stacks, Tag 015I]) of a bounded below complex of injective
objects representing `K`; its pages are identified by [Stacks, Tag 0130] and its second page is
rewritten with [Stacks, Tag 015J] and
`StacksDraft.DerivedCoyoneda.rightDerivedSmallCoyonedaIso`. As in [Stacks, Tag 0132] and
[Stacks, Tag 015N], "converging to `H^*(K)`" means that the spectral sequence is presented as
that of a filtered complex whose cohomology is the abutment: the pages are the quotients
`Z_r^{p,q}/D_r^{p,q}` of [Stacks, Tag 012M], and boundedness, finiteness of the induced
filtration `F^pH^n` and convergence (`d_r = 0` for `r ≫ 0` and the equalities (012S) and (012T)
for the stable cycles and boundaries, which by [Stacks, Tag 012V] say exactly that `E_∞^{p,q}` is
the graded piece `gr^pH^n`) are properties of that presentation. The filtered complex is
`Tot(Hom(M, I))` and its cohomology is identified with `Extⁿ(M, K)` in each degree.

## References

* [Stacks Project, Tag 0AVH](https://stacks.math.columbia.edu/tag/0AVH)
* [Stacks Project, Tag 0AVI](https://stacks.math.columbia.edu/tag/0AVI)
-/


open CategoryTheory CategoryTheory.Limits

open HomologicalComplex StacksDraft.StupidTruncation

attribute [local instance] mono_ιStupidTrunc

namespace StacksDraft.ExtSpectralSequence

universe u v w

/-- The indexing of the spectral sequence of a decreasing filtration, starting at `E₁`. -/
@[expose] public def spectralSequenceDataCoreE₁ :
    Abelian.SpectralObject.SpectralSequenceDataCore ℤ
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq _ := -pq.1 - r
  i₁ pq := -pq.1 - 1
  i₂ pq := -pq.1
  i₃ r pq _ := -pq.1 + r - 1
  le₀₁ r pq hr := by omega
  le₁₂ pq := by omega
  le₂₃ r pq hr := by omega
  hc := by rintro r pq _ rfl _; dsimp; omega
  hc₀₂ := by rintro r pq _ rfl _; dsimp; omega
  hc₁₃ := by rintro r pq _ rfl _; dsimp; omega
  antitone_i₀ r r' pq hr hrr' := by omega
  monotone_i₃ r r' pq hr hrr' := by omega
  i₀_prev := by rintro r r' pq _ rfl hrr' _; dsimp; omega
  i₃_next := by rintro r r' pq _ rfl hrr' _; dsimp; omega

/-- `spectralSequenceDataCoreE₁`, under its original file-local name. -/
private def coreE₁Cohomological :
    Abelian.SpectralObject.SpectralSequenceDataCore ℤ
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 :=
  spectralSequenceDataCoreE₁

/-- Every spectral object indexed by `ℤ` has the spectral sequence of
`StacksDraft.ExtSpectralSequence.spectralSequenceDataCoreE₁`: the vanishing conditions are vacuous
because the indexing shape has no boundary. -/
public theorem hasSpectralSequence_spectralSequenceDataCoreE₁
    {A : Type*} [Category* A] [Abelian A] (X : Abelian.SpectralObject A ℤ) :
    X.HasSpectralSequence spectralSequenceDataCoreE₁ where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := (hpq _ rfl).elim
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := (hpq (pq - (r, 1 - r)) (by simp)).elim

/-- `hasSpectralSequence_spectralSequenceDataCoreE₁`, under its original file-local name. -/
private theorem hasSpectralSequence_coreE₁Cohomological
    {A : Type*} [Category* A] [Abelian A] (X : Abelian.SpectralObject A ℤ) :
    X.HasSpectralSequence coreE₁Cohomological :=
  hasSpectralSequence_spectralSequenceDataCoreE₁ X

/-- The first page of `StacksDraft.ExtSpectralSequence.spectralSequenceDataCoreE₁` is computed by
the arrow `i₁ pq ≤ i₂ pq`. -/
public theorem hasFirstPageComputation_spectralSequenceDataCoreE₁ :
    spectralSequenceDataCoreE₁.HasFirstPageComputation where
  hi₀₁ pq := rfl
  hi₂₃ pq := by dsimp [spectralSequenceDataCoreE₁]; omega

/-- `hasFirstPageComputation_spectralSequenceDataCoreE₁`, under its original file-local name. -/
private theorem hasFirstPageComputation_coreE₁Cohomological :
    coreE₁Cohomological.HasFirstPageComputation :=
  hasFirstPageComputation_spectralSequenceDataCoreE₁

attribute [local instance] hasSpectralSequence_spectralSequenceDataCoreE₁
  hasFirstPageComputation_spectralSequenceDataCoreE₁

/-- **Derived `Hom` out of `M` applied to a tower of complexes, as a spectral object.** The
tower is turned into a spectral object of the homotopy category by the mapping-cone spectral
object, pushed to the derived category, and composed with the homological functor
`Hom(M, -)`. -/
public noncomputable abbrev extSpectralObjectOfTower
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (F : ℤ ⥤ CochainComplex C ℤ) :
    Abelian.SpectralObject AddCommGrpCat.{w} ℤ :=
  (((HomotopyCategory.spectralObjectMappingCone C).precomp F).mapTriangulatedFunctor
    DerivedCategory.Qh).mapHomologicalFunctor (preadditiveCoyoneda.obj (Opposite.op M))

/-- `extSpectralObjectOfTower`, under its original file-local name. -/
private noncomputable abbrev towerExtSpectralObject
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (F : ℤ ⥤ CochainComplex C ℤ) :
    Abelian.SpectralObject AddCommGrpCat.{w} ℤ :=
  extSpectralObjectOfTower M F

/-- Derived Hom applied to a tower gives a cohomological spectral sequence. -/
@[expose] public noncomputable def extSpectralSequenceOfTower
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (F : ℤ ⥤ CochainComplex C ℤ) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  (extSpectralObjectOfTower M F).spectralSequence spectralSequenceDataCoreE₁

/-- `extSpectralSequenceOfTower`, under its original file-local name. -/
private noncomputable def towerExtSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (F : ℤ ⥤ CochainComplex C ℤ) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  extSpectralSequenceOfTower M F

/-- The first page is the derived Hom of successive mapping cones in the tower. -/
private noncomputable def towerExtSpectralSequenceFirstPageIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (F : ℤ ⥤ CochainComplex C ℤ) (p q : ℤ) :
    ((towerExtSpectralSequence M F).page 1).X (p, q) ≅
      AddCommGrpCat.of (DerivedCategory.Ext M
        (DerivedCategory.Q.obj
          (CochainComplex.mappingCone (F.map (homOfLE (show -p - 1 ≤ -p by omega)))))
        (p + q)) :=
  (extSpectralObjectOfTower M F).spectralSequenceFirstPageXIso spectralSequenceDataCoreE₁
      (p, q) (-p - 1) (-p) rfl rfl (p + q) rfl ≪≫
    ((preadditiveCoyoneda.obj (Opposite.op M)).shift (p + q)).mapIso
      ((DerivedCategory.quotientCompQhIso C).app _)

section FirstPage

open HomologicalComplex
open ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def stupidTruncGEConeIso [HasDerivedCategory.{w} C] (p : ℤ) :
    DerivedCategory.Q.obj
        (CochainComplex.mappingCone (stupidTruncGEMapLE K (show p ≤ p + 1 by omega))) ≅
      (DerivedCategory.singleFunctor C p).obj (K.X p) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex
    (stupidTruncGEShortComplex_shortExact K p)
  exact asIso (DerivedCategory.Q.map
    (CochainComplex.mappingCone.descShortComplex (stupidTruncGEShortComplex K p)))

private noncomputable def extSingleIso [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (N : C) (p q : ℤ) :
    AddCommGrpCat.of (DerivedCategory.Ext M ((DerivedCategory.singleFunctor C p).obj N)
      (p + q)) ≅
    AddCommGrpCat.of (DerivedCategory.Ext M ((DerivedCategory.singleFunctor C 0).obj N) q) :=
  (preadditiveCoyoneda.obj (Opposite.op M)).mapIso
    ((shiftFunctorAdd (DerivedCategory C) p q).app _ ≪≫
      (shiftFunctor (DerivedCategory C) q).mapIso
        (((DerivedCategory.singleFunctors C).shiftIso p 0 p (by omega)).app N))

/-- **The hyper-`Ext` spectral sequence of a complex**: the spectral sequence of the tower of
stupid truncations of `K` under derived `Hom` out of `M`. This is the spectral sequence
`StacksDraft.ExtSpectralSequence.exists_ext_complex_spectralSequence` produces. -/
@[expose] public noncomputable def hyperExtSpectralSequence [HasDerivedCategory.{w} C]
    (M : C) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  extSpectralSequenceOfTower ((DerivedCategory.singleFunctor C 0).obj M) (stupidTruncTower K)

/-- `hyperExtSpectralSequence`, under its original file-local name. -/
private noncomputable def extComplexSpectralSequence [HasDerivedCategory.{w} C] (M : C) :
    CohomologicalSpectralSequence AddCommGrpCat.{w} 1 :=
  hyperExtSpectralSequence K M

private noncomputable def extComplexSpectralSequenceFirstPageIso
    [HasDerivedCategory.{w} C] (M : C) (p q : ℤ) :
    ((extComplexSpectralSequence K M).page 1).X (p, q) ≅
      AddCommGrpCat.of (Abelian.zExt M (K.X p) q) := by
  let A := (DerivedCategory.singleFunctor C 0).obj M
  have hcone (a b : ℤ) (hab : a ≤ b) (ha : a = p) (hb : b = p + 1) :
      DerivedCategory.Q.obj (CochainComplex.mappingCone (stupidTruncGEMapLE K hab)) =
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        (stupidTruncGEMapLE K (show p ≤ p + 1 by omega))) := by
    subst a b
    rfl
  exact towerExtSpectralSequenceFirstPageIso A (stupidTruncTower K) p q ≪≫
    ((preadditiveCoyoneda.obj (Opposite.op A)).shift (p + q)).mapIso
      (eqToIso (hcone (-(-p)) (-(-p - 1)) (by omega) (by omega) (by omega)) ≪≫
        stupidTruncGEConeIso K p) ≪≫ extSingleIso A (K.X p) p q

end FirstPage

section AbutmentFiltration

set_option backward.isDefEq.respectTransparency false

open HomologicalComplex
open ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private lemma isZero_ext_of_isLE_of_isGE (M N : DerivedCategory C) (a b n : ℤ)
    [M.IsLE a] [N.IsGE b] (h : n + a < b) :
    IsZero (AddCommGrpCat.of (DerivedCategory.Ext M N n)) := by
  have := DerivedCategory.TStructure.t.isGE_shift N b n (b - n) (by omega)
  have : Subsingleton (DerivedCategory.Ext M N n) :=
    subsingleton_of_forall_eq 0 (fun f ↦
      DerivedCategory.TStructure.t.zero f a (b - n) (by omega))
  exact AddCommGrpCat.isZero_of_subsingleton _

omit [HasDerivedCategory.{w} C] in
private lemma isIso_ιStupidTrunc (K : CochainComplex C ℤ) (p : ℤ) [K.IsStrictlyGE p] :
    IsIso (ιStupidTrunc K (embeddingUpIntGE p)) := by
  have : ∀ n, IsIso ((ιStupidTrunc K (embeddingUpIntGE p)).f n) := by
    intro n
    by_cases hn : p ≤ n
    · rw [ιStupidTruncGE_f K p n hn]
      infer_instance
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE p)) p n
          (by omega)) (K.isZero_of_isStrictlyGE p n (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The filtration on derived Hom induced by the inclusions of stupid truncations. -/
@[expose] public noncomputable def hyperExtFiltration (K : CochainComplex C ℤ) (M : C)
    (p n : ℤ) :
    Subobject (AddCommGrpCat.of (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor C 0).obj M) (DerivedCategory.Q.obj K) n)) :=
  imageSubobject ((preadditiveCoyoneda.obj
    (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))).map
      ((DerivedCategory.Q.map (ιStupidTrunc K (embeddingUpIntGE p)))⟦n⟧'))

/-- `hyperExtFiltration`, under its original file-local name. -/
private noncomputable def extComplexFiltration (K : CochainComplex C ℤ) (M : C) (p n : ℤ) :
    Subobject (AddCommGrpCat.of (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor C 0).obj M) (DerivedCategory.Q.obj K) n)) :=
  hyperExtFiltration K M p n

/-- The filtration `StacksDraft.ExtSpectralSequence.hyperExtFiltration` is decreasing in the
filtration index: the inclusion `σ^{≥p'}K ⟶ σ^{≥p}K` for `p ≤ p'` factors the one of `σ^{≥p'}K`
through the one of `σ^{≥p}K`. -/
public lemma hyperExtFiltration_antitone (K : CochainComplex C ℤ) (M : C) (n : ℤ) :
    Antitone (fun p => hyperExtFiltration K M p n) := by
  intro p p' h
  let F := DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory C) n ⋙
    preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))
  change imageSubobject (F.map (ιStupidTrunc K (embeddingUpIntGE p'))) ≤
    imageSubobject (F.map (ιStupidTrunc K (embeddingUpIntGE p)))
  apply imageSubobject_le _ (F.map (stupidTruncGEMapLE K h) ≫
    factorThruImageSubobject (F.map (ιStupidTrunc K (embeddingUpIntGE p))))
  rw [Category.assoc, imageSubobject_arrow_comp, ← F.map_comp, stupidTruncGEMapLE_ι]

/-- `hyperExtFiltration_antitone`, under its original file-local name. -/
private lemma extComplexFiltration_antitone (K : CochainComplex C ℤ) (M : C) (n : ℤ) :
    Antitone (fun p => extComplexFiltration K M p n) :=
  hyperExtFiltration_antitone K M n

private lemma extComplexFiltration_eq_top (K : CochainComplex C ℤ) (M : C) (p n : ℤ)
    [K.IsStrictlyGE p] : extComplexFiltration K M p n = ⊤ := by
  have := isIso_ιStupidTrunc K p
  dsimp only [extComplexFiltration, hyperExtFiltration]
  rw [imageSubobject_mono, Subobject.mk_eq_top_of_isIso]

private lemma extComplexFiltration_eq_bot (K : CochainComplex C ℤ) (M : C) (p n : ℤ)
    (h : n < p) : extComplexFiltration K M p n = ⊥ := by
  have hzero := isZero_ext_of_isLE_of_isGE ((DerivedCategory.singleFunctor C 0).obj M)
    (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE p))) 0 p n (by omega)
  dsimp only [extComplexFiltration, hyperExtFiltration]
  have heq := hzero.eq_of_src ((preadditiveCoyoneda.obj
    (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))).map
      ((DerivedCategory.Q.map (ιStupidTrunc K (embeddingUpIntGE p)))⟦n⟧')) 0
  simpa only [heq] using (imageSubobject_zero (A := AddCommGrpCat.of (DerivedCategory.Ext
    ((DerivedCategory.singleFunctor C 0).obj M)
    (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE p))) n))
    (B := AddCommGrpCat.of (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor C 0).obj M) (DerivedCategory.Q.obj K) n)))

/-- For a bounded below complex the filtration
`StacksDraft.ExtSpectralSequence.hyperExtFiltration` of each abutment group is finite: it is
everything below the bound and zero above the degree. -/
public lemma hyperExtFiltration_finite (K : CochainComplex C ℤ) (M : C)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) (n : ℤ) :
    ∃ a b : ℤ, a ≤ b ∧ hyperExtFiltration K M a n = ⊤ ∧
      hyperExtFiltration K M b n = ⊥ := by
  obtain ⟨a, ha⟩ := hK
  exact ⟨a, max a (n + 1), le_max_left _ _, extComplexFiltration_eq_top K M a n,
    extComplexFiltration_eq_bot K M _ n (by omega)⟩

/-- `hyperExtFiltration_finite`, under its original file-local name. -/
private lemma extComplexFiltration_finite (K : CochainComplex C ℤ) (M : C)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) (n : ℤ) :
    ∃ a b : ℤ, a ≤ b ∧ extComplexFiltration K M a n = ⊤ ∧
      extComplexFiltration K M b n = ⊥ :=
  hyperExtFiltration_finite K M hK n

end AbutmentFiltration

section Stabilization


variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℤ) (M : C)

private lemma extComplexSpectralSequence_isZero_of_firstPage
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (h : IsZero (((extComplexSpectralSequence K M).page 1).X (p, q))) :
    IsZero (((extComplexSpectralSequence K M).page r hr).X (p, q)) := by
  let X := extSpectralObjectOfTower ((DerivedCategory.singleFunctor C 0).obj M)
    (stupidTruncTower K)
  exact X.isZero_spectralSequence_page_X_of_isZero_H' spectralSequenceDataCoreE₁ r hr (p, q)
    (h.of_iso (X.spectralSequenceFirstPageXIso spectralSequenceDataCoreE₁
      (p, q) _ _ rfl rfl _ rfl).symm)

private lemma extComplexSpectralSequence_isZero_of_lt (a : ℤ) [K.IsStrictlyGE a]
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (h : p < a ∨ q < 0) :
    IsZero (((extComplexSpectralSequence K M).page r hr).X (p, q)) := by
  apply extComplexSpectralSequence_isZero_of_firstPage
  refine IsZero.of_iso ?_ (extComplexSpectralSequenceFirstPageIso K M p q)
  rcases h with hp | hq
  · exact ((preadditiveCoyoneda.obj
      (Opposite.op ((DerivedCategory.singleFunctor C 0).obj M))).shift q).map_isZero
        ((DerivedCategory.singleFunctor C 0).map_isZero (K.isZero_of_isStrictlyGE a p hp))
  · exact isZero_ext_of_isLE_of_isGE ((DerivedCategory.singleFunctor C 0).obj M)
      ((DerivedCategory.singleFunctor C 0).obj (K.X p)) 0 0 q (by omega)

/-- For a bounded below complex the differentials into and out of a fixed bidegree of
`StacksDraft.ExtSpectralSequence.hyperExtSpectralSequence` vanish from some page on, both
source and target of a late differential lying outside the region where the first page can be
nonzero. -/
public lemma hyperExtSpectralSequence_eventually_d_eq_zero
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) (p q : ℤ) :
    ∃ r₀ : ℤ, 1 ≤ r₀ ∧ ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
      ((hyperExtSpectralSequence K M).page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
      ((hyperExtSpectralSequence K M).page r hr).d (p - r, q + r - 1) (p, q) = 0 := by
  obtain ⟨a, ha⟩ := hK
  refine ⟨max 1 (max (q + 2) (p - a + 1)), le_max_left _ _, ?_⟩
  intro r hr hbound
  constructor
  · exact (extComplexSpectralSequence_isZero_of_lt K M a r hr (p + r) (q + 1 - r)
      (Or.inr (by omega))).eq_of_tgt _ _
  · exact (extComplexSpectralSequence_isZero_of_lt K M a r hr (p - r) (q + r - 1)
      (Or.inl (by omega))).eq_of_src _ _

/-- `hyperExtSpectralSequence_eventually_d_eq_zero`, under its original file-local name. -/
private lemma extComplexSpectralSequence_eventually_d_eq_zero
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) (p q : ℤ) :
    ∃ r₀ : ℤ, 1 ≤ r₀ ∧ ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
      ((extComplexSpectralSequence K M).page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
      ((extComplexSpectralSequence K M).page r hr).d (p - r, q + r - 1) (p, q) = 0 :=
  hyperExtSpectralSequence_eventually_d_eq_zero K M hK p q

end Stabilization

private lemma isZero_cokernel_ofLE_of_eq
    {A : Type*} [Category* A] [Abelian A] {X : A}
    (P Q : Subobject X) (h : P ≤ Q) (heq : P = Q) :
    IsZero (cokernel (Subobject.ofLE P Q h)) := by
  subst Q
  rw [Subobject.ofLE_refl]
  exact isZero_cokernel_of_epi _

section ImageQuotient

set_option backward.isDefEq.respectTransparency false

open ComposableArrows

/-- An epimorphic presentation of a subquotient identifies its cokernel with the quotient
of the two image subobjects. -/
private noncomputable def cokernelIsoImageQuotient
    {A : Type*} [Category* A] [Abelian A]
    {U V T O : A} (a : U ⟶ T) (b : V ⟶ T) (h : imageSubobject a ≤ imageSubobject b)
    (e : V ⟶ O) [Epi e] (m : O ⟶ T) [Mono m] (he : e ≫ m = b)
    (f : U ⟶ O) (hf : f ≫ m = a) :
    cokernel f ≅ cokernel (Subobject.ofLE (imageSubobject a) (imageSubobject b) h) := by
  have := strongEpi_of_epi e
  let i : O ≅ (imageSubobject b : A) :=
    image.isoStrongEpiMono e m he ≪≫ (imageSubobjectIso b).symm
  have hi : i.hom ≫ (imageSubobject b).arrow = m := by simp [i]
  have hfi : f ≫ i.hom = factorThruImageSubobject a ≫
      Subobject.ofLE (imageSubobject a) (imageSubobject b) h := by
    apply (cancel_mono (imageSubobject b).arrow).1
    simp only [Category.assoc, hi, hf, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  exact cokernel.mapIso f _ (Iso.refl _) i (by simpa using hfi) ≪≫
    cokernelEpiComp (factorThruImageSubobject a) (Subobject.ofLE _ _ h)

/-- A spectral-object page is the quotient of the images of the two middle terms,
whenever cone inclusions identify those terms with their cohomology. -/
private noncomputable def spectralObjectPageIsoImageQuotient
    {A I : Type*} [Category* A] [Abelian A] [Category* I]
    (X : Abelian.SpectralObject A I) {i j k l : I}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (f₁₂₃ : i ⟶ l) (h₁₂₃ : f₁₂ ≫ f₃ = f₁₂₃) (n : ℤ)
    {U V T : A} (a : U ⟶ T) (b : V ⟶ T)
    (h : imageSubobject a ≤ imageSubobject b)
    (eA : U ⟶ (X.H n).obj (mk₁ f₁)) [Epi eA]
    (eB : V ⟶ (X.H n).obj (mk₁ f₁₂)) [Epi eB]
    (t : (X.H n).obj (mk₁ f₁₂₃) ⟶ T) [IsIso t]
    (ha : eA ≫ (X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫
      (X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃) ≫ t = a)
    (hb : eB ≫ (X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃) ≫ t = b) :
    X.E f₁ f₂ f₃ (n - 1) n (n + 1) ≅
      cokernel (Subobject.ofLE (imageSubobject a) (imageSubobject b) h) := by
  let S := X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ (n - 1) n (n + 1)
  let m := X.fromOpcycles f₁₂ f₃ f₁₂₃ h₁₂₃ n ≫ t
  have hm : Mono m := by dsimp [m]; infer_instance
  have he : (eB ≫ X.pOpcycles f₁₂ f₃ n) ≫ m = b := by
    simpa [m, Category.assoc] using hb
  have hf : (eA ≫ S.f) ≫ m = a := by
    simpa [S, m, Category.assoc] using ha
  have hS := X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ (n - 1) n (n + 1)
  exact hS.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel S.f) ≪≫
    (cokernelEpiComp eA S.f).symm ≪≫
    cokernelIsoImageQuotient a b h (eB ≫ X.pOpcycles f₁₂ f₃ n) m he (eA ≫ S.f) hf

end ImageQuotient

section ConeComparison

set_option backward.isDefEq.respectTransparency false

open ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private noncomputable abbrev complexExtFunctor (M : DerivedCategory C) (n : ℤ) :
    CochainComplex C ℤ ⥤ AddCommGrpCat.{w} :=
  DerivedCategory.Q ⋙ (preadditiveCoyoneda.obj (Opposite.op M)).shift n

/-- The cone inclusion, with the canonical comparison between the two localization functors. -/
private noncomputable def towerExtInr (M : DerivedCategory C)
    (F : ℤ ⥤ CochainComplex C ℤ) {i j : ℤ} (f : i ⟶ j) (n : ℤ) :
    (complexExtFunctor M n).obj (F.obj j) ⟶
      ((towerExtSpectralObject M F).H n).obj (mk₁ f) :=
  (complexExtFunctor M n).map (CochainComplex.mappingCone.inr (F.map f)) ≫
    ((preadditiveCoyoneda.obj (Opposite.op M)).shift n).map
      ((DerivedCategory.quotientCompQhIso C).inv.app _)

private lemma towerExtInr_naturality (M : DerivedCategory C)
    (F : ℤ ⥤ CochainComplex C ℤ) {i j i' j' : ℤ} (f : i ⟶ j) (g : i' ⟶ j')
    (α : mk₁ f ⟶ mk₁ g) (n : ℤ) :
    towerExtInr M F f n ≫ ((towerExtSpectralObject M F).H n).map α =
      (complexExtFunctor M n).map (F.map (α.app 1)) ≫ towerExtInr M F g n := by
  let G := (preadditiveCoyoneda.obj (Opposite.op M)).shift n
  change (G.map (DerivedCategory.Q.map _) ≫ G.map _) ≫ G.map _ =
    G.map (DerivedCategory.Q.map _) ≫ G.map (DerivedCategory.Q.map _) ≫ G.map _
  simp only [← G.map_comp, Category.assoc]
  congr 1
  change DerivedCategory.Q.map _ ≫ (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
    (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      (CochainComplex.mappingCone.map (F.map f) (F.map g) (F.map (α.app 0))
        (F.map (α.app 1)) (by rw [← F.map_comp, ← F.map_comp]; congr 1)) = _
  rw [← (DerivedCategory.quotientCompQhIso C).inv.naturality]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  congr 2
  simp [CochainComplex.mappingCone.map]

private lemma isIso_map_mappingCone_inr (M : DerivedCategory C)
    {L N : CochainComplex C ℤ} (f : L ⟶ N) (n : ℤ)
    (h₀ : IsZero ((complexExtFunctor M n).obj L))
    (h₁ : IsZero ((complexExtFunctor M (n + 1)).obj L)) :
    IsIso ((complexExtFunctor M n).map (CochainComplex.mappingCone.inr f)) := by
  let G := preadditiveCoyoneda.obj (Opposite.op M)
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have hT := DerivedCategory.mappingCone_triangle_distinguished f
  have : Mono ((G.shift n).map T.mor₂) :=
    (G.homologySequence_mono_shift_map_mor₂_iff T hT n).2 (h₀.eq_of_src _ _)
  have : Epi ((G.shift n).map T.mor₂) :=
    (G.homologySequence_epi_shift_map_mor₂_iff T hT n (n + 1) rfl).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((G.shift n).map T.mor₂)

private lemma isIso_towerExtInr (M : DerivedCategory C)
    (F : ℤ ⥤ CochainComplex C ℤ) {i j : ℤ} (f : i ⟶ j) (n : ℤ)
    (h₀ : IsZero ((complexExtFunctor M n).obj (F.obj i)))
    (h₁ : IsZero ((complexExtFunctor M (n + 1)).obj (F.obj i))) :
    IsIso (towerExtInr M F f n) := by
  have := isIso_map_mappingCone_inr M (F.map f) n h₀ h₁
  dsimp only [towerExtInr]
  infer_instance

end ConeComparison

section Convergence

set_option backward.isDefEq.respectTransparency false

open ComposableArrows ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℤ) (M : C)

/-- Once the extreme truncations are invisible in degree `n`, the page is the corresponding
quotient of the image filtration. -/
private noncomputable def extComplexPageIsoFiltration
    (i j k l : ℤ) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (n : ℤ) (hn : n + 1 < -i) [K.IsStrictlyGE (-l)] :
    (towerExtSpectralObject ((DerivedCategory.singleFunctor C 0).obj M)
      (stupidTruncTower K)).E (homOfLE hij) (homOfLE hjk) (homOfLE hkl)
        (n - 1) n (n + 1) ≅
      cokernel (Subobject.ofLE (extComplexFiltration K M (-j) n)
        (extComplexFiltration K M (-k) n)
        (extComplexFiltration_antitone K M n (by omega))) := by
  let D := (DerivedCategory.singleFunctor C 0).obj M
  let F := stupidTruncTower K
  let X := extSpectralObjectOfTower D F
  let H := complexExtFunctor D n
  have : (DerivedCategory.Q.obj (F.obj i)).IsGE (-i) := by
    change (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE (-i)))).IsGE (-i)
    infer_instance
  have h₀ : IsZero ((complexExtFunctor D n).obj (F.obj i)) :=
    isZero_ext_of_isLE_of_isGE D (DerivedCategory.Q.obj (F.obj i)) 0 (-i) n (by omega)
  have h₁ : IsZero ((complexExtFunctor D (n + 1)).obj (F.obj i)) :=
    isZero_ext_of_isLE_of_isGE D (DerivedCategory.Q.obj (F.obj i)) 0 (-i) (n + 1) (by omega)
  have hInr (s : ℤ) (his : i ≤ s) : IsIso (towerExtInr D F (homOfLE his) n) :=
    isIso_towerExtInr D F _ n h₀ h₁
  have hι := isIso_ιStupidTrunc K (-l)
  let t : (X.H n).obj (mk₁ (homOfLE (hij.trans (hjk.trans hkl)))) ⟶ H.obj K :=
    inv (towerExtInr D F (homOfLE (hij.trans (hjk.trans hkl))) n) ≫
      H.map (ιStupidTrunc K (embeddingUpIntGE (-l)))
  have ht : IsIso t := by dsimp [t]; infer_instance
  have hfac (s : ℤ) (his : i ≤ s) (hsl : s ≤ l) :
      towerExtInr D F (homOfLE his) n ≫
        (X.H n).map (twoδ₂Toδ₁ (homOfLE his) (homOfLE hsl)
          (homOfLE (hij.trans (hjk.trans hkl))) (Subsingleton.elim _ _)) ≫ t =
        H.map (ιStupidTrunc K (embeddingUpIntGE (-s))) := by
    rw [← Category.assoc, towerExtInr_naturality]
    dsimp only [t]
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
    change H.map (stupidTruncGEMapLE K (neg_le_neg hsl)) ≫
      H.map (ιStupidTrunc K (embeddingUpIntGE (-l))) = _
    rw [← H.map_comp, stupidTruncGEMapLE_ι]
  refine spectralObjectPageIsoImageQuotient X (homOfLE hij) (homOfLE hjk) (homOfLE hkl)
    (homOfLE (hij.trans hjk)) (Subsingleton.elim _ _)
    (homOfLE (hij.trans (hjk.trans hkl))) (Subsingleton.elim _ _) n
    (H.map (ιStupidTrunc K (embeddingUpIntGE (-j))))
    (H.map (ιStupidTrunc K (embeddingUpIntGE (-k))))
    (hyperExtFiltration_antitone K M n (by omega))
    (towerExtInr D F (homOfLE hij) n)
    (towerExtInr D F (homOfLE (hij.trans hjk)) n) t ?_ (hfac k (hij.trans hjk) hkl)
  rw [← Category.assoc, ← Category.assoc, towerExtInr_naturality, Category.assoc, Category.assoc,
    hfac k (hij.trans hjk) hkl]
  change H.map (stupidTruncGEMapLE K (neg_le_neg hjk)) ≫
    H.map (ιStupidTrunc K (embeddingUpIntGE (-k))) = _
  rw [← H.map_comp, stupidTruncGEMapLE_ι]

/-- **A late page of the hyper-`Ext` spectral sequence is a graded piece of the abutment
filtration.** Once the page index `r` is large enough that the extreme truncations are invisible
in the relevant degree, the term in bidegree `(p, q)` is the quotient of `Fil^p` by `Fil^{p+1}`
in degree `p + q`. -/
public noncomputable def hyperExtSpectralSequencePageIsoFiltration
    (a : ℤ) [K.IsStrictlyGE a] (p q r : ℤ) (hr : 1 ≤ r)
    (hhigh : q + 2 ≤ r) (hlow : p - a + 1 ≤ r) :
    ((hyperExtSpectralSequence K M).page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE (hyperExtFiltration K M (p + 1) (p + q))
        (hyperExtFiltration K M p (p + q))
        (hyperExtFiltration_antitone K M (p + q) (by omega))) := by
  have := CochainComplex.isStrictlyGE_of_ge K (-(-p + r - 1)) a (by omega)
  let X := extSpectralObjectOfTower ((DerivedCategory.singleFunctor C 0).obj M)
    (stupidTruncTower K)
  refine X.spectralSequencePageXIso spectralSequenceDataCoreE₁ r hr (p, q)
    (-p - r) (-p - 1) (-p) (-p + r - 1) rfl rfl rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl ≪≫ ?_
  convert extComplexPageIsoFiltration K M (-p - r) (-p - 1) (-p) (-p + r - 1)
      (by omega) (by omega) (by omega) (p + q) (by omega) using 1
  have heq (j k : ℤ) (hjk : k ≤ j) (hj : j = p + 1) (hk : k = p) :
      cokernel (Subobject.ofLE (hyperExtFiltration K M j (p + q))
        (hyperExtFiltration K M k (p + q)) (hyperExtFiltration_antitone K M _ hjk)) =
      cokernel (Subobject.ofLE (hyperExtFiltration K M (p + 1) (p + q))
        (hyperExtFiltration K M p (p + q))
        (hyperExtFiltration_antitone K M _ (by omega))) := by
    subst j k
    rfl
  exact (heq _ _ (by omega) (by omega) (by omega)).symm

/-- `hyperExtSpectralSequencePageIsoFiltration`, under its original file-local name. -/
private noncomputable def extComplexSpectralSequencePageIsoFiltration
    (a : ℤ) [K.IsStrictlyGE a] (p q r : ℤ) (hr : 1 ≤ r)
    (hhigh : q + 2 ≤ r) (hlow : p - a + 1 ≤ r) :
    ((extComplexSpectralSequence K M).page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE (extComplexFiltration K M (p + 1) (p + q))
        (extComplexFiltration K M p (p + q))
        (extComplexFiltration_antitone K M (p + q) (by omega))) :=
  hyperExtSpectralSequencePageIsoFiltration K M a p q r hr hhigh hlow

end Convergence

/-- **Stacks 0AVI.** If a bounded below complex `K` represents an object of the bounded below
derived category, there is a cohomological spectral sequence
`E₁ⁱʲ = Extʲ(M, Kⁱ)` abutting to `Extⁱ⁺ʲ(M, K)`. -/
@[stacks 0AVI]
public theorem exists_ext_complex_spectralSequence
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] (M : C) (K : CochainComplex C ℤ)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{w} 1)
      (_e₁ : ∀ i j : ℤ, (E.page 1).X (i, j) ≅
        AddCommGrpCat.of (Abelian.zExt.{u, v, w} M (K.X i) j))
      (G : ∀ _p n : ℤ, Subobject
        (AddCommGrpCat.of
          (DerivedCategory.Ext.{u, v, w}
            ((DerivedCategory.singleFunctor.{w, v, u} C 0).obj M)
            (DerivedCategory.Q.obj K) n)))
      (hG : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ G a n = ⊤ ∧ G b n = ⊥) ∧
      ∀ p q : ℤ, ∃ r₀ : ℤ, 1 ≤ r₀ ∧ ∀ (r : ℤ) (hr : 1 ≤ r), r₀ ≤ r →
        (E.page r hr).d (p, q) (p + r, q + 1 - r) = 0 ∧
        (E.page r hr).d (p - r, q + r - 1) (p, q) = 0 ∧
        Nonempty ((E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE (G (p + 1) (p + q)) (G p (p + q))
            (hG p (p + 1) (p + q) (by omega)))) := by
  refine ⟨hyperExtSpectralSequence K M, extComplexSpectralSequenceFirstPageIso K M,
    hyperExtFiltration K M, fun _ _ n h => hyperExtFiltration_antitone K M n h,
    hyperExtFiltration_finite K M hK, ?_⟩
  obtain ⟨a, ha⟩ := hK
  intro p q
  obtain ⟨r₁, hr₁, hd⟩ := hyperExtSpectralSequence_eventually_d_eq_zero K M ⟨a, ha⟩ p q
  refine ⟨max r₁ (max (q + 2) (p - a + 1)), by omega, ?_⟩
  intro r hr hbound
  exact ⟨(hd r hr (by omega)).1, (hd r hr (by omega)).2,
    ⟨hyperExtSpectralSequencePageIsoFiltration K M a p q r hr (by omega) (by omega)⟩⟩

section HomologyPage

open Opposite StacksDraft.DerivedCoyoneda

/-- For `M` in an abelian category with enough injectives and `K` in its bounded below derived
category, there is a filtered complex `T` of abelian groups with `Hⁿ(T) ≅ Extⁿ(M, K)` for all `n`,
whose spectral sequence `E`, presented as in [Stacks, Tag 012M] by its pages `Z_r^{p,q}/D_r^{p,q}`,
has `E₂ⁱʲ ≅ Extⁱ(M, Hʲ(K))`, is bounded, induces a finite filtration on each `Hⁿ(T)`, and
converges to `H^*(T)`.

This is the filtered-object-idiom helper, universally quantified over the filtration, cycle,
boundary and induced-filtration data `Fil`, `Z`, `D`, `FH` of [Stacks, Tag 012M]; it is **not**
the `0AVH` endpoint. The endpoint is
`StacksDraft.ExtSpectralSequence.exists_ext_homology_spectralSequence`, which produces that data
instead of quantifying over it, identifies `E₂` with `Ext` through the canonical page-`2`
subquotient, records that the differentials are induced by `d`, and adds the page-index vanishing
of [Stacks, Tag 0AVH]. On the `Fil`, `Z`, `D`, `FH` axis alone the two would be equivalent, since
each of those four is uniquely determined by the equation required of it; the endpoint is stronger
in the three conjuncts the statement below does not have. -/
public theorem exists_ext_homology_spectralSequence_of_data
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] (M : C) (K : DerivedCategory.Plus C) :
    ∃ T : FilteredObject (CochainComplex AddCommGrpCat.{w} ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (T.X.homology n ≅
        AddCommGrpCat.of (DerivedCategory.Ext.{u, v, w}
          ((DerivedCategory.singleFunctor.{w, v, u} C 0).obj M)
          (DerivedCategory.Plus.ι.{w, v, u}.obj K) n))) ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (T.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (T.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{w} 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ i j : ℤ, Nonempty ((E.page 2 zero_le_two).X (i, j) ≅
          AddCommGrpCat.of (Abelian.zExt.{u, v, w} M
            ((DerivedCategory.homologyFunctor.{w, v, u} C j).obj
              (DerivedCategory.Plus.ι.{w, v, u}.obj K)) i))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (T.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (T.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) := by
  classical
  let := HasDerivedCategory.standard AddCommGrpCat.{w}
  -- a bounded below complex `L` of injective objects representing `K`
  obtain ⟨b, hb⟩ := K.property
  have : K.IsGE b := (K.isGE_ι_obj_iff b).1 hb
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := K.exists_injective_nonempty_iso b
  let L := (InjectiveObject.ι C).mapCochainComplexPlus.obj J
  have : L.obj.IsStrictlyGE b :=
    inferInstanceAs
      (CochainComplex.IsStrictlyGE
        (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj J.obj) b)
  -- a Cartan-Eilenberg resolution of `L`, and the double complex `Hom(M, I)`
  obtain ⟨I, hI⟩ := CochainComplex.exists_cartanEilenbergResolution L.obj b
  have := hI
  let F := smallCoyoneda.{u, v, w} M
  let B : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((F.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj I.bicomplex
  have hq : ∀ p q, q < 0 → IsZero ((B.X p).X q) := fun p q hq =>
    F.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q hq)
  have hp : ∀ p, p < b → IsZero (B.X p) := fun p hp =>
    (F.mapHomologicalComplex (.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex b p hp)
  have hfin := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded B b hq hp
  have : B.HasTotal (ComplexShape.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded B b hq hp
  obtain ⟨-, h2, h3⟩ := I.exists_homologyIso_rightDerivedPlus F L.property
  -- `Hʲ(L) ≅ Hʲ(K)`
  have eH : ∀ q : ℤ, L.obj.homology q ≅
      (DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Plus.ι.obj K) :=
    fun q => ((DerivedCategory.homologyFunctorFactors C q).app L.obj).symm ≪≫
      (DerivedCategory.homologyFunctor C q).mapIso (DerivedCategory.Plus.ι.mapIso eJ)
  refine ⟨B.totalFiltration₂, fun n => ?_, fun Fil hFil Z hZ D hD FH hFH => ?_⟩
  · obtain ⟨e⟩ := h3 n
    exact ⟨e ≪≫ (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{w} n).mapIso
      (F.rightDerivedFunctorPlus.mapIso eJ) ≪≫ rightDerivedSmallCoyonedaHomologyIso M K n⟩
  · obtain ⟨E, e, -, hδ, -, -, -⟩ :=
      CochainComplex.exists_cohomologicalSpectralSequence B.totalFiltration₂ Fil hFil Z hZ D hD
    obtain ⟨-, -, hE2⟩ := B.exists_iso_pages_totalFiltration₂ Fil hFil Z hZ D hD E e hδ
    obtain ⟨c₁, c₂, c₃, c₄, -⟩ :=
      B.isBounded_and_converges_totalFiltration₂ hfin Fil hFil Z hZ D hD FH hFH E e
    refine ⟨E, e, fun i j => ?_, c₁, c₂, c₃, c₄⟩
    obtain ⟨e₂⟩ := hE2 i j
    obtain ⟨e₂'⟩ := h2 i j
    exact ⟨e₂ ≪≫ e₂' ≪≫ (F.rightDerivedPlus i).mapIso (eH j) ≪≫
      rightDerivedSmallCoyonedaIso M _ i⟩

/-- **Stacks 0AVH.** For `M` in an abelian category with enough injectives and `K` in its bounded
below derived category, there is a filtered complex `T` of abelian groups, together with the
filtration, cycle, boundary and induced-filtration data `Fil`, `Z`, `D`, `FH` of
[Stacks, Tag 012M], a spectral sequence `E` whose page at `(r, p, q)` is identified with the
canonical subquotient `Z_r^{p,q}/(D_r^{p,q} ⊓ Z_r^{p,q})` and whose differential is induced by the
differential of `T`, and isomorphisms `Hⁿ(T) ≅ Extⁿ(M, K)` and `E₂ⁱʲ ≅ Extⁱ(M, Hʲ(K))`, the latter
factoring through the canonical page-`2` subquotient. The spectral sequence is bounded, the
filtration it induces on each `Hⁿ(T)` is finite, it converges to `H^*(T)` (the differentials
vanish for `r ≫ 0` and the inclusions (012S) and (012T) for the stable cycles and boundaries are
equalities, which by [Stacks, Tag 012V] says exactly that `E_∞^{p,q}` is the graded piece
`gr^pHⁿ(T)`), and on each total-degree diagonal every page vanishes outside a finite range of
columns, so the spectral sequence degenerates there.

`T` is `Tot(Hom(M, I))` for `I` a Cartan-Eilenberg resolution ([Stacks, Tag 015I]) of a bounded
below complex of injective objects representing `K`, filtered by the second coordinate; the pages
are identified by [Stacks, Tag 0130] and the second page is rewritten with [Stacks, Tag 015J] and
`StacksDraft.DerivedCoyoneda.rightDerivedSmallCoyonedaIso`. The column vanishing is deduced from
the finiteness of the diagonals of the zeroth page, which propagates to every later page because
each page object is the homology of the previous one
(`CategoryTheory.SpectralSequence.isZero_page_of_le`); it does not involve the stable cycles.

This is the `0AVH` endpoint; `exists_ext_homology_spectralSequence_of_data` is the same statement
with `Fil`, `Z`, `D`, `FH` universally quantified, with the `e₂`/`filteredE₂Iso` compatibility,
the differential compatibility and the column-vanishing conjuncts dropped, and with `E₂`
identified with `Ext` by an isomorphism not tied to the canonical subquotient. -/
@[stacks 0AVH]
public theorem exists_ext_homology_spectralSequence
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] (M : C) (K : DerivedCategory.Plus C) :
    ∃ (T : FilteredObject (CochainComplex AddCommGrpCat.{w} ℤ) ℤᵒᵖ)
      (Fil : ∀ (_p n : ℤ), Subobject (T.X.X n))
      (_hFil : ∀ p n : ℤ, Fil p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
      (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
      (_hZ : ∀ r p n : ℤ, Z r p n =
        Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
      (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
      (_hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
        (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
      (FH : ∀ (n _p : ℤ), Subobject (T.X.homology n))
      (_hFH : ∀ n p : ℤ, FH n p =
        imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
      (E : CohomologicalSpectralSequence AddCommGrpCat.{w} 0)
      (pageIso : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
      (filteredE₂Iso : ∀ i j : ℤ,
        cokernel (Subobject.ofLE _ _
            (inf_le_right : D 2 i (i + j) ⊓ Z 2 i (i + j) ≤ Z 2 i (i + j))) ≅
          AddCommGrpCat.of (Abelian.zExt.{u, v, w} M
            ((DerivedCategory.homologyFunctor.{w, v, u} C j).obj
              (DerivedCategory.Plus.ι.{w, v, u}.obj K)) i))
      (e₂ : ∀ i j : ℤ, (E.page 2 zero_le_two).X (i, j) ≅
        AddCommGrpCat.of (Abelian.zExt.{u, v, w} M
          ((DerivedCategory.homologyFunctor.{w, v, u} C j).obj
            (DerivedCategory.Plus.ι.{w, v, u}.obj K)) i))
      (_abutmentIso : ∀ n : ℤ, T.X.homology n ≅
        AddCommGrpCat.of (DerivedCategory.Ext.{u, v, w}
          ((DerivedCategory.singleFunctor.{w, v, u} C 0).obj M)
          (DerivedCategory.Plus.ι.{w, v, u}.obj K) n)),
      (∀ i j : ℤ, (e₂ i j).hom =
        (pageIso 2 i j (i + j) zero_le_two rfl).hom ≫ (filteredE₂Iso i j).hom) ∧
      (∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
        ∃ δ : (Z r p n : AddCommGrpCat.{w}) ⟶ (Z r (p + r) (n + 1) : AddCommGrpCat.{w}),
          δ ≫ (Z r (p + r) (n + 1)).arrow = (Z r p n).arrow ≫ T.X.d n (n + 1) ∧
          cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
              (pageIso r p q n hr hn).inv ≫ (E.page r hr).d (p, q) (p + r, q - r + 1) =
            δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
                D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
              (pageIso r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) ∧
      (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0 le_rfl).X (p, n - p))}.Finite) ∧
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
      (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
        (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
      (∀ p n : ℤ,
        IsGLB (Set.range fun r : ℕ =>
            Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
              Fil (p + 1) n)
          (kernelSubobject (T.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
        IsLUB (Set.range fun r : ℕ =>
            Fil p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
              Fil (p + 1) n)
          (imageSubobject (T.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) ∧
      ∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧
        ∀ (r i j : ℤ) (hr : 0 ≤ r), i + j = n → (i < a ∨ b < i) →
          IsZero ((E.page r hr).X (i, j)) := by
  classical
  let := HasDerivedCategory.standard AddCommGrpCat.{w}
  -- a bounded below complex `L` of injective objects representing `K`
  obtain ⟨b, hb⟩ := K.property
  have : K.IsGE b := (K.isGE_ι_obj_iff b).1 hb
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := K.exists_injective_nonempty_iso b
  let L := (InjectiveObject.ι C).mapCochainComplexPlus.obj J
  have : L.obj.IsStrictlyGE b :=
    inferInstanceAs
      (CochainComplex.IsStrictlyGE
        (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj J.obj) b)
  -- a Cartan-Eilenberg resolution of `L`, and the double complex `Hom(M, I)`
  obtain ⟨I, hI⟩ := CochainComplex.exists_cartanEilenbergResolution L.obj b
  have := hI
  let F := smallCoyoneda.{u, v, w} M
  let B : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
    ((F.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj I.bicomplex
  have hq : ∀ p q, q < 0 → IsZero ((B.X p).X q) := fun p q hq =>
    F.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X p) 0 q hq)
  have hp : ∀ p, p < b → IsZero (B.X p) := fun p hp =>
    (F.mapHomologicalComplex (.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex b p hp)
  have hfin := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded B b hq hp
  have : B.HasTotal (ComplexShape.up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded B b hq hp
  obtain ⟨-, h2, h3⟩ := I.exists_homologyIso_rightDerivedPlus F L.property
  -- `Hʲ(L) ≅ Hʲ(K)`
  have eH : ∀ q : ℤ, L.obj.homology q ≅
      (DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Plus.ι.obj K) :=
    fun q => ((DerivedCategory.homologyFunctorFactors C q).app L.obj).symm ≪≫
      (DerivedCategory.homologyFunctor C q).mapIso (DerivedCategory.Plus.ι.mapIso eJ)
  -- the filtered complex `Tot(Hom(M, I))` and the data of [Stacks, Tag 012M] attached to it
  let T := B.totalFiltration₂
  let Fil : ∀ (_p n : ℤ), Subobject (T.X.X n) :=
    fun p n => Subobject.mk ((T.filtration.ι.app (op p)).f n)
  let Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1))
  let D : ∀ (_r _p n : ℤ), Subobject (T.X.X n) := fun r p n =>
    Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))
  let FH : ∀ (n _p : ℤ), Subobject (T.X.homology n) := fun n p =>
    imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)
  have hFil : ∀ p n : ℤ, Fil p n = Subobject.mk ((T.filtration.ι.app (op p)).f n) :=
    fun _ _ => rfl
  have hZ : ∀ r p n : ℤ, Z r p n =
      Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) :=
    fun _ _ _ => rfl
  have hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)) :=
    fun _ _ _ => rfl
  have hFH : ∀ n p : ℤ, FH n p =
      imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n) :=
    fun _ _ => rfl
  obtain ⟨E, e, -, hδ, -, -, -⟩ :=
    CochainComplex.exists_cohomologicalSpectralSequence T Fil hFil Z hZ D hD
  obtain ⟨-, -, hE2⟩ := B.exists_iso_pages_totalFiltration₂ Fil hFil Z hZ D hD E e hδ
  obtain ⟨c₁, c₂, c₃, c₄, -⟩ :=
    B.isBounded_and_converges_totalFiltration₂ hfin Fil hFil Z hZ D hD FH hFH E e
  -- the canonical page-`2` subquotient is `Extⁱ(M, Hʲ(K))`
  obtain ⟨fE₂, -⟩ : ∃ _fE₂ : ∀ i j : ℤ,
      cokernel (Subobject.ofLE _ _
          (inf_le_right : D 2 i (i + j) ⊓ Z 2 i (i + j) ≤ Z 2 i (i + j))) ≅
        AddCommGrpCat.of (Abelian.zExt.{u, v, w} M
          ((DerivedCategory.homologyFunctor.{w, v, u} C j).obj
            (DerivedCategory.Plus.ι.{w, v, u}.obj K)) i), True :=
    ⟨fun i j => (e 2 i j (i + j) zero_le_two rfl).symm ≪≫ Classical.choice (hE2 i j) ≪≫
      Classical.choice (h2 i j) ≪≫ (F.rightDerivedPlus i).mapIso (eH j) ≪≫
      rightDerivedSmallCoyonedaIso M _ i, trivial⟩
  refine ⟨T, Fil, hFil, Z, hZ, D, hD, FH, hFH, E, e, fE₂,
    fun i j => e 2 i j (i + j) zero_le_two rfl ≪≫ fE₂ i j,
    fun n => Classical.choice (h3 n) ≪≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{w} n).mapIso
        (F.rightDerivedFunctorPlus.mapIso eJ) ≪≫
      rightDerivedSmallCoyonedaHomologyIso M K n,
    fun _ _ => rfl, hδ, c₁, c₂, c₃, c₄, ?_⟩
  -- on each diagonal, only finitely many columns of the zeroth page are nonzero, and a vanishing
  -- page object stays zero on every later page
  intro n
  obtain ⟨a, ha⟩ := (c₁ n).bddBelow
  obtain ⟨b', hb'⟩ := (c₁ n).bddAbove
  refine ⟨min a b', max a b', min_le_max, ?_⟩
  intro r i j hr hn hij
  obtain rfl : j = n - i := by omega
  have h0 : IsZero ((E.page 0 le_rfl).X (i, n - i)) := by
    by_contra hz
    rcases hij with hij | hij
    · exact absurd (ha hz) (by omega)
    · exact absurd (hb' hz) (by omega)
  exact E.isZero_page_of_le le_rfl (i, n - i) h0 r hr hr

end HomologyPage

end StacksDraft.ExtSpectralSequence
