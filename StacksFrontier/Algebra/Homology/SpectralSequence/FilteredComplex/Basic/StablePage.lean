module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring.RingNF
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.InducedFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.PageComplex

/-!
# Spectral sequences of filtered complexes: the page turn and the limit

The page-turning isomorphisms and the spectral sequence of a filtered complex, its zeroth and
first pages, eventual control of the filtration, and the limit `E_∞` of [Stacks, Tag 012Q] and
[Stacks, Tag 012V] with the maps out of `Ker(d^n) ∩ F^p K^n` as data.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Preadditive Opposite

namespace FilteredComplexSpectralSequence

-- `Subobject` is opened for the unqualified `comp_cokernel_π_eq_zero_iff`,
-- `factors_of_epi_comp`, `mk_le_of_factors`, ... of the subobject toolkit.
open Subobject

variable {A : Type u} [Category.{v} A] [Abelian A]

section Generic

variable (K : CochainComplex A ℤ) (F : ℤ → ∀ n : ℤ, Subobject (K.X n))


/-- Left homology data of the page complex at `pq`, taken on the short complex `sc'` with
*explicit* neighbouring indices `pq ± (r, 1 - r)` rather than on `sc pq`, whose neighbours are
`ComplexShape.prev`/`next`.  The two have isomorphic homology
(`HomologicalComplex.homologyIsoSc'`), and the explicit form is what makes the incoming
differential `S.f` computable: `pageComplex_d` applies to it directly, whereas `(sc pq).f` has
`ComplexShape.prev pq` in the type of its *source*, which no rewrite can reach.

The fields are stated against `S.X₂ = (pageComplex K F r).X pq`, and `S.f`, `S.g` are the page
differentials; `HomologicalComplex.shortComplexFunctor'` is not reducible, so these are the places
where the short complex is identified with its defining data. -/
@[simps K H i π, implicit_reducible]
noncomputable def pageLHD (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r : ℤ) (pq : ℤ × ℤ) :
    ((pageComplex K F r).sc' (pq - (r, 1 - r)) pq (pq + (r, 1 - r))).LeftHomologyData where
  K := pageCycles K F hanti r pq.1 (pq.1 + pq.2)
  H := pageObj K F (r + 1) pq.1 (pq.1 + pq.2)
  i := pageCyclesι K F hanti r pq.1 (pq.1 + pq.2)
  π := pageπ K F hanti r pq.1 (pq.1 + pq.2)
  wi := (comp_d_eq_zero_iff K F r pq _).2 (pageCyclesι_comp_pageMap K F hanti r _ _)
  hi := KernelFork.isLimitOfIsLimitOfIff' (pageCyclesιIsKernel K F hanti r pq.1 (pq.1 + pq.2))
    ((pageComplex K F r).d pq (pq + (r, 1 - r)))
    (fun _ φ => (comp_d_eq_zero_iff K F r pq φ).symm)
  wπ := wπ_aux K F hanti r pq _ (Fork.IsLimit.lift_ι _)
  hπ := hπ_aux K F hanti r pq _ (Fork.IsLimit.lift_ι _)


/-- **The page-turning isomorphism.**  For `r ≥ 0` the homology of the `r`-th page at `(p, q)` is
the `(p, q)` object of the `(r + 1)`-st page: the numerator of `E_r^{p,q}` cut down to the kernel
of `d_r` is `Z_{r + 1}^{p, q}`, and the image of `d_r` from `(p - r, q + r - 1)` adds
`d(Z_r^{p - r, q + r - 1})` to the denominator, so that the denominator becomes
`D_{r + 1}^{p, q} ⊓ Z_{r + 1}^{p, q}`.  The two presentations of the page are identified by
`CategoryTheory.Subobject.exists_iso_cokernel_of_factors_iff` (in `exists_pageTurn`).

The homology is first transported off `sc pq` onto the explicitly-indexed `sc' (pq - (r, 1 - r)) pq
(pq + (r, 1 - r))`, where `pageLHD` lives. -/
noncomputable def pageHomologyIso (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r : ℤ) (pq : ℤ × ℤ) :
    (pageComplex K F r).homology pq ≅ pageObj K F (r + 1) pq.1 (pq.1 + pq.2) :=
  (pageComplex K F r).homologyIsoSc' (pq - (r, 1 - r)) pq (pq + (r, 1 - r))
      ((ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev_eq'
        (by rw [ComplexShape.up'_Rel]; abel))
      ((ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next_eq' (by rw [ComplexShape.up'_Rel]))
    ≪≫ (pageLHD K F hanti r pq).homologyIso ≪≫ eqToIso (pageLHD_H K F hanti r pq)

/-- **The page turn on classes.**  A cycle of the `r`-th page represented by an element `x` of
`Z_{r + 1}^{p, q}` is sent by `pageHomologyIso` to the class of `x` in `E_{r + 1}^{p, q}`. -/
lemma homologyπ_comp_pageHomologyIso_hom
    (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r : ℤ) (pq : ℤ × ℤ) {T : A}
    (y : T ⟶ (pageComplex K F r).cycles pq)
    (x : T ⟶ (cycles K F (r + 1) pq.1 (pq.1 + pq.2) : A))
    (x' : T ⟶ (cycles K F r pq.1 (pq.1 + pq.2) : A))
    (hx : x' ≫ (cycles K F r pq.1 (pq.1 + pq.2)).arrow =
      x ≫ (cycles K F (r + 1) pq.1 (pq.1 + pq.2)).arrow)
    (hy : y ≫ (pageComplex K F r).iCycles pq = x' ≫ cokernel.π (den K F r pq.1 (pq.1 + pq.2))) :
    y ≫ (pageComplex K F r).homologyπ pq ≫ (pageHomologyIso K F hanti r pq).hom =
      x ≫ cokernel.π (den K F (r + 1) pq.1 (pq.1 + pq.2)) := by
  have hprev : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev pq = pq - (r, 1 - r) :=
    (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).prev_eq' (by rw [ComplexShape.up'_Rel]; abel)
  have hnext : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next pq = pq + (r, 1 - r) :=
    (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next_eq' (by rw [ComplexShape.up'_Rel])
  have hx' : x' = x ≫ Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r pq.1 _) ≫
      Subobject.ofLE _ _ (kernelNumerator_le_cycles K F r pq.1 _) := by
    rw [← cancel_mono (cycles K F r pq.1 (pq.1 + pq.2)).arrow, hx, Category.assoc,
      Category.assoc, Subobject.ofLE_arrow, Subobject.ofLE_arrow]
  -- the cycle `y`, read in the left homology data `pageLHD`, is the class of `x`
  have hz : x' ≫ cokernel.π (den K F r pq.1 (pq.1 + pq.2)) =
      (x ≫ Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r pq.1 _) ≫
        cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator K F hanti r pq.1 _))) ≫
        pageCyclesι K F hanti r pq.1 (pq.1 + pq.2) := by
    simp [hx']
  have key : y ≫ ((pageComplex K F r).cyclesIsoSc' _ pq _ hprev hnext).hom ≫
        (pageLHD K F hanti r pq).cyclesIso.hom =
      x ≫ Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r pq.1 _) ≫
        cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator K F hanti r pq.1 _)) :=
    (cancel_mono (pageLHD K F hanti r pq).i).1 <|
      (Category.assoc _ _ _).trans <| (congrArg (y ≫ ·) <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (pageLHD K F hanti r pq).cyclesIso_hom_comp_i).trans
          ((pageComplex K F r).cyclesIsoSc'_hom_iCycles _ pq _ hprev hnext)).trans <|
        hy.trans hz
  have hπ : cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator K F hanti r pq.1 _)) ≫
      pageπ K F hanti r pq.1 (pq.1 + pq.2) =
      cokernel.π (Subobject.ofLE _ _ (denV_le_kernelNumerator K F hanti r pq.1 _)) ≫
        (exists_pageTurn K F hanti r pq.1 (pq.1 + pq.2)).choose.hom := by
    rw [pageπ, ← Category.assoc, Subobject.π_enlargeDen]
  have hturn := (exists_pageTurn K F hanti r pq.1 (pq.1 + pq.2)).choose_spec
  calc y ≫ (pageComplex K F r).homologyπ pq ≫ (pageHomologyIso K F hanti r pq).hom
      = (y ≫ ((pageComplex K F r).cyclesIsoSc' _ pq _ hprev hnext).hom ≫
          (pageLHD K F hanti r pq).cyclesIso.hom) ≫ pageπ K F hanti r pq.1 (pq.1 + pq.2) := by
        simp only [pageHomologyIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id,
          HomologicalComplex.π_homologyIsoSc'_hom_assoc, Category.assoc]
        exact congrArg (fun t => y ≫ _ ≫ t)
          (pageLHD K F hanti r pq).homologyπ_comp_homologyIso_hom
    _ = x ≫ cokernel.π (den K F (r + 1) pq.1 (pq.1 + pq.2)) := by
        rw [key, Category.assoc, Category.assoc, hπ, hturn]

/-- The spectral sequence of a filtered complex: the pages are the `E_r^{p, q}`, the differentials
are induced by `d`, and the page-turning isomorphisms are `pageHomologyIso`. -/
noncomputable abbrev spectralSequence (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) :
    CohomologicalSpectralSequence A 0 where
  page r _ := pageComplex K F r
  iso r r' pq hrr' hr := by
    subst hrr'
    exact pageHomologyIso K F hanti r pq

/-- The page objects of `spectralSequence` are the quotients `Z_r^{p, q} / (D_r^{p,q} ⊓ Z_r^{p,q})`
on the nose. -/
noncomputable def eIso (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) :
    ((spectralSequence K F hanti).page r hr).X (p, q) ≅ cokernel (den K F r p n) :=
  eqToIso (by subst hn; rfl)

/-- For `n = p + q` definitionally, `eIso` is the identity. -/
@[simp]
lemma eIso_hom_rfl (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r p q : ℤ)
    (hr : 0 ≤ r) : (eIso K F hanti r p q (p + q) hr rfl).hom = 𝟙 _ := by
  simp [eIso]

/-- For `n = p + q` definitionally, the inverse of `eIso` is the identity. -/
@[simp]
lemma eIso_inv_rfl (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r p q : ℤ)
    (hr : 0 ≤ r) : (eIso K F hanti r p q (p + q) hr rfl).inv = 𝟙 _ := by
  simp [eIso]

/-- The differential of `spectralSequence` out of `(p, q)`, read through `eIso` at the target. -/
lemma spectralSequence_d (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r p q : ℤ) (hr : 0 ≤ r) :
    ((spectralSequence K F hanti).page r hr).d (p, q) (p + r, q - r + 1) =
      pageMap K F r p (p + q) ≫
        (eIso K F hanti r (p + r) (q - r + 1) (p + q + 1) hr (by ring)).inv := by
  rw [pageComplex_d K F r (pq := (p, q)) (pq' := (p + r, q - r + 1))
    (Prod.ext rfl (by simp only [Prod.snd_add]; ring))]
  simp [pageMap', eIso]

end Generic

section GradedPiece

/-- The inclusion `F^p K^• ⟶ K^•` of a step of the filtration, with its codomain spelled `K.X`.
The structure map `K.filtration.ι.app (op p)` itself has codomain
`((Functor.const ℤᵒᵖ).obj K.X).obj (op p)`, so its commutation squares are stated against that
spelling of the differential rather than against `K.X.d`. -/
abbrev filtrationIncl (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (p : ℤ) :
    K.filtration.obj (op p) ⟶ K.X :=
  K.filtration.ι.app (op p)

/-- `Z_0^{p, q} = F^p K^n`: `Z_eq_F` for the cycles of the filtration. -/
public lemma cycles_zero_eq (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ℤ → ∀ n : ℤ, Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n)) (p n : ℤ) :
    cycles K.X F 0 p n = F p n :=
  Z_eq_F K F hF (cycles K.X F) (fun _ _ _ => by rw [cycles]) le_rfl p n

/-- `D_0^{p, q} ⊓ Z_0^{p, q} = F^{p + 1}K^n`: the denominator of the zeroth page, so that
`E_0^{p, q} = gr^p K^n`. -/
public lemma boundaries_zero_inf_cycles_zero (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ℤ → ∀ n : ℤ, Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n)) (p n : ℤ) :
    boundaries K.X F 0 p n ⊓ cycles K.X F 0 p n = F (p + 1) n := by
  rw [D_zero_eq_F K F hF (cycles K.X F) (fun _ _ _ => by rw [cycles])
      (boundaries K.X F) (fun _ _ _ => by rw [boundaries]) p n,
    cycles_zero_eq K F hF p n, inf_eq_left]
  exact F_antitone K F hF (by omega) n

/-- **`gr^p K^n` is the cokernel of `F^{p + 1}K^n ⟶ F^p K^n`.**  The graded piece `gr^p K^•` is
a cokernel in the category of complexes; cokernels there are computed degreewise, the evaluation
functor preserving them. -/
noncomputable def gradedPieceXIso
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (p n : ℤ) :
    ((FilteredObject.gr p).obj K).X n ≅
      cokernel ((K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).f n) :=
  PreservesCokernel.iso (HomologicalComplex.eval A (ComplexShape.up ℤ) n) _

/-- The identification `gradedPieceXIso` carries the projection onto `gr^p K^n` to the cokernel
projection.  This and `gradedPieceXIso` are where `gr^p K^n` is identified with the cokernel it is
defined as; everything below goes through these two. -/
lemma gradedPieceπ_f_gradedPieceXIso_hom
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (p n : ℤ) :
    (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n ≫ (gradedPieceXIso K p n).hom =
      cokernel.π ((K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).f n) :=
  PreservesCokernel.π_iso_hom (HomologicalComplex.eval A (ComplexShape.up ℤ) n) _

/-- **The zeroth page is the graded piece.**  `Z_0^{p, q} = F^p K^n` and
`D_0^{p, q} ⊓ Z_0^{p, q} = F^{p + 1}K^n`, so `E_0^{p, q} = coker(F^{p + 1}K^n ⟶ F^p K^n)
= gr^p K^n`, compatibly with the two projections out of `F^p K^n`. -/
lemma exists_iso_zeroPage_gradedPiece
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (F : ℤ → ∀ n : ℤ, Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n)) (p n : ℤ) :
    ∃ e : cokernel (den K.X F 0 p n) ≅
        ((FilteredObject.gr p).obj K).X n,
      ∀ u : (cycles K.X F 0 p n : A) ⟶ (K.filtration.obj (op p)).X n,
        u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X F 0 p n).arrow →
        cokernel.π (den K.X F 0 p n) ≫ e.hom =
          u ≫ (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n := by
  obtain ⟨e, he⟩ := exists_iso_cokernel_ofLE_of_eq
    (inf_le_right : boundaries K.X F 0 p n ⊓ cycles K.X F 0 p n ≤ _)
    ((K.filtration.ι.app (op (p + 1))).f n) ((K.filtration.ι.app (op p)).f n)
    ((K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).f n)
    (by rw [← HomologicalComplex.comp_f, K.filtration.diagram_map_comp_ι_app])
    (by rw [boundaries_zero_inf_cycles_zero K F hF p n, hF])
    (by rw [cycles_zero_eq K F hF p n, hF])
  have hπ : cokernel.π ((K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).f n) ≫
      (gradedPieceXIso K p n).inv = (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n :=
    (Iso.comp_inv_eq _).2 (gradedPieceπ_f_gradedPieceXIso_hom K p n).symm
  refine ⟨e ≪≫ (gradedPieceXIso K p n).symm, fun u hu => ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, he u hu, Category.assoc, Iso.symm_hom, hπ]

/-- **The zeroth page is the graded complex.**  `Z_0^{p, q} = F^p K^n` and
`D_0^{p, q} = F^{p + 1} K^n`, so `E_0^{p, q} = gr^p K^n`; under that identification the zeroth
differential is `gr^p(d^n)`, and therefore the first page is the cohomology of `gr^p K^•`.

The isomorphism `α` and its compatibility with the projections out of `F^p K^n` are
`exists_iso_zeroPage_gradedPiece` above.  That `d_0 = gr^p(d)` is checked on `Z_0^{p, q}`, where
both sides are `d^n` followed by the projection to `gr^p K^{n + 1}`; the first page is then the
homology of the zeroth, and `α` is an isomorphism of the three-term complexes computing it. -/
lemma exists_iso_gradedPiece_zeroPage
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (F : ℤ → ∀ n : ℤ, Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) :
    ∃ α : ∀ (p q n : ℤ), n = p + q →
        (((spectralSequence K.X F hanti).page 0 le_rfl).X (p, q) ≅
          ((FilteredObject.gr p).obj K).X n),
      (∀ (p q n : ℤ) (hn : n = p + q)
          (u : (cycles K.X F 0 p n : A) ⟶ (K.filtration.obj (op p)).X n),
        u ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X F 0 p n).arrow →
        cokernel.π (den K.X F 0 p n) ≫ (eIso K.X F hanti 0 p q n le_rfl hn).inv ≫
            (α p q n hn).hom = u ≫ (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n) ∧
      (∀ (p q n : ℤ) (hn : n = p + q),
        ((spectralSequence K.X F hanti).page 0 le_rfl).d (p, q) (p, q + 1) ≫
            (α p (q + 1) (n + 1) (by omega)).hom =
          (α p q n hn).hom ≫
            ((FilteredObject.gr p).obj K).d n (n + 1)) ∧
      (∀ p q n : ℤ, n = p + q →
        Nonempty (((spectralSequence K.X F hanti).page 1).X (p, q) ≅
          ((FilteredObject.gr p).obj K).homology n)) := by
  choose e he using exists_iso_zeroPage_gradedPiece K F hF
  -- `Z_0^{p, q}` is `F^p K^n`, so it lifts canonically through `F^p K^• ⟶ K^•`
  have hex : ∀ p n : ℤ, ∃ w : ((cycles K.X F 0 p n : Subobject (K.X.X n)) : A) ⟶
      (K.filtration.obj (op p)).X n,
      w ≫ (K.filtration.ι.app (op p)).f n = (cycles K.X F 0 p n).arrow := fun p n =>
    ⟨Subobject.ofLE _ _ (by rw [cycles_zero_eq K F hF p n, hF])
      ≫ (Subobject.underlyingIso _).hom, by
      rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]⟩
  choose v hv using hex
  -- the zeroth differential is `gr^p(d^n)`, with the indices given up to arithmetic
  have key : ∀ (p q n q' n' : ℤ) (hn : n = p + q) (hn' : n' = p + q'), q' = q + 1 →
      ((spectralSequence K.X F hanti).page 0 le_rfl).d (p, q) (p, q') ≫
          (eIso K.X F hanti 0 p q' n' le_rfl hn' ≪≫ e p n').hom =
        (eIso K.X F hanti 0 p q n le_rfl hn ≪≫ e p n).hom ≫
          ((FilteredObject.gr p).obj K).d n n' := by
    intro p q n q' n' hn hn' hq'
    subst hq'; subst hn; subst hn'
    -- the two lifts are compatible with the differential of `F^p K^•`
    have hstep : deltaCycles' K.X F 0 p (p + q) p (p + (q + 1)) (by omega) (by omega) ≫
        v p (p + (q + 1)) =
        v p (p + q) ≫ (K.filtration.obj (op p)).d (p + q) (p + (q + 1)) := by
      rw [← cancel_mono ((filtrationIncl K p).f (p + (q + 1))), Category.assoc,
        Category.assoc, hv, deltaCycles'_arrow, ← (filtrationIncl K p).comm, ← Category.assoc,
        hv]
    rw [Iso.trans_hom, Iso.trans_hom, eIso_hom_rfl, eIso_hom_rfl, Category.id_comp,
      Category.id_comp, pageComplex_d K.X F 0 (pq := (p, q)) (pq' := (p, q + 1))
        (Prod.ext (by simp) (by simp)),
      ← cancel_epi (cokernel.π (den K.X F 0 p (p + q))), ← Category.assoc, π_comp_pageMap',
      Category.assoc, he p (p + (q + 1)) _ (hv p (p + (q + 1))), ← Category.assoc, hstep,
      Category.assoc, ← (FilteredObject.grMapπ (FilteredObject.succHom p) K).comm, ← Category.assoc,
      ← he p (p + q) _ (hv p (p + q)), Category.assoc]
  refine ⟨fun p q n hn => eIso K.X F hanti 0 p q n le_rfl hn ≪≫ e p n,
    fun p q n hn u hu => by rw [Iso.trans_hom, Iso.inv_hom_id_assoc]; exact he p n u hu,
    fun p q n hn => key p q n (q + 1) (n + 1) hn (by omega) rfl, fun p q n hn => ⟨?_⟩⟩
  -- `E_1^{p, q} = H(E_0)^{p, q} = H^n(gr^p K^•)`
  have hsc : ((spectralSequence K.X F hanti).page 0 le_rfl).sc' (p, q - 1) (p, q) (p, q + 1) ≅
      ((FilteredObject.gr p).obj K).sc' (n - 1) n (n + 1) :=
    ShortComplex.isoMk
      (eIso K.X F hanti 0 p (q - 1) (n - 1) le_rfl (by omega) ≪≫ e p (n - 1))
      (eIso K.X F hanti 0 p q n le_rfl hn ≪≫ e p n)
      (eIso K.X F hanti 0 p (q + 1) (n + 1) le_rfl (by omega) ≪≫ e p (n + 1))
      (key p (q - 1) (n - 1) q n (by omega) hn (by omega)).symm
      (key p q n (q + 1) (n + 1) hn (by omega) rfl).symm
  exact ((spectralSequence K.X F hanti).iso 0 1 (p, q)).symm ≪≫
    ((spectralSequence K.X F hanti).page 0 le_rfl).homologyIsoSc' (p, q - 1) (p, q) (p, q + 1)
      (ComplexShape.prev_eq' _ (by simp [ComplexShape.up'_Rel]))
      (ComplexShape.next_eq' _ (by simp [ComplexShape.up'_Rel])) ≪≫
    ShortComplex.homologyMapIso hsc ≪≫
    (((FilteredObject.gr p).obj K).homologyIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).symm

end GradedPiece

end FilteredComplexSpectralSequence

namespace CochainComplex

section HomologyControl

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A subcomplex which injects on cohomology contains every ambient boundary lying in it.
Only injectivity in degree `n`, not a degreewise support bound, is needed. -/
public lemma image_d_eq_inf_of_mono_homologyMap {L X : CochainComplex C ℤ}
    (f : L ⟶ X) [Mono f] (n : ℤ) [Mono (HomologicalComplex.homologyMap f n)] :
    (Subobject.exists (X.d (n - 1) n)).obj (Subobject.mk (f.f (n - 1))) =
      imageSubobject (X.d (n - 1) n) ⊓ Subobject.mk (f.f n) := by
  have him : (Subobject.exists (X.d (n - 1) n)).obj (Subobject.mk (f.f (n - 1))) =
      (Subobject.exists (f.f n)).obj (imageSubobject (L.d (n - 1) n)) := by
    rw [Subobject.exists_mk_eq_imageSubobject, f.comm, Subobject.imageSubobject_comp_eq_exists]
  rw [him]
  refine le_antisymm ?_ ?_
  · rw [← Subobject.imageSubobject_comp_eq_exists, ← f.comm]
    exact le_inf (imageSubobject_comp_le _ _) (by
      rw [f.comm]; exact (imageSubobject_comp_le _ _).trans (by rw [imageSubobject_mono]))
  · let V := imageSubobject (X.d (n - 1) n) ⊓ Subobject.mk (f.f n)
    obtain ⟨l, hl, hlπ⟩ := exists_liftCycles_comp_homologyπ_eq_zero
      (X := X) (D := V) inf_le_left
    obtain ⟨l', hl'⟩ := exists_liftCycles f n l (by
      rw [hl]; exact Subobject.inf_arrow_factors_right _ _)
    have hz : l' ≫ L.homologyπ n = 0 := by
      rw [← cancel_mono (HomologicalComplex.homologyMap f n), zero_comp, Category.assoc,
        HomologicalComplex.homologyπ_naturality, ← Category.assoc, hl', hlπ]
    have hb := exists_factors (L.iCycles n) (kernelSubobject_factors _ _ hz)
    rw [exists_iCycles_kernelSubobject_homologyπ] at hb
    refine Subobject.le_of_factors ?_
    have hh := exists_factors (f.f n) hb
    rwa [Category.assoc, ← HomologicalComplex.cyclesMap_i, ← Category.assoc, hl', hl] at hh

/-- Injectivity on cohomology in the next degree allows an approximate cycle to be corrected
by a term of the subcomplex. -/
public lemma pullback_eq_sup_kernel_of_mono_homologyMap {L X : CochainComplex C ℤ}
    (f : L ⟶ X) [Mono f] (n : ℤ) [Mono (HomologicalComplex.homologyMap f (n + 1))] :
    (Subobject.pullback (X.d n (n + 1))).obj (Subobject.mk (f.f (n + 1))) =
      Subobject.mk (f.f n) ⊔ kernelSubobject (X.d n (n + 1)) := by
  have hb := image_d_eq_inf_of_mono_homologyMap f (n + 1)
  rw [show n + 1 - 1 = n by omega] at hb
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · have hh : (Subobject.exists (X.d n (n + 1))).obj
        ((Subobject.pullback (X.d n (n + 1))).obj (Subobject.mk (f.f (n + 1)))) ≤
        (Subobject.exists (X.d n (n + 1))).obj (Subobject.mk (f.f n)) := by
      rw [Abelian.Subobject.exists_pullback_eq_inf, inf_comm, hb]
    have hh' := (Subobject.exists_le_iff_le_pullback _ _ _).mp hh
    rwa [Abelian.Subobject.pullback_exists_eq_sup] at hh'
  · exact Subobject.mk_le_of_factors _ ((pullback_factors_iff _ _ _).mpr (by
      rw [f.comm]; exact Subobject.factors_of_factors_right _ (Subobject.mk_factors_self _)))
  · rw [← Subobject.pullback_bot]
    exact (Subobject.pullback _).monotone bot_le

/-- Surjectivity on cohomology says that every ambient cycle is a cycle of the subcomplex
modulo an ambient boundary. The inclusion need not be a monomorphism for this assertion. -/
public lemma kernel_le_sup_image_of_epi_homologyMap {L X : CochainComplex C ℤ}
    (f : L ⟶ X) (n : ℤ) [Epi (HomologicalComplex.homologyMap f n)] :
    kernelSubobject (X.d n (n + 1)) ≤
      imageSubobject (f.f n) ⊔ imageSubobject (X.d (n - 1) n) := by
  obtain ⟨T, e, he, x, hx, y, hxy⟩ :=
    (HomologicalComplex.epi_homologyMap_iff_up_to_refinements f (n - 1) n (n + 1)
      (by simp) (by simp)).mp inferInstance
      (kernelSubobject (X.d n (n + 1))).arrow (kernelSubobject_arrow_comp _)
  refine Subobject.le_of_factors (Subobject.factors_of_epi_comp e _ ?_)
  rw [hxy]
  exact Subobject.factors_add _ _
    (Subobject.sup_factors_of_factors_left (imageSubobject_factors_comp_self _ _))
    (Subobject.sup_factors_of_factors_right (imageSubobject_factors_comp_self _ _))

/-- The cycle numerator for the quotient by a subcomplex is a boundary when its inclusion
surjects on `H^n` and injects on `H^(n+1)`. -/
public lemma pullback_le_sup_image_of_epi_of_mono_homologyMap {L X : CochainComplex C ℤ}
    (f : L ⟶ X) [Mono f] (n : ℤ) [Epi (HomologicalComplex.homologyMap f n)]
    [Mono (HomologicalComplex.homologyMap f (n + 1))] :
    (Subobject.pullback (X.d n (n + 1))).obj (Subobject.mk (f.f (n + 1))) ≤
      Subobject.mk (f.f n) ⊔ imageSubobject (X.d (n - 1) n) := by
  rw [pullback_eq_sup_kernel_of_mono_homologyMap]
  refine sup_le le_sup_left ?_
  simpa only [imageSubobject_mono] using kernel_le_sup_image_of_epi_homologyMap f n

end HomologyControl

section EventualFiltration

variable {A : Type u} [Category.{v} A] [Abelian A]
  (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
  (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
  (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))

include hF

/-- A finite cycle numerator has already stabilized once the deeper inclusion is injective on
cohomology in the next degree. This includes every acyclic deeper step. -/
public lemma cycles_sup_eq_of_mono_homologyMap (p s n : ℤ) (hps : p + 1 ≤ s)
    [Mono (HomologicalComplex.homologyMap (K.filtration.ι.app (op s)) (n + 1))] :
    F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F s (n + 1)) ⊔ F (p + 1) n =
      kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n := by
  rw [hF s (n + 1), pullback_eq_sup_kernel_of_mono_homologyMap, ← hF s n]
  have hs := F_antitone K F hF hps n
  have hp := F_antitone K F hF (show p ≤ p + 1 by omega) n
  apply le_antisymm
  · calc
      _ ≤ F p n ⊓ (F (p + 1) n ⊔ kernelSubobject (K.X.d n (n + 1))) ⊔ F (p + 1) n :=
        sup_le_sup_right (inf_le_inf_left _ (sup_le_sup_right hs _)) _
      _ ≤ (F (p + 1) n ⊔ kernelSubobject (K.X.d n (n + 1)) ⊓ F p n) ⊔ F (p + 1) n :=
        sup_le_sup_right (by rw [inf_comm]; exact sup_inf_le_assoc_of_le _ hp) _
      _ = _ := by simp [sup_comm]
  · exact sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans le_sup_right)) _

/-- A finite boundary numerator has already stabilized once an earlier inclusion is injective
on cohomology in the same degree. -/
public lemma boundaries_inf_eq_of_mono_homologyMap (p s n : ℤ) (hsp : s ≤ p)
    [Mono (HomologicalComplex.homologyMap (K.filtration.ι.app (op s)) n)] :
    F p n ⊓ (Subobject.exists (K.X.d (n - 1) n)).obj (F s (n - 1)) =
      imageSubobject (K.X.d (n - 1) n) ⊓ F p n := by
  rw [hF s (n - 1), image_d_eq_inf_of_mono_homologyMap, ← hF s n]
  exact le_antisymm (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    (le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans (F_antitone K F hF hsp n))))

/-- Eventual vanishing of the homology of the filtration steps in degree `n + 1` supplies the
stable-cycle greatest lower bound, without completeness or degreewise finiteness assumptions. -/
public lemma isGLB_stableCycles_of_eventually_isZero (p n : ℤ)
    (hzero : ∃ b : ℤ, ∀ s : ℤ, b ≤ s → IsZero ((K.filtration.obj (op s)).homology (n + 1))) :
    IsGLB (Set.range fun r : ℕ ↦
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n)
      (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) := by
  obtain ⟨b, hb⟩ := hzero
  let r := (max 1 (b - p)).toNat
  have hr : p + 1 ≤ p + (r : ℤ) := by dsimp [r]; omega
  have : Mono (HomologicalComplex.homologyMap (K.filtration.ι.app (op (p + (r : ℤ))))
      (n + 1)) := (hb _ (by dsimp [r]; omega)).mono _
  refine IsLeast.isGLB ⟨⟨r, cycles_sup_eq_of_mono_homologyMap K F hF p _ n hr⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  refine sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans ?_)) _
  rw [← Subobject.pullback_bot]
  exact (Subobject.pullback _).monotone bot_le

/-- Eventual isomorphisms from filtration-step homology supply the stable-boundary least upper
bound. Only their injectivity in degree `n` is used. -/
public lemma isLUB_stableBoundaries_of_eventually_isIso (p n : ℤ)
    (hiso : ∃ a : ℤ, ∀ s : ℤ, s ≤ a →
      IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op s)) n)) :
    IsLUB (Set.range fun r : ℕ ↦
      F p n ⊓ (Subobject.exists (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n)
      (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n) := by
  obtain ⟨a, ha⟩ := hiso
  let r := (p - a).toNat
  have : IsIso (HomologicalComplex.homologyMap (K.filtration.ι.app (op (p - (r : ℤ)))) n) :=
    ha _ (by dsimp [r]; omega)
  refine IsGreatest.isLUB ⟨⟨r, ?_⟩, ?_⟩
  · dsimp only
    rw [boundaries_inf_eq_of_mono_homologyMap K F hF p (p - (r : ℤ)) n (by omega)]
  · rintro _ ⟨i, rfl⟩
    exact sup_le_sup_right
      (le_inf (inf_le_right.trans (exists_le_imageSubobject _ _)) inf_le_left) _

/-- The first-page numerator is a boundary if the adjacent filtration transition is
surjective on `H^n` and injective on `H^(n+1)`. This is the local vanishing criterion used at
both ends of an eventually controlled filtration. -/
public lemma firstPage_cycles_le_boundaries (p n : ℤ)
    (hepi : Epi (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n))
    (hmono : Mono (HomologicalComplex.homologyMap (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) (n + 1))) :
    F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + 1) (n + 1)) ≤
      F (p + 1) n ⊔ (Subobject.exists (K.X.d (n - 1) n)).obj (F p (n - 1)) := by
  let f := K.filtration.ι.app (op p)
  let g := K.filtration.diagram.map
    (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op
  have hgf : g ≫ f = K.filtration.ι.app (op (p + 1)) := Filtration.diagram_map_comp_ι_app _ _
  have hgf' (i : ℤ) : g.f i ≫ f.f i = (K.filtration.ι.app (op (p + 1))).f i :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ i) hgf
  let V := F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + 1) (n + 1))
  obtain ⟨x, hx⟩ := exists_comp_eq_of_factors_mk (f.f n)
    (show (Subobject.mk (f.f n)).Factors V.arrow from by
      rw [← hF p n]; exact Subobject.inf_arrow_factors_left _ _)
  obtain ⟨y, hy⟩ := exists_comp_eq_of_factors_mk
    ((K.filtration.ι.app (op (p + 1))).f (n + 1))
    (show (Subobject.mk ((K.filtration.ι.app (op (p + 1))).f (n + 1))).Factors
      (V.arrow ≫ K.X.d n (n + 1)) from by
        rw [← hF]; exact (pullback_factors_iff _ _ _).mp (Subobject.inf_arrow_factors_right _ _))
  have hxy : y ≫ g.f (n + 1) = x ≫ (K.filtration.obj (op p)).d n (n + 1) := by
    rw [← cancel_mono (f.f (n + 1)), Category.assoc, hgf', hy, Category.assoc,
      ← f.comm, ← Category.assoc, hx]
    rfl
  have hh : ((Subobject.pullback ((K.filtration.obj (op p)).d n (n + 1))).obj
      (Subobject.mk (g.f (n + 1)))).Factors x :=
    (pullback_factors_iff _ _ _).mpr (mk_factors_of_fac _ hxy)
  have hh' := Subobject.factors_of_le _
    (pullback_le_sup_image_of_epi_of_mono_homologyMap g n) hh
  have hh'' := exists_factors (f.f n) hh'
  rw [(Subobject.existsPullbackAdj (f.f n)).gc.l_sup,
    ← imageSubobject_mono (g.f n), ← Subobject.imageSubobject_comp_eq_exists, hgf',
        imageSubobject_mono,
    ← Subobject.imageSubobject_comp_eq_exists, ← f.comm, hx] at hh''
  refine Subobject.le_of_factors ?_
  rw [hF (p + 1) n, hF p (n - 1), Subobject.exists_mk_eq_imageSubobject]
  exact hh''


end EventualFiltration


/-- A cycle lying in `F^pK^n` factors through any greatest lower bound `Z` of the stable cycles. -/
private lemma factors_cycles_of_isGLB
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) (p n : ℤ)
    (F : ℤ → ∀ m : ℤ, Subobject (K.X.X m)) (A : Subobject (K.X.cycles n))
    (Z : Subobject (K.X.X n))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z) :
    Z.Factors (A.arrow ≫ K.X.iCycles n) := by
  have : Mono (A.arrow ≫ K.X.iCycles n) := mono_comp _ _
  exact isGLB_factors_of_comp_eq_zero hZ (A.arrow ≫ K.X.iCycles n)
    ((pullback_factors_iff (K.X.iCycles n) (F p n) A.arrow).1
      (by rw [← hA]; exact Subobject.factors_self A))
    (by rw [Category.assoc, K.X.iCycles_d, comp_zero])

/-- **Stacks 012Q.** Let `𝒜` be an abelian category and let `(K^•, F)` be a filtered complex of
`𝒜`, with degreewise filtration subobjects `F^p K^n`. Fix `p, n : ℤ` and write `q = n - p`.
Assume the stable cycles `Z_∞^{p, q}` and the stable boundaries `B_∞^{p, q}` exist, i.e. that
`Z` is the greatest lower bound of the subobjects `F^p K^n ∩ (d^n)⁻¹(F^{p + r}K^{n + 1})
+ F^{p + 1}K^n` and `B` the least upper bound of the subobjects
`F^p K^n ∩ d^{n - 1}(F^{p - r}K^{n - 1}) + F^{p + 1}K^n` of `K^n`. Then
`B_∞^{p, q} ≤ Z_∞^{p, q}`, so the limit `E_∞^{p, q} = Z_∞^{p, q}/B_∞^{p, q}` exists, and the
graded piece `gr^p H^n(K^•)` of the induced filtration on cohomology is a subquotient of it: the
object `A = Ker(d^n) ∩ F^p K^n` maps to `Z_∞^{p, q}` and to `F^p H^n(K^•)`, its image `S` in
`E_∞^{p, q}` is a subobject of `E_∞^{p, q}`, and the induced map `S ⟶ gr^p H^n(K^•)` is an
epimorphism. -/
@[stacks 012Q]
public theorem exists_epi_gradedPiece_homology_of_isGLB_isLUB
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) (p n : ℤ)
    (F : ℤ → ∀ m : ℤ, Subobject (K.X.X m))
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (A : Subobject (K.X.cycles n)) (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (Z B : Subobject (K.X.X n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z)
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B) :
    B ≤ Z ∧
    ∃ (a : (A : C) ⟶ (Z : C))
      (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
      (S : Subobject (cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right)))
      (g : (A : C) ⟶ (S : C))
      (e : (S : C) ⟶ cokernel (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))),
      A.arrow ≫ K.X.iCycles n = a ≫ Z.arrow ∧
      A.arrow ≫ K.X.homologyπ n =
        b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) ∧
      Epi g ∧ Epi e ∧
      g ≫ S.arrow = a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ∧
      g ≫ e = b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) := by
  -- (1) the stable boundaries are contained in the stable cycles: a boundary is a cycle
  refine ⟨isLUB_le_isGLB_of_comp_eq_zero (K.X.d_comp_d (n - 1) n (n + 1)) hZ hB, ?_⟩
  -- the source's (012T): the stable boundaries lie in `Im(d^{n - 1}) ∩ F^pK^n + F^{p + 1}K^n`
  have hBD := isLUB_le_imageSubobject_inf_sup hB
  -- the source's (012S): `A = Ker(d^n) ∩ F^pK^n` is a stable cycle
  have hAZ := factors_cycles_of_isGLB K p n F A Z hA hZ
  obtain ⟨a, ha⟩ : ∃ a : (A : C) ⟶ (Z : C), a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n :=
    ⟨Z.factorThru _ hAZ, Z.factorThru_arrow _ hAZ⟩
  -- the classes of the cycles in `F^pK^n` exhaust `F^pH^n(K^•)`
  obtain ⟨b, hbepi, hb⟩ := exists_epi_comp_image_ι_homologyMap (X := K.X)
    (K.filtration.ι.app (op p)) n A (by rw [hA, hF])
  -- (2) the kernel of `A ⟶ E_∞^{p, q}` dies in `gr^pH^n(K^•)`
  have hker : ∀ {T : C} (u : T ⟶ (A : C)),
      u ≫ a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) = 0 →
      u ≫ b ≫ cokernel.π (image.preComp
        (HomologicalComplex.homologyMap (K.filtration.diagram.map
          (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
        (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)) = 0 := by
    intro T u hu
    rw [← Category.assoc]
    refine comp_cokernel_π_image_preComp_eq_zero_of_factors_sup
      (g := K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
      (f := K.filtration.ι.app (op p)) (h := K.filtration.ι.app (op (p + 1))) (X := K.X)
      (D := imageSubobject (K.X.d (n - 1) n) ⊓ F p n) (y := u ≫ A.arrow) (β := u ≫ b)
      (K.filtration.diagram_map_comp_ι_app _) inf_le_left ?_
      (by rw [Category.assoc, Category.assoc, hb])
    rw [← hF, Category.assoc, ← ha, ← Category.assoc]
    exact Subobject.factors_of_le _ (inf_le_left.trans hBD)
      (factors_of_comp_cokernel_π_ofLE_eq_zero _ _ (by rw [Category.assoc]; exact hu))
  obtain ⟨S, g, e, hg, he, hgS, hge⟩ := exists_epi_of_ker_le _ _ hker
  exact ⟨a, b, S, g, e, ha.symm, hb.symm, hg, he, hgS, hge⟩

/-- **Stacks 012V.** Let `𝒜` be an abelian category, let `(K^•, F)` be a filtered complex of `𝒜`
with degreewise filtration subobjects `F p n = F^p K^n`, and fix `p n : ℤ`; write `q = n - p`,
`A = Ker(d^n) ∩ F^p K^n`, `N = Ker(d^n) ∩ F^p K^n + F^{p + 1}K^n` (the left-hand side of the
inclusion (012S)), `D = Im(d^{n - 1}) ∩ F^p K^n + F^{p + 1}K^n` (the right-hand side of the
inclusion (012T)), and `FH p' = F^{p'} H^n(K^•)` for the induced filtration on cohomology. Then:

1. whenever `Z = Z_∞^{p, q}` and `B = B_∞^{p, q}` exist, the graded piece `gr^p H^n(K^•)` is the
   whole of the limit `E_∞^{p, q} = Z/B` — that is, there is an isomorphism between them
   compatible with the two canonical maps out of `A` — if and only if `Z = N` and `B = D`, i.e.
   if and only if (012S) and (012T) are equalities;
2. the induced filtration on `H^n(K^•)` is separated, `⋂_{p'} F^{p'} H^n(K^•) = 0`, if and only if
   `⋂_{p'} (Ker(d^n) ∩ F^{p'}K^n + Im(d^{n - 1})) = Im(d^{n - 1})`, and it is exhaustive,
   `⋃_{p'} F^{p'}H^n(K^•) = H^n(K^•)`, if and only if
   `⋃_{p'} (Ker(d^n) ∩ F^{p'}K^n + Im(d^{n - 1})) = Ker(d^n)`.

Weak convergence to `H^*(K^•)` is (1) for all `p, n`, and abutment is weak convergence together
with (2) for all `n`. -/
@[stacks 012V]
public theorem exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) (p n : ℤ)
    (F : ℤ → ∀ m : ℤ, Subobject (K.X.X m))
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (A : Subobject (K.X.cycles n))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (N D : Subobject (K.X.X n))
    (hN : N = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hD : D = imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)
    (FH : ℤ → Subobject (K.X.homology n))
    (hFH : ∀ p' : ℤ, FH p' =
      Subobject.mk (image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p')) n))) :
    (∀ Z B : Subobject (K.X.X n),
        IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z →
        IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n) B →
        ∀ a : (A : C) ⟶ (Z : C), a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n →
        ∀ b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n),
          b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
            A.arrow ≫ K.X.homologyπ n →
        ((∃ e : cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≅
              cokernel (image.preComp
                (HomologicalComplex.homologyMap (K.filtration.diagram.map
                  (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
                (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)),
            a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ e.hom =
              b ≫ cokernel.π (image.preComp
                (HomologicalComplex.homologyMap (K.filtration.diagram.map
                  (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
                (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))) ↔
          Z = N ∧ B = D)) ∧
      (IsGLB (Set.range FH) ⊥ ↔
        IsGLB (Set.range fun p' : ℤ => kernelSubobject (K.X.d n (n + 1)) ⊓ F p' n ⊔
          imageSubobject (K.X.d (n - 1) n)) (imageSubobject (K.X.d (n - 1) n))) ∧
      (IsLUB (Set.range FH) ⊤ ↔
        IsLUB (Set.range fun p' : ℤ => kernelSubobject (K.X.d n (n + 1)) ⊓ F p' n ⊔
          imageSubobject (K.X.d (n - 1) n)) (kernelSubobject (K.X.d n (n + 1)))) := by
  have hT : ∀ p' : ℤ, kernelSubobject (K.X.d n (n + 1)) ⊓ F p' n ⊔
      imageSubobject (K.X.d (n - 1) n) =
      (Subobject.exists (K.X.iCycles n)).obj
        ((Subobject.pullback (K.X.homologyπ n)).obj (FH p')) := by
    intro p'
    rw [hFH p', sub_image_homologyMap K n F hF p']
  refine ⟨fun Z B hZ hB a ha bb hbb =>
      weakly_converges_iff K p n F hF A hA N D hN hD Z B hZ hB a ha bb hbb, ?_, ?_⟩
  · rw [isGLB_bot_iff_isGLB_exists_kernelSubobject (K.X.iCycles n) (K.X.homologyπ n) FH _ hT,
      exists_iCycles_kernelSubobject_homologyπ]
  · rw [isLUB_top_iff_isLUB_mk (K.X.iCycles n) (K.X.homologyπ n) FH _ hT, mk_iCycles]

/-! ### The comparison of [Stacks, Tag 012V], as data

[Stacks, Tag 012Q] produces the two maps `a : A ⟶ Z_∞^{p, q}` and `b : A ⟶ F^pH^n(K^•)` out of
`A = Ker(d^n) ∩ F^pK^n`, and [Stacks, Tag 012V] the comparison
`e : E_∞^{p, q} ≅ gr^pH^n(K^•)` over them, all three by existence statements.  All three are in
fact *unique*: `a` and `b` are pinned by monomorphisms, and `a ≫ cokernel.π` is an
**epimorphism** onto `E_∞^{p, q} = Z_∞^{p, q}/B_∞^{p, q}` as soon as the inclusion (012S) is an
equality, so a morphism out of `E_∞^{p, q}` is determined by its restriction along `A`.

This section records the uniqueness and turns the existence statements into `def`s together with
the equations characterising them.  That is what a *natural* comparison needs: two choices made
at two objects of an ambient category are related by nothing, whereas two morphisms each
uniquely determined by an equation are related by the naturality of the equations.  The
`∃`-statements are kept, so nothing downstream changes.
-/

section StableComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) (p n : ℤ)
  (F : ℤ → ∀ m : ℤ, Subobject (K.X.X m)) (A : Subobject (K.X.cycles n))
  (Z B : Subobject (K.X.X n))

/-- **`F^{p + 1}K^n` lies in the stable boundaries.** The family whose least upper bound is
`B_∞^{p, q}` has `F^{p + 1}K^n` as a summand of each member, so in particular of the member at
`r = 0`. -/
public lemma le_isLUB_stableBoundaries
    (hB : IsLUB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔ F (p + 1) n) B) :
    F (p + 1) n ≤ B :=
  le_trans le_sup_right (hB.1 ⟨0, rfl⟩)

/-- **The cycles of `K^•` lying in `F^pK^n` generate `E_∞^{p, q} = Z_∞^{p, q}/B_∞^{p, q}`**, as
soon as the inclusion (012S) is an equality, `Z_∞^{p, q} = Ker(d^n) ∩ F^pK^n + F^{p + 1}K^n`.
Indeed the numerator is then the join of the image of `A = Ker(d^n) ∩ F^pK^n` with `F^{p + 1}K^n`,
and `F^{p + 1}K^n` lies in the denominator `B_∞^{p, q}`.

Nothing is assumed about `B` beyond `F^{p + 1}K^n ≤ B`, which
`CochainComplex.le_isLUB_stableBoundaries` supplies for the stable boundaries; the equality (012T)
is not needed.  This is the fact that makes the comparison of [Stacks, Tag 012V] *unique*. -/
public lemma epi_comp_cokernel_π_ofLE_of_eq_sup
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hFB : F (p + 1) n ≤ B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n) :
    Epi (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right)) := by
  have hmonoA : Mono (A.arrow ≫ K.X.iCycles n) := mono_comp _ _
  have hmono : Mono (a ≫ Z.arrow) := by rw [ha]; exact hmonoA
  have hmkmk : Subobject.mk (A.arrow ≫ K.X.iCycles n) = Subobject.mk (a ≫ Z.arrow) :=
    Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, ha])
  have hmk : Subobject.mk (a ≫ Z.arrow) = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n := by
    rw [← hmkmk, ← imageSubobject_mono, ← Subobject.exists_eq_imageSubobject, hA,
      Subobject.exists_pullback_eq_inf_of_mono, inf_comm, mk_iCycles]
  refine Subobject.epi_comp_cokernel_π (Y := F (p + 1) n) _ (Subobject.ofLE_arrow _) a ?_ ?_
  · rw [hmk]
    exact hZN.le
  · exact le_inf hFB (by rw [hZN]; exact le_sup_right)

/-- **A morphism out of `E_∞^{p, q}` is determined by its restriction along `A`**, where the
inclusion (012S) is an equality.  This is `epi_comp_cokernel_π_ofLE_of_eq_sup` read as a
cancellation rule. -/
public lemma hom_ext_cokernel_ofLE_of_eq_sup
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hFB : F (p + 1) n ≤ B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    {T : C} {f g : cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ⟶ T}
    (h : a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ f =
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ g) :
    f = g := by
  have := epi_comp_cokernel_π_ofLE_of_eq_sup K p n F A Z B hA hZN hFB a ha
  refine (cancel_epi (a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right))).1 ?_
  rw [Category.assoc, Category.assoc]
  exact h

/-- **The comparison of [Stacks, Tag 012V] is unique.** Two isomorphisms out of `E_∞^{p, q}`
compatible with the same morphism out of `A = Ker(d^n) ∩ F^pK^n` are equal, where the inclusion
(012S) is an equality.

With `β = b ≫ cokernel.π (Limits.image.preComp ..)` this is uniqueness of the isomorphism
`E_∞^{p, q} ≅ gr^pH^n(K^•)` whose existence is
`exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff`.  It answers the question the
`∃`-form leaves open: the comparison is not merely available but canonical. -/
public lemma iso_eq_of_comp_cokernel_π_eq_of_eq_sup
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZN : Z = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n)
    (hFB : F (p + 1) n ≤ B)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n)
    {T : C} {β : (A : C) ⟶ T}
    (e e' : cokernel (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≅ T)
    (he : a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ e.hom = β)
    (he' : a ≫ cokernel.π (Subobject.ofLE (B ⊓ Z) Z inf_le_right) ≫ e'.hom = β) :
    e = e' :=
  Iso.ext (hom_ext_cokernel_ofLE_of_eq_sup K p n F A Z B hA hZN hFB a ha (by rw [he, he']))

/-! #### The two maps out of `A = Ker(d^n) ∩ F^pK^n` of [Stacks, Tag 012Q], as data -/

/-- **A cycle of `K^•` lying in `F^pK^n` is a stable cycle**, the source's (012S): `A` factors
through `Z_∞^{p, q}`.  This is the side condition of `CochainComplex.stableCyclesLift`. -/
public lemma factors_stableCycles
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z) :
    Z.Factors (A.arrow ≫ K.X.iCycles n) :=
  factors_cycles_of_isGLB K p n F A Z hA hZ

/-- **The map `A ⟶ Z_∞^{p, q}` of [Stacks, Tag 012Q], as data.** The inclusion of
`A = Ker(d^n) ∩ F^pK^n` into the stable cycles, which exists because a cycle lying in `F^pK^n` is
a stable cycle (`CochainComplex.factors_stableCycles`).  It is the unique morphism over `K^n`
(`CochainComplex.stableCyclesLift_comp_arrow`, `CochainComplex.stableCyclesLift_unique`). -/
noncomputable def stableCyclesLift
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z) :
    (A : C) ⟶ (Z : C) :=
  Z.factorThru (A.arrow ≫ K.X.iCycles n) (factors_stableCycles K p n F A Z hA hZ)

/-- The equation characterising `CochainComplex.stableCyclesLift`: it lies over `K^n`. -/
public lemma stableCyclesLift_comp_arrow
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z) :
    stableCyclesLift K p n F A Z hA hZ ≫ Z.arrow = A.arrow ≫ K.X.iCycles n :=
  Z.factorThru_arrow _ _

/-- **`CochainComplex.stableCyclesLift` is the only map `A ⟶ Z_∞^{p, q}` over `K^n`**, because
`Z_∞^{p, q}` is a subobject.  So the `∃`-bound map `a` of
`CochainComplex.exists_epi_gradedPiece_homology_of_isGLB_isLUB` is this one. -/
public lemma stableCyclesLift_unique
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (hZ : IsGLB (Set.range fun r : ℕ =>
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n) Z)
    (a : (A : C) ⟶ (Z : C)) (ha : a ≫ Z.arrow = A.arrow ≫ K.X.iCycles n) :
    a = stableCyclesLift K p n F A Z hA hZ :=
  (cancel_mono Z.arrow).1 (by rw [ha, stableCyclesLift_comp_arrow])

/-- **The classes of the cycles of `K^•` lying in `F^pK^n` exhaust `F^pH^n(K^•)`.** The
existence statement behind `CochainComplex.toImageHomologyMap`, specialised to the filtration of
`K^•` from the degreewise subobjects `F`. -/
public lemma exists_epi_comp_image_ι_homologyMap_filtration
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n)) :
    ∃ β : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n),
      Epi β ∧ β ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
        A.arrow ≫ K.X.homologyπ n :=
  exists_epi_comp_image_ι_homologyMap (X := K.X) (K.filtration.ι.app (op p)) n A (by rw [hA, hF])

/-- **The map `A ⟶ F^pH^n(K^•)` of [Stacks, Tag 012Q], as data.** The classes of the cycles of
`K^•` lying in `F^pK^n` exhaust `F^pH^n(K^•) = Im(H^n(F^pK^•) ⟶ H^n(K^•))`; this is the
resulting epimorphism.  It is the unique morphism over `H^n(K^•)`
(`CochainComplex.toImageHomologyMap_comp_image_ι`,
`CochainComplex.toImageHomologyMap_unique`). -/
noncomputable def toImageHomologyMap
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n)) :
    (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) :=
  (exists_epi_comp_image_ι_homologyMap_filtration K p n F A hF hA).choose

/-- The equation characterising `CochainComplex.toImageHomologyMap`: it computes the class in
`H^n(K^•)` of a cycle lying in `F^pK^n`. -/
public lemma toImageHomologyMap_comp_image_ι
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n)) :
    toImageHomologyMap K p n F A hF hA ≫
        image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n :=
  (exists_epi_comp_image_ι_homologyMap_filtration K p n F A hF hA).choose_spec.2

/-- `CochainComplex.toImageHomologyMap` is an epimorphism: the cycles lying in `F^pK^n` exhaust
`F^pH^n(K^•)`. -/
public lemma epi_toImageHomologyMap
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n)) :
    Epi (toImageHomologyMap K p n F A hF hA) :=
  (exists_epi_comp_image_ι_homologyMap_filtration K p n F A hF hA).choose_spec.1

/-- **`CochainComplex.toImageHomologyMap` is the only map `A ⟶ F^pH^n(K^•)` over `H^n(K^•)`**,
because `F^pH^n(K^•)` is presented by a monomorphism.  So the `∃`-bound map `b` of
`CochainComplex.exists_epi_gradedPiece_homology_of_isGLB_isLUB` is this one. -/
public lemma toImageHomologyMap_unique
    (hF : ∀ p' m : ℤ, F p' m = Subobject.mk ((K.filtration.ι.app (op p')).f m))
    (hA : A = (Subobject.pullback (K.X.iCycles n)).obj (F p n))
    (b : (A : C) ⟶ image (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (hb : b ≫ image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n) =
      A.arrow ≫ K.X.homologyπ n) :
    b = toImageHomologyMap K p n F A hF hA :=
  (cancel_mono (image.ι (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))).1
    (by rw [hb, toImageHomologyMap_comp_image_ι])

end StableComparison

end CochainComplex

end
