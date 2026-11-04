module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexSpectralSequences

/-!
# Naturality of the identification of the pages of the spectral sequence of a double complex

Let `K^{•,•}` be a double complex whose total complex exists, and let `(''E_r, ''d_r)` be the
spectral sequence of `Tot(K^{•,•})` filtered by the second coordinate. The identifications
`''E_1^{p,q} = H^q(K^{•,p})` and `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))` of
[Stacks, Tag 0130] are available as data, `HomologicalComplex₂.isOnePageTotalFiltration₂` and
`HomologicalComplex₂.isoTwoPageTotalFiltration₂`. This file shows that they are *natural* in
`K^{•,•}`.

Naturality is not a well-formed question about `exists_iso_pages_totalFiltration₂` as it stands,
because that statement takes the spectral sequence `E` and the presentation `e` of its pages as
`Z_r^{p,q}/D_r^{p,q}` as *inputs*: a square can only be asked to commute once those inputs are
themselves functorial in `K^{•,•}`. So the naturality statements come in two layers. The general
one takes, besides a morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes, a morphism
`g : E ⟶ E'` of the two spectral sequences together with the one hypothesis `hg` that `g` is the
map induced by `φ` *on representatives*: on the class of an element of `Z_1^{p,q}` it is the
class of the image of that element. The concrete one instantiates it at `spectralSequence₂`, the
spectral sequence of `Tot(K^{•,•})` filtered by `⨁_{j ≥ p} K^{i,j}` with its tautological
presentation `pageIso₂` of the pages, where `hg` is `pageIso₂_spectralSequenceMap₂` and nothing
is left to assume.

## Main definitions

* `HomologicalComplex₂.spectralSequence₂`, `HomologicalComplex₂.spectralSequenceMap₂`: the second
  spectral sequence of a double complex and the morphism induced by a morphism of double
  complexes. `HomologicalComplex₂.spectralSequence₂_eq` identifies it with
  `Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor`.
* `HomologicalComplex₂.pageIso₂`: the identification of its pages with `Z_r^{p,q}/D_r^{p,q}`.
* `HomologicalComplex₂.cyclesMap₂`: the map `Z_r^{p,q}(K) ⟶ Z_r^{p,q}(L)` induced by `Tot(φ)`.

## Main results

* `CategoryTheory.ShortComplex.homologyMap_eq_of_τ₂`: two morphisms of short complexes with the
  same middle component induce the same map on homology.
* `HomologicalComplex₂.iso_naturality_of_spec`: an identification pinned down by representatives
  is natural as soon as the representatives are carried to representatives. This is the engine of
  every statement below: the page-one identification is not given by a formula, it is
  characterized by what it does to the class of a cycle, and that characterization determines it,
  the characterizing composite being an epimorphism.
* `HomologicalComplex₂.isoTwoPage_naturality`: the identification `E_2^{p,q} ≅ H^p(M)` obtained
  from an identification of the line `p ↦ E_1^{p,q}` with a cochain complex `M` is natural: it
  only involves the page-turning isomorphism of the spectral sequence, which a morphism of
  spectral sequences commutes with by definition, and the homology of the identification of
  lines, which is natural because the homology of a short complex only depends on the middle
  component of a morphism.
* `HomologicalComplex₂.isoOnePageTotalFiltration₂_naturality` and
  `HomologicalComplex₂.isoTwoPageTotalFiltration₂_naturality`: naturality of the identifications
  `''E_1^{p,q} = H^q(K^{•,p})` and `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`, given `hg`.
* `HomologicalComplex₂.isoOnePageTotalFiltration₂_naturality_functor` and
  `HomologicalComplex₂.isoTwoPageTotalFiltration₂_naturality_functor`: the same for
  `spectralSequence₂` and `spectralSequenceMap₂`, with no hypotheses left.

## Implementation notes

The identification `''E_1^{p,q} = H^q(K^{•,p})` bottoms out in
`CochainComplex.exists_iso_homology_page_of_mem_cycles`, an existence statement, so
`HomologicalComplex₂.isoOnePage` is an `Exists.choose`. That is harmless for naturality: the
isomorphism it chooses is a *function* of the data, and `HomologicalComplex₂.isoOnePage_spec`
determines it uniquely, which is exactly what `iso_naturality_of_spec` consumes.

The abutment of the spectral sequence is *not* made functorial here; nor is the comparison of a
`CohomologicalSpectralSequence` on `ℤ × ℤ` with an `E₂CohomologicalSpectralSequenceNat` on
`ℕ × ℕ`.

## References

* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 012O](https://stacks.math.columbia.edu/tag/012O)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.ShortComplex

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Two morphisms of short complexes with the same middle component induce the same map on
homology: the map on cycles is determined by the middle component because `iCycles` is a
monomorphism, and `homologyπ` is an epimorphism. -/
lemma homologyMap_eq_of_τ₂ {A B : ShortComplex D} (φ ψ : A ⟶ B) (h : φ.τ₂ = ψ.τ₂) :
    homologyMap φ = homologyMap ψ := by
  have hc : cyclesMap φ = cyclesMap ψ := by
    rw [← cancel_mono B.iCycles, cyclesMap_i, cyclesMap_i, h]
  rw [← cancel_epi A.homologyπ, homologyπ_naturality, homologyπ_naturality, hc]

/-- A square of short complexes whose vertical sides are isomorphisms and which commutes in the
middle component induces a commuting square in homology. -/
lemma homologyMap_comp_homologyMapIso_hom {A A' B B' : ShortComplex D} (u : A ⟶ A') (v : B ⟶ B')
    (eA : A ≅ B) (eA' : A' ≅ B') (h : u.τ₂ ≫ eA'.hom.τ₂ = eA.hom.τ₂ ≫ v.τ₂) :
    homologyMap u ≫ (homologyMapIso eA').hom = (homologyMapIso eA).hom ≫ homologyMap v := by
  rw [homologyMapIso_hom, homologyMapIso_hom, ← homologyMap_comp, ← homologyMap_comp]
  exact homologyMap_eq_of_τ₂ _ _ (by rw [comp_τ₂, comp_τ₂, h])

end CategoryTheory.ShortComplex

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

section Spec

omit [Abelian C] in
/-- **An identification pinned down by representatives is natural.** Suppose `β : A ≅ H` and
`β' : A' ≅ H'` are identifications characterized by sending a representative `a`, resp. `a'`, to
the projection `π`, resp. `π'`, with `π` an epimorphism, and suppose a map `g : A ⟶ A'` carries
`a` to `u` followed by `a'`. Then `g` corresponds to the map `h` induced by `u`. -/
lemma iso_naturality_of_spec {X Y H H' A A' : C} (π : X ⟶ H) [Epi π] (π' : Y ⟶ H')
    (u : X ⟶ Y) (h : H ⟶ H') (hu : π ≫ h = u ≫ π') (β : A ≅ H) (β' : A' ≅ H') (g : A ⟶ A')
    (a : X ⟶ A) (a' : Y ⟶ A') (ha : a ≫ β.hom = π) (ha' : a' ≫ β'.hom = π')
    (hag : a ≫ g = u ≫ a') : g ≫ β'.hom = β.hom ≫ h := by
  have hepi : Epi a := by
    have hfac : a = π ≫ β.inv := by
      rw [← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hfac]
    infer_instance
  rw [← cancel_epi a, reassoc_of% hag, ha', ← hu, ← ha, Category.assoc]

end Spec

section TwoPage

variable {E E' : CohomologicalSpectralSequence C 0}

/-- **Naturality of the identification of the second page.** A morphism `g : E ⟶ E'` of spectral
sequences which matches two identifications `β`, `β'` of the lines `p ↦ E_1^{p,q}` and
`p ↦ E_1'^{p,q}` with cochain complexes `M`, `M'` — the same unit `s` twisting the differentials
on both sides — also matches the resulting identifications of the second pages with `H^p(M)` and
`H^p(M')`. -/
lemma isoTwoPage_naturality (g : E ⟶ E') (q : ℤ) {M M' : CochainComplex C ℤ} (s : ℤˣ)
    (ν : M ⟶ M') (β : ∀ p, (E.page 1 zero_le_one).X (p, q) ≅ M.X p)
    (hβ : ∀ p p', p' = p + 1 →
      (E.page 1 zero_le_one).d (p, q) (p', q) ≫ (β p').hom = (β p).hom ≫ (s • M.d p p'))
    (β' : ∀ p, (E'.page 1 zero_le_one).X (p, q) ≅ M'.X p)
    (hβ' : ∀ p p', p' = p + 1 →
      (E'.page 1 zero_le_one).d (p, q) (p', q) ≫ (β' p').hom = (β' p).hom ≫ (s • M'.d p p'))
    (hg : ∀ p, (g.hom 1 zero_le_one).f (p, q) ≫ (β' p).hom = (β p).hom ≫ ν.f p) (p : ℤ) :
    (g.hom 2 zero_le_two).f (p, q) ≫ (isoTwoPage E' q M' s β' hβ' p).hom =
      (isoTwoPage E q M s β hβ p).hom ≫ HomologicalComplex.homologyMap ν p := by
  have hcomm : (E.iso 1 2 (p, q) one_add_one_eq_two zero_le_one).hom ≫
      (g.hom 2 zero_le_two).f (p, q) =
      HomologicalComplex.homologyMap (g.hom 1 zero_le_one) (p, q) ≫
        (E'.iso 1 2 (p, q) one_add_one_eq_two zero_le_one).hom :=
    (g.comm 1 2 (p, q) one_add_one_eq_two zero_le_one).symm
  rw [← cancel_epi (E.iso 1 2 (p, q) one_add_one_eq_two zero_le_one).hom, reassoc_of% hcomm,
    iso_hom_comp_isoTwoPage_hom, ← Category.assoc, iso_hom_comp_isoTwoPage_hom]
  exact ShortComplex.homologyMap_comp_homologyMapIso_hom
    ((HomologicalComplex.shortComplexFunctor C _ (p, q)).map (g.hom 1 zero_le_one))
    ((HomologicalComplex.shortComplexFunctor C _ p).map ν) _ _ (by
      rw [lineScIso_hom_τ₂, lineScIso_hom_τ₂]
      exact hg p)

end TwoPage

section SecondFiltration

variable {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]

/-- The cycles `Z_r^{p,q}` of the second filtration of `Tot(K^{•,•})`. -/
noncomputable abbrev cycles₂ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r p n : ℤ) :
    Subobject ((K.total (ComplexShape.up ℤ)).X n) :=
  FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
    (K.stepSubobject fun (_ : ℤ) j => j) r p n

/-- The boundaries `D_r^{p,q}` of the second filtration of `Tot(K^{•,•})`. -/
noncomputable abbrev boundaries₂
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r p n : ℤ) :
    Subobject ((K.total (ComplexShape.up ℤ)).X n) :=
  FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ))
    (K.stepSubobject fun (_ : ℤ) j => j) r p n

omit [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] in
/-- The morphism of rows `K^{•,p} ⟶ L^{•,p}` induced by a morphism of double complexes. -/
def rowHom (φ : K ⟶ L) (p : ℤ) : K.row p ⟶ L.row p where
  f q := (φ.f q).f p
  comm' q q' _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, φ.comm]

omit [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] in
/-- The component of `rowHom φ p` in degree `q` is the `(q, p)` component of `φ`. -/
@[simp]
lemma rowHom_f (φ : K ⟶ L) (p q : ℤ) : (rowHom φ p).f q = (φ.f q).f p := rfl

/-- A morphism of double complexes carries `⨁_{j ≥ p} K^{i,j} ⊆ Tot(K^{•,•})^n` into
`⨁_{j ≥ p} L^{i,j} ⊆ Tot(L^{•,•})^n`. -/
lemma exists_stepSubobject₂_le (φ : K ⟶ L) (p n : ℤ) :
    (Subobject.«exists» ((HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n)).obj
        (K.stepSubobject (fun (_ : ℤ) j => j) p n) ≤
      L.stepSubobject (fun (_ : ℤ) j => j) p n :=
  Subobject.exists_le_of_comm _
    ((Stacks.Cohomology.CechSpectral.totalFiltrationStepMap (fun (_ : ℤ) j => j)
      (fun _ _ => le_rfl) (fun _ _ => Int.le_add_one le_rfl) φ p).f n)
    (Stacks.Cohomology.CechSpectral.totalFiltrationStepMap_f_arrow _ _ _ φ p n)

/-- The map `Z_r^{p,q}(K) ⟶ Z_r^{p,q}(L)` on the cycles of the second filtration induced by a
morphism of double complexes: the restriction of `Tot(φ)`. -/
noncomputable def cyclesMap₂ (φ : K ⟶ L) (r p n : ℤ) :
    (cycles₂ K r p n : C) ⟶ (cycles₂ L r p n : C) :=
  FilteredComplexSpectralSequence.cyclesMap
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) (exists_stepSubobject₂_le φ) r p n

/-- The map `cyclesMap₂ φ r p n` is compatible with the inclusions of the cycles into
`Tot(K^{•,•})^n` and `Tot(L^{•,•})^n` and the map `Tot(φ)`. -/
@[reassoc]
lemma cyclesMap₂_arrow (φ : K ⟶ L) (r p n : ℤ) :
    cyclesMap₂ φ r p n ≫ (cycles₂ L r p n).arrow =
      (cycles₂ K r p n).arrow ≫ (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n :=
  FilteredComplexSpectralSequence.cyclesMap_arrow _ _ r p n

/-- Reading a cycle of the row `K^{•,p}` as an element of `Z_r^{p,q}` commutes with a morphism of
double complexes. -/
lemma rowCycles_cyclesMap₂ (φ : K ⟶ L) (r p q : ℤ) (hr : r ≤ 1) :
    rowCycles r p q hr ≫ cyclesMap₂ φ r p (p + q) =
      HomologicalComplex.cyclesMap (rowHom φ p) q ≫ rowCycles (K := L) r p q hr := by
  rw [← cancel_mono (cycles₂ L r p (p + q)).arrow, Category.assoc, cyclesMap₂_arrow,
    rowCycles_arrow_assoc, Category.assoc, rowCycles_arrow,
    HomologicalComplex.cyclesMap_i_assoc, rowHom_f, ιTotal_map]

omit [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] in
/-- The identification of the cohomology of the row `K^{•,p}` with the `p`-th term of
`H^q_I(K^{•,•})` is natural in the double complex. -/
lemma homologyMap_rowHom (φ : K ⟶ L) (p q : ℤ) :
    HomologicalComplex.homologyMap (rowHom φ p) q ≫ (rowHomologyIso (K := L) p q).hom =
      (rowHomologyIso (K := K) p q).hom ≫ (HomologicalComplex.homologyMap φ q).f p :=
  ShortComplex.mapHomologyIso_hom_naturality
    (φ := (HomologicalComplex.shortComplexFunctor (CochainComplex C ℤ) (ComplexShape.up ℤ) q).map φ)
    (F := HomologicalComplex.eval C (ComplexShape.up ℤ) p)

variable (E : CohomologicalSpectralSequence C 0)
  (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right :
      boundaries₂ K r p n ⊓ cycles₂ K r p n ≤ cycles₂ K r p n)))
  (hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ) (hp' : p' = p + r)
    (hq' : q' = q - r + 1) (hn' : n' = n + 1),
    ∃ δ : (cycles₂ K r p n : C) ⟶ (cycles₂ K r p' n' : C),
      δ ≫ (cycles₂ K r p' n').arrow =
        (cycles₂ K r p n).arrow ≫ (K.total (ComplexShape.up ℤ)).d n n' ∧
      cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e r p q n hr hn).inv ≫
          (E.page r hr).d (p, q) (p', q') =
        δ ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
          (e r p' q' n' hr (add_eq_of_indices hn hp' hq' hn')).inv)
  (E' : CohomologicalSpectralSequence C 0)
  (e' : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E'.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right :
      boundaries₂ L r p n ⊓ cycles₂ L r p n ≤ cycles₂ L r p n)))
  (hδ' : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ) (hp' : p' = p + r)
    (hq' : q' = q - r + 1) (hn' : n' = n + 1),
    ∃ δ : (cycles₂ L r p n : C) ⟶ (cycles₂ L r p' n' : C),
      δ ≫ (cycles₂ L r p' n').arrow =
        (cycles₂ L r p n).arrow ≫ (L.total (ComplexShape.up ℤ)).d n n' ∧
      cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e' r p q n hr hn).inv ≫
          (E'.page r hr).d (p, q) (p', q') =
        δ ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
          (e' r p' q' n' hr (add_eq_of_indices hn hp' hq' hn')).inv)
  (φ : K ⟶ L) (g : E ⟶ E')
  (hg : ∀ p q : ℤ, cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p q (p + q) zero_le_one rfl).inv ≫ (g.hom 1 zero_le_one).f (p, q) =
    cyclesMap₂ φ 1 p (p + q) ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e' 1 p q (p + q) zero_le_one rfl).inv)

include hδ hδ' hg in
/-- **Naturality of the identification `''E_1^{p,q} = H^q(K^{•,p})`, on the rows.** -/
lemma isoOnePageRow_naturality (p q : ℤ) :
    (g.hom 1 zero_le_one).f (p, q) ≫ (isoOnePageRow L E' e' hδ' p q).hom =
      (isoOnePageRow K E e hδ p q).hom ≫ HomologicalComplex.homologyMap (rowHom φ p) q := by
  refine iso_naturality_of_spec ((K.row p).homologyπ q) ((L.row p).homologyπ q) _ _
    (HomologicalComplex.homologyπ_naturality (rowHom φ p) q) (isoOnePageRow K E e hδ p q)
    (isoOnePageRow L E' e' hδ' p q) _
    (rowCycles 1 p q le_rfl ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p q (p + q) zero_le_one rfl).inv)
    (rowCycles (K := L) 1 p q le_rfl ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e' 1 p q (p + q) zero_le_one rfl).inv)
    (by rw [Category.assoc, Category.assoc]; exact isoOnePageRow_spec K E e hδ p q)
    (by rw [Category.assoc, Category.assoc]; exact isoOnePageRow_spec L E' e' hδ' p q) ?_
  rw [Category.assoc, Category.assoc, hg p q, ← Category.assoc,
    rowCycles_cyclesMap₂ φ 1 p q le_rfl, Category.assoc]

include hδ hδ' hg in
/-- **Naturality of the identification `''E_1^{p,q} = H^q(K^{•,p})`.** With `H^q(K^{•,p})` written
as the `p`-th term of `H^q_I(K^{•,•})`, a morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes
induces a commuting square. -/
theorem isoOnePageTotalFiltration₂_naturality (p q : ℤ) :
    (g.hom 1 zero_le_one).f (p, q) ≫ (isoOnePageTotalFiltration₂ L E' e' hδ' p q).hom =
      (isoOnePageTotalFiltration₂ K E e hδ p q).hom ≫
        (HomologicalComplex.homologyMap φ q).f p := by
  rw [isoOnePageTotalFiltration₂_eq, isoOnePageTotalFiltration₂_eq, Iso.trans_hom, Iso.trans_hom,
    reassoc_of% isoOnePageRow_naturality E e hδ E' e' hδ' φ g hg p q,
    homologyMap_rowHom φ p q, Category.assoc]

include hδ hδ' hg in
/-- **Naturality of the identification `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`.** A morphism
`φ : K^{•,•} ⟶ L^{•,•}` of double complexes, together with a morphism `g` of the two spectral
sequences inducing on the classes of `Z_1^{p,q}` the map induced by `φ`, gives a commuting
square between the second pages and `H^p_{II}(H^q_I(-))`. -/
theorem isoTwoPageTotalFiltration₂_naturality (p q : ℤ) :
    (g.hom 2 zero_le_two).f (p, q) ≫ (isoTwoPageTotalFiltration₂ L E' e' hδ' p q).hom =
      (isoTwoPageTotalFiltration₂ K E e hδ p q).hom ≫
        HomologicalComplex.homologyMap (HomologicalComplex.homologyMap φ q) p := by
  rw [isoTwoPageTotalFiltration₂_eq, isoTwoPageTotalFiltration₂_eq]
  exact isoTwoPage_naturality g q q.negOnePow (HomologicalComplex.homologyMap φ q) _ _ _ _
    (fun p => isoOnePageTotalFiltration₂_naturality E e hδ E' e' hδ' φ g hg p q) p

end SecondFiltration

section Functorial

variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- The spectral sequence of a filtered complex depends only on the family of subobjects cutting
out the filtration, not on the presentation of that family. -/
lemma spectralSequence_congr {X : CochainComplex C ℤ}
    {F F' : ∀ (_p n : ℤ), Subobject (X.X n)} (h : F = F')
    (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (hanti' : ∀ p p' n : ℤ, p ≤ p' → F' p' n ≤ F' p n) :
    FilteredComplexSpectralSequence.spectralSequence X F hanti =
      FilteredComplexSpectralSequence.spectralSequence X F' hanti' := by
  subst h
  rfl

/-- The filtration `⨁_{j ≥ p} K^{i,j}` of `Tot(K^{•,•})` decreases in `p`. -/
lemma antitone_stepSubobject₂ : ∀ p p' n : ℤ, p ≤ p' →
    K.stepSubobject (fun (_ : ℤ) j => j) p' n ≤ K.stepSubobject (fun (_ : ℤ) j => j) p n :=
  fun _ _ n hp => K.totalProjector_le _ _ (fun _ _ hj => hp.trans hj) n

/-- **The second spectral sequence of a double complex.** The spectral sequence of `Tot(K^{•,•})`
filtered by the second coordinate, with the filtration presented as `⨁_{j ≥ p} K^{i,j}` rather
than as the image of the subcomplex inclusion; `spectralSequence₂_eq` identifies it with
`Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor`. -/
noncomputable abbrev spectralSequence₂ : CohomologicalSpectralSequence C 0 :=
  FilteredComplexSpectralSequence.spectralSequence (K.total (ComplexShape.up ℤ))
    (K.stepSubobject fun (_ : ℤ) j => j) (antitone_stepSubobject₂ K)

/-- The pages of `spectralSequence₂` are the quotients `Z_r^{p,q}/D_r^{p,q}` on the nose. -/
noncomputable abbrev pageIso₂ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) :
    ((spectralSequence₂ K).page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right :
        boundaries₂ K r p n ⊓ cycles₂ K r p n ≤ cycles₂ K r p n)) :=
  FilteredComplexSpectralSequence.eIso (K.total (ComplexShape.up ℤ))
    (K.stepSubobject fun (_ : ℤ) j => j) (antitone_stepSubobject₂ K) r p q n hr hn

/-- **The differentials of `spectralSequence₂` are induced by `d`.** This is the hypothesis `hδ`
of [Stacks, Tag 0130] for `spectralSequence₂` and `pageIso₂`. -/
lemma exists_delta₂ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ)
    (hp' : p' = p + r) (hq' : q' = q - r + 1) (hn' : n' = n + 1) :
    ∃ δ : (cycles₂ K r p n : C) ⟶ (cycles₂ K r p' n' : C),
      δ ≫ (cycles₂ K r p' n').arrow =
        (cycles₂ K r p n).arrow ≫ (K.total (ComplexShape.up ℤ)).d n n' ∧
      cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (pageIso₂ K r p q n hr hn).inv ≫
          ((spectralSequence₂ K).page r hr).d (p, q) (p', q') =
        δ ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
          (pageIso₂ K r p' q' n' hr (add_eq_of_indices hn hp' hq' hn')).inv := by
  subst hp' hq' hn' hn
  refine ⟨FilteredComplexSpectralSequence.deltaCycles _ _ r p (p + q),
    FilteredComplexSpectralSequence.deltaCycles_arrow _ _ r p (p + q), ?_⟩
  rw [FilteredComplexSpectralSequence.spectralSequence_d,
    FilteredComplexSpectralSequence.eIso_inv_rfl, Category.id_comp, ← Category.assoc,
    FilteredComplexSpectralSequence.π_comp_pageMap, Category.assoc]

omit [K.HasTotal (ComplexShape.up ℤ)] in
/-- `spectralSequence₂` is the second spectral sequence of a double complex as constructed by
`Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor`: the two differ only in how the
steps of the filtration are presented as subobjects of `Tot(K^{•,•})^n`. -/
lemma spectralSequence₂_eq
    [∀ (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
      M.HasTotal (ComplexShape.up ℤ)] :
    spectralSequence₂ K =
      (Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor C).obj K :=
  spectralSequence_congr
    (funext fun p => funext fun n => (K.mk_totalFiltration_ι_f _ _ _ p n).symm)
    (antitone_stepSubobject₂ K)
    (CochainComplex.filtrationSubobject_antitone K.totalFiltration₂)

variable {K} {L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [L.HasTotal (ComplexShape.up ℤ)]

/-- The morphism of second spectral sequences induced by a morphism of double complexes
([Stacks, Tag 012O]). -/
noncomputable abbrev spectralSequenceMap₂ (φ : K ⟶ L) :
    spectralSequence₂ K ⟶ spectralSequence₂ L :=
  FilteredComplexSpectralSequence.spectralSequenceMap
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) (exists_stepSubobject₂_le φ)
    (antitone_stepSubobject₂ K) (antitone_stepSubobject₂ L)

/-- `spectralSequenceMap₂ φ` is, on the classes of `Z_1^{p,q}`, the map induced by `Tot(φ)`. -/
lemma pageIso₂_spectralSequenceMap₂ (φ : K ⟶ L) (p q : ℤ) :
    cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
        (pageIso₂ K 1 p q (p + q) zero_le_one rfl).inv ≫
        ((spectralSequenceMap₂ φ).hom 1 zero_le_one).f (p, q) =
      cyclesMap₂ φ 1 p (p + q) ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
        (pageIso₂ L 1 p q (p + q) zero_le_one rfl).inv := by
  rw [FilteredComplexSpectralSequence.eIso_inv_rfl, FilteredComplexSpectralSequence.eIso_inv_rfl,
    Category.id_comp, Category.comp_id]
  exact FilteredComplexSpectralSequence.π_pageObjMap _ _ 1 p (p + q)

/-- **Naturality of `''E_1^{p,q} = H^q(K^{•,p})` in the double complex.** For the second spectral
sequence `spectralSequence₂` and the identification `pageIso₂` of its pages with the quotients
`Z_r^{p,q}/D_r^{p,q}`, a morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes induces a commuting
square between the first pages and `H^q_I(-)`. -/
theorem isoOnePageTotalFiltration₂_naturality_functor (φ : K ⟶ L) (p q : ℤ) :
    ((spectralSequenceMap₂ φ).hom 1 zero_le_one).f (p, q) ≫
        (isoOnePageTotalFiltration₂ L (spectralSequence₂ L) (pageIso₂ L)
          (exists_delta₂ L) p q).hom =
      (isoOnePageTotalFiltration₂ K (spectralSequence₂ K) (pageIso₂ K)
          (exists_delta₂ K) p q).hom ≫ (HomologicalComplex.homologyMap φ q).f p :=
  isoOnePageTotalFiltration₂_naturality _ _ (exists_delta₂ K) _ _ (exists_delta₂ L) φ _
    (pageIso₂_spectralSequenceMap₂ φ) p q

/-- **Naturality of `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))` in the double complex.** This is
[Stacks, Tag 0130] (6) made natural: for the second spectral sequence `spectralSequence₂` of a
double complex and the identification `pageIso₂` of its pages with `Z_r^{p,q}/D_r^{p,q}`, a
morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes induces a commuting square between the
second pages and `H^p_{II}(H^q_I(-))`. -/
theorem isoTwoPageTotalFiltration₂_naturality_functor (φ : K ⟶ L) (p q : ℤ) :
    ((spectralSequenceMap₂ φ).hom 2 zero_le_two).f (p, q) ≫
        (isoTwoPageTotalFiltration₂ L (spectralSequence₂ L) (pageIso₂ L)
          (exists_delta₂ L) p q).hom =
      (isoTwoPageTotalFiltration₂ K (spectralSequence₂ K) (pageIso₂ K)
          (exists_delta₂ K) p q).hom ≫
        HomologicalComplex.homologyMap (HomologicalComplex.homologyMap φ q) p :=
  isoTwoPageTotalFiltration₂_naturality _ _ (exists_delta₂ K) _ _ (exists_delta₂ L) φ _
    (pageIso₂_spectralSequenceMap₂ φ) p q

end Functorial

end HomologicalComplex₂

end
