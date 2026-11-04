module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Filtration

/-!
# Spectral sequences of double complexes: the pages

The identifications of the pages `E_0`, `E_1`, `E_2` of the spectral sequence of a double complex
filtered by an arbitrary weight (`isoOnePage`, `isoTwoPage`), the theorem
`exists_iso_pages_totalFiltration₁` for the first filtration, and the identifications of the pages
of the second filtration as data (`isoPagesTotalFiltration₂`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

section LineHomology

variable {D : Type*} [Category* D] [Abelian D]

/-- Multiplication by a unit, as an automorphism. -/
def unitIso (s : ℤˣ) (X : D) : X ≅ X where
  hom := s • 𝟙 X
  inv := s⁻¹ • 𝟙 X
  hom_inv_id := by simp [smul_smul]
  inv_hom_id := by simp [smul_smul]

/-- A line `k ↦ φ k` of slope `v` in a complex `X` of shape `up' v`, identified term by term with
a cochain complex `L` whose differential is rescaled by a unit `s`, has the short complexes of
`L`. -/
lemma lineScIso_comm₁₂ {v : ℤ × ℤ} (X : HomologicalComplex D (ComplexShape.up' v))
    (φ : ℤ → ℤ × ℤ) (L : CochainComplex D ℤ) (s : ℤˣ) (α : ∀ k, X.X (φ k) ≅ L.X k)
    (hα : ∀ k k', k' = k + 1 → X.d (φ k) (φ k') ≫ (α k').hom = (α k).hom ≫ (s • L.d k k'))
    (k : ℤ) :
    (α (k - 1) ≪≫ unitIso s _).hom ≫ L.d (k - 1) k = X.d (φ (k - 1)) (φ k) ≫ (α k).hom := by
  rw [Iso.trans_hom, Category.assoc, unitIso, Linear.units_smul_comp, Category.id_comp]
  exact (hα (k - 1) k (by omega)).symm

lemma lineScIso_comm₂₃ {v : ℤ × ℤ} (X : HomologicalComplex D (ComplexShape.up' v))
    (φ : ℤ → ℤ × ℤ) (L : CochainComplex D ℤ) (s : ℤˣ) (α : ∀ k, X.X (φ k) ≅ L.X k)
    (hα : ∀ k k', k' = k + 1 → X.d (φ k) (φ k') ≫ (α k').hom = (α k).hom ≫ (s • L.d k k'))
    (k : ℤ) :
    (α k).hom ≫ L.d k (k + 1) = X.d (φ k) (φ (k + 1)) ≫ (α (k + 1) ≪≫ unitIso s⁻¹ _).hom := by
  rw [Iso.trans_hom, unitIso, reassoc_of% hα k (k + 1) rfl]
  simp [smul_smul]

/-- A line `k ↦ φ k` of slope `v` in a complex `X` of shape `up' v`, identified term by term with
a cochain complex `L` whose differential is rescaled by a unit `s`, has the short complexes of
`L`. -/
noncomputable def lineScIso {v : ℤ × ℤ} (X : HomologicalComplex D (ComplexShape.up' v))
    (φ : ℤ → ℤ × ℤ) (hφ : ∀ k, φ k + v = φ (k + 1)) (L : CochainComplex D ℤ) (s : ℤˣ)
    (α : ∀ k, X.X (φ k) ≅ L.X k)
    (hα : ∀ k k', k' = k + 1 → X.d (φ k) (φ k') ≫ (α k').hom = (α k).hom ≫ (s • L.d k k'))
    (k : ℤ) : X.sc (φ k) ≅ L.sc k :=
  X.isoSc' (φ (k - 1)) (φ k) (φ (k + 1))
      ((ComplexShape.up' v).prev_eq' (by rw [ComplexShape.up'_Rel, hφ, sub_add_cancel]))
      ((ComplexShape.up' v).next_eq' (by rw [ComplexShape.up'_Rel, hφ])) ≪≫
    ShortComplex.isoMk (S₁ := X.sc' (φ (k - 1)) (φ k) (φ (k + 1)))
      (S₂ := L.sc' (k - 1) k (k + 1)) (α (k - 1) ≪≫ unitIso s _) (α k)
      (α (k + 1) ≪≫ unitIso s⁻¹ _) (lineScIso_comm₁₂ X φ L s α hα k)
      (lineScIso_comm₂₃ X φ L s α hα k) ≪≫
    (L.isoSc' (k - 1) k (k + 1) (by simp) (by simp)).symm

lemma lineScIso_hom_τ₂ {v : ℤ × ℤ} (X : HomologicalComplex D (ComplexShape.up' v))
    (φ : ℤ → ℤ × ℤ) (hφ : ∀ k, φ k + v = φ (k + 1)) (L : CochainComplex D ℤ) (s : ℤˣ)
    (α : ∀ k, X.X (φ k) ≅ L.X k)
    (hα : ∀ k k', k' = k + 1 → X.d (φ k) (φ k') ≫ (α k').hom = (α k).hom ≫ (s • L.d k k'))
    (k : ℤ) : (lineScIso X φ hφ L s α hα k).hom.τ₂ = (α k).hom := by
  dsimp [lineScIso]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- A short complex isomorphism sends the class of a cycle to the class of its image. -/
private lemma homologyπ_homologyMapIso_hom {A B : ShortComplex D} (e : A ≅ B) {W : D}
    (x : W ⟶ A.cycles) (y : W ⟶ B.cycles) (h : x ≫ A.iCycles ≫ e.hom.τ₂ = y ≫ B.iCycles) :
    x ≫ A.homologyπ ≫ (ShortComplex.homologyMapIso e).hom = y ≫ B.homologyπ := by
  rw [ShortComplex.homologyMapIso_hom, ShortComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono B.iCycles, Category.assoc, ShortComplex.cyclesMap_i, h]

end LineHomology

section Components

variable {K}

/-- The summand `K^{a,b}` of `Tot^n` has no component in `K^{i',j'}` of `Tot^{n'}` under the
differential if `a ∉ {i' - 1, i'}`. -/
private lemma ι_total_d_totalSummandπ_of_ne (a b n i' j' : ℤ) (hab : a + b = n)
    (h' : i' + j' = n + 1) (h₁ : a + 1 ≠ i') (h₂ : a ≠ i') :
    K.ιTotal (ComplexShape.up ℤ) a b n hab ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1) ≫
      totalSummandπ i' j' (n + 1) h' = 0 := by
  rw [ι_total_d_assoc, Preadditive.add_comp, Category.assoc, Linear.units_smul_comp,
    Category.assoc, ι_totalSummandπ_of_ne _ _ _ _ _ _ _ h₁, ι_totalSummandπ_of_ne _ _ _ _ _ _ _ h₂,
    comp_zero, comp_zero, smul_zero, add_zero]

/-- The component `K^{p,q} ⟶ K^{p,q+1}` of the differential of `Tot` on `F_I^p` is `(-1)^p d_2`. -/
private lemma totalProjector₁_d_totalSummandπ (p q n n' : ℤ) (h : p + q = n)
    (h' : p + (q + 1) = n') :
    K.totalProjector (fun a (_ : ℤ) => p ≤ a) n ≫ (K.total (ComplexShape.up ℤ)).d n n' ≫
        totalSummandπ p (q + 1) n' h' =
      totalSummandπ p q n h ≫ (p.negOnePow • (K.X p).d q (q + 1)) := by
  subst h
  obtain rfl : n' = p + q + 1 := by omega
  refine HomologicalComplex₂.total.hom_ext _ fun a b hab => ?_
  have hab' : a + b = p + q := hab
  rw [ι_totalProjector_assoc]
  by_cases ha : a = p
  · subst ha
    obtain rfl : b = q := by omega
    rw [ite_eq_left le_rfl, ι_total_d_assoc, Preadditive.add_comp, Category.assoc,
      ι_totalSummandπ_of_ne _ _ _ _ _ _ _ (by omega), comp_zero, zero_add,
      Linear.units_smul_comp, Category.assoc, ι_totalSummandπ, Category.comp_id,
      ι_totalSummandπ_assoc]
  · rw [ι_totalSummandπ_of_ne_assoc _ _ _ _ _ _ hab' ha, zero_comp]
    split_ifs with hp
    exacts [ι_total_d_totalSummandπ_of_ne _ _ _ _ _ hab' (by omega) (by omega) ha, zero_comp]

/-- The component `K^{q,p} ⟶ K^{q+1,p}` of the differential of `Tot` on `F_{II}^p` is `d_1`. -/
private lemma totalProjector₂_d_totalSummandπ (p q n n' : ℤ) (h : q + p = n)
    (h' : q + 1 + p = n') :
    K.totalProjector (fun (_ : ℤ) b => p ≤ b) n ≫ (K.total (ComplexShape.up ℤ)).d n n' ≫
        totalSummandπ (q + 1) p n' h' =
      totalSummandπ q p n h ≫ (K.d q (q + 1)).f p := by
  obtain rfl : n = p + q := by omega
  obtain rfl : n' = p + q + 1 := by omega
  refine HomologicalComplex₂.total.hom_ext _ fun a b hab => ?_
  have hab' : a + b = p + q := hab
  rw [ι_totalProjector_assoc]
  by_cases ha : a = q
  · subst ha
    obtain rfl : b = p := by omega
    rw [ite_eq_left le_rfl, ι_total_d_assoc, Preadditive.add_comp, Category.assoc,
      ι_totalSummandπ, Category.comp_id, Linear.units_smul_comp, Category.assoc,
      ι_totalSummandπ_of_ne _ _ _ _ _ _ _ (by omega), comp_zero, smul_zero, add_zero,
      ι_totalSummandπ_assoc]
  · rw [ι_totalSummandπ_of_ne_assoc _ _ _ _ _ _ hab' ha, zero_comp]
    split_ifs with hp
    exacts [ι_total_d_totalSummandπ_of_ne _ _ _ _ _ hab' (by omega) (by omega) (by omega),
      zero_comp]

end Components

section Rows

omit [K.HasTotal (ComplexShape.up ℤ)]

/-- The row `K^{•,p}` of a double complex, with differential `d_1`. -/
abbrev row (p : ℤ) : CochainComplex C ℤ where
  X q := (K.X q).X p
  d q q' := (K.d q q').f p
  shape q q' h := by rw [K.shape q q' h, HomologicalComplex.zero_f]
  d_comp_d' q q' q'' _ _ := by
    rw [← HomologicalComplex.comp_f, K.d_comp_d, HomologicalComplex.zero_f]

/-- The morphism of rows `K^{•,p} ⟶ K^{•,p'}` given by `d_2`. -/
abbrev rowMap (p p' : ℤ) : K.row p ⟶ K.row p' where
  f q := (K.X q).d p p'
  comm' q q' _ := ((K.d q q').comm p p').symm

end Rows

section Cycles


variable {K}

lemma stepSubobject_factors_ιTotal (w : ℤ → ℤ → ℤ) (p i j n : ℤ) (hij : i + j = n)
    (hp : p ≤ w i j) : (K.stepSubobject w p n).Factors (K.ιTotal (ComplexShape.up ℤ) i j n hij) :=
  Subobject.factors_of_le _ (K.imageSubobject_ιTotal_le_totalProjector _ i j n hij hp)
    (by simpa using imageSubobject_factors_comp_self (K.ιTotal (ComplexShape.up ℤ) i j n hij) (𝟙 _))

/-- The differential of `Tot` on a cycle of the column `K^{p,•}`. -/
private lemma iCycles_ιTotal_d (p q n' : ℤ) (h : p + 1 + q = n') :
    (K.X p).iCycles q ≫ K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
        (K.total (ComplexShape.up ℤ)).d (p + q) n' =
      HomologicalComplex.cyclesMap (K.d p (p + 1)) q ≫ (K.X (p + 1)).iCycles q ≫
        K.ιTotal (ComplexShape.up ℤ) (p + 1) q n' h := by
  obtain rfl : n' = p + q + 1 := by omega
  rw [ι_total_d, Preadditive.comp_add, Linear.comp_units_smul,
    ← Category.assoc ((K.X p).iCycles q) ((K.X p).d q (q + 1)), HomologicalComplex.iCycles_d,
    zero_comp, smul_zero, add_zero, ← Category.assoc, ← Category.assoc,
    HomologicalComplex.cyclesMap_i]

/-- The differential of `Tot` on a cycle of the row `K^{•,p}`. -/
lemma iCycles_row_ιTotal_d (p q n' : ℤ) (h : q + (p + 1) = n') :
    (K.row p).iCycles q ≫ K.ιTotal (ComplexShape.up ℤ) q p (p + q) (by dsimp; omega) ≫
        (K.total (ComplexShape.up ℤ)).d (p + q) n' =
      (q.negOnePow • HomologicalComplex.cyclesMap (K.rowMap p (p + 1)) q) ≫
        (K.row (p + 1)).iCycles q ≫ K.ιTotal (ComplexShape.up ℤ) q (p + 1) n' h := by
  obtain rfl : n' = p + q + 1 := by omega
  rw [ι_total_d, Preadditive.comp_add,
    ← Category.assoc ((K.row p).iCycles q) ((K.d q (q + 1)).f p),
    (K.row p).iCycles_d, zero_comp, zero_add, Linear.comp_units_smul,
    Linear.units_smul_comp, ← Category.assoc, ← Category.assoc,
    HomologicalComplex.cyclesMap_i]

end Cycles

/-- The arithmetic of the bidegrees of the differential `d_r`: the total degree `n'` of the target
of `d_r^{p,q}` is the sum of the bidegree `(p', q')` of that target. Named rather than proved by
`omega` inline, because an `omega` call inside the *type* of a section variable is turned into an
anonymous module-private auxiliary constant, which a public declaration may not mention. -/
lemma add_eq_of_indices {r p q n p' q' n' : ℤ} (hn : n = p + q) (hp' : p' = p + r)
    (hq' : q' = q - r + 1) (hn' : n' = n + 1) : n' = p' + q' := by omega

section Pages


variable (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1))
  (E : CohomologicalSpectralSequence C 0)
  (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right :
      FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ)) (stepSubobject K w)
          r p n ⊓
        FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) r
            p n ≤
      FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) r p
          n)))
  (hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ) (hp' : p' = p + r)
    (hq' : q' = q - r + 1) (hn' : n' = n + 1),
    ∃ δ : (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w)
        r p n : C) ⟶
        (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) r
            p' n' : C),
      δ ≫ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w)
          r p' n').arrow =
        (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) r
            p n).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n n' ∧
      cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e r p q n hr hn).inv ≫
          (E.page r hr).d (p, q) (p', q') =
        δ ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
          (e r p' q' n' hr (add_eq_of_indices hn hp' hq' hn')).inv)

include h₁ h₂ hδ in
/-- **The zeroth differential.** Under the identifications of `E_0` with the summands of weight
`p`, the zeroth differential is the component `d` of the differential of `Tot` between them. -/
private lemma zeroPage_d (p q q' n n' : ℤ) (hn : n = p + q) (hq' : q' = q + 1) (hn' : n' = p + q')
    (i j i' j' : ℤ) (hij : i + j = n) (hp : w i j = p)
    (hw : ∀ a b, a + b = n → w a b = p → a = i) (hij' : i' + j' = n') (hp' : w i' j' = p)
    (hw' : ∀ a b, a + b = n' → w a b = p → a = i') (d : (K.X i).X j ⟶ (K.X i').X j')
    (hd : K.totalProjector (fun a b => p ≤ w a b) n ≫ (K.total (ComplexShape.up ℤ)).d n n' ≫
      totalSummandπ i' j' n' hij' = totalSummandπ i j n hij ≫ d) :
    (E.page 0 le_rfl).d (p, q) (p, q') ≫
        (e 0 p q' n' le_rfl hn' ≪≫ zeroPageObjectIso K w h₁ h₂ p n' i' j' hij' hp' hw').hom =
      (e 0 p q n le_rfl hn ≪≫ zeroPageObjectIso K w h₁ h₂ p n i j hij hp hw).hom ≫ d := by
  obtain ⟨δ, hδ₁, hδ₂⟩ := hδ 0 p q n le_rfl hn p q' n' (by omega) (by omega) (by omega)
  have hA : Subobject.mk
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
          n).arrow =
      imageSubobject (K.totalProjector (fun a b => p ≤ w a b) n) := by
    rw [Subobject.mk_arrow, cycles_zero_stepSubobject K w h₁ h₂]
  rw [Iso.trans_hom, Iso.trans_hom, ← cancel_epi (e 0 p q n le_rfl hn).inv,
    ← cancel_epi (cokernel.π _), ← cancel_epi (imageRetraction _ _ hA)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hδ₂, Iso.inv_hom_id_assoc, π_zeroPageObjectIso_hom_assoc,
    π_zeroPageObjectIso_hom, reassoc_of% hδ₁, imageRetraction_arrow_assoc,
    imageRetraction_arrow_assoc, hd, totalProjector_totalSummandπ_assoc _ _ _ _ _ (by omega)]

include h₁ h₂ hδ in
/-- **The first page.** If a line `q ↦ E_0^{p,q}` of the zeroth page is identified with a cochain
complex `L`, differentials up to a unit, then `E_1^{p,q} = H^q(L)`, by an isomorphism sending the
class of an element `c` of `Z_1^{p,q}` representing a cycle of `L` to the class of that cycle. -/
lemma exists_iso_onePage (p : ℤ) (L : CochainComplex C ℤ) (s : ℤˣ)
    (α : ∀ q, (E.page 0 le_rfl).X (p, q) ≅ L.X q)
    (hα : ∀ q q', q' = q + 1 →
      (E.page 0 le_rfl).d (p, q) (p, q') ≫ (α q').hom = (α q).hom ≫ (s • L.d q q'))
    (c : ∀ q, L.cycles q ⟶
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 1 p
          (p + q) : C))
    (c' : ∀ q, L.cycles q ⟶
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
          (p + q) : C))
    (hc : ∀ q, c' q ≫
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
          (p + q)).arrow =
        c q ≫
          (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w)
              1 p (p + q)).arrow)
    (hc' : ∀ q, c' q ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 0 p q (p + q) le_rfl rfl).inv ≫ (α q).hom = L.iCycles q) :
    ∃ β : ∀ q, (E.page 1 zero_le_one).X (p, q) ≅ L.homology q,
      ∀ q, c q ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
        (e 1 p q (p + q) zero_le_one rfl).inv ≫ (β q).hom = L.homologyπ q := by
  choose ψ hψ using fun q => CochainComplex.exists_iso_homology_page_of_mem_cycles
    (K.totalFiltration w h₁ h₂) (stepSubobject K w) (stepSubobject_eq K w h₁ h₂) _
    (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) E e
    (fun r p q n hr hn => hδ r p q n hr hn _ _ _ rfl rfl rfl) 0 1 p q (p + q) le_rfl rfl rfl
  have hφ : ∀ q : ℤ, (p, q) + ((0 : ℤ), 1 - 0) = (p, q + 1) :=
    fun q => Prod.ext (add_zero p) (by rw [Prod.snd_add, sub_zero])
  let sc := lineScIso (E.page 0 le_rfl) (fun q => (p, q)) hφ L s α hα
  refine ⟨fun q => (ψ q).symm ≪≫ ShortComplex.homologyMapIso (sc q), fun q => ?_⟩
  have h : (sc q).hom.τ₂ ≫ (sc q).inv.τ₂ = 𝟙 _ := by
    rw [← ShortComplex.comp_τ₂, Iso.hom_inv_id, ShortComplex.id_τ₂]
  have hτ : (sc q).inv.τ₂ = (α q).inv :=
    (Iso.inv_ext (f := α q) (g := (sc q).inv.τ₂) (by
      rw [← lineScIso_hom_τ₂ (E.page 0 le_rfl) (fun q => (p, q)) hφ L s α hα q]
      exact h)).symm
  have e₁ : ShortComplex.cyclesMap (sc q).inv ≫ (E.page 0 le_rfl).iCycles (p, q) =
      L.iCycles q ≫ (α q).inv :=
    (ShortComplex.cyclesMap_i (sc q).inv).trans (congrArg (L.iCycles q ≫ ·) hτ)
  have e₂ : c' q ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 0 p q (p + q) le_rfl rfl).inv = L.iCycles q ≫ (α q).inv := by
    rw [← cancel_mono (α q).hom, Category.assoc, Category.assoc, Category.assoc, hc' q,
      Iso.inv_hom_id, Category.comp_id]
  have hcl := hψ q (ShortComplex.cyclesMap (sc q).inv) (c q) (c' q) (hc q) (e₁.trans e₂.symm)
  have e₄ : ShortComplex.cyclesMap (sc q).inv ≫ (E.page 0 le_rfl).homologyπ (p, q) ≫
      (ShortComplex.homologyMapIso (sc q)).hom = L.homologyπ q :=
    (homologyπ_homologyMapIso_hom (sc q) _ (𝟙 _) (by
      rw [Category.id_comp, ← Category.assoc, ShortComplex.cyclesMap_i, Category.assoc,
        ← ShortComplex.comp_τ₂, Iso.inv_hom_id, ShortComplex.id_τ₂, Category.comp_id])).trans
      (Category.id_comp _)
  -- assemble, the page and the line being related through `Mathlib`'s `sc` spelling
  have hψ' : (ShortComplex.cyclesMap (sc q).inv ≫ (E.page 0 le_rfl).homologyπ (p, q) ≫
      (ψ q).hom) ≫ (ψ q).inv =
      ShortComplex.cyclesMap (sc q).inv ≫ (E.page 0 le_rfl).homologyπ (p, q) :=
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (ψ q).hom_inv_id).trans (Category.comp_id _))))
  exact (congrArg (c q ≫ ·) (Category.assoc _ _ _).symm).trans ((Category.assoc _ _ _).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => (t ≫ (ψ q).inv) ≫ (ShortComplex.homologyMapIso (sc q)).hom)
        hcl.symm).trans
      ((congrArg (· ≫ (ShortComplex.homologyMapIso (sc q)).hom) hψ').trans
        ((Category.assoc _ _ _).trans e₄)))))

section OnePage

variable (p : ℤ) (L : CochainComplex C ℤ) (s : ℤˣ)
  (α : ∀ q, (E.page 0 le_rfl).X (p, q) ≅ L.X q)
  (hα : ∀ q q', q' = q + 1 →
    (E.page 0 le_rfl).d (p, q) (p, q') ≫ (α q').hom = (α q).hom ≫ (s • L.d q q'))
  (c : ∀ q, L.cycles q ⟶
    (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 1 p
        (p + q) : C))
  (c' : ∀ q, L.cycles q ⟶
    (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
        (p + q) : C))
  (hc : ∀ q, c' q ≫
    (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 0 p
        (p + q)).arrow =
      c q ≫
        (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w)
            1 p (p + q)).arrow)
  (hc' : ∀ q, c' q ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
    (e 0 p q (p + q) le_rfl rfl).inv ≫ (α q).hom = L.iCycles q)

include h₁ h₂ hδ hα hc hc' in
/-- **The first page, as a construction.** The isomorphism `E_1^{p,q} ≅ H^q(L)` whose existence
`exists_iso_onePage` asserts, as data rather than as an existence statement; it is pinned down
by `isoOnePage_spec`, which determines it uniquely. -/
noncomputable def isoOnePage (q : ℤ) : (E.page 1 zero_le_one).X (p, q) ≅ L.homology q :=
  (exists_iso_onePage K w h₁ h₂ E e hδ p L s α hα c c' hc hc').choose q

/-- **The first page identification, on representatives.** `isoOnePage` sends the class of an
element `c q` of `Z_1^{p,q}` representing a cycle of `L` to the class of that cycle. The composite
on the left is an epimorphism, so this property determines `isoOnePage` uniquely. -/
lemma isoOnePage_spec (q : ℤ) :
    c q ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
        (e 1 p q (p + q) zero_le_one rfl).inv ≫
          (isoOnePage K w h₁ h₂ E e hδ p L s α hα c c' hc hc' q).hom =
      L.homologyπ q :=
  (exists_iso_onePage K w h₁ h₂ E e hδ p L s α hα c c' hc hc').choose_spec q

end OnePage

include hδ in
/-- **The first differential, on representatives.** If classes of elements `c` of `Z_1` represent
the elements of `H` and `H'`, and `d` carries `c` to `f` followed by `c'`, then `d_1` is the map
`h` induced by `f`. -/
private lemma onePage_d (p p' q : ℤ) (hp' : p' = p + 1) {X Y H H' : C} (π : X ⟶ H) [Epi π]
    (π' : Y ⟶ H') (f : X ⟶ Y) (h : H ⟶ H') (hf : π ≫ h = f ≫ π')
    (β : (E.page 1 zero_le_one).X (p, q) ≅ H) (β' : (E.page 1 zero_le_one).X (p', q) ≅ H')
    (c : X ⟶ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K
        w) 1 p (p + q) : C))
    (c' : Y ⟶
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 1
          p' (p' + q) : C))
    (hc : c ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p q (p + q) zero_le_one rfl).inv ≫ β.hom = π)
    (hc' : c' ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p' q (p' + q) zero_le_one rfl).inv ≫ β'.hom = π')
    (hdc : c ≫
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 1 p
          (p + q)).arrow ≫
        (K.total (ComplexShape.up ℤ)).d (p + q) (p' + q) = f ≫ c' ≫
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 1
          p' (p' + q)).arrow) :
    (E.page 1 zero_le_one).d (p, q) (p', q) ≫ β'.hom = β.hom ≫ h := by
  obtain ⟨δ, hδ₁, hδ₂⟩ := hδ 1 p q (p + q) zero_le_one rfl p' q (p' + q) hp' (by omega)
    (by omega)
  have hδc : c ≫ δ = f ≫ c' := by
    rw [← cancel_mono
      (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ)) (stepSubobject K w) 1
          p' (p' + q)).arrow,
      Category.assoc, hδ₁, hdc, Category.assoc]
  have ha : (c ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p q (p + q) zero_le_one rfl).inv) = π ≫ β.inv := by
    rw [← hc, Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : Epi (c ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p q (p + q) zero_le_one rfl).inv) := by
    rw [ha]
    infer_instance
  rw [← cancel_epi (c ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
      (e 1 p q (p + q) zero_le_one rfl).inv), Category.assoc, Category.assoc, reassoc_of% hδ₂,
    reassoc_of% hδc, hc', ← hf, ← hc]
  simp

/-- **The second page, as a construction.** If a line `p ↦ E_1^{p,q}` of the first page is
identified with a cochain complex `M`, differentials up to a unit, then `E_2^{p,q} ≅ H^p(M)`: the
page-turning isomorphism of `E` followed by the homology of that identification of lines. -/
noncomputable def isoTwoPage (q : ℤ) (M : CochainComplex C ℤ) (s : ℤˣ)
    (β : ∀ p, (E.page 1 zero_le_one).X (p, q) ≅ M.X p)
    (hβ : ∀ p p', p' = p + 1 →
      (E.page 1 zero_le_one).d (p, q) (p', q) ≫ (β p').hom = (β p).hom ≫ (s • M.d p p'))
    (p : ℤ) : (E.page 2 zero_le_two).X (p, q) ≅ M.homology p :=
  (E.iso 1 2 (p, q) one_add_one_eq_two zero_le_one).symm ≪≫ ShortComplex.homologyMapIso
    (lineScIso (E.page 1 zero_le_one) (fun p => (p, q))
      (fun p => Prod.ext rfl (by rw [Prod.snd_add, sub_self, add_zero])) M s β hβ p)

/-- **`isoTwoPage` after the page turn.** Composed with the page-turning isomorphism of `E`,
`isoTwoPage` is the homology of the identification of the line `p ↦ E_1^{p,q}` with `M`. Stated
this way rather than as an equality of isomorphisms: the two factors of `isoTwoPage` meet at
`H^{(p,q)}(E_1)`, which is the homology of `(E_1).sc (p, q)` by definition but not by
notation. -/
lemma iso_hom_comp_isoTwoPage_hom (q : ℤ) (M : CochainComplex C ℤ) (s : ℤˣ)
    (β : ∀ p, (E.page 1 zero_le_one).X (p, q) ≅ M.X p)
    (hβ : ∀ p p', p' = p + 1 →
      (E.page 1 zero_le_one).d (p, q) (p', q) ≫ (β p').hom = (β p).hom ≫ (s • M.d p p'))
    (p : ℤ) :
    (E.iso 1 2 (p, q) one_add_one_eq_two zero_le_one).hom ≫ (isoTwoPage E q M s β hβ p).hom =
      (ShortComplex.homologyMapIso
        (lineScIso (E.page 1 zero_le_one) (fun p => (p, q))
          (fun p => Prod.ext rfl (by rw [Prod.snd_add, sub_self, add_zero])) M s β hβ p)).hom :=
  Iso.hom_inv_id_assoc _ _

/-- **The second page.** If a line `p ↦ E_1^{p,q}` of the first page is identified with a
cochain complex `M`, differentials up to a unit, then `E_2^{p,q} ≅ H^p(M)`. -/
private lemma nonempty_iso_twoPage (q : ℤ) (M : CochainComplex C ℤ) (s : ℤˣ)
    (β : ∀ p, (E.page 1 zero_le_one).X (p, q) ≅ M.X p)
    (hβ : ∀ p p', p' = p + 1 →
      (E.page 1 zero_le_one).d (p, q) (p', q) ≫ (β p').hom = (β p).hom ≫ (s • M.d p p'))
    (p : ℤ) : Nonempty ((E.page 2 zero_le_two).X (p, q) ≅ M.homology p) :=
  ⟨isoTwoPage E q M s β hβ p⟩

end Pages

section FirstFiltration


variable {K}

/-- A cycle of the column `K^{p,•}` in degree `q`, as an element of `Z_r^{p,q}` of the first
filtration for `r ≤ 1`. -/
private noncomputable def columnCycles (r p q : ℤ) (hr : r ≤ 1) :
    (K.X p).cycles q ⟶ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun i (_ : ℤ) => i) r p (p + q) : C) :=
  Subobject.factorThru _ ((K.X p).iCycles q ≫ K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl) (by
    rw [FilteredComplexSpectralSequence.cycles, Subobject.inf_factors, pullback_factors_iff]
    refine ⟨Subobject.factors_of_factors_right _
      (stepSubobject_factors_ιTotal _ p p q _ rfl le_rfl), ?_⟩
    rw [Category.assoc, iCycles_ιTotal_d p q _ (by omega)]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_of_factors_right _
      (stepSubobject_factors_ιTotal _ (p + r) (p + 1) q _ _ (by omega))))

@[reassoc]
private lemma columnCycles_arrow (r p q : ℤ) (hr : r ≤ 1) :
    columnCycles r p q hr ≫ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun i (_ : ℤ) => i) r p (p + q)).arrow =
      (K.X p).iCycles q ≫ K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl :=
  Subobject.factorThru_arrow _ _ _

variable (K)

/-- **Stacks 0130, the first filtration.** Let `('E_r, 'd_r)` be the spectral sequence of the total
complex of a double complex `K^{•,•}` filtered by the first coordinate, presented as in
[Stacks, Tag 012M] by its pages `Z_r^{p,q}/D_r^{p,q}` and its differentials induced by `d`. Then
1. `'E_0^{p,q} = K^{p,q}` with `'d_0^{p,q} = (-1)^p d_2^{p,q}`;
3. `'E_1^{p,q} = H^q(K^{p,•})` with `'d_1^{p,q} = H^q(d_1^{p,•})`;
5. `'E_2^{p,q} = H^p_I(H^q_{II}(K^{•,•}))`, the cohomology in degree `p` of the complex
   `p ↦ H^q(K^{p,•})`.

That the filtration `F` this is stated for really is `F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j}`
is the companion statement `isLeast_totalFiltration₁`, which shares the parameters `F` and `hF`
with this one; the two together are the content of [Stacks, Tag 0130] for the first filtration. -/
@[stacks 0130 "(1), (3) and (5)"]
public theorem exists_iso_pages_totalFiltration₁
    (F : ∀ (_p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.totalFiltration₁.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hZ : ∀ r p n : ℤ, Z r p n = F p n ⊓
      (Subobject.pullback ((K.total (ComplexShape.up ℤ)).d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» ((K.total (ComplexShape.up ℤ)).d (n - 1) n)).obj
        (Z (r - 1) (p - r + 1) (n - 1)))
    (E : CohomologicalSpectralSequence C 0)
    (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
    (hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
      ∃ δ : (Z r p n : C) ⟶ (Z r (p + r) (n + 1) : C),
        δ ≫ (Z r (p + r) (n + 1)).arrow =
          (Z r p n).arrow ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1) ∧
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
            (e r p q n hr hn).inv ≫ (E.page r hr).d (p, q) (p + r, q - r + 1) =
          δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
              D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
            (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) :
    (∃ α : ∀ p q : ℤ, (E.page 0 le_rfl).X (p, q) ≅ (K.X p).X q,
      ∀ p q : ℤ, (E.page 0 le_rfl).d (p, q) (p, q + 1) ≫ (α p (q + 1)).hom =
        (α p q).hom ≫ (p.negOnePow • (K.X p).d q (q + 1))) ∧
    (∃ β : ∀ p q : ℤ, (E.page 1 zero_le_one).X (p, q) ≅ (K.X p).homology q,
      ∀ p q : ℤ, (E.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
        (β p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p + 1)) q) ∧
    ∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
      (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology p) := by
  have h₁ : ∀ i j : ℤ, (fun i (_ : ℤ) => i) i j ≤ (fun i (_ : ℤ) => i) (i + 1) j :=
    fun i _ => by dsimp only; omega
  have h₂ : ∀ i j : ℤ, (fun i (_ : ℤ) => i) i j ≤ (fun i (_ : ℤ) => i) i (j + 1) :=
    fun _ _ => le_rfl
  have hF' : F = K.stepSubobject fun i (_ : ℤ) => i := by
    funext p n
    rw [hF, K.mk_totalFiltration_ι_f]
  subst hF'
  have hZ' : Z = FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun i (_ : ℤ) => i) := by
    funext r p n
    rw [hZ, FilteredComplexSpectralSequence.cycles]
  subst hZ'
  have hD' : D = FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun i (_ : ℤ) => i) := by
    funext r p n
    rw [hD, FilteredComplexSpectralSequence.boundaries]
  subst hD'
  have hδ' : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ) (hp' : p' = p + r)
      (hq' : q' = q - r + 1) (hn' : n' = n + 1),
      ∃ δ : (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun i (_ : ℤ) => i) r p n : C) ⟶
          (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
            (K.stepSubobject fun i (_ : ℤ) => i) r p' n' : C),
        δ ≫ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
            (K.stepSubobject fun i (_ : ℤ) => i) r p' n').arrow =
          (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
            (K.stepSubobject fun i (_ : ℤ) => i) r p n).arrow ≫
            (K.total (ComplexShape.up ℤ)).d n n' ∧
        cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e r p q n hr hn).inv ≫
            (E.page r hr).d (p, q) (p', q') =
          δ ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
            (e r p' q' n' hr (by omega)).inv := by
    rintro r p q n hr hn _ _ _ rfl rfl rfl
    exact hδ r p q n hr hn
  -- the zeroth page
  let α : ∀ p q : ℤ, (E.page 0 le_rfl).X (p, q) ≅ (K.X p).X q := fun p q =>
    e 0 p q (p + q) le_rfl rfl ≪≫
      K.zeroPageObjectIso _ h₁ h₂ p (p + q) p q rfl rfl fun _ _ _ ha => ha
  have hα : ∀ p q q' : ℤ, q' = q + 1 → (E.page 0 le_rfl).d (p, q) (p, q') ≫ (α p q').hom =
      (α p q).hom ≫ (p.negOnePow • (K.X p).d q q') := by
    rintro p q _ rfl
    exact zeroPage_d K _ h₁ h₂ E e hδ' p q (q + 1) (p + q) (p + (q + 1)) rfl rfl rfl p q p (q + 1)
      rfl rfl (fun _ _ _ ha => ha) rfl rfl (fun _ _ _ ha => ha) _
      (totalProjector₁_d_totalSummandπ p q (p + q) (p + (q + 1)) rfl rfl)
  -- the first page
  have hc' : ∀ p q : ℤ, columnCycles 0 p q zero_le_one ≫
      cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e 0 p q (p + q) le_rfl rfl).inv ≫
        (α p q).hom = (K.X p).iCycles q := by
    intro p q
    rw [Iso.trans_hom, Iso.inv_hom_id_assoc, π_zeroPageObjectIso_hom,
      columnCycles_arrow_assoc, ι_totalSummandπ, Category.comp_id]
  choose β hβ using fun p => exists_iso_onePage K _ h₁ h₂ E e hδ' p (K.X p) p.negOnePow
    (α p) (hα p) (fun q => columnCycles 1 p q le_rfl) (fun q => columnCycles 0 p q zero_le_one)
    (fun q => by rw [columnCycles_arrow, columnCycles_arrow]) (hc' p)
  have hβd : ∀ p q : ℤ, (E.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
      (β p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p + 1)) q := fun p q =>
    onePage_d K _ E e hδ' p (p + 1) q rfl ((K.X p).homologyπ q) ((K.X (p + 1)).homologyπ q)
      (HomologicalComplex.cyclesMap (K.d p (p + 1)) q) _
      (HomologicalComplex.homologyπ_naturality _ _) (β p q) (β (p + 1) q)
      (columnCycles 1 p q le_rfl) (columnCycles 1 (p + 1) q le_rfl) (hβ p q) (hβ (p + 1) q)
      (by rw [columnCycles_arrow_assoc, columnCycles_arrow, iCycles_ιTotal_d])
  refine ⟨⟨α, fun p q => hα p q (q + 1) rfl⟩, ⟨β, hβd⟩, fun p q => ?_⟩
  -- the second page
  exact nonempty_iso_twoPage E q _ 1 (fun p => β p q) (fun p p' hp' => by
    subst hp'
    rw [one_smul]
    exact hβd p q) p

end FirstFiltration

section SecondFiltration


variable {K}

/-- A cycle of the row `K^{•,p}` in degree `q`, as an element of `Z_r^{p,q}` of the second
filtration for `r ≤ 1`. -/
noncomputable def rowCycles (r p q : ℤ) (hr : r ≤ 1) :
    (K.row p).cycles q ⟶ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun (_ : ℤ) j => j) r p (p + q) : C) :=
  Subobject.factorThru _ ((K.row p).iCycles q ≫
    K.ιTotal (ComplexShape.up ℤ) q p (p + q) (by dsimp; omega)) (by
    rw [FilteredComplexSpectralSequence.cycles, Subobject.inf_factors, pullback_factors_iff]
    refine ⟨Subobject.factors_of_factors_right _
      (stepSubobject_factors_ιTotal _ p q p _ _ le_rfl), ?_⟩
    rw [Category.assoc, iCycles_row_ιTotal_d p q _ (by omega)]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_of_factors_right _
      (stepSubobject_factors_ιTotal _ (p + r) q (p + 1) _ _ (by omega))))

@[reassoc]
lemma rowCycles_arrow (r p q : ℤ) (hr : r ≤ 1) :
    rowCycles r p q hr ≫ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun (_ : ℤ) j => j) r p (p + q)).arrow =
      (K.row p).iCycles q ≫ K.ιTotal (ComplexShape.up ℤ) q p (p + q) (by dsimp; omega) :=
  Subobject.factorThru_arrow _ _ _

/-- The cohomology of the row `K^{•,p}` in degree `q` is the `p`-th term of `H^q_I(K^{•,•})`. -/
noncomputable def rowHomologyIso (p q : ℤ) :
    (K.row p).homology q ≅ (K.homology q).X p :=
  (K.sc q).mapHomologyIso (HomologicalComplex.eval C (ComplexShape.up ℤ) p)

omit [K.HasTotal (ComplexShape.up ℤ)] in
/-- The map on the cohomology of the rows induced by `d_2` is the differential of the complex
`H^q_I(K^{•,•})`. -/
private lemma homologyMap_rowMap (p p' q : ℤ) :
    HomologicalComplex.homologyMap (K.rowMap p p') q ≫ (rowHomologyIso p' q).hom =
      (rowHomologyIso p q).hom ≫ (K.homology q).d p p' :=
  (congrArg (· ≫ _) (ShortComplex.homologyMap_mapNatTrans (K.sc q)
      (HomologicalComplex.dNatTrans C (ComplexShape.up ℤ) p p'))).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _)))))

variable (K)

section DefForm

/-! ### The identifications of the pages as data

The three identifications asserted by `exists_iso_pages_totalFiltration₂` below, as `def`s.  The
filtration is spelled out directly as `K.stepSubobject fun (_ : ℤ) j => j`, which is the form the
hypotheses `hF`, `hZ`, `hD` of that theorem reduce its data to. -/

variable (E : CohomologicalSpectralSequence C 0)
  (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right :
      FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun (_ : ℤ) j => j) r p n ⊓
        FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun (_ : ℤ) j => j) r p n ≤
      FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
        (K.stepSubobject fun (_ : ℤ) j => j) r p n)))
  (hδ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ) (hp' : p' = p + r)
    (hq' : q' = q - r + 1) (hn' : n' = n + 1),
    ∃ δ : (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
        (K.stepSubobject fun (_ : ℤ) j => j) r p n : C) ⟶
        (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun (_ : ℤ) j => j) r p' n' : C),
      δ ≫ (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun (_ : ℤ) j => j) r p' n').arrow =
        (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun (_ : ℤ) j => j) r p n).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n n' ∧
      cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e r p q n hr hn).inv ≫
          (E.page r hr).d (p, q) (p', q') =
        δ ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
          (e r p' q' n' hr (add_eq_of_indices hn hp' hq' hn')).inv)

/-- **Stacks 0130 (2), as a construction.** The identification `''E_0^{p,q} = K^{q,p}` of the
zeroth page of the spectral sequence of the second filtration. -/
noncomputable def isoZeroPageTotalFiltration₂ (p q : ℤ) :
    (E.page 0 le_rfl).X (p, q) ≅ (K.X q).X p :=
  e 0 p q (p + q) le_rfl rfl ≪≫
    K.zeroPageObjectIso (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
      (fun _ _ => Int.le_add_one le_rfl) p (p + q) q p (Int.add_comm q p) rfl
      fun _ _ _ _ => by omega

/-- `isoZeroPageTotalFiltration₂` unfolded. -/
lemma isoZeroPageTotalFiltration₂_eq (p q : ℤ) :
    isoZeroPageTotalFiltration₂ K E e p q = e 0 p q (p + q) le_rfl rfl ≪≫
      K.zeroPageObjectIso (fun (_ : ℤ) j => j) (fun _ _ => le_rfl)
        (fun _ _ => Int.le_add_one le_rfl) p (p + q) q p (Int.add_comm q p) rfl
        fun _ _ _ _ => by omega :=
  rfl

include hδ in
/-- **Stacks 0130 (2), the differential.** Under `isoZeroPageTotalFiltration₂` the zeroth
differential is `d_1^{q,p}`. -/
lemma isoZeroPageTotalFiltration₂_hom_d (p q q' : ℤ) (hq' : q' = q + 1) :
    (E.page 0 le_rfl).d (p, q) (p, q') ≫ (isoZeroPageTotalFiltration₂ K E e p q').hom =
      (isoZeroPageTotalFiltration₂ K E e p q).hom ≫ (K.d q q').f p := by
  subst hq'
  exact zeroPage_d K (fun (_ : ℤ) j => j) (fun _ _ => le_rfl) (fun _ _ => by omega) E e hδ p q
    (q + 1) (p + q) (p + (q + 1)) rfl rfl rfl q p (q + 1) p (by omega) rfl
    (fun _ _ _ _ => by omega) (by omega) rfl (fun _ _ _ _ => by omega) _
    (totalProjector₂_d_totalSummandπ p q (p + q) (p + (q + 1)) _ _)

/-- The identification of the line `q ↦ ''E_0^{p,q}` with the row `K^{•,p}`. -/
noncomputable def rowZeroPageIso (p : ℤ) : ∀ q, (E.page 0 le_rfl).X (p, q) ≅ (K.row p).X q :=
  fun q => isoZeroPageTotalFiltration₂ K E e p q

include hδ in
/-- The identification of the line `q ↦ ''E_0^{p,q}` with the row `K^{•,p}` matches the
differentials, with no sign. -/
lemma rowZeroPageIso_hom_d (p : ℤ) : ∀ q q', q' = q + 1 →
    (E.page 0 le_rfl).d (p, q) (p, q') ≫ (rowZeroPageIso K E e p q').hom =
      (rowZeroPageIso K E e p q).hom ≫ ((1 : ℤˣ) • (K.row p).d q q') := fun q q' hq' => by
  rw [one_smul]
  exact isoZeroPageTotalFiltration₂_hom_d K E e hδ p q q' hq'

/-- A cycle of the row `K^{•,p}`, read on the zeroth page through
`isoZeroPageTotalFiltration₂`, is that cycle. -/
lemma rowCycles_rowZeroPageIso (p : ℤ) : ∀ q, rowCycles 0 p q zero_le_one ≫
    cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫ (e 0 p q (p + q) le_rfl rfl).inv ≫
      (rowZeroPageIso K E e p q).hom = (K.row p).iCycles q := fun q => by
  rw [rowZeroPageIso, isoZeroPageTotalFiltration₂_eq, Iso.trans_hom, Iso.inv_hom_id_assoc,
    π_zeroPageObjectIso_hom, rowCycles_arrow_assoc, ι_totalSummandπ, Category.comp_id]

/-- The two readings of a cycle of the row `K^{•,p}`, as an element of `Z_0^{p,q}` and as an
element of `Z_1^{p,q}`, have the same image in `Tot^{p+q}`. -/
lemma rowCycles_arrow_eq (p : ℤ) : ∀ q : ℤ, rowCycles 0 p q zero_le_one ≫
    (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun (_ : ℤ) j => j) 0 p (p + q)).arrow =
      rowCycles 1 p q le_rfl ≫
        (FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
          (K.stepSubobject fun (_ : ℤ) j => j) 1 p (p + q)).arrow := fun q => by
  rw [rowCycles_arrow, rowCycles_arrow]

include hδ in
/-- **Stacks 0130 (4), as a construction, on the row.** The identification
`''E_1^{p,q} = H^q(K^{•,p})` of the first page; it is pinned down by `isoOnePageRow_spec`. -/
noncomputable def isoOnePageRow (p q : ℤ) :
    (E.page 1 zero_le_one).X (p, q) ≅ (K.row p).homology q :=
  isoOnePage K (fun (_ : ℤ) j => j) (fun _ _ => le_rfl) (fun _ _ => Int.le_add_one le_rfl) E e hδ p
    (K.row p) 1 (rowZeroPageIso K E e p) (rowZeroPageIso_hom_d K E e hδ p)
    (fun q => rowCycles 1 p q le_rfl) (fun q => rowCycles 0 p q zero_le_one)
    (rowCycles_arrow_eq K p) (rowCycles_rowZeroPageIso K E e p) q

include hδ in
/-- **The first page identification, on representatives.** `isoOnePageRow` sends the class of a
cycle of the row `K^{•,p}`, read in `Z_1^{p,q}`, to the class of that cycle. -/
lemma isoOnePageRow_spec (p q : ℤ) :
    rowCycles 1 p q le_rfl ≫ cokernel.π (Subobject.ofLE _ _ inf_le_right) ≫
        (e 1 p q (p + q) zero_le_one rfl).inv ≫ (isoOnePageRow K E e hδ p q).hom =
      (K.row p).homologyπ q :=
  isoOnePage_spec K (fun (_ : ℤ) j => j) (fun _ _ => le_rfl) (fun _ _ => Int.le_add_one le_rfl) E e
    hδ p (K.row p) 1 (rowZeroPageIso K E e p) (rowZeroPageIso_hom_d K E e hδ p)
    (fun q => rowCycles 1 p q le_rfl) (fun q => rowCycles 0 p q zero_le_one)
    (rowCycles_arrow_eq K p) (rowCycles_rowZeroPageIso K E e p) q

include hδ in
/-- **Stacks 0130 (4), as a construction.** The identification `''E_1^{p,q} = H^q(K^{•,p})` of the
first page, with `H^q(K^{•,p})` written as the `p`-th term of `H^q_I(K^{•,•})`. -/
noncomputable def isoOnePageTotalFiltration₂ (p q : ℤ) :
    (E.page 1 zero_le_one).X (p, q) ≅ (K.homology q).X p :=
  isoOnePageRow K E e hδ p q ≪≫ rowHomologyIso p q

include hδ in
/-- `isoOnePageTotalFiltration₂` unfolded. -/
lemma isoOnePageTotalFiltration₂_eq (p q : ℤ) :
    isoOnePageTotalFiltration₂ K E e hδ p q = isoOnePageRow K E e hδ p q ≪≫ rowHomologyIso p q :=
  rfl

include hδ in
/-- **Stacks 0130 (4), the differential.** Under `isoOnePageTotalFiltration₂` the first
differential is `(-1)^q` times the differential of `H^q_I(K^{•,•})`. -/
lemma isoOnePageTotalFiltration₂_hom_d (p p' q : ℤ) (hp' : p' = p + 1) :
    (E.page 1 zero_le_one).d (p, q) (p', q) ≫ (isoOnePageTotalFiltration₂ K E e hδ p' q).hom =
      (isoOnePageTotalFiltration₂ K E e hδ p q).hom ≫ (q.negOnePow • (K.homology q).d p p') := by
  subst hp'
  have hβd : (E.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (isoOnePageRow K E e hδ (p + 1) q).hom =
      (isoOnePageRow K E e hδ p q).hom ≫
        (q.negOnePow • HomologicalComplex.homologyMap (K.rowMap p (p + 1)) q) :=
    onePage_d K (fun (_ : ℤ) j => j) E e hδ p (p + 1) q rfl ((K.row p).homologyπ q)
      ((K.row (p + 1)).homologyπ q)
      (q.negOnePow • HomologicalComplex.cyclesMap (K.rowMap p (p + 1)) q) _
      (by rw [Linear.comp_units_smul, Linear.units_smul_comp,
        HomologicalComplex.homologyπ_naturality])
      (isoOnePageRow K E e hδ p q) (isoOnePageRow K E e hδ (p + 1) q)
      (rowCycles 1 p q le_rfl) (rowCycles 1 (p + 1) q le_rfl)
      (isoOnePageRow_spec K E e hδ p q) (isoOnePageRow_spec K E e hδ (p + 1) q)
      (by rw [rowCycles_arrow_assoc, rowCycles_arrow, iCycles_row_ιTotal_d])
  rw [isoOnePageTotalFiltration₂_eq, isoOnePageTotalFiltration₂_eq, Iso.trans_hom, Iso.trans_hom,
    reassoc_of% hβd, Linear.units_smul_comp, homologyMap_rowMap, Linear.comp_units_smul,
    Linear.comp_units_smul, Category.assoc]

include hδ in
/-- **Stacks 0130 (6), as a construction.** The identification
`''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))` of the second page of the spectral sequence of the second
filtration: the page-turning isomorphism of `E` followed by the homology of
`isoOnePageTotalFiltration₂`. -/
noncomputable def isoTwoPageTotalFiltration₂ (p q : ℤ) :
    (E.page 2 zero_le_two).X (p, q) ≅ (K.homology q).homology p :=
  isoTwoPage E q (K.homology q) q.negOnePow
    (fun p => isoOnePageTotalFiltration₂ K E e hδ p q)
    (fun p p' hp' => isoOnePageTotalFiltration₂_hom_d K E e hδ p p' q hp') p

include hδ in
/-- `isoTwoPageTotalFiltration₂` unfolded. -/
lemma isoTwoPageTotalFiltration₂_eq (p q : ℤ) :
    isoTwoPageTotalFiltration₂ K E e hδ p q =
      isoTwoPage E q (K.homology q) q.negOnePow
        (fun p => isoOnePageTotalFiltration₂ K E e hδ p q)
        (fun p p' hp' => isoOnePageTotalFiltration₂_hom_d K E e hδ p p' q hp') p :=
  rfl

include hδ in
/-- **Stacks 0130, the second filtration, as a construction.** The three identifications
`''E_0^{p,q} = K^{q,p}`, `''E_1^{p,q} = H^q(K^{•,p})` and `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`
of `exists_iso_pages_totalFiltration₂`, as data; their compatibility with the differentials is
`isoZeroPageTotalFiltration₂_hom_d` and `isoOnePageTotalFiltration₂_hom_d`. -/
noncomputable def isoPagesTotalFiltration₂ :
    (∀ p q : ℤ, (E.page 0 le_rfl).X (p, q) ≅ (K.X q).X p) ×
      (∀ p q : ℤ, (E.page 1 zero_le_one).X (p, q) ≅ (K.homology q).X p) ×
      (∀ p q : ℤ, (E.page 2 zero_le_two).X (p, q) ≅ (K.homology q).homology p) :=
  ⟨fun p q => isoZeroPageTotalFiltration₂ K E e p q,
    fun p q => isoOnePageTotalFiltration₂ K E e hδ p q,
    fun p q => isoTwoPageTotalFiltration₂ K E e hδ p q⟩

end DefForm

end SecondFiltration

end HomologicalComplex₂
