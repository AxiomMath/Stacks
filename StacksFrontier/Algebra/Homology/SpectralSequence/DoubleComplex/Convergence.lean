module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Filtration
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Pages

/-!
# Spectral sequences of double complexes: the second filtration and convergence

The theorem `exists_iso_pages_totalFiltration₂` identifying the first three pages of the spectral
sequence of the second filtration, and the convergence of both spectral sequences for a double
complex with finite diagonals (`isBounded_and_converges_totalFiltration₁`, `...₂`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

section SecondFiltration

variable {K}

variable (K)

/-- **Stacks 0130, the second filtration.** Let `(''E_r, ''d_r)` be the spectral sequence of the
total complex of a double complex `K^{•,•}` filtered by the second coordinate, presented as in
[Stacks, Tag 012M] by its pages `Z_r^{p,q}/D_r^{p,q}` and its differentials induced by `d`. Then
2. `''E_0^{p,q} = K^{q,p}` with `''d_0^{p,q} = d_1^{q,p}`;
4. `''E_1^{p,q} = H^q(K^{•,p})` with `''d_1^{p,q} = (-1)^q H^q(d_2^{•,p})`; here `H^q(K^{•,p})`
   is written as the `p`-th term of `H^q_I(K^{•,•})`, whose differential is induced by `d_2`;
6. `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`.

That the filtration `F` this is stated for really is
`F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j}` is the companion statement
`isLeast_totalFiltration₂`, which shares the parameters `F` and `hF` with this one; the two
together are the content of [Stacks, Tag 0130] for the second filtration. -/
@[stacks 0130 "(2), (4) and (6)"]
public theorem exists_iso_pages_totalFiltration₂
    (F : ∀ (_p n : ℤ), Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.totalFiltration₂.filtration.ι.app (op p)).f n))
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
    (∃ α : ∀ p q : ℤ, (E.page 0 le_rfl).X (p, q) ≅ (K.X q).X p,
      ∀ p q : ℤ, (E.page 0 le_rfl).d (p, q) (p, q + 1) ≫ (α p (q + 1)).hom =
        (α p q).hom ≫ (K.d q (q + 1)).f p) ∧
    (∃ β : ∀ p q : ℤ, (E.page 1 zero_le_one).X (p, q) ≅ (K.homology q).X p,
      ∀ p q : ℤ, (E.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
        (β p q).hom ≫ (q.negOnePow • (K.homology q).d p (p + 1))) ∧
    ∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅ (K.homology q).homology p) := by
  have hF' : F = K.stepSubobject fun (_ : ℤ) j => j := by
    funext p n
    rw [hF, K.mk_totalFiltration_ι_f]
  subst hF'
  have hZ' : Z = FilteredComplexSpectralSequence.cycles (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun (_ : ℤ) j => j) := by
    funext r p n
    rw [hZ, FilteredComplexSpectralSequence.cycles]
  subst hZ'
  have hD' : D = FilteredComplexSpectralSequence.boundaries (K.total (ComplexShape.up ℤ))
      (K.stepSubobject fun (_ : ℤ) j => j) := by
    funext r p n
    rw [hD, FilteredComplexSpectralSequence.boundaries]
  subst hD'
  have hδ' : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (p' q' n' : ℤ) (hp' : p' = p + r)
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
            (e r p' q' n' hr (by omega)).inv := by
    intro r p q n hr hn p' q' n' hp' hq' hn'
    subst hp' hq' hn'
    exact hδ r p q n hr hn
  exact ⟨⟨fun p q => isoZeroPageTotalFiltration₂ K E e p q,
      fun p q => isoZeroPageTotalFiltration₂_hom_d K E e hδ' p q (q + 1) rfl⟩,
    ⟨fun p q => isoOnePageTotalFiltration₂ K E e hδ' p q,
      fun p q => isoOnePageTotalFiltration₂_hom_d K E e hδ' p (p + 1) q rfl⟩,
    fun p q => ⟨isoTwoPageTotalFiltration₂ K E e hδ' p q⟩⟩

end SecondFiltration

section Convergence


variable {K}

private lemma totalProjector_eq_id (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (n : ℤ)
    (hP : ∀ i j, i + j = n → ¬ IsZero ((K.X i).X j) → P i j) :
    K.totalProjector P n = 𝟙 _ := by
  refine HomologicalComplex₂.total.hom_ext _ fun i j h => ?_
  rw [ι_totalProjector, Category.comp_id]
  split_ifs with hij
  · rfl
  · exact ((not_not.mp fun hz => hij (hP i j h hz)).eq_of_src _ _).symm

private lemma totalProjector_eq_zero (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)] (n : ℤ)
    (hP : ∀ i j, i + j = n → ¬ IsZero ((K.X i).X j) → ¬ P i j) :
    K.totalProjector P n = 0 := by
  refine HomologicalComplex₂.total.hom_ext _ fun i j h => ?_
  rw [ι_totalProjector, comp_zero]
  split_ifs with hij
  · exact (not_not.mp fun hz => hP i j h hz hij).eq_of_src _ _
  · rfl

/-- The filtration by a weight is finite in each degree as soon as the weights of the nonzero
summands of each `Tot^n` are bounded. -/
private lemma isDegreewiseFinite_totalFiltration (w : ℤ → ℤ → ℤ)
    (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1))
    (hw : ∀ n, ∃ a b : ℤ, ∀ i j, i + j = n → ¬ IsZero ((K.X i).X j) → a ≤ w i j ∧ w i j < b) :
    (K.totalFiltration w h₁ h₂).filtration.IsDegreewiseFinite := by
  intro n
  obtain ⟨a, b, hab⟩ := hw n
  refine ⟨a, b, ?_, ?_⟩
  · have hfac := (imageSubobject_arrow_comp (K.totalProjector (fun i j => a ≤ w i j) n)).trans
      (totalProjector_eq_id _ n fun i j h hz => (hab i j h hz).1)
    have : Epi (imageSubobject (K.totalProjector (fun i j => a ≤ w i j) n)).arrow :=
      epi_of_epi_fac hfac
    exact isIso_of_mono_of_epi (imageSubobject (K.totalProjector (fun i j => a ≤ w i j) n)).arrow
  · have hz : IsZero (imageSubobject (K.totalProjector (fun i j => b ≤ w i j) n) : C) :=
      IsZero.of_mono_eq_zero _ (zero_of_epi_comp _ ((imageSubobject_arrow_comp _).trans
        (totalProjector_eq_zero _ n fun i j h hz => not_le.mpr (hab i j h hz).2)))
    exact hz

/-- If each antidiagonal has finitely many positions satisfying `P`, any function of the position
is bounded on those. -/
private lemma exists_bounds_of_finite (P : ℤ → ℤ → Prop)
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ P pq.1 pq.2}.Finite)
    (f : ℤ × ℤ → ℤ) (n : ℤ) :
    ∃ a b : ℤ, ∀ i j, i + j = n → P i j → a ≤ f (i, j) ∧ f (i, j) < b := by
  obtain ⟨a, ha⟩ := ((hK n).image f).bddBelow
  obtain ⟨b, hb⟩ := ((hK n).image f).bddAbove
  exact ⟨a, b + 1, fun i j h hz => ⟨ha ⟨(i, j), ⟨h, hz⟩, rfl⟩,
    Int.lt_add_one_iff.mpr (hb ⟨(i, j), ⟨h, hz⟩, rfl⟩)⟩⟩

variable (K)

/-- **The first filtration of a diagonally finite double complex is degreewise finite.**  If every
antidiagonal of `K^{•,•}` has only finitely many nonzero terms then the filtration
`F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j}` of `Tot(K^{•,•})` reaches `⊤` and `⊥` in each degree.

This is the hypothesis of [Stacks, Tag 012W] and of every convergence statement built on it, so
it is stated separately from `isBounded_and_converges_totalFiltration₁` for consumers which hold
the spectral sequence of `Tot(K^{•,•})` in some other presentation. -/
public lemma isDegreewiseFinite_totalFiltration₁
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    K.totalFiltration₁.filtration.IsDegreewiseFinite := by
  exact isDegreewiseFinite_totalFiltration _ _ _ (exists_bounds_of_finite _ hK Prod.fst)

/-- **The second filtration of a diagonally finite double complex is degreewise finite.**  If every
antidiagonal of `K^{•,•}` has only finitely many nonzero terms then the filtration
`F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j}` of `Tot(K^{•,•})` reaches `⊤` and `⊥` in each
degree.

This is the hypothesis of [Stacks, Tag 012W] and of every convergence statement built on it, so
it is stated separately from `isBounded_and_converges_totalFiltration₂` for consumers which hold
the spectral sequence of `Tot(K^{•,•})` in some other presentation -- in particular for the
Grothendieck spectral sequence of [Stacks, Tag 015N], whose filtered complex is the second total
filtration of `G(I)` for a Cartan-Eilenberg resolution `I`. -/
public lemma isDegreewiseFinite_totalFiltration₂
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    K.totalFiltration₂.filtration.IsDegreewiseFinite := by
  exact isDegreewiseFinite_totalFiltration _ _ _ (exists_bounds_of_finite _ hK Prod.snd)

/-- **Stacks 0132, the first filtration.** If every diagonal of the double complex `K^{•,•}` has
only finitely many nonzero terms, then the spectral sequence `E` of `Tot(K^{•,•})` filtered by the
first coordinate, presented as in `CochainComplex.isBounded_and_converges_of_isDegreewiseFinite`, is
bounded, the filtration it induces on each `H^n(Tot(K^{•,•}))` is finite, `E` converges to
`H^*(Tot(K^{•,•}))`, and a weak Serre subcategory containing one whole page of `E` contains every
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0132]
public theorem isBounded_and_converges_totalFiltration₁
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (F : ∀ (_p n : ℤ), Subobject (K.totalFiltration₁.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.totalFiltration₁.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₁.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.totalFiltration₁.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₁.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.totalFiltration₁.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject (K.totalFiltration₁.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject
        (HomologicalComplex.homologyMap (K.totalFiltration₁.filtration.ι.app (op p)) n))
    (E : CohomologicalSpectralSequence C 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0 le_rfl).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (K.totalFiltration₁.X.d n (n + 1))).obj (F (p + r) (n + 1))
            ⊔ F (p + 1) n)
        (kernelSubobject (K.totalFiltration₁.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (K.totalFiltration₁.X.d (n - 1) n)).obj (F (p - r) (n - 1))
            ⊔ F (p + 1) n)
        (imageSubobject (K.totalFiltration₁.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
    (∀ (P : ObjectProperty C) [P.IsWeakSerreClass] (r : ℤ) (hr : 0 ≤ r),
      (∀ p q : ℤ, P ((E.page r hr).X (p, q))) → ∀ n : ℤ, P (K.totalFiltration₁.X.homology n)) :=
  CochainComplex.isBounded_and_converges_of_isDegreewiseFinite _
    (K.isDegreewiseFinite_totalFiltration₁ hK) F hF Z hZ D hD FH hFH E hE

/-- **Stacks 0132, the second filtration.** If every diagonal of the double complex `K^{•,•}` has
only finitely many nonzero terms, then the spectral sequence `E` of `Tot(K^{•,•})` filtered by the
second coordinate, presented as in `CochainComplex.isBounded_and_converges_of_isDegreewiseFinite`,
is bounded, the filtration it induces on each `H^n(Tot(K^{•,•}))` is finite, `E` converges to
`H^*(Tot(K^{•,•}))`, and a weak Serre subcategory containing one whole page of `E` contains every
`H^n(Tot(K^{•,•}))`. -/
@[stacks 0132]
public theorem isBounded_and_converges_totalFiltration₂
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (F : ∀ (_p n : ℤ), Subobject (K.totalFiltration₂.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.totalFiltration₂.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₂.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.totalFiltration₂.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.totalFiltration₂.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.totalFiltration₂.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject (K.totalFiltration₂.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject
        (HomologicalComplex.homologyMap (K.totalFiltration₂.filtration.ι.app (op p)) n))
    (E : CohomologicalSpectralSequence C 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0 le_rfl).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (K.totalFiltration₂.X.d n (n + 1))).obj (F (p + r) (n + 1))
            ⊔ F (p + 1) n)
        (kernelSubobject (K.totalFiltration₂.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (K.totalFiltration₂.X.d (n - 1) n)).obj (F (p - r) (n - 1))
            ⊔ F (p + 1) n)
        (imageSubobject (K.totalFiltration₂.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
    (∀ (P : ObjectProperty C) [P.IsWeakSerreClass] (r : ℤ) (hr : 0 ≤ r),
      (∀ p q : ℤ, P ((E.page r hr).X (p, q))) → ∀ n : ℤ, P (K.totalFiltration₂.X.homology n)) :=
  CochainComplex.isBounded_and_converges_of_isDegreewiseFinite _
    (K.isDegreewiseFinite_totalFiltration₂ hK) F hF Z hZ D hD FH hFH E hE

end Convergence

end HomologicalComplex₂
