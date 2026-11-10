module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.ElementaryReplacementComplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Resolutions by objects of bounded cohomological dimension: coresolutions

The elementary replacement theorems, and right coresolutions of objects by objects of
`d`-value `0`.

## Main results

* `elementary_replacement`: a quasi-isomorphism making degree `n` of `d`-value `0`, while
  `d (K'.X (n + 1)) ≤ max (d (K.X n) - 1) (d (K.X (n + 1)))` and other degrees keep their
  `d`-value.
* `exists_dZeroCoresolution`: every object has a right coresolution by objects of `d`-value
  `0`.
* `exists_dZero_window`: a quasi-isomorphism making the degrees `m ≤ n < m + k` of
  `d`-value `0`.

## References

* [Stacks: Tag 07K6](https://stacks.math.columbia.edu/tag/07K6)
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.BoundedCohomologicalDimension

variable {A : Type*} [Category A] [Abelian A]

open ElemReplConstruction in
/-- The elementary replacement of `K` at degree `n` along a mono `ι : K.X n ⟶ M`: the
complex `Kp K n M ι`, the chain map `fmap K n M ι`, and the cokernel short exact sequence
`0 → K^n → M ⊞ K^{n+1} → K'.X (n+1) → 0`. -/
noncomputable def elemReplBuild (d : A → ℕ∞) (K : CochainComplex A ℤ) (n : ℤ) (M : A)
    (ι : K.X n ⟶ M) (hιmono : Mono ι) : ElemReplBuild d K n M ι
    where
  K' := Kp K n M ι
  f := fmap K n M ι
  g := cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ eqToHom (XX_n1 K n M _).symm
  hg := by rw [← Category.assoc, cokernel.condition, zero_comp]
  hK'n := by simp [Kp, XX]
  hoff := by
    intro m hm1 hm2
    congr 1
    simp only [Kp, XX]
    exact XX_off K n M _ m hm1 hm2
  hses := by
    have hmono : Mono (biprod.lift ι (K.d n (n + 1))) :=
      mono_of_mono_fac (biprod.lift_fst ι (K.d n (n + 1)))
    have hse :
      (ShortComplex.mk (biprod.lift ι (K.d n (n + 1))) (cokernel.π (biprod.lift ι (K.d n (n + 1))))
          (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_cokernel _, mono_f := hmono, epi_g := coequalizer.π_epi }
    let e :
      (ShortComplex.mk (biprod.lift ι (K.d n (n + 1))) (cokernel.π (biprod.lift ι (K.d n (n + 1))))
          (cokernel.condition _)) ≅
        (ShortComplex.mk (biprod.lift ι (K.d n (n + 1)))
          (cokernel.π (biprod.lift ι (K.d n (n + 1))) ≫ eqToHom (XX_n1 K n M _).symm)
          (by rw [← Category.assoc, cokernel.condition, zero_comp])) :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        (eqToIso (XX_n1 K n M (cokernel (biprod.lift ι (K.d n (n + 1))))).symm) (by simp)
        (by simp [eqToIso])
    exact (ShortComplex.shortExact_iff_of_iso e).mp hse

/-- The comparison map of the elementary replacement `elemReplBuild` is a
quasi-isomorphism. -/
theorem elemReplBuild_quasiIso (d : A → ℕ∞) (K : CochainComplex A ℤ) (n : ℤ) (M : A)
    (ι : K.X n ⟶ M) (hιmono : Mono ι) : QuasiIso (elemReplBuild d K n M ι hιmono).f := by
  change QuasiIso (ElemReplConstruction.fmap K n M ι)
  have := hιmono
  have hcomp : ElemReplConstruction.fmap K n M ι ≫ ElemReplConstruction.pmap K n M ι = 0 := by
    ext i
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    exact ElemReplConstruction.ffpff_zero K n M ι i
  set S : ShortComplex (CochainComplex A ℤ) :=
    ShortComplex.mk (ElemReplConstruction.fmap K n M ι) (ElemReplConstruction.pmap K n M ι)
      hcomp with
    hS_def
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    have heq :
      (S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)) =
        ShortComplex.mk (ElemReplConstruction.ff K n M ι i) (ElemReplConstruction.pff K n M ι i)
          (ElemReplConstruction.ffpff_zero K n M ι i) :=
      rfl
    rw [heq]
    by_cases hn : i = n
    · subst i; exact ElemReplConstruction.degSE_n K n M ι
    by_cases hn1 : i = n + 1
    · subst hn1; exact ElemReplConstruction.degSE_n1 K n M ι
    · exact ElemReplConstruction.degSE_off K n M ι i hn hn1
  have hQ : ∀ i, IsZero (S.X₃.homology i) := ElemReplConstruction.Q_acyclic K n M ι
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hfeq :
    HomologicalComplex.homologyMap (ElemReplConstruction.fmap K n M ι) i =
      HomologicalComplex.homologyMap S.f i :=
    rfl
  rw [hfeq]
  have hmono : Mono (HomologicalComplex.homologyMap S.f i) := by
    have hex :=
      hS.homology_exact₁ (i - 1) i
        (by
          rw [ComplexShape.up_Rel]; omega)
    refine hex.mono_g ?_
    exact (hQ (i - 1)).eq_of_src _ _
  have hepi : Epi (HomologicalComplex.homologyMap S.f i) := by
    have hex := hS.homology_exact₂ i
    refine hex.epi_f ?_
    exact (hQ i).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- For a mono `ι : K.X n ⟶ M`, there is a quasi-isomorphism `f : K ⟶ K'` with
`K'.X n = M`, `d (K'.X m) = d (K.X m)` for `m ∉ {n, n + 1}`, and a short exact sequence
`0 → K^n → M ⊞ K^{n+1} → K'.X (n+1) → 0` whose first map is `biprod.lift ι (K.d n (n + 1))`. -/
theorem elem_repl_data (d : A → ℕ∞) (K : CochainComplex A ℤ) (n : ℤ) (M : A) (ι : K.X n ⟶ M)
    (hιmono : Mono ι) :
    ∃ (K' : CochainComplex A ℤ) (f : K ⟶ K') (g : (M ⊞ K.X (n + 1)) ⟶ K'.X (n + 1)) (hg :
      biprod.lift ι (K.d n (n + 1)) ≫ g = 0),
      QuasiIso f ∧
        K'.X n = M ∧
        (∀ m : ℤ, m ≠ n → m ≠ n + 1 → d (K'.X m) = d (K.X m)) ∧
        (ShortComplex.mk (biprod.lift ι (K.d n (n + 1))) g hg).ShortExact := by
  set B := elemReplBuild d K n M ι hιmono with hB
  exact ⟨B.K', B.f, B.g, B.hg, elemReplBuild_quasiIso d K n M ι hιmono, B.hK'n, B.hoff, B.hses⟩

/-- The `d`-bound on the new degree `n + 1` of an elementary replacement along an embedding into
`M` with `d M = 0`. -/
private theorem elem_repl_le (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    {K : CochainComplex A ℤ} {n : ℤ} {M Z : A} {ι : K.X n ⟶ M} {g : (M ⊞ K.X (n + 1)) ⟶ Z}
    {hg : biprod.lift ι (K.d n (n + 1)) ≫ g = 0} (hM : d M = 0)
    (hses : (ShortComplex.mk (biprod.lift ι (K.d n (n + 1))) g hg).ShortExact) :
    d Z ≤ max (d (K.X n) - 1) (d (K.X (n + 1))) := by
  refine le_trans (hd.shortExact_le _ hses) ?_
  have hbip : d (M ⊞ K.X (n + 1)) ≤ max (d M) (d (K.X (n + 1))) := hd.biprod_le _ _
  rw [hM, zero_max] at hbip
  exact max_le_max le_rfl hbip

/-- **Elementary replacement.** For every degree `n` there is a quasi-isomorphism
`f : K ⟶ K'` with `d (K'.X n) = 0`, `d (K'.X (n + 1)) ≤ max (d (K.X n) - 1) (d (K.X (n + 1)))`,
and `d (K'.X m) = d (K.X m)` for `m ∉ {n, n + 1}`. -/
theorem elementary_replacement (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (n : ℤ) :
    ∃ (K' : CochainComplex A ℤ) (f : K ⟶ K'),
      QuasiIso f ∧
        d (K'.X n) = 0 ∧
        d (K'.X (n + 1)) ≤ max (d (K.X n) - 1) (d (K.X (n + 1))) ∧
        ∀ m : ℤ, m ≠ n → m ≠ n + 1 → d (K'.X m) = d (K.X m) := by
  obtain ⟨M, ι, hιmono, hM⟩ := hd.embed (K.X n)
  obtain ⟨K', f, g, hg, hqi, hK'n, hoff, hses⟩ := elem_repl_data d K n M ι hιmono
  refine ⟨K', f, hqi, ?_, ?_, hoff⟩
  · rw [hK'n, hM]
  · exact elem_repl_le d hd hM hses

/-- **Strengthened elementary replacement.** As `elementary_replacement`, and moreover for
`m ∉ {n, n + 1}` one has `K'.X m = K.X m`, with `f.f m` the corresponding `eqToHom`. -/
theorem elementary_replacement' (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (n : ℤ) :
    ∃ (K' : CochainComplex A ℤ) (f : K ⟶ K'),
      QuasiIso f ∧
        d (K'.X n) = 0 ∧
        d (K'.X (n + 1)) ≤ max (d (K.X n) - 1) (d (K.X (n + 1))) ∧
        (∀ m : ℤ, m ≠ n → m ≠ n + 1 → d (K'.X m) = d (K.X m)) ∧
        (∀ m : ℤ, m ≠ n → m ≠ n + 1 → ∃ h : K'.X m = K.X m, f.f m = eqToHom h.symm) := by
  obtain ⟨M, ι, hιmono, hM⟩ := hd.embed (K.X n)
  refine
    ⟨ElemReplConstruction.Kp K n M ι, ElemReplConstruction.fmap K n M ι,
      elemReplBuild_quasiIso d K n M ι hιmono, ?_, ?_, ?_, ?_⟩
  · change d (ElemReplConstruction.XX K n M _ n) = 0
    rw [ElemReplConstruction.XX_n, hM]
  · exact elem_repl_le d hd hM (elemReplBuild d K n M ι hιmono).hses
  · intro m hm1 hm2
    change d (ElemReplConstruction.XX K n M _ m) = d (K.X m)
    rw [ElemReplConstruction.XX_off K n M _ m hm1 hm2]
  · intro m hm1 hm2
    have hobj : (ElemReplConstruction.Kp K n M ι).X m = K.X m :=
      ElemReplConstruction.XX_off K n M _ m hm1 hm2
    refine ⟨hobj, ?_⟩
    change ElemReplConstruction.ff K n M ι m = eqToHom hobj.symm
    unfold ElemReplConstruction.ff
    rw [dite_eq_right hm1, dite_eq_right hm2]

/-- If every member of a finite family `X : ι → A` has `d (X i) = 0`, then the biproduct
`⨁ X` satisfies `d (⨁ X) = 0`. -/
theorem dZero_biproduct {d : A → ℕ∞} (hd : BoundedCohomologicalDimension d) {ι : Type*} [Finite ι]
    (X : ι → A) [CategoryTheory.Limits.HasBiproduct X] (hX : ∀ i, d (X i) = 0) :
    d (CategoryTheory.Limits.biproduct X) = 0 := by
  have hzero : d (0 : A) = 0 := by
    obtain ⟨B, _, _, hB⟩ := hd.embed 0
    have hse : (ShortComplex.mk (𝟙 B) (0 : B ⟶ 0) (by simp)).ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · exact (ShortComplex.exact_iff_epi _ rfl).mpr inferInstance
      · dsimp; infer_instance
      · dsimp; infer_instance
    have hle := hd.shortExact_le _ hse
    rw [hB] at hle
    have : d (0 : A) ≤ 0 := by simpa using hle
    exact le_antisymm this bot_le
  have hiso : ∀ {Y Z : A}, (Y ≅ Z) → d Y = d Z := by
    intro Y Z e
    have hf : ∀ {Y Z : A} (e : Y ≅ Z), d Z ≤ d Y := by
      intro Y Z e
      have hse : (ShortComplex.mk (0 : (0 : A) ⟶ Y) e.hom (by simp)).ShortExact := by
        refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
        · exact (ShortComplex.exact_iff_mono _ rfl).mpr inferInstance
        · dsimp; infer_instance
        · dsimp; infer_instance
      have hle := hd.shortExact_le _ hse
      rw [hzero] at hle
      simpa using hle
    exact le_antisymm (hf e.symm) (hf e)
  have hbin : ∀ {Y Z : A}, d Y = 0 → d Z = 0 → d (Y ⊞ Z) = 0 := by
    intro Y Z hY hZ
    have hle := hd.biprod_le Y Z
    rw [hY, hZ] at hle
    exact le_antisymm (by simpa using hle) zero_le
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  suffices H : ∀ (β : Type _) [Fintype β] (Y : β → A), (∀ b, d (Y b) = 0) → d (⨁ Y) = 0
    by
    have := Fintype.ofFinite ι
    exact H ι X hX
  intro β _
  refine
    Fintype.induction_empty_option (P := fun γ _ =>
      ∀ (Y : γ → A), (∀ b, d (Y b) = 0) → d (⨁ Y) = 0) ?_ ?_ ?_ β
  · intro α β _ e ih Y hY
    have : Fintype α := Fintype.ofEquiv β e.symm
    have key := ih (fun a => Y (e a)) (fun a => hY (e a))
    rwa [hiso (biproduct.whiskerEquiv e (fun a => Iso.refl (Y (e a))))] at key
  · intro Y _
    have hz : IsZero (⨁ Y) := by
      rw [IsZero.iff_id_eq_zero]; ext (i : PEmpty); exact i.elim
    rw [hiso hz.isoZero]; exact hzero
  · intro α _ ih Y hY
    have split : (⨁ Y) ≅ (Y none) ⊞ (⨁ (fun a => Y (some a))) :=
      { hom :=
          biproduct.desc
            (fun i =>
              Option.rec biprod.inl (fun a => biproduct.ι (fun a => Y (some a)) a ≫ biprod.inr) i)
        inv := biprod.desc (biproduct.ι Y none) (biproduct.desc (fun a => biproduct.ι Y (some a)))
        hom_inv_id := by
          ext (i : Option α) (j : Option α)
          cases i <;> cases j <;> simp
        inv_hom_id := by
          apply biprod.hom_ext' <;>
            simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.comp_id]
          · simp
          · apply biproduct.hom_ext'
            intro j; simp }
    rw [hiso split]
    exact hbin (hY none) (ih (fun a => Y (some a)) (fun a => hY (some a)))

namespace CoresConstruction

/-- The recursive embedding data of a `d`-acyclic right coresolution:
`C 0 = X`, embed `C k ↪ B k` into a `d`-acyclic object, `C (k+1) = coker (emb k)`. -/
structure CoresData (d : A → ℕ∞) (X : A) where
  /-- The successive cokernels, starting with `C 0 = X`. -/
  C : ℕ → A
  /-- The `d`-acyclic objects into which the `C k` embed. -/
  B : ℕ → A
  /-- The embedding `C k ⟶ B k`. -/
  emb : ∀ k, C k ⟶ B k
  /-- Each `emb k` is a monomorphism. -/
  emb_mono : ∀ k, Mono (emb k)
  dB : ∀ k, d (B k) = 0
  hC0 : C 0 = X
  hCsucc : ∀ k, C (k + 1) = cokernel (emb k)

/-- Build the recursive coresolution data by iterating the embedding hypothesis. -/
noncomputable def buildCores (d : A → ℕ∞) (hemb : ∀ Y : A, ∃ (B : A) (i : Y ⟶ B), Mono i ∧ d B = 0)
    (X : A) : CoresData d X :=
  let Cf : ℕ → A := fun k => Nat.rec X (fun _ prev => cokernel ((hemb prev).choose_spec.choose)) k
  { C := Cf
    B := fun k => (hemb (Cf k)).choose
    emb := fun k => (hemb (Cf k)).choose_spec.choose
    emb_mono := fun k => (hemb (Cf k)).choose_spec.choose_spec.1
    dB := fun k => (hemb (Cf k)).choose_spec.choose_spec.2
    hC0 := rfl
    hCsucc := fun _ => rfl }

variable (d : A → ℕ∞) (X : A) (D : CoresData d X)

/-- Underlying objects of the coresolution complex: `B n` in degree `n ≥ 0`, `0` otherwise. -/
noncomputable def RX (n : ℤ) : A :=
  if 0 ≤ n then D.B n.toNat else 0

/-- In negative degrees the coresolution objects are `0`. -/
@[simp]
lemma RX_neg (n : ℤ) (h : n < 0) : RX d X D n = 0 := by
  unfold RX; rw [ite_eq_right (by omega)]

/-- In a degree `n ≥ 0` the coresolution object is `D.B n.toNat`. -/
lemma RX_nonneg (n : ℤ) (h : 0 ≤ n) : RX d X D n = D.B n.toNat := by
  unfold RX; rw [ite_eq_left h]

/-- In degree `0` the coresolution object is `D.B 0`. -/
lemma RX_zero : RX d X D 0 = D.B 0 := by
  rw [RX_nonneg d X D 0 le_rfl]; rfl

/-- The connecting map `B k ⟶ B (k+1)`: cokernel projection followed by the next embedding. -/
noncomputable def delta (k : ℕ) : D.B k ⟶ D.B (k + 1) :=
  cokernel.π (D.emb k) ≫ eqToHom (D.hCsucc k).symm ≫ D.emb (k + 1)

/-- Two consecutive connecting maps compose to zero. -/
lemma delta_delta (k : ℕ) : delta d X D k ≫ delta d X D (k + 1) = 0 := by
  unfold delta
  have : D.emb (k + 1) ≫ cokernel.π (D.emb (k + 1)) = 0 := cokernel.condition _
  simp only [Category.assoc]
  rw [reassoc_of%
      (show eqToHom (D.hCsucc k).symm ≫ D.emb (k + 1) ≫ cokernel.π (D.emb (k + 1)) = 0 from by
        rw [this, comp_zero])];
  simp

/-- The `ℤ`-indexed differential of the coresolution complex. -/
noncomputable def Rd (i j : ℤ) : RX d X D i ⟶ RX d X D j :=
  if h : j = i + 1 ∧ 0 ≤ i then
    eqToHom (RX_nonneg d X D i h.2) ≫
      delta d X D i.toNat ≫
      eqToHom
        (by
          rw [RX_nonneg d X D j (by omega)]; congr 1; omega)
  else 0

/-- For `b = a + 1`, `delta a` followed by `eqToHom` and `delta b` is zero. -/
lemma delta_glue_zero (a b : ℕ) (e1 : D.B (a + 1) = D.B b) (hb : b = a + 1) :
    delta d X D a ≫ eqToHom e1 ≫ delta d X D b = 0 := by
  subst hb; simp only [eqToHom_refl, Category.id_comp]; rw [delta_delta]

/-- Two consecutive differentials `Rd` compose to zero. -/
lemma Rd_dd (i j k : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    Rd d X D i j ≫ Rd d X D j k = 0 := by
  simp only [ComplexShape.up_Rel] at hij hjk
  by_cases hi : 0 ≤ i
  · unfold Rd
    rw [dite_eq_left ⟨hij.symm, hi⟩, dite_eq_left ⟨hjk.symm, by omega⟩]
    have hjt : j.toNat = i.toNat + 1 := by omega
    simp only [Category.assoc, eqToHom_trans_assoc]
    rw [reassoc_of% (delta_glue_zero d X D i.toNat j.toNat (by rw [hjt]) hjt)]; simp
  · unfold Rd;
    rw [dite_eq_right
        (by
          rintro ⟨_, h⟩; omega)];
    simp

/-- The coresolution cochain complex `R`: `B n` in degree `n ≥ 0`, `0` in negative degrees. -/
noncomputable def Rcomplex : CochainComplex A ℤ where
  X := RX d X D
  d := Rd d X D
  shape i j hij := by
    unfold Rd; rw [dite_eq_right]; rintro ⟨h1, h2⟩; apply hij; simp [ComplexShape.up_Rel]; omega
  d_comp_d' i j k hij hjk := Rd_dd d X D i j k hij hjk

/-- The objects of `Rcomplex d X D` are given by `RX`. -/
@[simp]
lemma Rcomplex_X (n : ℤ) : (Rcomplex d X D).X n = RX d X D n :=
  rfl

/-- In degrees `n ≥ 0` the objects of `Rcomplex d X D` have `d`-value `0`. -/
lemma Rcomplex_pos (n : ℤ) (h : 0 ≤ n) : d ((Rcomplex d X D).X n) = 0 := by
  change d (RX d X D n) = 0; rw [RX_nonneg d X D n h]; exact D.dB _

/-- In negative degrees the objects of `Rcomplex d X D` are zero. -/
lemma Rcomplex_neg (n : ℤ) (h : n < 0) : IsZero ((Rcomplex d X D).X n) := by
  change IsZero (RX d X D n); rw [RX_neg d X D n h]; exact isZero_zero A

/-- The degree-0 component of the augmentation `X ⟶ R^0 = B 0` (the first embedding). -/
noncomputable def augφ : X ⟶ (Rcomplex d X D).X 0 :=
  eqToHom (D.hC0.symm) ≫ D.emb 0 ≫ eqToHom (by rw [Rcomplex_X, RX_zero])

/-- The degree-`0` augmentation `augφ` composed with the differential of `Rcomplex` vanishes. -/
lemma augφ_cond (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    augφ d X D ≫ (Rcomplex d X D).d 0 k = 0 := by
  simp only [ComplexShape.up_Rel] at hk
  subst hk
  unfold augφ
  change _ ≫ Rd d X D 0 1 = 0
  unfold Rd
  rw [dite_eq_left ⟨by ring, le_rfl⟩]
  rw [show delta d X D (0 : ℤ).toNat = delta d X D 0 from rfl]
  unfold delta
  have key : D.emb 0 ≫ cokernel.π (D.emb 0) = 0 := cokernel.condition _
  simp [reassoc_of% key]

/-- The augmentation chain map `X[0] ⟶ R`. -/
noncomputable def augMap :
    (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X ⟶ Rcomplex d X D :=
  HomologicalComplex.mkHomFromSingle (augφ d X D) (augφ_cond d X D)

/-- `delta (k+1)` factored as cokernel projection followed by the mono
`coker(emb (k+1)) ≅ C(k+2) ↪ B(k+2)`. -/
lemma delta_eq_factor (k : ℕ) :
    delta d X D (k + 1) =
      cokernel.π (D.emb (k + 1)) ≫ (eqToHom (D.hCsucc (k + 1)).symm ≫ D.emb (k + 1 + 1)) := by
  unfold delta; rfl

/-- The two consecutive differentials `delta k`, `delta (k+1)` form an exact sequence at
`B (k+1)`. -/
lemma delta_sc_exact (k : ℕ) :
    (ShortComplex.mk (delta d X D k) (delta d X D (k + 1)) (delta_delta d X D k)).Exact := by
  have := D.emb_mono (k + 1)
  have := D.emb_mono (k + 2)
  have hzeroTp : D.emb (k + 1) ≫ delta d X D (k + 1) = 0 := by
    unfold delta; rw [← Category.assoc, cokernel.condition, zero_comp]
  have hE :
    (ShortComplex.mk (D.emb (k + 1)) (cokernel.π (D.emb (k + 1))) (cokernel.condition _)).Exact :=
    ShortComplex.exact_cokernel _
  have hETp :
    (ShortComplex.mk (D.emb (k + 1)) (cokernel.π (D.emb (k + 1))) (cokernel.condition _)).Exact ↔
      (ShortComplex.mk (D.emb (k + 1)) (delta d X D (k + 1)) hzeroTp).Exact := by
    let ψ :
      (ShortComplex.mk (D.emb (k + 1)) (cokernel.π (D.emb (k + 1))) (cokernel.condition _)) ⟶
        (ShortComplex.mk (D.emb (k + 1)) (delta d X D (k + 1)) hzeroTp) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := eqToHom (D.hCsucc (k + 1)).symm ≫ D.emb (k + 1 + 1)
        comm₁₂ := by
          dsimp; simp
        comm₂₃ := by
          dsimp; unfold delta; simp }
    have : Mono ψ.τ₃ := by
      change Mono (eqToHom _ ≫ D.emb (k + 1 + 1)); apply mono_comp
    have : Epi ψ.τ₁ := by
      change Epi (𝟙 _); infer_instance
    have : IsIso ψ.τ₂ := by
      change IsIso (𝟙 _); infer_instance
    exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ
  have hTpExact := hETp.mp hE
  let φ :
    (ShortComplex.mk (delta d X D k) (delta d X D (k + 1)) (delta_delta d X D k)) ⟶
      (ShortComplex.mk (D.emb (k + 1)) (delta d X D (k + 1)) hzeroTp) :=
    { τ₁ := cokernel.π (D.emb k) ≫ eqToHom (D.hCsucc k).symm
      τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp; unfold delta; simp [Category.assoc]
      comm₂₃ := by
        dsimp; simp }
  have : Epi φ.τ₁ := by
    change Epi (cokernel.π (D.emb k) ≫ eqToHom _); apply epi_comp
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 _); infer_instance
  have : Mono φ.τ₃ := by
    change Mono (𝟙 _); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hTpExact

/-- `Rd i j` rewritten with the source index reified as a natural number `p`. -/
lemma Rd_eq' (i j : ℤ) (p : ℕ) (hp : (p : ℤ) = i) (hj : j = i + 1) (hi : 0 ≤ i)
    (eI : RX d X D i = D.B p) (eJ : RX d X D j = D.B (p + 1)) :
    Rd d X D i j = eqToHom eI ≫ delta d X D p ≫ eqToHom eJ.symm := by
  unfold Rd
  rw [dite_eq_left ⟨hj, hi⟩]
  subst hp
  simp only [Int.toNat_natCast]

/-- `RX` at a nonnegative integer reified as a natural number. -/
lemma RX_eqB (i : ℤ) (p : ℕ) (hp : (p : ℤ) = i) : RX d X D i = D.B p := by
  subst hp; rw [RX_nonneg d X D _ (by positivity), Int.toNat_natCast]

/-- For `n ≥ 1` the coresolution complex `Rcomplex d X D` is exact at degree `n`. -/
lemma Rcomplex_exactAt_pos (n : ℤ) (hn : 1 ≤ n) : (Rcomplex d X D).ExactAt n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ ((m : ℤ) + 1 - 1) ((m : ℤ) + 1) ((m : ℤ) + 1 + 1)
      (by simp [CochainComplex.prev]) (by simp [CochainComplex.next])]
  have e1 : RX d X D ((m : ℤ) + 1 - 1) = D.B m := RX_eqB d X D _ m (by omega)
  have e2 : RX d X D ((m : ℤ) + 1) = D.B (m + 1) :=
    RX_eqB d X D _ (m + 1)
      (by
        push_cast; ring)
  have e3 : RX d X D ((m : ℤ) + 1 + 1) = D.B (m + 1 + 1) :=
    RX_eqB d X D _ (m + 1 + 1)
      (by
        push_cast; ring)
  refine (ShortComplex.exact_iff_of_iso ?_).mp (delta_sc_exact d X D m)
  refine ShortComplex.isoMk (eqToIso e1.symm) (eqToIso e2.symm) (eqToIso e3.symm) ?_ ?_
  · change
      eqToHom e1.symm ≫ Rd d X D ((m : ℤ) + 1 - 1) ((m : ℤ) + 1) = delta d X D m ≫ eqToHom e2.symm
    rw [Rd_eq' d X D ((m : ℤ) + 1 - 1) ((m : ℤ) + 1) m (by omega) (by ring) (by omega) e1 e2]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · change
      eqToHom e2.symm ≫ Rd d X D ((m : ℤ) + 1) ((m : ℤ) + 1 + 1) =
        delta d X D (m + 1) ≫ eqToHom e3.symm
    rw [Rd_eq' d X D ((m : ℤ) + 1) ((m : ℤ) + 1 + 1) (m + 1)
        (by
          push_cast; ring)
        (by ring) (by omega) e2 e3]
    simp only [eqToHom_refl, Category.id_comp]

/-! ### Kernels under composition with isomorphisms and monomorphisms -/

/-- A monomorphism `f` that is a kernel of `g` is also a kernel of `g ≫ m` for any
monomorphism `m`. -/
noncomputable def ker_postcomp_mono {X₀ Y₀ Z₀ W₀ : A} (f : X₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀) (m : Z₀ ⟶ W₀)
    [Mono m] (h0 : f ≫ g = 0) (hf : IsLimit (KernelFork.ofι f h0)) :
    IsLimit (KernelFork.ofι f (show f ≫ (g ≫ m) = 0 by rw [← Category.assoc, h0, zero_comp])) := by
  refine
    KernelFork.IsLimit.ofι _ _
      (fun {W'} u hu =>
        hf.lift
          (KernelFork.ofι u
            (by
              have : (u ≫ g) ≫ m = 0 := by
                rw [Category.assoc]; exact hu
              exact (cancel_mono m).1 (by simpa using this))))
      (fun {W'} u hu => hf.fac _ WalkingParallelPair.zero)
      (fun {W'} u hu l hl => by
        have : Mono f := by
          rw [Preadditive.mono_iff_cancel_zero]; intro Z' v hv
          exact Fork.IsLimit.hom_ext hf (by simpa [Fork.ι] using hv)
        apply (cancel_mono f).1
        exact
          hl.trans
            (hf.fac
                (KernelFork.ofι u
                  (by
                    have : (u ≫ g) ≫ m = 0 := by
                      rw [Category.assoc]; exact hu
                    exact (cancel_mono m).1 (by simpa using this)))
                WalkingParallelPair.zero).symm)

/-- If `f` is a kernel of `g`, then `e ≫ f` (for an iso `e`) is also a kernel of `g`. -/
noncomputable def ker_precomp_iso {W' W₀ X₀ Y₀ : A} (e : W' ⟶ W₀) [IsIso e] (f : W₀ ⟶ X₀)
    (g : X₀ ⟶ Y₀) (h0 : f ≫ g = 0) (hf : IsLimit (KernelFork.ofι f h0)) :
    IsLimit
      (KernelFork.ofι (e ≫ f) (show (e ≫ f) ≫ g = 0 by rw [Category.assoc, h0, comp_zero])) := by
  haveI : Mono f := by
    rw [Preadditive.mono_iff_cancel_zero]; intro Z' v hv
    exact Fork.IsLimit.hom_ext hf (by simpa [Fork.ι] using hv)
  refine
    KernelFork.IsLimit.ofι _ _ (fun {W''} u hu => hf.lift (KernelFork.ofι u hu) ≫ (asIso e).inv)
      (fun {W''} u hu => by
        have hfac : hf.lift (KernelFork.ofι u hu) ≫ f = u :=
          hf.fac (KernelFork.ofι u hu) WalkingParallelPair.zero
        change (hf.lift (KernelFork.ofι u hu) ≫ (asIso e).inv) ≫ e ≫ f = u
        simp only [asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
        simpa using hfac)
      (fun {W''} u hu l hl => by
        have hfac : hf.lift (KernelFork.ofι u hu) ≫ f = u :=
          hf.fac (KernelFork.ofι u hu) WalkingParallelPair.zero
        have hl' : (l ≫ e) ≫ f = u := by
          rw [Category.assoc]; exact hl
        have hle : l ≫ e = hf.lift (KernelFork.ofι u hu) := (cancel_mono f).1 (hl'.trans hfac.symm)
        have hfin : l = (l ≫ e) ≫ (asIso e).inv := by simp
        rw [hle] at hfin
        exact hfin)

/-- "Conjugation by isomorphisms" for kernels: if `f` is a kernel of `g`, `ε`, `δ` are
isos, and the square `g ≫ δ = ε ≫ g'` commutes, then `f ≫ ε` is a kernel of `g'`. -/
noncomputable def ker_conj_target {K₀ Y₀ Z₀ Y' Z' : A} (f : K₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀) (ε : Y₀ ⟶ Y')
    [IsIso ε] (δ : Z₀ ⟶ Z') [IsIso δ] (g' : Y' ⟶ Z') (sq : g ≫ δ = ε ≫ g') (h0 : f ≫ g = 0)
    (hf : IsLimit (KernelFork.ofι f h0)) :
    IsLimit
      (KernelFork.ofι (f ≫ ε)
        (show (f ≫ ε) ≫ g' = 0 by
          rw [Category.assoc, ← sq, ← Category.assoc, h0, zero_comp])) := by
  haveI : Mono f := by
    rw [Preadditive.mono_iff_cancel_zero]; intro Z2 v hv
    exact Fork.IsLimit.hom_ext hf (by simpa [Fork.ι] using hv)
  have hkey : inv ε ≫ g = g' ≫ inv δ := by
    rw [← cancel_epi ε, ← cancel_mono δ]
    simp only [IsIso.hom_inv_id_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact sq
  have hzero : ∀ {W : A} (u : W ⟶ Y'), u ≫ g' = 0 → (u ≫ inv ε) ≫ g = 0 := by
    intro W u hu
    rw [Category.assoc, hkey, ← Category.assoc, hu, zero_comp]
  refine
    KernelFork.IsLimit.ofι _ _ (fun {W} u hu => hf.lift (KernelFork.ofι (u ≫ inv ε) (hzero u hu)))
      (fun {W} u hu => by
        have hfac : hf.lift (KernelFork.ofι (u ≫ inv ε) (hzero u hu)) ≫ f = u ≫ inv ε :=
          hf.fac (KernelFork.ofι (u ≫ inv ε) (hzero u hu)) WalkingParallelPair.zero
        change hf.lift (KernelFork.ofι (u ≫ inv ε) (hzero u hu)) ≫ f ≫ ε = u
        rw [← Category.assoc, hfac]
        simp)
      (fun {W} u hu l hl => by
        have hfac : hf.lift (KernelFork.ofι (u ≫ inv ε) (hzero u hu)) ≫ f = u ≫ inv ε :=
          hf.fac (KernelFork.ofι (u ≫ inv ε) (hzero u hu)) WalkingParallelPair.zero
        have hlf : l ≫ f = u ≫ inv ε :=
          (cancel_mono ε).1
            (by
              have hl' : l ≫ f ≫ ε = u := hl
              simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
              rw [hl'])
        exact (cancel_mono f).1 (hlf.trans hfac.symm))

/-- If `f : W ⟶ K.X i` is a kernel of `K.d i j` and `l : W ⟶ K.cycles i` lifts `f`
through `K.iCycles i`, then `l` is an isomorphism. -/
lemma isIso_lift_of_kernel (K : CochainComplex A ℤ) (i j : ℤ) (hj : (ComplexShape.up ℤ).next i = j)
    {W : A} (f : W ⟶ K.X i) (hf0 : f ≫ K.d i j = 0) (hf : IsLimit (KernelFork.ofι f hf0))
    (l : W ⟶ K.cycles i) (hl : l ≫ K.iCycles i = f) : IsIso l := by
  have hker : IsLimit (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) := K.cyclesIsKernel i j hj
  set m : K.cycles i ⟶ W := hf.lift (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) with hm
  have key : m ≫ f = K.iCycles i :=
    hf.fac (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) WalkingParallelPair.zero
  have : Mono f := Fork.IsLimit.mono hf
  refine ⟨m, ?_, ?_⟩
  · rw [← cancel_mono f, Category.assoc, key, hl, Category.id_comp]
  · apply Fork.IsLimit.hom_ext hker
    change (m ≫ l) ≫ K.iCycles i = 𝟙 _ ≫ K.iCycles i
    rw [Category.assoc, hl, key, Category.id_comp]

/-- `R^1 = B 1`. -/
lemma RX_one : RX d X D 1 = D.B 1 := by
  rw [RX_nonneg d X D 1 (by norm_num)]; rfl

/-- The differential of `R` into degree `0` vanishes (`R` is `0` in negative degrees). -/
lemma Rd_neg0 : (Rcomplex d X D).d (-1) 0 = 0 := by
  change Rd d X D (-1) 0 = 0; unfold Rd; rw [dite_eq_right]; rintro ⟨_, h⟩; omega

/-- `emb 0` is a kernel of `delta 0` (since `delta 0 = π(emb 0) ≫ mono`). -/
noncomputable def emb0_ker_delta0 :
    IsLimit
      (KernelFork.ofι (D.emb 0)
        (show D.emb 0 ≫ delta d X D 0 = 0 by
          unfold delta; rw [← Category.assoc, cokernel.condition, zero_comp])) := by
  haveI := D.emb_mono 0; haveI := D.emb_mono 1
  have hk0 : IsLimit (KernelFork.ofι (D.emb 0) (cokernel.condition (D.emb 0))) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  have key :=
    ker_postcomp_mono (D.emb 0) (cokernel.π (D.emb 0)) (eqToHom (D.hCsucc 0).symm ≫ D.emb 1)
      (cokernel.condition (D.emb 0)) hk0
  convert key using 2

/-- Commuting square relating `delta 0` and `R.d 0 1` (both equal to `delta 0` up to
the `eqToHom` transports baked into `R`). -/
lemma sq01 :
    delta d X D 0 ≫ eqToHom (show D.B 1 = (Rcomplex d X D).X 1 by rw [Rcomplex_X, RX_one]) =
      eqToHom (show D.B 0 = (Rcomplex d X D).X 0 by rw [Rcomplex_X, RX_zero]) ≫
        (Rcomplex d X D).d 0 1 := by
  change _ = _ ≫ Rd d X D 0 1
  unfold Rd
  rw [dite_eq_left ⟨by ring, le_rfl⟩]
  change delta d X D 0 ≫ eqToHom _ = eqToHom _ ≫ eqToHom _ ≫ delta d X D (0 : ℤ).toNat ≫ eqToHom _
  simp only [Int.toNat_zero, ← Category.assoc, eqToHom_refl, Category.id_comp]

/-- The augmentation `augφ : X ⟶ R⁰` is a kernel of `R.d 0 1`. -/
noncomputable def augφ_isKernel :
    IsLimit (KernelFork.ofι (augφ d X D) (augφ_cond d X D 1 (by simp))) := by
  haveI := D.emb_mono 0; haveI := D.emb_mono 1
  have hemb0d : D.emb 0 ≫ delta d X D 0 = 0 := by
    unfold delta; rw [← Category.assoc, cokernel.condition, zero_comp]
  have stepA :=
    ker_conj_target (D.emb 0) (delta d X D 0)
      (eqToHom (show D.B 0 = (Rcomplex d X D).X 0 by rw [Rcomplex_X, RX_zero]))
      (eqToHom (show D.B 1 = (Rcomplex d X D).X 1 by rw [Rcomplex_X, RX_one]))
      ((Rcomplex d X D).d 0 1) (sq01 d X D) hemb0d (emb0_ker_delta0 d X D)
  have stepB :=
    ker_precomp_iso (eqToHom D.hC0.symm)
      (D.emb 0 ≫ eqToHom (show D.B 0 = (Rcomplex d X D).X 0 by rw [Rcomplex_X, RX_zero]))
      ((Rcomplex d X D).d 0 1)
      (show (D.emb 0 ≫ eqToHom _) ≫ (Rcomplex d X D).d 0 1 = 0 by
        rw [Category.assoc, ← sq01 d X D, ← Category.assoc, hemb0d, zero_comp])
      stepA
  convert stepB using 2
  rw [augφ]

/-- The augmentation `augMap d X D` induces an isomorphism on degree-`0` cohomology. -/
lemma augMap_homologyMap_zero_isIso : IsIso (HomologicalComplex.homologyMap (augMap d X D) 0) := by
  have hsπ : IsIso (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).homologyπ 0) :=
    HomologicalComplex.isIso_homologyπ _ (-1) 0 (by simp [CochainComplex.prev]) (by simp)
  have htπ : IsIso ((Rcomplex d X D).homologyπ 0) :=
    HomologicalComplex.isIso_homologyπ _ (-1) 0 (by simp [CochainComplex.prev]) (Rd_neg0 d X D)
  have hcyc : IsIso (HomologicalComplex.cyclesMap (augMap d X D) 0) := by
    set S := (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X with hS
    have hsι : IsIso (S.iCycles 0) :=
      HomologicalComplex.isIso_iCycles _ 0 1 (by simp)
        (by
          rw [hS]; simp)
    have hf0 : (S.iCycles 0 ≫ (augMap d X D).f 0) ≫ (Rcomplex d X D).d 0 1 = 0 := by
      rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc,
        HomologicalComplex.iCycles_d, zero_comp]
    have hfeq :
      (augMap d X D).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ augφ d X D :=
      HomologicalComplex.mkHomFromSingle_f _ _
    have hker : IsLimit (KernelFork.ofι (S.iCycles 0 ≫ (augMap d X D).f 0) hf0) := by
      have heq :
        S.iCycles 0 ≫ (augMap d X D).f 0 =
          (S.iCycles 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom) ≫
            augφ d X D := by
        rw [hfeq, Category.assoc]
      rw [show
          (KernelFork.ofι (S.iCycles 0 ≫ (augMap d X D).f 0) hf0) =
            KernelFork.ofι
              ((S.iCycles 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom) ≫
                augφ d X D)
              (by
                rw [← heq]; exact hf0)
          from by congr 1]
      exact
        ker_precomp_iso _ (augφ d X D) ((Rcomplex d X D).d 0 1) (augφ_cond d X D 1 (by simp))
          (augφ_isKernel d X D)
    exact
      isIso_lift_of_kernel (Rcomplex d X D) 0 1 (by simp) (S.iCycles 0 ≫ (augMap d X D).f 0) hf0
        hker (HomologicalComplex.cyclesMap (augMap d X D) 0)
        (by rw [HomologicalComplex.cyclesMap_i])
  have nat := HomologicalComplex.homologyπ_naturality (augMap d X D) 0
  have hmap :
    HomologicalComplex.homologyMap (augMap d X D) 0 =
      inv (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).homologyπ 0) ≫
        HomologicalComplex.cyclesMap (augMap d X D) 0 ≫ (Rcomplex d X D).homologyπ 0 := by
    rw [← nat]; simp
  rw [hmap]; infer_instance

/-- The augmentation `X[0] ⟶ Rcomplex d X D` is a quasi-isomorphism. -/
theorem augMap_quasiIso : QuasiIso (augMap d X D) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain rfl | hi := eq_or_ne i 0
  · exact augMap_homologyMap_zero_isIso d X D
  · have hsrc :
      IsZero (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).homology i) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact
        HomologicalComplex.ExactAt.of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    have htgt : IsZero ((Rcomplex d X D).homology i) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact HomologicalComplex.ExactAt.of_isZero (Rcomplex_neg d X D i hi)
      · exact Rcomplex_exactAt_pos d X D i (by omega)
    exact ⟨hsrc.from_ _, hsrc.eq_of_src _ _, htgt.eq_of_tgt _ _⟩

/-- The data `D` yields a complex `R`, zero in negative degrees and with `d (R.X n) = 0` for
`n ≥ 0`, with a quasi-isomorphism `X[0] ⟶ R`. -/
theorem coresToComplex (d : A → ℕ∞) (X : A) (D : CoresData d X) :
    ∃ (R : CochainComplex A ℤ) (_ : ∀ n : ℤ, 0 ≤ n → d (R.X n) = 0) (_ :
      ∀ n : ℤ, n < 0 → CategoryTheory.Limits.IsZero (R.X n)) (ι :
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X ⟶ R), QuasiIso ι :=
  ⟨Rcomplex d X D, Rcomplex_pos d X D, Rcomplex_neg d X D, augMap d X D, augMap_quasiIso d X D⟩

end CoresConstruction

/-- Every object `X` admits a right coresolution by objects of `d`-value `0`: a complex `R`,
zero in negative degrees and with `d (R.X n) = 0` for `n ≥ 0`, with a quasi-isomorphism
`X[0] ⟶ R`. -/
theorem exists_dZeroCoresolution {d : A → ℕ∞} (hd : BoundedCohomologicalDimension d) (X : A) :
    ∃ (R : CochainComplex A ℤ) (_ : ∀ n : ℤ, 0 ≤ n → d (R.X n) = 0) (_ :
      ∀ n : ℤ, n < 0 → CategoryTheory.Limits.IsZero (R.X n)) (ι :
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X ⟶ R), QuasiIso ι :=
  CoresConstruction.coresToComplex d X (CoresConstruction.buildCores d hd.embed X)

/-- Under the growth hypothesis `TendsToNegInfty d K`, for each `m` the set of degrees
`q ≤ m` with `d (K.X q)` finite and `m ≤ q + d (K.X q)` is finite. -/
theorem ce_fiber_finite (d : A → ℕ∞) (K : CochainComplex A ℤ) (hK : TendsToNegInfty d K) (m : ℤ) :
    {q : ℤ | q ≤ m ∧ ∃ k : ℕ, d (K.X q) = (k : ℕ∞) ∧ m ≤ q + (k : ℤ)}.Finite := by
  obtain ⟨n₀, h⟩ := hK (m - 1)
  refine (Set.finite_Icc (n₀ + 1) m).subset fun q hq => ?_
  simp only [Set.mem_ofPred_eq] at hq
  obtain ⟨hqm, k, hdk, hmk⟩ := hq
  simp only [Set.mem_Icc]
  refine ⟨?_, hqm⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨k', hdk', hk'⟩ := h q (by omega)
  rw [hdk] at hdk'
  have : k = k' := by exact_mod_cast hdk'
  omega

/-- For every `m` and `k`, there is a quasi-isomorphism `g : K ⟶ K'` with `d (K'.X n) = 0`
for `m ≤ n < m + k` and `d (K'.X n) = d (K.X n)` for `n < m`. -/
theorem exists_dZero_window (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (m : ℤ) (k : ℕ) :
    ∃ (K' : CochainComplex A ℤ) (g : K ⟶ K'),
      QuasiIso g ∧
        (∀ n : ℤ, m ≤ n → n < m + (k : ℤ) → d (K'.X n) = 0) ∧
        (∀ n : ℤ, n < m → d (K'.X n) = d (K.X n)) := by
  induction k with
  | zero =>
    refine ⟨K, 𝟙 K, inferInstance, ?_, ?_⟩
    · intro n hmn hn
      push_cast at hn
      omega
    · intro n _
      rfl
  | succ k ih =>
    obtain ⟨K₀, g₀, hg₀, hwin₀, hbel₀⟩ := ih
    by_cases hpos : 0 < d (K₀.X (m + (k : ℤ)))
    · obtain ⟨K₁, g₁, hg₁, hzero, hbound, hoff⟩ := elementary_replacement d hd K₀ (m + (k : ℤ))
      refine ⟨K₁, g₀ ≫ g₁, ?_, ?_, ?_⟩
      · have := hg₀; have := hg₁; exact inferInstance
      · intro n hmn hn
        by_cases hne : n = m + (k : ℤ)
        · rw [hne]; exact hzero
        · have hlt : n < m + (k : ℤ) := by
            push_cast at hn; omega
          rw [hoff n hne
              (by
                push_cast at hn ⊢; omega)]
          exact hwin₀ n hmn hlt
      · intro n hn
        rw [hoff n (by omega) (by omega)]
        exact hbel₀ n hn
    · have hzero : d (K₀.X (m + (k : ℤ))) = 0 := by
        simpa only [not_lt, nonpos_iff_eq_zero] using hpos
      refine ⟨K₀, g₀, hg₀, ?_, hbel₀⟩
      intro n hmn hn
      by_cases hne : n = m + (k : ℤ)
      · rw [hne]; exact hzero
      · exact
          hwin₀ n hmn
            (by
              push_cast at hn; omega)

end Stacks.BoundedCohomologicalDimension
