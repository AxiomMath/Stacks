module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.StrictCokernel
import all StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.StrictCokernel

/-!
# The filtered complex of a tower of filtered objects

A `ℕ`-indexed tower `I^0 ⟶ I^1 ⟶ ⋯` of filtered objects with vanishing consecutive composites
assembles into a filtered cochain complex concentrated in degrees `≥ 0`; its graded pieces are the
complexes of the graded pieces, and a filtered complex concentrated in degree `0` maps to it.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveResolutionDegreeZero

namespace CochainComplex.FilteredInjective.Resolution

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

section Tower

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The cochain complex of `𝒜` concentrated in degrees `≥ 0` built from a `ℕ`-indexed tower `M`
with differentials `e` whose consecutive composites vanish: `M^n` in degree `n ≥ 0` and `0` in
negative degrees.

This is the shape in which the source's `I^0 ⟶ I^1 ⟶ ⋯` becomes a complex; it is applied both to
the underlying objects of a tower of filtered objects and, for each `p`, to its `p`-th filtration
steps, which is what makes `F^p I^•` a subcomplex of `I^•`. -/
private noncomputable def towerComplex (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) : CochainComplex 𝒜 ℤ :=
  (CochainComplex.of M e he).extend ComplexShape.embeddingUpNat

private lemma isStrictlyGE_towerComplex (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) : (towerComplex M e he).IsStrictlyGE 0 := by
  dsimp only [towerComplex]
  infer_instance

/-- In degree `n = k` with `k : ℕ` the complex of a tower is the tower's `k`-th object. -/
private noncomputable def towerComplexXIso (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) {n : ℤ} {k : ℕ} (h : (k : ℤ) = n) :
    (towerComplex M e he).X n ≅ M k :=
  HomologicalComplex.extendXIso _ _ h

/-- In negative degrees the complex of a tower vanishes. -/
private lemma isZero_towerComplex_X (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) {n : ℤ} (hn : n < 0) :
    IsZero ((towerComplex M e he).X n) := by
  have := isStrictlyGE_towerComplex M e he
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 n hn

/-- The morphism of complexes induced by a morphism of towers. -/
private noncomputable def towerComplexMap {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {he : ∀ n : ℕ, e n ≫ e (n + 1) = 0} {f : ∀ n : ℕ, N n ⟶ N (n + 1)}
    {hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0} (φ : ∀ n : ℕ, M n ⟶ N n)
    (hφ : ∀ n : ℕ, φ n ≫ f n = e n ≫ φ (n + 1)) :
    towerComplex M e he ⟶ towerComplex N f hf :=
  HomologicalComplex.extendMap (CochainComplex.ofHom φ (fun i => by simpa using hφ i)) _

private lemma towerComplexMap_f {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {he : ∀ n : ℕ, e n ≫ e (n + 1) = 0} {f : ∀ n : ℕ, N n ⟶ N (n + 1)}
    {hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0} (φ : ∀ n : ℕ, M n ⟶ N n)
    (hφ : ∀ n : ℕ, φ n ≫ f n = e n ≫ φ (n + 1)) {n : ℤ} {k : ℕ} (h : (k : ℤ) = n) :
    (towerComplexMap φ hφ).f n =
      (towerComplexXIso M e he h).hom ≫ φ k ≫ (towerComplexXIso N f hf h).inv :=
  HomologicalComplex.extendMap_f _ _ h

/-- A morphism of towers that is a monomorphism in every degree induces a monomorphism of
complexes: this is what makes the filtration steps of a tower of filtered objects into
subcomplexes. -/
private lemma mono_towerComplexMap {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {he : ∀ n : ℕ, e n ≫ e (n + 1) = 0} {f : ∀ n : ℕ, N n ⟶ N (n + 1)}
    {hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0} (φ : ∀ n : ℕ, M n ⟶ N n)
    (hφ : ∀ n : ℕ, φ n ≫ f n = e n ≫ φ (n + 1)) (hm : ∀ n : ℕ, Mono (φ n)) :
    Mono (towerComplexMap (he := he) (hf := hf) φ hφ) := by
  refine HomologicalComplex.mono_of_mono_f _ (fun n => ?_)
  rcases lt_or_ge n 0 with hn | hn
  · exact ⟨fun {_} g h _ => (isZero_towerComplex_X M e he hn).eq_of_tgt g h⟩
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [towerComplexMap_f φ hφ (k := k) rfl]
    have := hm k
    infer_instance

/-- Composites of morphisms of towers are computed degreewise, so a degreewise identity between
composites of tower morphisms is an identity of morphisms of complexes. This is the coherence that
makes the subcomplexes `F^p I^•` a filtration. -/
private lemma towerComplexMap_comp_eq {M N P : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {he : ∀ n : ℕ, e n ≫ e (n + 1) = 0} {f : ∀ n : ℕ, N n ⟶ N (n + 1)}
    {hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0} {g : ∀ n : ℕ, P n ⟶ P (n + 1)}
    {hg : ∀ n : ℕ, g n ≫ g (n + 1) = 0} (φ : ∀ n : ℕ, M n ⟶ N n)
    (hφ : ∀ n : ℕ, φ n ≫ f n = e n ≫ φ (n + 1)) (χ : ∀ n : ℕ, N n ⟶ P n)
    (hχ : ∀ n : ℕ, χ n ≫ g n = f n ≫ χ (n + 1)) (ξ : ∀ n : ℕ, M n ⟶ P n)
    (hξ : ∀ n : ℕ, ξ n ≫ g n = e n ≫ ξ (n + 1)) (h : ∀ n : ℕ, φ n ≫ χ n = ξ n) :
    towerComplexMap (he := he) (hf := hf) φ hφ ≫
        towerComplexMap (he := hf) (hf := hg) χ hχ =
      towerComplexMap (he := he) (hf := hg) ξ hξ := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · exact (isZero_towerComplex_X P g hg hn).eq_of_tgt _ _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HomologicalComplex.comp_f, towerComplexMap_f φ hφ (k := k) rfl,
      towerComplexMap_f χ hχ (k := k) rfl, towerComplexMap_f ξ hξ (k := k) rfl, ← h k]
    simp

/-! ### The filtered complex of a tower of filtered objects -/

/-- The `p`-th filtration step of the complex of a tower `I` of filtered objects: the complex of
the tower `n ↦ F^p I^n`, which is a subcomplex of the complex of `n ↦ I^n` because the
differentials are morphisms of filtered objects. -/
private noncomputable def towerStepComplex (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  towerComplex (fun n => (I n).filtration.obj (op p)) (fun n => (d n).natTrans.app (op p))
    (fun n => natTrans_app_eq_zero (d n ≫ d (n + 1)) (hd n) (op p))

/-- The inclusion `F^p I^• ⟶ I^•` of the `p`-th filtration step. -/
private noncomputable def towerStepComplexι (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    towerStepComplex I d hd p ⟶ towerComplex (fun n => (I n).X) (fun n => (d n).hom) hd :=
  towerComplexMap (he := fun n => natTrans_app_eq_zero (d n ≫ d (n + 1)) (hd n) (op p)) (hf := hd)
    (fun n => (I n).filtration.ι.app (op p)) (fun n => ((d n).comm (op p)).symm)

private lemma mono_towerStepComplexι (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    Mono (towerStepComplexι I d hd p) :=
  mono_towerComplexMap _ _ (fun _ => inferInstance)

/-- The transition `F^{p + 1} I^• ⟶ F^p I^•` between two consecutive filtration steps. -/
private noncomputable def towerStepComplexMap (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    towerStepComplex I d hd (p + 1) ⟶ towerStepComplex I d hd p :=
  towerComplexMap
    (he := fun n => natTrans_app_eq_zero (d n ≫ d (n + 1)) (hd n) (op (p + 1)))
    (hf := fun n => natTrans_app_eq_zero (d n ≫ d (n + 1)) (hd n) (op p))
    (fun n => (I n).filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (fun n => (d n).natTrans.naturality _)

private lemma towerStepComplexMap_comp_ι (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    towerStepComplexMap I d hd p ≫ towerStepComplexι I d hd p =
      towerStepComplexι I d hd (p + 1) :=
  towerComplexMap_comp_eq _ _ _ _ _ _ (fun n => (I n).filtration.diagram_map_comp_ι_app _)

/-- The filtered complex assembled from a tower `I^0 ⟶ I^1 ⟶ ⋯` of filtered objects whose
consecutive differentials compose to zero: the complex of the underlying objects in degrees `≥ 0`,
filtered by the subcomplexes `F^p I^•`. -/
private noncomputable def towerFilteredComplex (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) :
    FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  X := towerComplex (fun n => (I n).X) (fun n => (d n).hom) hd
  filtration := filtrationOfSteps
    (fun p => @MonoOver.mk _ _ _ _ (towerStepComplexι I d hd p) (mono_towerStepComplexι I d hd p))
    (fun _ _ hqp => nonempty_hom_of_steps
      (fun p => @MonoOver.mk _ _ _ _ (towerStepComplexι I d hd p)
        (mono_towerStepComplexι I d hd p))
      (fun r => ⟨MonoOver.homMk (towerStepComplexMap I d hd r)
        (towerStepComplexMap_comp_ι I d hd r)⟩) hqp)

private lemma towerFilteredComplex_ι_app (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    (towerFilteredComplex I d hd).filtration.ι.app (op p) = towerStepComplexι I d hd p := rfl

private lemma isStrictlyGE_towerFilteredComplex (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) :
    (towerFilteredComplex I d hd).X.IsStrictlyGE 0 :=
  isStrictlyGE_towerComplex _ _ hd

omit [Abelian 𝒜] in
/-- Conjugating an isomorphism by isomorphisms gives an isomorphism. -/
private lemma isIso_hom_comp_comp_hom {A B X Y : 𝒜} (e : A ≅ X) (g : Y ≅ B) (f : X ⟶ Y)
    (hf : IsIso f) : IsIso (e.hom ≫ f ≫ g.hom) := by
  have := hf
  infer_instance

/-- The filtration of the complex of a tower of finitely filtered objects is finite in every
degree: in degree `n = k ≥ 0` the bounds of `F^• I^k` serve, and in negative degrees everything
vanishes. -/
private lemma exists_isIso_isZero_towerFilteredComplex (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0)
    (hfin : ∀ n : ℕ, (I n).filtration.IsFinite) (n : ℤ) :
    ∃ p q : ℤ, IsIso (((towerFilteredComplex I d hd).filtration.ι.app (op p)).f n) ∧
      IsZero (((towerFilteredComplex I d hd).filtration.obj (op q)).X n) := by
  rcases lt_or_ge n 0 with hn | hn
  · refine ⟨0, 0, IsZero.isIso ?_ (isZero_towerComplex_X _ _ hd hn) _,
      isZero_towerComplex_X _ _ _ hn⟩
    exact isZero_towerComplex_X _ _ _ hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    obtain ⟨p, hp⟩ := (hfin k).exists_isIso_ι
    obtain ⟨q, hq⟩ := (hfin k).exists_isZero_obj
    refine ⟨p, q, ?_, ?_⟩
    · have h1 : (towerStepComplexι I d hd p).f (k : ℤ) =
          (towerComplexXIso (fun n => (I n).filtration.obj (op p))
              (fun n => (d n).natTrans.app (op p)) _ (k := k) rfl).hom ≫
            (I k).filtration.ι.app (op p) ≫
              (towerComplexXIso (fun n => (I n).X) (fun n => (d n).hom) hd (k := k) rfl).inv :=
        towerComplexMap_f _ (fun n => ((d n).comm (op p)).symm) rfl
      rw [towerFilteredComplex_ι_app, h1]
      exact isIso_hom_comp_comp_hom _
        (towerComplexXIso (fun n => (I n).X) (fun n => (d n).hom) hd (k := k) rfl).symm _ hp
    · exact IsZero.of_iso hq (towerComplexXIso _ _ _ (k := k) rfl)

/-! ### Maps out of a complex concentrated in degree `0` -/

/-- The components of `homFromDegreeZero`: the morphism `g : C^0 ⟶ L^0` in degree `0`, read
through `HomologicalComplex.XIsoOfEq`, and `0` in every other degree. -/
public noncomputable def homFromDegreeZeroF {C L : CochainComplex 𝒜 ℤ} (g : C.X 0 ⟶ L.X 0)
    (n : ℤ) : C.X n ⟶ L.X n :=
  if h : n = 0 then (C.XIsoOfEq h).hom ≫ g ≫ (L.XIsoOfEq h.symm).hom else 0

/-- In degree `0` the components of `homFromDegreeZero` are the given morphism. -/
public lemma homFromDegreeZeroF_zero {C L : CochainComplex 𝒜 ℤ} (g : C.X 0 ⟶ L.X 0) :
    homFromDegreeZeroF g 0 = g := by
  simp [homFromDegreeZeroF]

/-- Away from degree `0` the components of `homFromDegreeZero` vanish. -/
public lemma homFromDegreeZeroF_of_ne {C L : CochainComplex 𝒜 ℤ} (g : C.X 0 ⟶ L.X 0) {n : ℤ}
    (hn : n ≠ 0) : homFromDegreeZeroF g n = 0 := by
  simp [homFromDegreeZeroF, hn]

/-- A morphism out of a cochain complex `C^•` concentrated in degree `0`, given by its degree `0`
component `g`. Only one square can fail to commute, and `g ≫ d_L^0 = 0` is exactly that square. -/
public noncomputable def homFromDegreeZero {C L : CochainComplex 𝒜 ℤ}
    (hC : ∀ n : ℤ, n ≠ 0 → IsZero (C.X n)) (g : C.X 0 ⟶ L.X 0) (hg : g ≫ L.d 0 1 = 0) : C ⟶ L where
  f n := homFromDegreeZeroF g n
  comm' i j hij := by
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := by simpa using hij.symm
      rw [homFromDegreeZeroF_zero, homFromDegreeZeroF_of_ne g one_ne_zero, comp_zero, hg]
    · rw [homFromDegreeZeroF_of_ne g hi, zero_comp]
      by_cases hj : j = 0
      · subst hj
        obtain rfl : i = -1 := by simp only [ComplexShape.up_Rel] at hij; omega
        exact ((hC (-1) (by decide)).eq_of_src _ _).symm
      · rw [homFromDegreeZeroF_of_ne g hj, comp_zero]

/-- A morphism out of a complex concentrated in degree `0` is the given morphism in degree `0`. -/
public lemma homFromDegreeZero_f_zero {C L : CochainComplex 𝒜 ℤ}
    (hC : ∀ n : ℤ, n ≠ 0 → IsZero (C.X n)) (g : C.X 0 ⟶ L.X 0) (hg : g ≫ L.d 0 1 = 0) :
    (homFromDegreeZero hC g hg).f 0 = g :=
  homFromDegreeZeroF_zero g

/-- A morphism out of a complex concentrated in degree `0` vanishes in every other degree. -/
public lemma homFromDegreeZero_f_of_ne {C L : CochainComplex 𝒜 ℤ}
    (hC : ∀ n : ℤ, n ≠ 0 → IsZero (C.X n)) (g : C.X 0 ⟶ L.X 0) (hg : g ≫ L.d 0 1 = 0) {n : ℤ}
    (hn : n ≠ 0) : (homFromDegreeZero hC g hg).f n = 0 :=
  homFromDegreeZeroF_of_ne g hn

/-- Two morphisms out of a complex concentrated in degree `0` that agree in degree `0` agree. -/
private lemma hom_ext_of_degreeZero {C L : CochainComplex 𝒜 ℤ}
    (hC : ∀ n : ℤ, n ≠ 0 → IsZero (C.X n)) {φ ψ : C ⟶ L} (h : φ.f 0 = ψ.f 0) : φ = ψ := by
  ext n
  by_cases hn : n = 0
  · subst hn; exact h
  · exact (hC n hn).eq_of_src _ _

/-- A complex is exact in a degree in which it vanishes. -/
private lemma exactAt_of_isZero_X (C : CochainComplex 𝒜 ℤ) (i : ℤ) (h : IsZero (C.X i)) :
    C.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-! ### Cokernels of morphisms of complexes, computed degreewise -/

/-- The cokernel projection of a morphism of complexes, read in one degree through the
identification of the cokernel with the degreewise cokernel. -/
private lemma π_comp_evalCokernelIso_inv {L T : CochainComplex 𝒜 ℤ} (φ : L ⟶ T) (i : ℤ) :
    cokernel.π (φ.f i) ≫
        (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) φ).inv =
      (cokernel.π φ).f i := by
  rw [Iso.comp_inv_eq]
  exact (PreservesCokernel.π_iso_hom (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) φ).symm

/-- A morphism out of the cokernel of a morphism of complexes, read in one degree. -/
private lemma cokernelDesc_f {K L T : CochainComplex 𝒜 ℤ} (φ : K ⟶ L) (t : L ⟶ T)
    (w : φ ≫ t = 0) (i : ℤ) (wi : φ.f i ≫ t.f i = 0) :
    (cokernel.desc φ t w).f i =
      (PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i) φ).hom ≫
        cokernel.desc (φ.f i) (t.f i) wi := by
  rw [← Iso.inv_comp_eq, ← cancel_epi (cokernel.π (φ.f i)), ← Category.assoc,
    π_comp_evalCokernelIso_inv, ← HomologicalComplex.comp_f, cokernel.π_desc, cokernel.π_desc]

/-! ### The differential of the complex of a tower -/

/-- The differential of the complex of a tower, between two consecutive nonnegative degrees. -/
private lemma towerComplex_d (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) (k : ℕ) {i j : ℤ} (hi : (k : ℤ) = i)
    (hj : ((k + 1 : ℕ) : ℤ) = j) :
    (towerComplex M e he).d i j = (towerComplexXIso M e he hi).hom ≫ e k ≫
      (towerComplexXIso M e he hj).inv := by
  dsimp only [towerComplex, towerComplexXIso]
  rw [HomologicalComplex.extend_d_eq _ _ hi hj]
  simp

/-- The complex of a tower is exact in degree `k + 1` as soon as the tower's short complex
`M^k ⟶ M^{k + 1} ⟶ M^{k + 2}` is exact: in nonnegative degrees the complex is the tower. -/
private lemma exactAt_towerComplex (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) (k : ℕ)
    (hex : (ShortComplex.mk (e k) (e (k + 1)) (he k)).Exact) :
    (towerComplex M e he).ExactAt ((k : ℤ) + 1) := by
  have h1 : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
  rw [← h1]
  dsimp only [towerComplex]
  refine (HomologicalComplex.extend_exactAt_iff (CochainComplex.of M e he)
    ComplexShape.embeddingUpNat (j := k + 1) (j' := ((k + 1 : ℕ) : ℤ)) rfl).mpr ?_
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 2)
      (ComplexShape.prev_eq' _ (by simp)) (ComplexShape.next_eq' _ (by simp))]
  exact exact_of_eq (CochainComplex.of_d M e k).symm (CochainComplex.of_d M e (k + 1)).symm hex

/-! ### The cokernel of a morphism of towers -/

/-- The tower of cokernels of a morphism of towers. -/
private noncomputable def cokernelTowerMap {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (n : ℕ) :
    cokernel (ω n) ⟶ cokernel (ω (n + 1)) :=
  cokernel.map (ω n) (ω (n + 1)) (e n) (f n) (hω n)

private lemma π_comp_cokernelTowerMap {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (n : ℕ) :
    cokernel.π (ω n) ≫ cokernelTowerMap ω hω n = f n ≫ cokernel.π (ω (n + 1)) := by
  dsimp only [cokernelTowerMap]; simp

private lemma cokernelTowerMap_comp_eq_zero {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) (n : ℕ) :
    cokernelTowerMap ω hω n ≫ cokernelTowerMap ω hω (n + 1) = 0 := by
  rw [← cancel_epi (cokernel.π (ω n)), comp_zero, ← Category.assoc,
    π_comp_cokernelTowerMap ω hω n, Category.assoc, π_comp_cokernelTowerMap ω hω (n + 1),
    ← Category.assoc, hf n, zero_comp]

/-- The complex of the tower of cokernels of a morphism of towers. -/
private noncomputable def cokernelTower {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) :
    CochainComplex 𝒜 ℤ :=
  towerComplex (fun n => cokernel (ω n)) (cokernelTowerMap ω hω)
    (cokernelTowerMap_comp_eq_zero ω hω hf)

private noncomputable def cokernelTowerXIso {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0)
    {n : ℤ} {k : ℕ} (h : (k : ℤ) = n) : (cokernelTower ω hω hf).X n ≅ cokernel (ω k) :=
  towerComplexXIso _ _ _ h

private lemma isZero_cokernelTower_X {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0)
    {n : ℤ} (hn : n < 0) : IsZero ((cokernelTower ω hω hf).X n) :=
  isZero_towerComplex_X _ _ _ hn

/-- The degreewise cokernel projection, as a morphism of complexes. -/
private noncomputable def cokernelTowerπ {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) :
    towerComplex N f hf ⟶ cokernelTower ω hω hf :=
  towerComplexMap (he := hf) (hf := cokernelTowerMap_comp_eq_zero ω hω hf)
    (fun n => cokernel.π (ω n)) (π_comp_cokernelTowerMap ω hω)

private lemma cokernelTowerπ_f {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0)
    {n : ℤ} {k : ℕ} (h : (k : ℤ) = n) :
    (cokernelTowerπ ω hω hf).f n = (towerComplexXIso N f hf h).hom ≫ cokernel.π (ω k) ≫
      (cokernelTowerXIso ω hω hf h).inv :=
  towerComplexMap_f _ _ h

private lemma towerComplexMap_comp_cokernelTowerπ {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0)
    (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) :
    towerComplexMap (he := he) (hf := hf) ω hω ≫ cokernelTowerπ ω hω hf = 0 := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · exact (isZero_cokernelTower_X ω hω hf hn).eq_of_tgt _ _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HomologicalComplex.comp_f, towerComplexMap_f ω hω (k := k) rfl,
      cokernelTowerπ_f ω hω hf (k := k) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (ω k), cokernel.condition, zero_comp, comp_zero,
      HomologicalComplex.zero_f]

private lemma isIso_cokernelTowerDesc {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0)
    (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) :
    IsIso (cokernel.desc (towerComplexMap (he := he) (hf := hf) ω hω) (cokernelTowerπ ω hω hf)
      (towerComplexMap_comp_cokernelTowerπ he hf ω hω)) := by
  suffices hall : ∀ i : ℤ, IsIso ((cokernel.desc (towerComplexMap (he := he) (hf := hf) ω hω)
      (cokernelTowerπ ω hω hf) (towerComplexMap_comp_cokernelTowerπ he hf ω hω)).f i) by
    exact HomologicalComplex.Hom.isIso_of_components _
  intro i
  have wi : (towerComplexMap (he := he) (hf := hf) ω hω).f i ≫
      (cokernelTowerπ ω hω hf).f i = 0 := by
    rw [← HomologicalComplex.comp_f, towerComplexMap_comp_cokernelTowerπ he hf ω hω]; simp
  have hd : IsIso (cokernel.desc ((towerComplexMap (he := he) (hf := hf) ω hω).f i)
      ((cokernelTowerπ ω hω hf).f i) wi) := ?main
  · rw [cokernelDesc_f _ _ _ i wi]; infer_instance
  case main =>
  rcases lt_or_ge i 0 with hi | hi
  · have : Epi ((towerComplexMap (he := he) (hf := hf) ω hω).f i) :=
      (isZero_towerComplex_X _ _ _ hi).epi _
    exact IsZero.isIso (isZero_cokernel_of_epi _) (isZero_cokernelTower_X ω hω hf hi) _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have hphi : (towerComplexMap (he := he) (hf := hf) ω hω).f (k : ℤ) =
        (towerComplexXIso M e he (k := k) rfl).hom ≫ ω k ≫
          (towerComplexXIso N f hf (k := k) rfl).inv :=
      towerComplexMap_f ω hω rfl
    have ht := cokernelTowerπ_f ω hω hf (n := (k : ℤ)) (k := k) rfl
    have hw : ω k ≫ (towerComplexXIso N f hf (k := k) rfl).inv ≫
        cokernel.π ((towerComplexMap (he := he) (hf := hf) ω hω).f (k : ℤ)) = 0 := by
      rw [← cancel_epi (towerComplexXIso M e he (k := k) rfl).hom, comp_zero]
      simp only [← Category.assoc]
      rw [show ((towerComplexXIso M e he (k := k) rfl).hom ≫ ω k) ≫
          (towerComplexXIso N f hf (k := k) rfl).inv =
          (towerComplexMap (he := he) (hf := hf) ω hω).f (k : ℤ) by
            rw [hphi, Category.assoc], cokernel.condition]
    refine ⟨(cokernelTowerXIso ω hω hf (n := (k : ℤ)) (k := k) rfl).hom ≫
      cokernel.desc (ω k) _ hw, ?_, ?_⟩
    · rw [← cancel_epi (cokernel.π ((towerComplexMap (he := he) (hf := hf) ω hω).f (k : ℤ)))]
      simp only [ht, Category.assoc, Iso.inv_hom_id_assoc, cokernel.π_desc_assoc,
        cokernel.π_desc, Iso.hom_inv_id_assoc, Category.comp_id]
    · rw [← cancel_epi (cokernel.π (ω k) ≫
        (cokernelTowerXIso ω hω hf (n := (k : ℤ)) (k := k) rfl).inv)]
      simp only [ht, Category.assoc, Iso.inv_hom_id_assoc, cokernel.π_desc_assoc,
        cokernel.π_desc, Category.comp_id]

/-- **The cokernel of a morphism of towers is the tower of cokernels.** Cokernels of complexes are
computed degreewise, and in nonnegative degrees the complex of a tower is the tower. -/
private noncomputable def cokernelTowerIso {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0)
    (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) :
    cokernel (towerComplexMap (he := he) (hf := hf) ω hω) ≅ cokernelTower ω hω hf :=
  @asIso _ _ _ _ _ (isIso_cokernelTowerDesc he hf ω hω)

private lemma π_comp_cokernelTowerIso_hom {M N : ℕ → 𝒜} {e : ∀ n : ℕ, M n ⟶ M (n + 1)}
    {f : ∀ n : ℕ, N n ⟶ N (n + 1)} (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0)
    (hf : ∀ n : ℕ, f n ≫ f (n + 1) = 0) (ω : ∀ n : ℕ, M n ⟶ N n)
    (hω : ∀ n : ℕ, ω n ≫ f n = e n ≫ ω (n + 1)) :
    cokernel.π (towerComplexMap (he := he) (hf := hf) ω hω) ≫
        (cokernelTowerIso he hf ω hω).hom = cokernelTowerπ ω hω hf :=
  cokernel.π_desc _ _ _

/-! ### The graded pieces of a filtered complex, degreewise -/

/-- The projection `F^p K^• ⟶ gr^p K^•` of a filtered complex onto its `p`-th graded piece. -/
private noncomputable abbrev gradedPieceProj (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (p : ℤ) : M.filtration.obj (op p) ⟶ (gr p).obj M :=
  cokernel.π (M.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)

private lemma gradedPieceProj_comp_map {M N : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (γ : M ⟶ N) (p : ℤ) :
    gradedPieceProj M p ≫ (gr p).map γ =
      γ.natTrans.app (op p) ≫ gradedPieceProj N p :=
  cokernel.π_desc _ _ _

private lemma gradedPieceπ_comp_evalGradedPieceIso_inv
    (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ) :
    grMapπ (succHom p) (evalFil M n) ≫ (evalGradedPieceIso M p n).inv = (gradedPieceProj M p).f n :=
  π_comp_evalCokernelIso_inv _ n

private lemma isZero_gradedPiece_X (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (p n : ℤ)
    (hM : IsZero ((M.filtration.obj (op p)).X n)) :
    IsZero (((gr p).obj M).X n) := by
  have : Epi ((evalFil M n).filtration.step (succHom p)) := hM.epi _
  exact IsZero.of_iso (isZero_cokernel_of_epi _) (evalGradedPieceIso M p n)

/-- A composite of morphisms of filtered objects whose underlying composite vanishes has vanishing
graded pieces. -/
lemma gradedPiece_map_comp_eq_zero {A B D : FilteredObject 𝒜 ℤᵒᵖ} (g₁ : A ⟶ B)
    (g₂ : B ⟶ D) (hg : (g₁ ≫ g₂).hom = 0) (p : ℤ) :
    (gr p).map g₁ ≫ (gr p).map g₂ = 0 := by
  rw [← cancel_epi (grMapπ (succHom p) A), comp_zero, ← Category.assoc, grMapπ_map,
    Category.assoc, grMapπ_map, ← Category.assoc,
    show g₁.natTrans.app (op p) ≫ g₂.natTrans.app (op p) = 0 from
      natTrans_app_eq_zero (g₁ ≫ g₂) hg (op p), zero_comp]

/-! ### The filtered complex of a tower, degreewise -/

private noncomputable def towerFilteredComplexXIso (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) {n : ℤ} {k : ℕ}
    (h : (k : ℤ) = n) :
    (towerComplex (fun m => (I m).X) (fun m => (d m).hom) hd).X n ≅ (I k).X :=
  towerComplexXIso _ _ _ h

private lemma towerFilteredComplex_d (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (k : ℕ) {i j : ℤ}
    (hi : (k : ℤ) = i) (hj : ((k + 1 : ℕ) : ℤ) = j) :
    (towerComplex (fun m => (I m).X) (fun m => (d m).hom) hd).d i j =
      (towerFilteredComplexXIso I d hd hi).hom ≫
        (d k).hom ≫ (towerFilteredComplexXIso I d hd hj).inv :=
  towerComplex_d _ _ _ k hi hj

private noncomputable def towerStepComplexXIso (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) {n : ℤ}
    {k : ℕ} (h : (k : ℤ) = n) :
    (towerStepComplex I d hd p).X n ≅ (I k).filtration.obj (op p) :=
  towerComplexXIso _ _ _ h

private lemma towerStepComplex_d (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) (k : ℕ)
    {i j : ℤ} (hi : (k : ℤ) = i) (hj : ((k + 1 : ℕ) : ℤ) = j) :
    (towerStepComplex I d hd p).d i j = (towerStepComplexXIso I d hd p hi).hom ≫
      (d k).natTrans.app (op p) ≫ (towerStepComplexXIso I d hd p hj).inv :=
  towerComplex_d _ _ _ k hi hj

private lemma isZero_towerStepComplex_X (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) {n : ℤ}
    (hn : n < 0) : IsZero ((towerStepComplex I d hd p).X n) :=
  isZero_towerComplex_X _ _ _ hn

private lemma towerStepComplexι_f (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) {n : ℤ}
    {k : ℕ} (h : (k : ℤ) = n) :
    (towerStepComplexι I d hd p).f n = (towerStepComplexXIso I d hd p h).hom ≫
      (I k).filtration.ι.app (op p) ≫ (towerFilteredComplexXIso I d hd h).inv :=
  towerComplexMap_f _ _ h

/-- The maps of the filtration diagram of the filtered complex of a tower are the maps of the
towers of filtration steps: `MonoOver` is thin, so there is nothing else they could be. -/
private lemma towerFilteredComplex_diagram_map (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    (towerFilteredComplex I d hd).filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op =
      towerStepComplexMap I d hd p := by
  have := mono_towerStepComplexι I d hd p
  refine (cancel_mono (towerStepComplexι I d hd p)).mp ?_
  exact (Filtration.diagram_map_comp_ι_app (towerFilteredComplex I d hd).filtration
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op).trans
    (towerStepComplexMap_comp_ι I d hd p).symm

/-! ### The graded pieces of the filtered complex of a tower -/

/-- The complex `gr^p(I^0) ⟶ gr^p(I^1) ⟶ ⋯` of graded pieces of a tower of filtered objects. -/
private noncomputable def gradedPieceTower (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  cokernelTower (fun n => (I n).filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (fun n => (d n).natTrans.naturality _)
    (fun n => natTrans_app_eq_zero (d n ≫ d (n + 1)) (hd n) (op p))

private noncomputable def gradedPieceTowerXIso (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) {n : ℤ}
    {k : ℕ} (h : (k : ℤ) = n) :
    (gradedPieceTower I d hd p).X n ≅ (gr p).obj (I k) :=
  cokernelTowerXIso _ _ _ h

private lemma isZero_gradedPieceTower_X (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) {n : ℤ}
    (hn : n < 0) : IsZero ((gradedPieceTower I d hd p).X n) :=
  isZero_cokernelTower_X _ _ _ hn

private lemma gradedPieceTower_d (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) (k : ℕ)
    {i j : ℤ} (hi : (k : ℤ) = i) (hj : ((k + 1 : ℕ) : ℤ) = j) :
    (gradedPieceTower I d hd p).d i j = (gradedPieceTowerXIso I d hd p hi).hom ≫
      (gr p).map (d k) ≫ (gradedPieceTowerXIso I d hd p hj).inv :=
  towerComplex_d _ _ _ k hi hj

/-- Exactness of `gr^p(I^k) ⟶ gr^p(I^{k + 1}) ⟶ gr^p(I^{k + 2})` is exactness of the complex of
graded pieces in degree `k + 1`. -/
private lemma exactAt_gradedPieceTower (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) (k : ℕ)
    (hex : (ShortComplex.mk ((gr p).map (d k)) ((gr p).map (d (k + 1)))
      (gradedPiece_map_comp_eq_zero (d k) (d (k + 1)) (hd k) p)).Exact) :
    (gradedPieceTower I d hd p).ExactAt ((k : ℤ) + 1) :=
  exactAt_towerComplex _ _ _ k hex

/-- The projection `F^p I^• ⟶ gr^p(I^•)` onto the complex of graded pieces. -/
private noncomputable def gradedPieceTowerπ (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    towerStepComplex I d hd p ⟶ gradedPieceTower I d hd p :=
  cokernelTowerπ _ _ _

private lemma gradedPieceTowerπ_f (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) {n : ℤ}
    {k : ℕ} (h : (k : ℤ) = n) :
    (gradedPieceTowerπ I d hd p).f n = (towerStepComplexXIso I d hd p h).hom ≫
      grMapπ (succHom p) (I k) ≫ (gradedPieceTowerXIso I d hd p h).inv :=
  cokernelTowerπ_f _ _ _ h

/-- **The graded pieces of the filtered complex of a tower are the complex of the graded pieces of
its terms.** The filtration steps `F^p I^•` are the complexes of the towers `n ↦ F^p I^n`, and
cokernels of complexes are computed degreewise. -/
private noncomputable def gradedPieceTowerIso (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    (gr p).obj (towerFilteredComplex I d hd) ≅
      gradedPieceTower I d hd p :=
  cokernelIsoOfEq (towerFilteredComplex_diagram_map I d hd p) ≪≫ cokernelTowerIso _ _ _ _

private lemma gradedPieceProj_comp_gradedPieceTowerIso_hom (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ) :
    gradedPieceProj (towerFilteredComplex I d hd) p ≫ (gradedPieceTowerIso I d hd p).hom =
      gradedPieceTowerπ I d hd p := by
  have h1 : gradedPieceProj (towerFilteredComplex I d hd) p ≫
      (gradedPieceTowerIso I d hd p).hom =
      (gradedPieceProj (towerFilteredComplex I d hd) p ≫
        (cokernelIsoOfEq (towerFilteredComplex_diagram_map I d hd p)).hom) ≫
        (cokernelTowerIso _ _ _ _).hom := (Category.assoc _ _ _).symm
  have h2 : gradedPieceProj (towerFilteredComplex I d hd) p ≫
      (cokernelIsoOfEq (towerFilteredComplex_diagram_map I d hd p)).hom =
      cokernel.π (towerStepComplexMap I d hd p) :=
    π_comp_cokernelIsoOfEq_hom _
  rw [h1, h2]
  exact π_comp_cokernelTowerIso_hom _ _ _ _

/-! ### The comparison map out of a filtered complex concentrated in degree `0` -/

/-- The filtration steps of a complex concentrated in degree `0` are concentrated in degree `0`,
being subobjects of it. -/
private lemma isZero_filtration_obj_X (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n)) (q : ℤᵒᵖ) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((K.filtration.obj q).X n) := by
  have h : IsZero ((evalFil K n).filtration.obj q) :=
    IsZero.of_mono ((evalFil K n).filtration.ι.app q) (hK n hn)
  exact h

omit [Abelian 𝒜] in
/-- Cancelling an isomorphism against its inverse on the left. -/
private lemma inv_comp_hom_comp {A B C : 𝒜} (e : A ≅ B) (w : B ⟶ C) :
    e.inv ≫ e.hom ≫ w = w := by
  rw [Iso.inv_hom_id_assoc]

omit [Abelian 𝒜] in
/-- Cancelling an isomorphism between two composites. -/
private lemma comp_inv_comp_hom_comp {X A B C : 𝒜} (u : X ⟶ A) (e : B ≅ A) (w : A ⟶ C) :
    (u ≫ e.inv) ≫ e.hom ≫ w = u ≫ w := by
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- The composite `X ⟶ M^0 ⟶ M^1` read in the complex of a tower vanishes when it vanishes in
the tower. Stated for a bare object `X` so that no filtered-object projection has to be
unfolded. -/
private lemma comp_towerComplex_d_eq_zero {X : 𝒜} (M : ℕ → 𝒜) (e : ∀ n : ℕ, M n ⟶ M (n + 1))
    (he : ∀ n : ℕ, e n ≫ e (n + 1) = 0) (g : X ⟶ M 0) (hg : g ≫ e 0 = 0) :
    (g ≫ (towerComplexXIso M e he (k := 0) (n := 0) rfl).inv) ≫
      (towerComplex M e he).d 0 1 = 0 := by
  rw [towerComplex_d M e he 0 (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hg, zero_comp]

/-- Compatibility with the inclusion of a filtration step, in degree `0`, stated for bare
objects. -/
private lemma comp_inv_comp_towerStepComplexι_f_zero {X Y : 𝒜} (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ)
    (d : ∀ n : ℕ, I n ⟶ I (n + 1)) (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (p : ℤ)
    (g : X ⟶ (I 0).filtration.obj (op p)) (u : X ⟶ Y) (v : Y ⟶ (I 0).X)
    (h : g ≫ (I 0).filtration.ι.app (op p) = u ≫ v) :
    (g ≫ (towerStepComplexXIso I d hd p (k := 0) (n := 0) rfl).inv) ≫
        (towerStepComplexι I d hd p).f 0 =
      u ≫ v ≫ (towerFilteredComplexXIso I d hd (k := 0) (n := 0) rfl).inv := by
  rw [towerStepComplexι_f I d hd p (k := 0) (n := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h, Category.assoc]

/-- The underlying morphism of complexes of the comparison map `K^• ⟶ I^•`: in degree `0` it is
the given `α : K^0 ⟶ I^0`, read through the identification of `I^•` in degree `0` with `I^0`. -/
private noncomputable def towerHomHom (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) :
    K.X ⟶ towerComplex (fun m => (I m).X) (fun m => (d m).hom) hd :=
  homFromDegreeZero hK (α.hom ≫ (towerFilteredComplexXIso I d hd (k := 0) (n := 0) rfl).inv)
    (comp_towerComplex_d_eq_zero _ _ hd α.hom (show α.hom ≫ (d 0).hom = 0 from hα))

private lemma towerHomHom_f_zero (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) :
    (towerHomHom K I α d hd hK hα).f 0 =
      α.hom ≫ (towerFilteredComplexXIso I d hd (k := 0) (n := 0) rfl).inv :=
  homFromDegreeZero_f_zero _ _ _

/-- The component of the comparison map on the `p`-th filtration step. -/
private noncomputable def towerHomApp (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) (q : ℤᵒᵖ) :
    K.filtration.obj q ⟶ towerStepComplex I d hd q.unop :=
  homFromDegreeZero (fun _ hn => isZero_filtration_obj_X K hK q hn)
    (α.natTrans.app q ≫ (towerStepComplexXIso I d hd q.unop (k := 0) (n := 0) rfl).inv)
    (comp_towerComplex_d_eq_zero (fun n => (I n).filtration.obj (op q.unop))
      (fun n => (d n).natTrans.app (op q.unop)) _ (α.natTrans.app q)
      (show α.natTrans.app q ≫ (d 0).natTrans.app (op q.unop) = 0 from
        natTrans_app_eq_zero (α ≫ d 0) hα q))

private lemma towerHomApp_f_zero (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) (q : ℤᵒᵖ) :
    (towerHomApp K I α d hd hK hα q).f 0 =
      α.natTrans.app q ≫ (towerStepComplexXIso I d hd q.unop (k := 0) (n := 0) rfl).inv :=
  homFromDegreeZero_f_zero _ _ _

/-- The comparison map is compatible with the inclusions of the filtration steps: in degree `0`
this is the compatibility `α.comm` of `α`, and there is nothing to check in other degrees. -/
private lemma towerHomApp_comp_ι (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) (q : ℤᵒᵖ) :
    towerHomApp K I α d hd hK hα q ≫ towerStepComplexι I d hd q.unop =
      K.filtration.ι.app q ≫ towerHomHom K I α d hd hK hα := by
  refine hom_ext_of_degreeZero (fun _ hn => isZero_filtration_obj_X K hK q hn) ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, towerHomApp_f_zero,
    towerHomHom_f_zero]
  exact comp_inv_comp_towerStepComplexι_f_zero I d hd q.unop (α.natTrans.app q)
    ((K.filtration.ι.app q).f 0) α.hom (α.comm q)

/-- The comparison map `K^• ⟶ I^•` of [Stacks, Tag 05TT], for a filtered complex `K^•`
concentrated in degree `0` and a tower `I` resolving its degree `0` term. -/
private noncomputable def towerHom (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) : K ⟶ towerFilteredComplex I d hd where
  hom := towerHomHom K I α d hd hK hα
  natTrans :=
    { app := fun q => towerHomApp K I α d hd hK hα q
      naturality := fun q q' g => by
        have := mono_towerStepComplexι I d hd q'.unop
        refine (cancel_mono (towerStepComplexι I d hd q'.unop)).mp ?_
        have e1 : (K.filtration.diagram.map g ≫ towerHomApp K I α d hd hK hα q') ≫
            towerStepComplexι I d hd q'.unop =
            K.filtration.ι.app q ≫ towerHomHom K I α d hd hK hα := by
          rw [Category.assoc, towerHomApp_comp_ι, ← Category.assoc,
            Filtration.diagram_map_comp_ι_app K.filtration g]
        have e3 : (towerFilteredComplex I d hd).filtration.diagram.map g ≫
            towerStepComplexι I d hd q'.unop = towerStepComplexι I d hd q.unop :=
          Filtration.diagram_map_comp_ι_app (towerFilteredComplex I d hd).filtration g
        have e2 : (towerHomApp K I α d hd hK hα q ≫
            (towerFilteredComplex I d hd).filtration.diagram.map g) ≫
            towerStepComplexι I d hd q'.unop =
            K.filtration.ι.app q ≫ towerHomHom K I α d hd hK hα :=
          (Category.assoc _ _ _).trans
            ((congrArg (fun m => towerHomApp K I α d hd hK hα q ≫ m) e3).trans
              (towerHomApp_comp_ι K I α d hd hK hα q))
        exact e1.trans e2.symm }
  comm := fun q => towerHomApp_comp_ι K I α d hd hK hα q

private lemma towerHom_natTrans_app_f_zero (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) (p : ℤ) :
    ((towerHom K I α d hd hK hα).natTrans.app (op p)).f 0 =
      α.natTrans.app (op p) ≫ (towerStepComplexXIso I d hd p (k := 0) (n := 0) rfl).inv :=
  towerHomApp_f_zero K I α d hd hK hα (op p)

/-- **In degree `0` the graded pieces of the comparison map are the graded pieces of `α`.** Both
sides are determined by their composite with the projection `F^p K^0 ⟶ gr^p K^0`. -/
private lemma towerHom_gradedPiece_f_zero (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (I : ℕ → FilteredObject 𝒜 ℤᵒᵖ) (α : evalFil K 0 ⟶ I 0) (d : ∀ n : ℕ, I n ⟶ I (n + 1))
    (hd : ∀ n : ℕ, (d n ≫ d (n + 1)).hom = 0) (hK : ∀ n : ℤ, n ≠ 0 → IsZero (K.X.X n))
    (hα : (α ≫ d 0).hom = 0) (p : ℤ) :
    (((gr p).map (towerHom K I α d hd hK hα)) ≫
        (gradedPieceTowerIso I d hd p).hom).f 0 =
      (evalGradedPieceIso K p 0).hom ≫ (gr p).map α ≫
        (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).inv := by
  rw [← Iso.inv_comp_eq, ← cancel_epi (grMapπ (succHom p) (evalFil K 0))]
  have hL : grMapπ (succHom p) (evalFil K 0) ≫ (evalGradedPieceIso K p 0).inv ≫
      (((gr p).map (towerHom K I α d hd hK hα)) ≫
        (gradedPieceTowerIso I d hd p).hom).f 0 =
      ((gradedPieceProj K p ≫ (gr p).map
        (towerHom K I α d hd hK hα) ≫ (gradedPieceTowerIso I d hd p).hom).f 0) := by
    rw [← Category.assoc, gradedPieceπ_comp_evalGradedPieceIso_inv]
    exact (HomologicalComplex.comp_f _ _ 0).symm
  have hR : grMapπ (succHom p) (evalFil K 0) ≫ (gr p).map α ≫
      (gradedPieceTowerXIso I d hd p (k := 0) rfl).inv =
      α.natTrans.app (op p) ≫ grMapπ (succHom p) (I 0) ≫
        (gradedPieceTowerXIso I d hd p (k := 0) (n := 0) rfl).inv := by
    rw [← Category.assoc, grMapπ_map, Category.assoc]
  rw [hL, hR, ← Category.assoc, gradedPieceProj_comp_map, Category.assoc,
    gradedPieceProj_comp_gradedPieceTowerIso_hom]
  have hsplit : ((towerHom K I α d hd hK hα).natTrans.app (op p) ≫
      gradedPieceTowerπ I d hd p).f 0 =
      ((towerHom K I α d hd hK hα).natTrans.app (op p)).f 0 ≫
        (gradedPieceTowerπ I d hd p).f 0 := HomologicalComplex.comp_f _ _ 0
  rw [hsplit, towerHom_natTrans_app_f_zero, gradedPieceTowerπ_f I d hd p (k := 0) (n := 0) rfl]
  exact comp_inv_comp_hom_comp _ _ _

end Tower

end CochainComplex.FilteredInjective.Resolution

end FilteredInjectiveResolutionDegreeZero

end
