module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Projective cokernels in a bounded above complex of projectives with a bounded below model

Let `A` be an abelian category and let `Y` be a bounded above cochain complex in `A` whose terms
are projective. Suppose that `Y` becomes isomorphic in the derived category to a bounded complex
`P` of projectives concentrated in degrees `≥ c`. Then for every `n ≤ c` the cokernel
`Y.opcycles n = Coker(Y^{n-1} → Y^n)` is projective.

This is the algebraic step of the implication (1) ⟹ (2) of [Stacks, Tag 03TT] in the form the
trace formula needs it, over a possibly noncommutative coefficient ring: a bounded above
resolution of a complex with perfect stalks can be truncated to a bounded complex whose terms are
projective at the stalks, provided the truncation degree lies below the lower bound of a perfect
model of every stalk.

## Main results

* `CochainComplex.exists_retraction_fromOpcycles_of_iso_Q_obj` — the map
  `Y.opcycles (n - 1) ⟶ Y.X n` induced by the differential has a retraction.
* `CochainComplex.projective_opcycles_of_iso_Q_obj` — `Y.opcycles n` is projective.

## Implementation notes

The argument is the splitting argument, with no Tor or Ext machinery. Morphisms out of `Q P`
into an object placed in degree `n - 1 < c` vanish, since `P` is K-projective and has no term in
that degree. As `Y` is K-projective too, the chain map
`Y ⟶ (single (n - 1)).obj (Y.opcycles (n - 1))` given by the canonical projection is
null-homotopic; the component of the homotopy in degree `n` is a map
`ψ : Y.X n ⟶ Y.opcycles (n - 1)` with `d^{n-1} ≫ ψ = pOpcycles`. Hence `fromOpcycles` is a split
monomorphism, `𝟙 - ψ ≫ fromOpcycles` descends to a section of `Y.X n ⟶ Y.opcycles n`, and
`Y.opcycles n` is a retract of the projective object `Y.X n`. No exactness of `Y` is needed.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Morphisms in the derived category from a bounded complex of projectives concentrated in
degrees `≥ c` into an object placed in a single degree `m < c` vanish. -/
theorem Q_map_eq_zero_of_isStrictlyGE {P : CochainComplex A ℤ} (c d : ℤ) [P.IsStrictlyGE c]
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] (N : A) (m : ℤ) (hm : m < c)
    (f : DerivedCategory.Q.obj P ⟶
      DerivedCategory.Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) m).obj N)) :
    f = 0 := by
  have : P.IsKProjective := isKProjective_of_projective P d
  obtain ⟨g, hg⟩ := (IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj ((HomologicalComplex.single A (ComplexShape.up ℤ) m).obj
      N))).2
    ((DerivedCategory.quotientCompQhIso _).hom.app P ≫ f ≫
      (DerivedCategory.quotientCompQhIso _).inv.app _)
  obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  obtain rfl : a = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    obtain rfl | hi := eq_or_ne i m
    · exact (P.isZero_of_isStrictlyGE c _ hm).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ m N i hi).eq_of_tgt _ _
  rw [Functor.map_zero, Functor.map_zero] at hg
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app P),
    ← cancel_mono ((DerivedCategory.quotientCompQhIso _).inv.app _)]
  simpa using hg.symm

/-- **The differential into degree `n` splits off the cokernel in degree `n - 1`.** Let `Y` be a
bounded above complex of projectives which is isomorphic in the derived category to a bounded
complex `P` of projectives concentrated in degrees `≥ c`, and let `n ≤ c`. Then the map
`Y.opcycles (n - 1) ⟶ Y.X n` induced by the differential has a retraction. -/
theorem exists_retraction_fromOpcycles_of_iso_Q_obj (Y : CochainComplex A ℤ) (b : ℤ)
    [Y.IsStrictlyLE b] [∀ i, Projective (Y.X i)] (P : CochainComplex A ℤ) (c d : ℤ)
    [P.IsStrictlyGE c] [P.IsStrictlyLE d] [∀ i, Projective (P.X i)]
    (e : DerivedCategory.Q.obj Y ≅ DerivedCategory.Q.obj P) (n : ℤ) (hn : n ≤ c) :
    ∃ ψ : Y.X n ⟶ Y.opcycles (n - 1), Y.fromOpcycles (n - 1) n ≫ ψ = 𝟙 _ := by
  have : Y.IsKProjective := isKProjective_of_projective Y b
  let N := Y.opcycles (n - 1)
  let S := (HomologicalComplex.single A (ComplexShape.up ℤ) (n - 1)).obj N
  let φ : Y ⟶ S := HomologicalComplex.mkHomToSingle (Y.pOpcycles (n - 1))
    fun i _ => Y.d_pOpcycles i (n - 1)
  have hQ : DerivedCategory.Q.map φ = 0 := by
    have h0 := Q_map_eq_zero_of_isStrictlyGE c d N (n - 1) (by omega)
      (e.inv ≫ DerivedCategory.Q.map φ)
    simpa using (cancel_epi e.inv).1 (h0.trans (comp_zero).symm)
  have hK : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ = 0 := by
    apply (IsKProjective.Qh_map_bijective Y ((HomotopyCategory.quotient _ _).obj S)).1
    rw [Functor.map_zero]
    have hnat := (DerivedCategory.quotientCompQhIso A).hom.naturality φ
    rw [hQ, comp_zero] at hnat
    rwa [← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app S), zero_comp]
  let h : Homotopy φ 0 := HomotopyCategory.homotopyOfEq _ _ (by rw [hK, Functor.map_zero])
  refine ⟨h.hom n (n - 1) ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n - 1) N).hom, ?_⟩
  rw [← cancel_epi (Y.pOpcycles (n - 1)), Y.p_fromOpcycles_assoc, Category.comp_id]
  have hcomm := h.comm (n - 1)
  rw [HomologicalComplex.zero_f, add_zero] at hcomm
  have hprev : prevD (n - 1) h.hom = 0 := by
    rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (n - 1 - 1) (n - 1) by simp),
      (HomologicalComplex.isZero_single_obj_X _ (n - 1) N (n - 1 - 1) (by omega)).eq_of_tgt
        (h.hom (n - 1) (n - 1 - 1)) 0, zero_comp]
  rw [hprev, add_zero, dNext_eq h.hom (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at hcomm
  have hφ : φ.f (n - 1) = Y.pOpcycles (n - 1) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n - 1) N).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  rw [← Category.assoc, ← hcomm, hφ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Projective cokernels below a projective model.** Let `Y` be a bounded above complex of
projectives in an abelian category which is isomorphic in the derived category to a bounded
complex `P` of projectives concentrated in degrees `≥ c`. Then `Y.opcycles n`, the cokernel of
`Y^{n-1} ⟶ Y^n`, is projective for every `n ≤ c`: it is a retract of `Y.X n`. -/
theorem projective_opcycles_of_iso_Q_obj (Y : CochainComplex A ℤ) (b : ℤ)
    [Y.IsStrictlyLE b] [∀ i, Projective (Y.X i)] (P : CochainComplex A ℤ) (c d : ℤ)
    [P.IsStrictlyGE c] [P.IsStrictlyLE d] [∀ i, Projective (P.X i)]
    (e : DerivedCategory.Q.obj Y ≅ DerivedCategory.Q.obj P) (n : ℤ) (hn : n ≤ c) :
    Projective (Y.opcycles n) := by
  obtain ⟨ψ, hψ⟩ := exists_retraction_fromOpcycles_of_iso_Q_obj Y b P c d e n hn
  let ι := Y.fromOpcycles (n - 1) n
  have hι : ι ≫ Y.pOpcycles n = 0 := by
    rw [← cancel_epi (Y.pOpcycles (n - 1)), comp_zero, ← Category.assoc, Y.p_fromOpcycles,
      Y.d_pOpcycles]
  let s : Y.opcycles n ⟶ Y.X n := Y.descOpcycles (𝟙 _ - ψ ≫ ι) (n - 1) (by simp) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Y.p_fromOpcycles (n - 1) n,
      Category.assoc, reassoc_of% hψ, sub_self])
  have hs : s ≫ Y.pOpcycles n = 𝟙 _ := by
    rw [← cancel_epi (Y.pOpcycles n), Category.comp_id, ← Category.assoc,
      Y.p_descOpcycles, Preadditive.sub_comp, Category.id_comp, Category.assoc, hι, comp_zero,
      sub_zero]
  exact ⟨fun f g _ => ⟨s ≫ Projective.factorThru (Y.pOpcycles n ≫ f) g, by
    rw [Category.assoc, Projective.factorThru_comp, ← Category.assoc, hs, Category.id_comp]⟩⟩

omit [HasDerivedCategory A] in
/-- **The truncation of a bounded above complex of projectives at a projective cokernel.** Let
`Y` be a bounded above complex of projectives with no cohomology in degrees `< m`, and suppose
that `Y.opcycles m` is projective. Then the canonical truncation `Y.truncGE m` is a bounded
complex of projectives concentrated in degrees `[m, b]`, quasi-isomorphic to `Y`. -/
theorem projective_truncGE_X (Y : CochainComplex A ℤ) [∀ i, Projective (Y.X i)] (m : ℤ)
    (hm : Projective (Y.opcycles m)) (i : ℤ) : Projective ((Y.truncGE m).X i) := by
  obtain hi | rfl | hi := lt_trichotomy i m
  · exact ((Y.truncGE m).isZero_of_isStrictlyGE m i hi).projective
  · exact Projective.of_iso (Y.truncGEXIsoOpcycles i).symm hm
  · exact Projective.of_iso (Y.truncGEXIso m i hi).symm inferInstance

/-- **Projectivity of the cokernels propagates downwards.** Let `Y` be a bounded above complex of
projectives in an abelian category with no cohomology in degrees `< m`. If the cokernel
`Y.opcycles m` is projective, so is `Y.opcycles n` for every `n ≤ m`: the truncation
`Y.truncGE m` is a bounded complex of projectives in degrees `≥ m` isomorphic to `Y` in the
derived category, and `CochainComplex.projective_opcycles_of_iso_Q_obj` applies. -/
theorem projective_opcycles_of_projective_opcycles (Y : CochainComplex A ℤ) (b : ℤ)
    [Y.IsStrictlyLE b] [∀ i, Projective (Y.X i)] (m : ℤ) [Y.IsGE m]
    (hm : Projective (Y.opcycles m)) (n : ℤ) (hn : n ≤ m) : Projective (Y.opcycles n) := by
  have : (Y.truncGE m).IsStrictlyLE b := by
    rw [isStrictlyLE_iff]
    intro i hi
    have : Epi ((Y.πTruncGE m).f i) := by
      unfold πTruncGE
      infer_instance
    exact IsZero.of_epi ((Y.πTruncGE m).f i) (Y.isZero_of_isStrictlyLE b i hi)
  have : ∀ i, Projective ((Y.truncGE m).X i) := projective_truncGE_X Y m hm
  exact projective_opcycles_of_iso_Q_obj Y b (Y.truncGE m) m b
    (asIso (DerivedCategory.Q.map (Y.πTruncGE m))) n hn

end CochainComplex
