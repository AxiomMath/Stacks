module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle

/-!
# A triangulated functor inverting a map of bounded complexes degreewise inverts it

Let `A` be an abelian category with a derived category, let `Φ : D(A) ⥤ D` be a triangulated
functor into a pretriangulated category, and let `φ : K ⟶ L` be a morphism of bounded cochain
complexes of objects of `A`.  If `Φ` inverts each of the maps of single complexes
`Kⁱ[-i] ⟶ Lⁱ[-i]` induced by the components `φⁱ`, then it inverts `φ` itself.

The proof is the stupid-filtration dévissage.  The morphism `φ` induces a morphism of the short
exact sequences

`0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ 0`

of `StacksDraft.StupidTruncation.stupidTruncGEShortComplex`, hence — by Mathlib's
`DerivedCategory.triangleOfSES.map` — a morphism of the distinguished triangles those sequences
produce.  Applying `Φ` and the triangulated five lemma
`CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃` advances the induction from `σ^{≥p+1}` to
`σ^{≥p}`: above the common upper bound of the two supports both truncations vanish, and below
the common lower bound the inclusions `σ^{≥a}K ⟶ K` and `σ^{≥a}L ⟶ L` are isomorphisms.

This is the morphism-level counterpart of
`Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex`, which runs the same
induction for a property of *objects*.  A property of objects cannot express "this map is
inverted": the cone of `φ` has `Kⁱ⁺¹ ⊕ Lⁱ` in degree `i`, so its terms are not controlled by the
hypothesis on the components of `φ`, and the two filtrations have to be compared instead.

## Main definitions

* `StacksDraft.StupidTruncation.stupidTruncGEShortComplexMap` — the morphism of stupid-filtration
  short exact sequences induced by a morphism of complexes.

## Main results

* `StacksDraft.StupidTruncation.stupidTruncMap_stupidTruncGEMapLE` and
  `StacksDraft.StupidTruncation.stupidTruncMap_stupidTruncGEπ` — the two naturality squares.
* `Stacks.DerivedCategory.BoundedInduction.isIso_map_Q_map_of_isIso_map_singleFunctor_map` — the
  dévissage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

section Naturality

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

attribute [local instance] mono_ιStupidTrunc

/-- **The comparisons of the stupid filtration are natural in the complex.** Both composites are
determined by their composites with the monomorphism `σ^{≥a}L ⟶ L`. -/
lemma stupidTruncMap_stupidTruncGEMapLE {a b : ℤ} (h : a ≤ b) :
    stupidTruncMap φ (embeddingUpIntGE b) ≫ stupidTruncGEMapLE L h =
      stupidTruncGEMapLE K h ≫ stupidTruncMap φ (embeddingUpIntGE a) := by
  apply (cancel_mono (ιStupidTrunc L (embeddingUpIntGE a))).1
  rw [Category.assoc, stupidTruncGEMapLE_ι, stupidTruncMap_ιStupidTrunc, Category.assoc,
    stupidTruncMap_ιStupidTrunc, ← Category.assoc, stupidTruncGEMapLE_ι]

/-- **The projection of the stupid filtration onto its bottom term is natural in the complex.** -/
lemma stupidTruncMap_stupidTruncGEπ (p : ℤ) :
    stupidTruncMap φ (embeddingUpIntGE p) ≫ stupidTruncGEπ L p =
      stupidTruncGEπ K p ≫ (single C (.up ℤ) p).map (φ.f p) := by
  apply to_single_hom_ext
  have hp : (embeddingUpIntGE p).f (p - p).toNat = p := by
    show p + (((p - p).toNat : ℤ)) = p; omega
  have hnat := stupidTruncMap_stupidTruncXIso_hom φ (embeddingUpIntGE p) hp
  simp only [HomologicalComplex.comp_f, stupidTruncGEπ_f, single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hnat, Category.assoc]

/-- **The morphism of stupid-filtration short exact sequences** induced by a morphism of
complexes: the two brutal truncations and the degree-`p` terms, each mapped by `φ`. -/
noncomputable def stupidTruncGEShortComplexMap (p : ℤ) :
    stupidTruncGEShortComplex K p ⟶ stupidTruncGEShortComplex L p where
  τ₁ := stupidTruncMap φ (embeddingUpIntGE (p + 1))
  τ₂ := stupidTruncMap φ (embeddingUpIntGE p)
  τ₃ := (single C (.up ℤ) p).map (φ.f p)
  comm₁₂ := stupidTruncMap_stupidTruncGEMapLE φ (show p ≤ p + 1 by omega)
  comm₂₃ := stupidTruncMap_stupidTruncGEπ φ p

/-- The first component of `stupidTruncGEShortComplexMap φ p` is the map
`σ^{≥p+1}K ⟶ σ^{≥p+1}L` induced by `φ`. -/
@[simp]
lemma stupidTruncGEShortComplexMap_τ₁ (p : ℤ) :
    (stupidTruncGEShortComplexMap φ p).τ₁ = stupidTruncMap φ (embeddingUpIntGE (p + 1)) :=
  rfl

/-- The second component of `stupidTruncGEShortComplexMap φ p` is the map
`σ^{≥p}K ⟶ σ^{≥p}L` induced by `φ`. -/
@[simp]
lemma stupidTruncGEShortComplexMap_τ₂ (p : ℤ) :
    (stupidTruncGEShortComplexMap φ p).τ₂ = stupidTruncMap φ (embeddingUpIntGE p) :=
  rfl

/-- The third component of `stupidTruncGEShortComplexMap φ p` is the map of single complexes
in degree `p` induced by `φ.f p`. -/
@[simp]
lemma stupidTruncGEShortComplexMap_τ₃ (p : ℤ) :
    (stupidTruncGEShortComplexMap φ p).τ₃ = (single C (.up ℤ) p).map (φ.f p) :=
  rfl

end Naturality

end StacksDraft.StupidTruncation

namespace Stacks.DerivedCategory.BoundedInduction

open StacksDraft.StupidTruncation

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (Φ : DerivedCategory A ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated]

attribute [local instance] mono_ιStupidTrunc

/-- The morphism of distinguished triangles of the `p`-th stupid filtration step induced by a
morphism of complexes. -/
noncomputable def stupidTruncGETriangleMap {K L : CochainComplex A ℤ} (φ : K ⟶ L) (p : ℤ) :
    stupidTruncGETriangle K p ⟶ stupidTruncGETriangle L p :=
  DerivedCategory.triangleOfSES.map (stupidTruncGEShortComplex_shortExact K p)
    (stupidTruncGEShortComplex_shortExact L p) (stupidTruncGEShortComplexMap φ p)

/-- The induction step: if `Φ` inverts the truncation `σ^{≥p+1}φ` and the degree-`p` component of
`φ`, it inverts `σ^{≥p}φ`. -/
lemma isIso_map_Q_map_stupidTruncMap_of_succ {K L : CochainComplex A ℤ} (φ : K ⟶ L) (p : ℤ)
    (h₁ : IsIso (Φ.map (DerivedCategory.Q.map (stupidTruncMap φ (embeddingUpIntGE (p + 1))))))
    (h₃ : IsIso (Φ.map ((DerivedCategory.singleFunctor A p).map (φ.f p)))) :
    IsIso (Φ.map (DerivedCategory.Q.map (stupidTruncMap φ (embeddingUpIntGE p)))) := by
  have := Pretriangulated.isIso₂_of_isIso₁₃
    (Φ.mapTriangle.map (stupidTruncGETriangleMap φ p))
    (Φ.map_distinguished _ (stupidTruncGETriangle_distinguished K p))
    (Φ.map_distinguished _ (stupidTruncGETriangle_distinguished L p)) h₁ h₃
  exact this

omit [HasZeroObject D] [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [Φ.CommShift ℤ] [Φ.IsTriangulated] in
/-- Above the supports of both complexes, `Φ` inverts every truncation of `φ`. -/
lemma isIso_map_Q_map_stupidTruncMap_of_upper {K L : CochainComplex A ℤ} (φ : K ⟶ L) (p : ℤ)
    (hK : ∀ i, p ≤ i → IsZero (K.X i)) (hL : ∀ i, p ≤ i → IsZero (L.X i)) :
    IsIso (Φ.map (DerivedCategory.Q.map (stupidTruncMap φ (embeddingUpIntGE p)))) := by
  have hz (M : CochainComplex A ℤ) (hM : ∀ i, p ≤ i → IsZero (M.X i)) :
      IsZero (M.stupidTrunc (embeddingUpIntGE p)) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    ext i
    refine IsZero.eq_of_src ?_ _ _
    by_cases hpi : p ≤ i
    · exact (hM i hpi).of_iso (stupidTruncGEXIso M p i hpi)
    · exact CochainComplex.isZero_of_isStrictlyGE _ p i (by omega)
  have hiso : IsIso (DerivedCategory.Q.map (stupidTruncMap φ (embeddingUpIntGE p))) :=
    IsZero.isIso (Functor.map_isZero _ (hz K hK)) (Functor.map_isZero _ (hz L hL)) _
  infer_instance

/-- **A triangulated functor which inverts a morphism of bounded complexes degreewise inverts
it.** -/
theorem isIso_map_Q_map_of_isIso_map_singleFunctor_map {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) (hL : {i : ℤ | ¬ IsZero (L.X i)}.Finite)
    (hsingle : ∀ i, IsIso (Φ.map ((DerivedCategory.singleFunctor A i).map (φ.f i)))) :
    IsIso (Φ.map (DerivedCategory.Q.map φ)) := by
  classical
  obtain ⟨bK, hbK⟩ := hK.bddAbove
  obtain ⟨bL, hbL⟩ := hL.bddAbove
  obtain ⟨aK, haK⟩ := hK.bddBelow
  obtain ⟨aL, haL⟩ := hL.bddBelow
  set b : ℤ := max bK bL with hb
  set a : ℤ := min aK aL with ha
  have upper (M : CochainComplex A ℤ) {c : ℤ} (hc : c ∈ upperBounds {i | ¬ IsZero (M.X i)})
      (i : ℤ) (hi : c < i) : IsZero (M.X i) :=
    not_not.1 fun h => absurd (hc h) (by omega)
  have trunc : ∀ (n : ℕ) (p : ℤ), b < p + n →
      IsIso (Φ.map (DerivedCategory.Q.map (stupidTruncMap φ (embeddingUpIntGE p)))) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      exact isIso_map_Q_map_stupidTruncMap_of_upper Φ φ p
        (fun i hi => upper K (upperBounds_mono_mem (le_max_left bK bL) hbK) i (by omega))
        (fun i hi => upper L (upperBounds_mono_mem (le_max_right bK bL) hbL) i (by omega))
    | succ n ih =>
      intro p hp
      exact isIso_map_Q_map_stupidTruncMap_of_succ Φ φ p
        (ih (p + 1) (by push_cast at hp ⊢; omega)) (hsingle p)
  have hι (M : CochainComplex A ℤ) (hM : ∀ i, i < a → IsZero (M.X i)) :
      IsIso (ιStupidTrunc M (embeddingUpIntGE a)) := by
    have (i : ℤ) : IsIso ((ιStupidTrunc M (embeddingUpIntGE a)).f i) := by
      by_cases hai : a ≤ i
      · rw [ιStupidTruncGE_f M a i hai]; infer_instance
      · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyGE _ a i (by omega))
          (hM i (by omega)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hιK := hι K fun i hi => not_not.1 fun h =>
    absurd ((min_le_left aK aL).trans (haK h)) (by omega)
  have hιL := hι L fun i hi => not_not.1 fun h =>
    absurd ((min_le_right aK aL).trans (haL h)) (by omega)
  have hsq : φ = inv (ιStupidTrunc K (embeddingUpIntGE a)) ≫
      stupidTruncMap φ (embeddingUpIntGE a) ≫ ιStupidTrunc L (embeddingUpIntGE a) := by
    rw [stupidTruncMap_ιStupidTrunc, IsIso.inv_hom_id_assoc]
  have htr := trunc ((b - a).toNat + 1) a (by omega)
  rw [hsq, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, Φ.map_comp, Φ.map_comp]
  have h1 : IsIso (Φ.map (DerivedCategory.Q.map
      (inv (ιStupidTrunc K (embeddingUpIntGE a))))) := by
    have : IsIso (DerivedCategory.Q.map (inv (ιStupidTrunc K (embeddingUpIntGE a)))) :=
      inferInstance
    infer_instance
  have h2 : IsIso (Φ.map (DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE a)))) := by
    have : IsIso (DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE a))) := inferInstance
    infer_instance
  infer_instance

end Stacks.DerivedCategory.BoundedInduction

end
