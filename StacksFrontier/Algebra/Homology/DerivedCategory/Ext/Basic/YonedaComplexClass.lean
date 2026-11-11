module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.YonedaClassMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESShift

/-!
# The class `δ(E) = f s⁻¹` of a Yoneda extension

Let `E : 0 → A → Z_{i - 1} → ⋯ → Z_0 → B → 0` be a degree `i` Yoneda extension in an abelian
category `𝒜`. The source attaches to it the class `δ(E) = f s⁻¹ ∈ Ext^i_𝒜(B, A)`, where `s` is
the quasi-isomorphism from the complex `(⋯ → 0 → A → Z_{i - 1} → ⋯ → Z_0 → 0 → ⋯)` (with `Z_0` in
degree `0`) to `B[0]` and `f` is the morphism from the same complex to `A[i]`. This file
constructs that complex, the two morphisms and the class, and proves the source's lemma for it:
every element of `Ext^i_𝒜(B, A)` is the class of a Yoneda extension, and two Yoneda extensions
of the same degree are equivalent if and only if they have the same class.

## Main definitions

* `CategoryTheory.Abelian.YonedaExtension.complex`: the complex of a Yoneda extension.
* `CategoryTheory.Abelian.YonedaExtension.complexπ`: the quasi-isomorphism `s` to `B[0]`.
* `CategoryTheory.Abelian.YonedaExtension.complexι`: the morphism `f` to `A[i]`.
* `CategoryTheory.Abelian.YonedaExtension.yonedaClass`: the class `δ(E) = f s⁻¹`.

## Main results

* `CategoryTheory.Abelian.YonedaExtension.yonedaClass_eq_units_smul_extClassMap`: `δ(E)` is, up
  to the sign `(-1)^{i(i + 1)/2}`, the class map `CategoryTheory.Abelian.extClassMap`,
  characterised by its value `CategoryTheory.ShortComplex.ShortExact.extClass` in degree `1` and
  its multiplicativity for splicing (`yonedaClass_zero`, `yonedaClass_succ`).
* `CategoryTheory.Abelian.YonedaExtension.surjective_yonedaClass`,
  `CategoryTheory.Abelian.YonedaExtension.equivalent_iff_yonedaClass_eq`: the source's lemma.

## Implementation notes

The sign comes from Mathlib's sign conventions: the connecting morphism of the distinguished
triangle of a short exact sequence `0 → A → X → C → 0` is `-(f s⁻¹)` for the two-term complex
`A → X`, and translating a mapping cone by `k` multiplies its third morphism by `(-1)^k`. The
degree `1` case and the splicing step are both computed through the mapping cone of
`A[0] ⟶ X[0]`, using `CochainComplex.mappingCone.lift`.

## References

* [Stacks Project, Tag 06XU](https://stacks.math.columbia.edu/tag/06XU)
-/

@[expose] public section

universe w w'

namespace CategoryTheory

namespace Abelian

open Limits ZeroObject ComposableArrows CochainComplex CochainComplex.HomComplex

namespace YonedaExtension

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-! ### The cochain complex of a sequence of composable arrows -/

section ArrowsComplex

variable {m : ℕ} (F : ComposableArrows 𝒜 m)

/-- The object in degree `j` of the cochain complex `F_0 → F_1 → ⋯ → F_m` placed in degrees
`-m, …, 0`: it is `F_{j + m}` for `-m ≤ j ≤ 0` and `0` otherwise. -/
noncomputable def arrowsComplexX (j : ℤ) : 𝒜 :=
  if h : 0 ≤ j + m ∧ j ≤ 0 then F.obj ⟨(j + m).toNat, by omega⟩ else (0 : 𝒜)

lemma arrowsComplexX_eq (j : ℤ) (k : ℕ) (hk : k ≤ m) (h : j + m = k) :
    arrowsComplexX F j = F.obj' k := by
  rw [arrowsComplexX, dite_eq_left (by omega)]
  exact congrArg F.obj (Fin.ext (show (j + m).toNat = k by omega))

lemma isZero_arrowsComplexX (j : ℤ) (h : j + m < 0 ∨ 0 < j) : IsZero (arrowsComplexX F j) := by
  rw [arrowsComplexX, dite_eq_right (by omega)]
  exact isZero_zero _

/-- The differential of the cochain complex `F_0 → F_1 → ⋯ → F_m` placed in degrees
`-m, …, 0`. -/
noncomputable def arrowsComplexD (i j : ℤ) : arrowsComplexX F i ⟶ arrowsComplexX F j :=
  if h : 0 ≤ i + m ∧ j ≤ 0 ∧ i + 1 = j then
    eqToHom (arrowsComplexX_eq F i (i + m).toNat (by omega) (by omega)) ≫
      F.map' (i + m).toNat ((i + m).toNat + 1) (by omega) (by omega) ≫
        eqToHom (arrowsComplexX_eq F j ((i + m).toNat + 1) (by omega) (by omega)).symm
  else 0

lemma arrowsComplexD_eq (i j : ℤ) (k : ℕ) (hk : k + 1 ≤ m) (hi : i + m = k) (hj : i + 1 = j) :
    arrowsComplexD F i j = eqToHom (arrowsComplexX_eq F i k (by omega) hi) ≫ F.map' k (k + 1) ≫
      eqToHom (arrowsComplexX_eq F j (k + 1) hk (by omega)).symm := by
  obtain rfl : k = (i + m).toNat := by omega
  rw [arrowsComplexD, dite_eq_left (by omega)]

lemma arrowsComplexD_eq_zero (i j : ℤ) (h : ¬ (0 ≤ i + m ∧ j ≤ 0 ∧ i + 1 = j)) :
    arrowsComplexD F i j = 0 :=
  dite_eq_right h

lemma arrowsComplexD_comp (hF : F.IsComplex) (i j l : ℤ) :
    arrowsComplexD F i j ≫ arrowsComplexD F j l = 0 := by
  by_cases h₁ : 0 ≤ i + m ∧ j ≤ 0 ∧ i + 1 = j
  · by_cases h₂ : 0 ≤ j + m ∧ l ≤ 0 ∧ j + 1 = l
    · have h0 : F.map' (i + m).toNat ((i + m).toNat + 1) ≫
          F.map' ((i + m).toNat + 1) ((i + m).toNat + 1 + 1) = 0 := hF.zero _ (by omega)
      rw [arrowsComplexD_eq F i j (i + m).toNat (by omega) (by omega) h₁.2.2,
        arrowsComplexD_eq F j l ((i + m).toNat + 1) (by omega) (by omega) h₂.2.2]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        reassoc_of% h0, zero_comp, comp_zero]
    · rw [arrowsComplexD_eq_zero F j l h₂, comp_zero]
  · rw [arrowsComplexD_eq_zero F i j h₁, zero_comp]

/-- The cochain complex `⋯ → 0 → F_0 → F_1 → ⋯ → F_m → 0 → ⋯` of a sequence of composable
arrows `F` whose consecutive composites vanish, with `F_m` in degree `0`. -/
noncomputable def arrowsComplex (hF : F.IsComplex) : CochainComplex 𝒜 ℤ where
  X := arrowsComplexX F
  d := arrowsComplexD F
  shape i j hij := arrowsComplexD_eq_zero F i j (by simp only [ComplexShape.up_Rel] at hij; omega)
  d_comp_d' i j l _ _ := arrowsComplexD_comp F hF i j l

/-- The complex of an exact sequence of composable arrows is exact in the degrees of the
interior objects. -/
lemma arrowsComplex_exactAt (hF : F.Exact) (j : ℤ) (i : ℕ) (hi : i + 2 ≤ m)
    (h : j - 1 + m = i) : (arrowsComplex F hF.toIsComplex).ExactAt j := by
  rw [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp)]
  refine ShortComplex.exact_of_iso ?_ (hF.exact i hi)
  refine ShortComplex.isoMk (eqToIso (arrowsComplexX_eq F (j - 1) i (by omega) h).symm)
    (eqToIso (arrowsComplexX_eq F j (i + 1) (by omega) (by omega)).symm)
    (eqToIso (arrowsComplexX_eq F (j + 1) (i + 2) hi (by omega)).symm) ?_ ?_
  · dsimp [arrowsComplex, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    rw [arrowsComplexD_eq F (j - 1) j i (by omega) h (by omega)]
    simp
  · dsimp [arrowsComplex, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    rw [arrowsComplexD_eq F j (j + 1) (i + 1) (by omega) (by omega) rfl]
    simp

end ArrowsComplex

section ArrowsComplexHom

variable {m : ℕ} (F : ComposableArrows 𝒜 (m + 1)) (G : ComposableArrows 𝒜 m)
  (u : ∀ (i : ℕ) (_ : i ≤ m), F.obj' (i + 1) ⟶ G.obj' i)

/-- The components of `arrowsComplexHom`. -/
noncomputable def arrowsComplexHomF (j : ℤ) : arrowsComplexX F j ⟶ arrowsComplexX G j :=
  if h : 0 ≤ j + m ∧ j ≤ 0 then
    eqToHom (arrowsComplexX_eq F j ((j + m).toNat + 1) (by omega) (by omega)) ≫
      u (j + m).toNat (by omega) ≫
        eqToHom (arrowsComplexX_eq G j (j + m).toNat (by omega) (by omega)).symm
  else 0

lemma arrowsComplexHomF_eq (j : ℤ) (k : ℕ) (hk : k ≤ m) (h : j + m = k) :
    arrowsComplexHomF F G u j =
      eqToHom (arrowsComplexX_eq F j (k + 1) (by omega) (by omega)) ≫ u k hk ≫
        eqToHom (arrowsComplexX_eq G j k hk h).symm := by
  obtain rfl : k = (j + m).toNat := by omega
  rw [arrowsComplexHomF, dite_eq_left (by omega)]

lemma arrowsComplexHomF_eq_zero (j : ℤ) (h : ¬ (0 ≤ j + m ∧ j ≤ 0)) :
    arrowsComplexHomF F G u j = 0 :=
  dite_eq_right h

/-- The morphism of complexes `arrowsComplex F ⟶ arrowsComplex G` given by maps
`u i : F_{i + 1} ⟶ G_i` commuting with the arrows, with `F_0 ⟶ F_1 ⟶ G_0` zero. -/
noncomputable def arrowsComplexHom (hF : F.IsComplex) (hG : G.IsComplex)
    (h₀ : F.map' 0 1 ≫ u 0 (by omega) = 0)
    (hu : ∀ (i : ℕ) (hi : i + 1 ≤ m),
      F.map' (i + 1) (i + 1 + 1) ≫ u (i + 1) hi = u i (by omega) ≫ G.map' i (i + 1)) :
    arrowsComplex F hF ⟶ arrowsComplex G hG where
  f := arrowsComplexHomF F G u
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    dsimp [arrowsComplex]
    by_cases hj : 0 ≤ i + 1 + m ∧ i + 1 ≤ 0
    · by_cases hi : 0 ≤ i + m
      · rw [arrowsComplexHomF_eq F G u i (i + m).toNat (by omega) (by omega),
          arrowsComplexHomF_eq F G u (i + 1) ((i + m).toNat + 1) (by omega) (by omega),
          arrowsComplexD_eq G i (i + 1) (i + m).toNat (by omega) (by omega) rfl,
          arrowsComplexD_eq F i (i + 1) ((i + m).toNat + 1) (by omega) (by omega) rfl]
        have key := hu (i + m).toNat (by omega)
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          reassoc_of% key]
      · rw [arrowsComplexHomF_eq_zero F G u i (by omega), zero_comp,
          arrowsComplexHomF_eq F G u (i + 1) 0 (by omega) (by omega),
          arrowsComplexD_eq F i (i + 1) 0 (by omega) (by omega) rfl]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          reassoc_of% h₀, zero_comp, comp_zero]
    · rw [arrowsComplexHomF_eq_zero F G u (i + 1) hj, comp_zero,
        arrowsComplexD_eq_zero G i (i + 1) (by omega), comp_zero]

lemma arrowsComplexHom_f (hF : F.IsComplex) (hG : G.IsComplex)
    (h₀ : F.map' 0 1 ≫ u 0 (by omega) = 0)
    (hu : ∀ (i : ℕ) (hi : i + 1 ≤ m),
      F.map' (i + 1) (i + 1 + 1) ≫ u (i + 1) hi = u i (by omega) ≫ G.map' i (i + 1))
    (j : ℤ) (k : ℕ) (hk : k ≤ m) (h : j + m = k) :
    (arrowsComplexHom F G u hF hG h₀ hu).f j =
      eqToHom (arrowsComplexX_eq F j (k + 1) (by omega) (by omega)) ≫ u k hk ≫
        eqToHom (arrowsComplexX_eq G j k hk h).symm :=
  arrowsComplexHomF_eq F G u j k hk h

end ArrowsComplexHom

/-! ### Morphisms to a translated single complex -/

section ToShiftSingle

/-- The object in degree `j` of the translate `X[0]⟦q⟧` of the complex `X[0]` concentrated in
degree `0` is `X` when `j + q = 0`. -/
noncomputable abbrev shiftSingleXIso (X : 𝒜) (q j : ℤ) (h : j + q = 0) :
    (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj X)⟦q⟧).X j ≅ X :=
  HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X (j + q) h

/-- The morphism `K ⟶ X[0]⟦q⟧` to the translate of the single complex `X[0]` (which is `X` in
degree `-q`) given by a map `u : K^{-q} ⟶ X` vanishing on the image of `K^{-q-1}`. -/
noncomputable def homToShiftSingle (K : CochainComplex 𝒜 ℤ) (X : 𝒜) (q : ℤ) (u : K.X (-q) ⟶ X)
    (hu : K.d (-q - 1) (-q) ≫ u = 0) :
    K ⟶ ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj X)⟦q⟧ :=
  Cocycle.homOf (Cocycle.mk (Cochain.single (p := -q) (q := -q)
    (u ≫ (shiftSingleXIso X q (-q) (by omega)).inv) 0) 1 (zero_add 1) (by
      rw [Cochain.δ_single _ 0 1 (zero_add 1) (-q - 1) (-q + 1) (by omega) (by omega)]
      simp [reassoc_of% hu]))

lemma homToShiftSingle_f (K : CochainComplex 𝒜 ℤ) (X : 𝒜) (q : ℤ) (u : K.X (-q) ⟶ X)
    (hu : K.d (-q - 1) (-q) ≫ u = 0) (j : ℤ) (h : j = -q) :
    (homToShiftSingle K X q u hu).f j =
      (K.XIsoOfEq h).hom ≫ u ≫ (shiftSingleXIso X q j (by omega)).inv := by
  subst h
  simp [homToShiftSingle]

lemma hom_ext_toShiftSingle {K : CochainComplex 𝒜 ℤ} {X : 𝒜} {q : ℤ}
    {g₁ g₂ : K ⟶ ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj X)⟦q⟧}
    (h : g₁.f (-q) = g₂.f (-q)) : g₁ = g₂ := by
  ext j
  by_cases hj : j = -q
  · subst hj
    exact h
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X (j + q)
      (by omega)).eq_of_tgt _ _

lemma single_map_f_of_eq {X Y : 𝒜} (u : X ⟶ Y) (i : ℤ) (hi : i = 0) :
    ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).map u).f i =
      (HomologicalComplex.singleObjXIsoOfEq _ 0 X i hi).hom ≫ u ≫
        (HomologicalComplex.singleObjXIsoOfEq _ 0 Y i hi).inv := by
  subst hi
  exact HomologicalComplex.single_map_f_self _ _ u

@[reassoc]
lemma singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom (X : 𝒜) (i j : ℤ) (hi : i = 0) (h : i = j) :
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X i hi).inv ≫
        (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj X).XIsoOfEq h).hom =
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X j (h ▸ hi)).inv := by
  subst h
  simp

@[reassoc]
lemma singleObjXIsoOfEq_inv_comp_XIsoOfEq_inv (X : 𝒜) (i j : ℤ) (hi : i = 0) (h : j = i) :
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X i hi).inv ≫
        (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj X).XIsoOfEq h).inv =
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X j (h ▸ hi)).inv := by
  subst h
  simp

end ToShiftSingle

/-! ### The complex of a Yoneda extension -/

section Complex

variable {B A : 𝒜} {n : ℕ}

/-- The complex `(⋯ → 0 → A → Z_n → ⋯ → Z_0 → 0 → ⋯)` of a degree `n + 1` Yoneda extension
`E : 0 → A → Z_n → ⋯ → Z_0 → B → 0`, with `Z_0` in degree `0` and `A` in degree `-(n + 1)`. -/
noncomputable def complex (E : YonedaExtension B A n) : CochainComplex 𝒜 ℤ :=
  arrowsComplex (E.Z.precomp E.f) E.exact.toIsComplex

lemma complex_X_eq (E : YonedaExtension B A n) (j : ℤ) (k : ℕ) (hk : k ≤ n + 1)
    (h : j + (n + 1 : ℕ) = k) : E.complex.X j = (E.Z.precomp E.f).obj' k :=
  arrowsComplexX_eq _ j k hk h

lemma complex_d_eq (E : YonedaExtension B A n) (i j : ℤ) (k : ℕ) (hk : k + 1 ≤ n + 1)
    (hi : i + (n + 1 : ℕ) = k) (hj : i + 1 = j) :
    E.complex.d i j = eqToHom (E.complex_X_eq i k (by omega) hi) ≫
      (E.Z.precomp E.f).map' k (k + 1) ≫ eqToHom (E.complex_X_eq j (k + 1) hk (by omega)).symm :=
  arrowsComplexD_eq _ i j k hk hi hj

lemma complex_d_eq' (E : YonedaExtension B A n) (i j : ℤ) (k k' : ℕ) (hk : k' ≤ n + 1)
    (hk' : k + 1 = k') (hi : i + (n + 1 : ℕ) = k) (hj : i + 1 = j) :
    E.complex.d i j = eqToHom (E.complex_X_eq i k (by omega) hi) ≫
      (E.Z.precomp E.f).map' k k' ≫ eqToHom (E.complex_X_eq j k' hk (by omega)).symm := by
  subst hk'
  exact E.complex_d_eq i j k hk hi hj

lemma complex_X_left (E : YonedaExtension B A n) : E.complex.X (-(n : ℤ)) = E.Z.left :=
  E.complex_X_eq _ 1 (by omega) (by omega)

lemma complex_X_right (E : YonedaExtension B A n) : E.complex.X 0 = E.Z.right :=
  E.complex_X_eq 0 (n + 1) le_rfl (by omega)

lemma complex_X_bot (E : YonedaExtension B A n) : E.complex.X (-(n : ℤ) - 1) = A :=
  E.complex_X_eq _ 0 (by omega) (by omega)

lemma complex_d_bot (E : YonedaExtension B A n) :
    E.complex.d (-(n : ℤ) - 1) (-(n : ℤ)) =
      eqToHom E.complex_X_bot ≫ E.f ≫ eqToHom E.complex_X_left.symm := by
  rw [E.complex_d_eq' (-(n : ℤ) - 1) (-(n : ℤ)) 0 1 (by omega) rfl (by omega) (by omega)]
  rfl

lemma complex_d_bot_comp (E : YonedaExtension B A n) {C : 𝒜} (p : E.Z.left ⟶ C)
    (hp : E.f ≫ p = 0) :
    E.complex.d (-(n : ℤ) - 1) (-(n : ℤ)) ≫ eqToHom E.complex_X_left ≫ p = 0 := by
  rw [E.complex_d_bot]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, hp, comp_zero]

lemma isZero_complex_X (E : YonedaExtension B A n) (j : ℤ) (h : j + (n + 1 : ℕ) < 0 ∨ 0 < j) :
    IsZero (E.complex.X j) :=
  isZero_arrowsComplexX _ j h

/-- The quasi-isomorphism `s` from the complex of a Yoneda extension
`0 → A → Z_n → ⋯ → Z_0 → B → 0` to `B[0]`, given by `Z_0 ⟶ B` in degree `0`. -/
noncomputable def complexπ (E : YonedaExtension B A n) :
    E.complex ⟶ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B :=
  HomologicalComplex.mkHomToSingle (eqToHom (E.complex_X_eq 0 (n + 1) le_rfl (by omega)) ≫ E.g)
    (fun i hi => by
      obtain rfl : i = -1 := by simp only [ComplexShape.up_Rel] at hi; omega
      have h0 : (E.Z.precomp E.f).map' n (n + 1) ≫ E.g = 0 := E.exact_g.toIsComplex.zero 0
      rw [E.complex_d_eq (-1) 0 n (by omega) (by omega) (by omega)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        h0, comp_zero])

lemma complexπ_f_zero (E : YonedaExtension B A n) :
    E.complexπ.f 0 = (eqToHom (E.complex_X_eq 0 (n + 1) le_rfl (by omega)) ≫ E.g) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

lemma complexπ_f_zero' (E : YonedaExtension B A n) :
    E.complexπ.f 0 = (eqToHom E.complex_X_right ≫ E.g) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  E.complexπ_f_zero

lemma complexπ_f (E : YonedaExtension B A n) (i : ℤ) (hi : i = 0) :
    E.complexπ.f i = (E.complex.XIsoOfEq hi).hom ≫ (eqToHom E.complex_X_right ≫ E.g) ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 B i hi).inv := by
  subst hi
  rw [complexπ_f_zero', HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rfl

/-- The morphism `f` from the complex of a Yoneda extension `0 → A → Z_n → ⋯ → Z_0 → B → 0` to
`A[n + 1]`, given by the identity of `A` in degree `-(n + 1)`. -/
noncomputable def complexι (E : YonedaExtension B A n) :
    E.complex ⟶ ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A)⟦((n + 1 : ℕ) : ℤ)⟧ :=
  homToShiftSingle E.complex A ((n + 1 : ℕ) : ℤ)
    (eqToHom (E.complex_X_eq (-((n + 1 : ℕ) : ℤ)) 0 (by omega) (by omega)))
    ((E.isZero_complex_X _ (by omega)).eq_of_src _ _)

lemma exactAt_complex (E : YonedaExtension B A n) (j : ℤ) (hj : j ≠ 0) :
    E.complex.ExactAt j := by
  by_cases h₁ : j + (n + 1 : ℕ) < 0 ∨ 0 < j
  · exact HomologicalComplex.ExactAt.of_isZero (E.isZero_complex_X j h₁)
  · by_cases h₂ : j + (n + 1 : ℕ) = 0
    · rw [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp),
        ShortComplex.exact_iff_mono _ ((E.isZero_complex_X (j - 1) (by omega)).eq_of_src _ _)]
      change Mono (E.complex.d j (j + 1))
      rw [E.complex_d_eq j (j + 1) 0 (by omega) (by omega) rfl]
      have : Mono ((E.Z.precomp E.f).map' 0 1) := E.mono_f
      exact mono_comp _ _
    · exact arrowsComplex_exactAt _ E.exact j ((j - 1 + (n + 1 : ℕ)).toNat) (by omega) (by omega)

lemma quasiIsoAt_complexπ_of_ne (E : YonedaExtension B A n) (j : ℤ) (hj : j ≠ 0) :
    QuasiIsoAt E.complexπ j := by
  have h1 := HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 B j hj
  have h2 := E.exactAt_complex j hj
  exact (quasiIsoAt_iff_exactAt' E.complexπ j h1).2 h2

lemma quasiIsoAt_complexπ_zero (E : YonedaExtension B A n) : QuasiIsoAt E.complexπ 0 := by
  have hg₁ : (E.complex.sc' (-1) 0 1).g = 0 := (E.isZero_complex_X 1 (by omega)).eq_of_tgt _ _
  have hf₂ : (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B).sc' (-1) 0 1).f = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 B (-1) 0
  have hg₂ : (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B).sc' (-1) 0 1).g = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 B 0 1
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.quasiIso_iff_of_zeros' _ hg₁ hf₂ hg₂]
  have hc : E.complex.d (-1) 0 ≫ E.complexπ.f 0 = 0 := by
    rw [← E.complexπ.comm, HomologicalComplex.single_obj_d, comp_zero]
  change (ShortComplex.mk (E.complex.d (-1) 0) (E.complexπ.f 0) hc).Exact ∧ Epi (E.complexπ.f 0)
  have h0 : (E.Z.precomp E.f).map' n (n + 1) ≫ E.g = 0 := E.exact_g.toIsComplex.zero 0
  have hE : (ShortComplex.mk _ _ h0).Exact :=
    (ShortComplex.exact_iff_exact_toComposableArrows _).2 E.exact_g
  refine ⟨ShortComplex.exact_of_iso ?_ hE, by rw [complexπ_f_zero]; exact epi_comp _ _⟩
  refine ShortComplex.isoMk (eqToIso (E.complex_X_eq (-1) n (by omega) (by omega)).symm)
    (eqToIso (E.complex_X_eq 0 (n + 1) le_rfl (by omega)).symm)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).symm ?_ ?_
  · dsimp only
    rw [E.complex_d_eq (-1) 0 n (by omega) (by omega) (by omega)]
    simp only [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · dsimp only
    rw [complexπ_f_zero]
    simp only [eqToIso.hom, Iso.symm_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

instance quasiIso_complexπ (E : YonedaExtension B A n) : QuasiIso E.complexπ := by
  rw [quasiIso_iff]
  intro j
  by_cases hj : j = 0
  · subst hj
    exact E.quasiIsoAt_complexπ_zero
  · exact E.quasiIsoAt_complexπ_of_ne j hj

end Complex

/-! ### Comparison with the mapping cone of a short exact sequence -/

section Cone

variable {B A : 𝒜} {k : ℕ} (E : YonedaExtension B A k) {C : 𝒜} (p : E.Z.left ⟶ C)
  (hp : E.f ≫ p = 0)

/-- The short exact sequence `0 → A[0] → Z_k[0] → C[0] → 0` of complexes given by a cokernel
`p : Z_k ⟶ C` of the first map of a Yoneda extension. -/
private noncomputable abbrev coneSES : ShortComplex (CochainComplex 𝒜 ℤ) :=
  (ShortComplex.mk E.f p hp).map (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0)

/-- The `1`-cochain from the complex of `E` to `A[0]⟦k⟧` which is the identity of `A` in degree
`-(k + 1)`. -/
private noncomputable def coneαCochain :
    Cochain E.complex (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A)⟦(k : ℤ)⟧) 1 :=
  Cochain.single (p := -(k : ℤ) - 1) (q := -(k : ℤ))
    (eqToHom E.complex_X_bot ≫ (shiftSingleXIso A (k : ℤ) (-(k : ℤ)) (by omega)).inv) 1

private lemma δ_coneαCochain : δ 1 2 (coneαCochain E) = 0 := by
  unfold coneαCochain
  rw [Cochain.δ_single _ 1 2 (by norm_num) (-(k : ℤ) - 1 - 1) (-(k : ℤ) + 1)
    (by omega) (by omega)]
  have h₁ : E.complex.d (-(k : ℤ) - 1 - 1) (-(k : ℤ) - 1) = 0 :=
    (E.isZero_complex_X _ (by omega)).eq_of_src _ _
  rw [h₁, zero_comp]
  simp

/-- The `1`-cocycle from the complex of `E` to `A[0]⟦k⟧` which is the identity of `A` in degree
`-(k + 1)`. -/
private noncomputable def coneα :
    Cocycle E.complex (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A)⟦(k : ℤ)⟧) 1 :=
  Cocycle.mk (coneαCochain E) 2 (by norm_num) (δ_coneαCochain E)

private lemma coneα_coe : (coneα E : Cochain _ _ 1) = coneαCochain E := rfl

/-- The `0`-cochain from the complex of `E` to `Z_k[0]⟦k⟧` which is the identity of `Z_k` in
degree `-k`. -/
private noncomputable def coneβ :
    Cochain E.complex (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj E.Z.left)⟦(k : ℤ)⟧)
      0 :=
  Cochain.single (p := -(k : ℤ)) (q := -(k : ℤ))
    (eqToHom E.complex_X_left ≫ (shiftSingleXIso E.Z.left (k : ℤ) (-(k : ℤ)) (by omega)).inv) 0

private lemma cone_eq :
    (δ 0 1 (coneβ E) : Cochain E.complex ((coneSES E p hp).X₂⟦(k : ℤ)⟧) 1) + (coneα E).1.comp
    (Cochain.ofHom ((coneSES E p hp).f⟦(k : ℤ)⟧')) (add_zero 1) = 0 := by
  rw [coneα_coe]
  unfold coneαCochain coneβ
  rw [Cochain.δ_single _ 0 1 (zero_add 1) (-(k : ℤ) - 1) (-(k : ℤ) + 1)
    (by omega) (by omega)]
  have hd : (((coneSES E p hp).X₂)⟦(k : ℤ)⟧).d (-(k : ℤ)) (-(k : ℤ) + 1) = 0 := by
    rw [shiftFunctor_obj_d', ShortComplex.map_X₂, HomologicalComplex.single_obj_d, smul_zero]
  rw [hd, comp_zero, Cochain.single_zero, zero_add]
  ext q r hqr
  by_cases hq : q = -(k : ℤ) - 1
  · subst hq
    obtain rfl : r = -(k : ℤ) := by omega
    rw [Cochain.add_v, Cochain.units_smul_v, Cochain.comp_zero_cochain_v,
      Cochain.single_v, Cochain.single_v,
      Cochain.ofHom_v, Cochain.zero_v, Int.negOnePow_one, Units.neg_smul, one_smul,
      E.complex_d_bot,
      shiftFunctor_map_f', ShortComplex.map_f, single_map_f_of_eq E.f (-(k : ℤ) + k) (by omega)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Iso.inv_hom_id_assoc, neg_add_cancel]
  · rw [Cochain.add_v, Cochain.units_smul_v, Cochain.comp_zero_cochain_v,
      Cochain.single_v_eq_zero _ _ _ _ _ hq, Cochain.single_v_eq_zero _ _ _ _ _ hq,
      zero_comp, smul_zero, add_zero, Cochain.zero_v]

/-- The morphism from the complex of `E` to the translate by `k` of the mapping cone of
`A[0] ⟶ Z_k[0]`, through which both `s` and `f` factor. -/
private noncomputable def coneπ : E.complex ⟶ (mappingCone (coneSES E p hp).f)⟦(k : ℤ)⟧ :=
  mappingCone.lift ((coneSES E p hp).f⟦(k : ℤ)⟧') (coneα E) (coneβ E) (cone_eq E p hp) ≫
    (mappingCone.shiftIso (coneSES E p hp).f (k : ℤ)).inv

private lemma coneπ_desc :
    coneπ E p hp ≫ (mappingCone.descShortComplex (coneSES E p hp))⟦(k : ℤ)⟧' =
      homToShiftSingle E.complex C (k : ℤ)
        (eqToHom E.complex_X_left ≫ p) (E.complex_d_bot_comp p hp) := by
  rw [coneπ, Category.assoc, DerivedCategory.shiftIso_inv_descShortComplex_shift]
  apply hom_ext_toShiftSingle
  rw [HomologicalComplex.comp_f]
  change (mappingCone.lift ((coneSES E p hp).f⟦(k : ℤ)⟧') (coneα E) (coneβ E)
      (cone_eq E p hp)).f (-(k : ℤ)) ≫ (mappingCone.desc ((coneSES E p hp).f⟦(k : ℤ)⟧') 0
        ((coneSES E p hp).g⟦(k : ℤ)⟧') (by simp [← Functor.map_comp, hp])).f (-(k : ℤ)) = _
  rw [mappingCone.lift_desc_f (n := -(k : ℤ)) (n' := -(k : ℤ) + 1) (hnn' := rfl),
    Cochain.zero_v, comp_zero, zero_add, homToShiftSingle_f _ _ _ _ _ _ rfl]
  unfold coneβ
  rw [Cochain.single_v, shiftFunctor_map_f', ShortComplex.map_g,
    single_map_f_of_eq p (-(k : ℤ) + k) (by omega)]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The third morphism `mappingCone (A[0] ⟶ Z_k[0]) ⟶ A[0]⟦1⟧` of the mapping cone triangle,
typed with the mapping cone as its source. -/
private noncomputable def coneMor₃ :
    mappingCone (coneSES E p hp).f ⟶ ((coneSES E p hp).X₁)⟦(1 : ℤ)⟧ :=
  (mappingCone.triangle (coneSES E p hp).f).mor₃

private lemma inl_v_coneMor₃_f (q r : ℤ) (h : q + (-1) = r) :
    (mappingCone.inl (coneSES E p hp).f).v q r h ≫ (coneMor₃ E p hp).f r =
      -((coneSES E p hp).X₁.shiftFunctorObjXIso 1 r q (by omega)).inv :=
  mappingCone.inl_v_triangle_mor₃_f _ _ _ _

private lemma coneπ_mor₃ :
    coneπ E p hp ≫ (coneMor₃ E p hp)⟦(k : ℤ)⟧' ≫
      (shiftFunctorAdd' (CochainComplex 𝒜 ℤ) 1 (k : ℤ) ((k + 1 : ℕ) : ℤ)
        (by push_cast; ring)).inv.app ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A) =
      (-(k : ℤ).negOnePow) • E.complexι := by
  refine hom_ext_toShiftSingle (K := E.complex) (X := A) (q := ((k + 1 : ℕ) : ℤ)) ?_
  have hj : -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 := by push_cast; ring
  rw [hj]
  simp only [coneπ, mappingCone.shiftIso, HomologicalComplex.comp_f,
    HomologicalComplex.units_smul_f_apply, Category.assoc]
  rw [← Category.assoc, mappingCone.lift_desc_f (n := -(k : ℤ) - 1) (n' := -(k : ℤ))
    (hnn' := by omega), coneα_coe]
  unfold coneαCochain coneβ complexι
  rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), zero_comp, add_zero,
    Cochain.units_smul_v, Cochain.shift_v',
    homToShiftSingle_f _ _ _ _ _ (-(k : ℤ) - 1) (by push_cast; ring), shiftFunctor_map_f']
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
  rw [reassoc_of% (inl_v_coneMor₃_f E p hp (-(k : ℤ) + k) (-(k : ℤ) - 1 + k) (by omega)),
    shiftFunctorAdd'_inv_app_f']
  rw [Preadditive.neg_comp, Preadditive.comp_neg, Preadditive.comp_neg, smul_neg, Units.neg_smul]
  congr 2
  change eqToHom _ ≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 A
      (-(k : ℤ) + k) _).inv ≫
    (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A).XIsoOfEq _).inv ≫
      (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A).XIsoOfEq _).hom = _
  rw [singleObjXIsoOfEq_inv_comp_XIsoOfEq_inv_assoc, singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom, eqToHom_trans_assoc]

end Cone

omit [Abelian 𝒜] in
private lemma eqToHom_comp_comp_aux {X P P' X' B' V : 𝒜} (h₁ : X = P) (u : P ⟶ P') (h₂ : P' = X')
    (h₃ : X' = P') (g : P' ⟶ B') (g' : P ⟶ B') (hw : u ≫ g = g') (v : B' ⟶ V) :
    (eqToHom h₁ ≫ u ≫ eqToHom h₂) ≫ (eqToHom h₃ ≫ g) ≫ v = (eqToHom h₁ ≫ g') ≫ v := by
  subst h₂ hw
  simp

/-! ### Cutting a Yoneda extension, on complexes -/

section Cut

variable {B A : 𝒜} {n : ℕ} (E : YonedaExtension B A (n + 1)) {C : 𝒜}
  (E' : YonedaExtension B C n) (p : E.Z.left ⟶ C) (h : E.f ≫ p = 0) (φ : E.Z.δ₀ ≅ E'.Z)
  (w₁ : E.Z.map' 0 1 ≫ app' φ.hom 0 = p ≫ E'.f)

/-- The morphism from the complex of a Yoneda extension `E` of degree `n + 2` to the complex of
a degree `n + 1` extension `E'` it is cut into: `Z_{n + 1} ⟶ C` in degree `-(n + 1)` and the
identifications `Z_i ≅ Z'_i` above. -/
private noncomputable def cutComplexHom : E.complex ⟶ E'.complex :=
  arrowsComplexHom (E.Z.precomp E.f) (E'.Z.precomp E'.f)
    (fun i hi => match i, hi with
      | 0, _ => p
      | i + 1, hi => app' φ.hom i (by omega))
    E.exact.toIsComplex E'.exact.toIsComplex h (fun i hi => by
      match i, hi with
      | 0, _ => exact w₁
      | i + 1, hi => exact naturality' φ.hom i (i + 1) (by omega) (by omega))

private lemma cutComplexHom_f_zero :
    (cutComplexHom E E' p h φ w₁).f 0 =
      eqToHom (E.complex_X_eq 0 (n + 1 + 1) le_rfl (by omega)) ≫
        (app' φ.hom n (by omega) :
          (E.Z.precomp E.f).obj' (n + 1 + 1) ⟶ (E'.Z.precomp E'.f).obj' (n + 1)) ≫
        eqToHom (E'.complex_X_eq 0 (n + 1) le_rfl (by omega)).symm :=
  arrowsComplexHom_f _ _ _ _ _ _ _ 0 (n + 1) le_rfl (by omega)

private lemma cutComplexHom_f_bot :
    (cutComplexHom E E' p h φ w₁).f (-((n + 1 : ℕ) : ℤ)) =
      eqToHom E.complex_X_left ≫ p ≫
        eqToHom (E'.complex_X_eq (-((n + 1 : ℕ) : ℤ)) 0 (by omega) (by omega)).symm :=
  arrowsComplexHom_f _ _ _ _ _ _ _ _ 0 (by omega) (by omega)

private lemma cutComplexHom_comp_complexπ (w₂ : app' φ.hom n ≫ E'.g = E.g) :
    cutComplexHom E E' p h φ w₁ ≫ E'.complexπ = E.complexπ := by
  have w₂' : (app' φ.hom n (by omega) :
      (E.Z.precomp E.f).obj' (n + 1 + 1) ⟶ (E'.Z.precomp E'.f).obj' (n + 1)) ≫
        (E'.g : (E'.Z.precomp E'.f).obj' (n + 1) ⟶ B) =
      (E.g : (E.Z.precomp E.f).obj' (n + 1 + 1) ⟶ B) := w₂
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, complexπ_f_zero, complexπ_f_zero, cutComplexHom_f_zero]
  exact eqToHom_comp_comp_aux _ _ _ _ _ _ w₂' _

private lemma cutComplexHom_comp_complexι :
    cutComplexHom E E' p h φ w₁ ≫ E'.complexι =
      homToShiftSingle E.complex C ((n + 1 : ℕ) : ℤ) (eqToHom E.complex_X_left ≫ p)
        (E.complex_d_bot_comp p h) := by
  apply hom_ext_toShiftSingle
  rw [HomologicalComplex.comp_f, homToShiftSingle_f _ _ _ _ _ _ rfl, cutComplexHom_f_bot]
  unfold complexι
  rw [homToShiftSingle_f _ _ _ _ _ _ rfl]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl]

end Cut

/-! ### The class `δ(E) = f s⁻¹` -/

section Class

variable [HasExt.{w} 𝒜]

private lemma units_smul_ext_hom [HasDerivedCategory.{w'} 𝒜] {X Y : 𝒜} {n : ℕ} (u : ℤˣ)
    (x : Ext.{w} X Y n) : (u • x).hom = u • x.hom := by
  obtain rfl | rfl := Int.units_eq_one_or u
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, Ext.neg_hom]

private lemma units_smul_ext_comp {X Y Z : 𝒜} {a b c : ℕ} (u : ℤˣ) (x : Ext.{w} X Y a)
    (y : Ext.{w} Y Z b) (h : a + b = c) : (u • x).comp y h = u • x.comp y h := by
  obtain rfl | rfl := Int.units_eq_one_or u
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, one_smul, Units.neg_smul, one_smul, Ext.neg_comp]

omit [HasExt.{w} 𝒜] in
/-- The computation behind both the degree `1` case and the splicing step, in the derived
category: if `δ : C₀ ⟶ A₀⟦1⟧` is `t d⁻¹` for morphisms of complexes `d : M ⟶ C₀` (inverted in the
derived category) and `t : M ⟶ A₀⟦1⟧`, and a morphism `π : K ⟶ M⟦k⟧` relates `d` and `t` to
`φ ≫ f'` and `f`, then `(f' s'⁻¹) ∘ δ` is `f s⁻¹` up to the sign `u`, where `s = φ ≫ s'`. -/
private lemma roof_comp [HasDerivedCategory.{w'} 𝒜] (k : ℕ) {B₀ C₀ A₀ M K K' : CochainComplex 𝒜 ℤ}
    (d : M ⟶ C₀) (t : M ⟶ A₀⟦(1 : ℤ)⟧) [IsIso (DerivedCategory.Q.map d)]
    (δ : DerivedCategory.Q.obj C₀ ⟶ (DerivedCategory.Q.obj A₀)⟦(1 : ℤ)⟧)
    (hδ : DerivedCategory.Q.map d ≫ δ =
      DerivedCategory.Q.map t ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app A₀)
    (s : K ⟶ B₀) (s' : K' ⟶ B₀) [IsIso (DerivedCategory.Q.map s)]
    [IsIso (DerivedCategory.Q.map s')] (φ : K ⟶ K') (hφ : φ ≫ s' = s)
    (f : K ⟶ A₀⟦((k + 1 : ℕ) : ℤ)⟧) (f' : K' ⟶ C₀⟦(k : ℤ)⟧)
    (π : K ⟶ M⟦(k : ℤ)⟧) (ha : π ≫ d⟦(k : ℤ)⟧' = φ ≫ f') (u : ℤˣ)
    (hb : π ≫ t⟦(k : ℤ)⟧' ≫ (shiftFunctorAdd' (CochainComplex 𝒜 ℤ) 1 (k : ℤ) ((k + 1 : ℕ) : ℤ)
        (by push_cast; ring)).inv.app A₀ = u • f) :
    (inv (DerivedCategory.Q.map s') ≫ DerivedCategory.Q.map f' ≫
        (DerivedCategory.Q.commShiftIso (k : ℤ)).hom.app C₀) ≫ δ⟦(k : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory 𝒜) 1 (k : ℤ) ((k + 1 : ℕ) : ℤ)
        (by push_cast; ring)).inv.app (DerivedCategory.Q.obj A₀) =
      u • (inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map f ≫
        (DerivedCategory.Q.commShiftIso ((k + 1 : ℕ) : ℤ)).hom.app A₀) := by
  rw [← cancel_epi (DerivedCategory.Q.map s), Linear.comp_units_smul, IsIso.hom_inv_id_assoc,
    ← hφ]
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← ha]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc (shiftFunctor (DerivedCategory 𝒜) (k : ℤ)), hδ,
    ← Linear.units_smul_comp, ← Functor.map_units_smul, ← hb,
    Functor.commShiftIso_add' DerivedCategory.Q
      (show (1 : ℤ) + k = ((k + 1 : ℕ) : ℤ) by push_cast; ring),
    Functor.CommShift.isoAdd'_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  slice_rhs 3 4 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, Category.id_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality_assoc]

end Class

lemma shiftFunctorZero'_inv_app_f (K : CochainComplex 𝒜 ℤ) (a : ℤ) (ha : a = 0) (q : ℤ) :
    ((CategoryTheory.shiftFunctorZero' (CochainComplex 𝒜 ℤ) a ha).inv.app K).f q =
      (K.XIsoOfEq (show q = q + a by omega)).hom := by
  subst ha
  simp [CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f]

/-! ### The class `δ(E) = f s⁻¹` and its comparison with the class map -/

section YonedaClass

variable [HasExt.{w} 𝒜] {B A : 𝒜}

/-- **The class `δ(E) = f s⁻¹` of a Yoneda extension.** For a degree `n + 1` Yoneda extension
`E : 0 → A → Z_n → ⋯ → Z_0 → B → 0`, it is the element of `Ext^{n + 1}_𝒜(B, A)` given by the
morphism `f s⁻¹ : B[0] ⟶ A[n + 1]` of the derived category, where
`s = E.complexπ : (⋯ → 0 → A → Z_n → ⋯ → Z_0 → 0 → ⋯) ⟶ B[0]` is the quasi-isomorphism and
`f = E.complexι` is the morphism to `A[n + 1]`. The derived category used is the standard one,
`HasDerivedCategory.standard`. -/
@[stacks 06XU "the class `δ(E) = f s⁻¹` of a Yoneda extension, defined before the lemma"]
noncomputable def yonedaClass {n : ℕ} (E : YonedaExtension B A n) : Ext.{w} B A (n + 1) :=
  letI := HasDerivedCategory.standard 𝒜
  Ext.homEquiv.symm (inv (DerivedCategory.Q.map E.complexπ) ≫
    DerivedCategory.Q.map E.complexι ≫
      (DerivedCategory.Q.commShiftIso ((n + 1 : ℕ) : ℤ)).hom.app
        ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A))

/-- In every model of the derived category, `yonedaClass E` is the morphism `f s⁻¹`. -/
lemma yonedaClass_hom [HasDerivedCategory 𝒜] {n : ℕ} (E : YonedaExtension B A n) :
    (yonedaClass.{w} E).hom = inv (DerivedCategory.Q.map E.complexπ) ≫
      DerivedCategory.Q.map E.complexι ≫
        (DerivedCategory.Q.commShiftIso ((n + 1 : ℕ) : ℤ)).hom.app
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A) := by
  have hπ : HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ) E.complexπ := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have : E.complex.IsGE 0 := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (asIso (DerivedCategory.Q.map E.complexπ)).symm 0
  have : E.complex.IsLE 0 := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (asIso (DerivedCategory.Q.map E.complexπ)).symm 0
  have : ((CochainComplex.singleFunctor 𝒜 0).obj B).IsGE 0 := inferInstance
  have : ((CochainComplex.singleFunctor 𝒜 0).obj B).IsLE 0 := inferInstance
  have : ((CochainComplex.singleFunctor 𝒜 0).obj A).IsGE 0 := inferInstance
  have : ((CochainComplex.singleFunctor 𝒜 0).obj A).IsLE 0 := inferInstance
  have : Localization.HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)) ℤ
      ((CochainComplex.singleFunctor 𝒜 0).obj B) E.complex :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  have : Localization.HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)) ℤ
      E.complex ((CochainComplex.singleFunctor 𝒜 0).obj A) :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  -- the class `f s⁻¹` as a formal roof, which every model of `D(𝒜)` sends to `f s⁻¹`
  obtain ⟨x, hx⟩ : ∃ x : Ext.{w} B A (n + 1), x =
      (Localization.SmallShiftedHom.mk₀Inv (0 : ℤ) rfl E.complexπ hπ).comp
        (Localization.SmallShiftedHom.mk _ E.complexι) (add_zero _) := ⟨_, rfl⟩
  have hyx : yonedaClass.{w} E = x := by
    letI := HasDerivedCategory.standard 𝒜
    apply Ext.homEquiv.injective
    refine (Equiv.apply_symm_apply _ _).trans ?_
    rw [hx]
    have key := Localization.SmallShiftedHom.equiv_comp
      (HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)) DerivedCategory.Q
      (Localization.SmallShiftedHom.mk₀Inv (0 : ℤ) rfl E.complexπ hπ)
      (Localization.SmallShiftedHom.mk _ E.complexι) (add_zero _)
    rw [Localization.SmallShiftedHom.equiv_mk₀Inv, Localization.SmallShiftedHom.equiv_mk,
      ShiftedHom.mk₀_comp, ShiftedHom.map,
      IsIso.eq_inv_of_hom_inv_id (Localization.isoOfHom_hom_inv_id _ _ E.complexπ hπ)] at key
    exact key.symm
  rw [hyx, hx]
  have key := Localization.SmallShiftedHom.equiv_comp
    (HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)) DerivedCategory.Q
    (Localization.SmallShiftedHom.mk₀Inv (0 : ℤ) rfl E.complexπ hπ)
    (Localization.SmallShiftedHom.mk _ E.complexι) (add_zero _)
  rw [Localization.SmallShiftedHom.equiv_mk₀Inv, Localization.SmallShiftedHom.equiv_mk,
    ShiftedHom.mk₀_comp, ShiftedHom.map,
    IsIso.eq_inv_of_hom_inv_id (Localization.isoOfHom_hom_inv_id _ _ E.complexπ hπ)] at key
  exact key

omit [HasExt.{w} 𝒜] in
private lemma isIso_Q_map_descShortComplex [HasDerivedCategory.{w'} 𝒜] {k : ℕ}
    (E : YonedaExtension B A k) {C : 𝒜} (p : E.Z.left ⟶ C) (hp : E.f ≫ p = 0)
    (hS : (ShortComplex.mk E.f p hp).ShortExact) :
    IsIso (DerivedCategory.Q.map (mappingCone.descShortComplex (coneSES E p hp))) := by
  have := mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0))
  infer_instance

private lemma Q_map_descShortComplex_comp_extClass_hom [HasDerivedCategory.{w'} 𝒜] {k : ℕ}
    (E : YonedaExtension B A k) {C : 𝒜} (p : E.Z.left ⟶ C) (hp : E.f ≫ p = 0)
    (hS : (ShortComplex.mk E.f p hp).ShortExact) :
    DerivedCategory.Q.map (mappingCone.descShortComplex (coneSES E p hp)) ≫ hS.extClass.hom =
      DerivedCategory.Q.map (coneMor₃ E p hp) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A) := by
  rw [hS.extClass_hom]
  exact DerivedCategory.descShortComplex_triangleOfSESδ _

private lemma yonedaClass_zero_of [h𝒟 : HasDerivedCategory.{w'} 𝒜] (E : YonedaExtension B A 0)
    (h : E.f ≫ E.g = 0) (hS : (ShortComplex.mk E.f E.g h).ShortExact)
    (hyc : (yonedaClass.{w} E).hom = inv (DerivedCategory.Q.map E.complexπ) ≫
      DerivedCategory.Q.map E.complexι ≫
        (DerivedCategory.Q.commShiftIso ((0 + 1 : ℕ) : ℤ)).hom.app
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A)) :
    yonedaClass.{w} E = -hS.extClass := by
  have := isIso_Q_map_descShortComplex E E.g h hS
  have hz : ((0 : ℕ) : ℤ) = 0 := Nat.cast_zero
  have h0 : (Ext.mk₀ (𝟙 B)).hom =
      inv (DerivedCategory.Q.map (𝟙 ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B))) ≫
        DerivedCategory.Q.map ((shiftFunctorZero' (CochainComplex 𝒜 ℤ) ((0 : ℕ) : ℤ) hz).inv.app
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B)) ≫
          (DerivedCategory.Q.commShiftIso ((0 : ℕ) : ℤ)).hom.app
            ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B) := by
    rw [Ext.mk₀_hom, Functor.commShiftIso_zero' DerivedCategory.Q ℤ ((0 : ℕ) : ℤ) hz,
      Functor.CommShift.isoZero'_hom_app]
    simp only [ShiftedHom.mk₀, Functor.map_id, IsIso.inv_id, Category.id_comp]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  have hπ0 : E.complexπ ≫ (shiftFunctorZero' (CochainComplex 𝒜 ℤ) ((0 : ℕ) : ℤ) hz).inv.app
      ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj B) =
      homToShiftSingle E.complex B ((0 : ℕ) : ℤ) (eqToHom E.complex_X_left ≫ E.g)
        (E.complex_d_bot_comp E.g h) := by
    apply hom_ext_toShiftSingle
    rw [HomologicalComplex.comp_f, E.complexπ_f _ (by simp),
      homToShiftSingle_f _ _ _ _ _ _ rfl, shiftFunctorZero'_inv_app_f, Category.assoc,
      Category.assoc, singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom]
  have key := roof_comp 0 (A₀ := (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A)
    (mappingCone.descShortComplex (coneSES E E.g h)) (coneMor₃ E E.g h) hS.extClass.hom
    (Q_map_descShortComplex_comp_extClass_hom E E.g h hS) E.complexπ (𝟙 _) E.complexπ
    (Category.comp_id _) E.complexι _ (coneπ E E.g h) ((coneπ_desc E E.g h).trans hπ0.symm) _
    (coneπ_mor₃ E E.g h)
  have key2 : ((Ext.mk₀ (𝟙 B)).comp hS.extClass rfl).hom =
      (-(((0 : ℕ) : ℤ).negOnePow)) • (yonedaClass.{w} E).hom := by
    rw [Ext.comp_hom, h0, hyc]
    exact key
  have e : (Ext.mk₀ (𝟙 B)).comp hS.extClass rfl = hS.extClass := Ext.mk₀_id_comp _
  rw [e] at key2
  apply Ext.ext
  rw [Ext.neg_hom, key2]
  simp

/-- In degree `1`, the class `f s⁻¹` of a short exact sequence `0 → A → Z_0 → B → 0` is the
opposite of `CategoryTheory.ShortComplex.ShortExact.extClass`. -/
lemma yonedaClass_zero (E : YonedaExtension B A 0) (h : E.f ≫ E.g = 0)
    (hS : (ShortComplex.mk E.f E.g h).ShortExact) : yonedaClass.{w} E = -hS.extClass :=
  letI := HasDerivedCategory.standard 𝒜
  yonedaClass_zero_of E h hS (yonedaClass_hom E)

private lemma yonedaClass_succ_of [h𝒟 : HasDerivedCategory.{w'} 𝒜] {n : ℕ}
    (E : YonedaExtension B A (n + 1)) {C : 𝒜} (E' : YonedaExtension B C n) (p : E.Z.left ⟶ C)
    (h : E.f ≫ p = 0) (hS : (ShortComplex.mk E.f p h).ShortExact) (φ : E.Z.δ₀ ≅ E'.Z)
    (w₁ : E.Z.map' 0 1 ≫ app' φ.hom 0 = p ≫ E'.f) (w₂ : app' φ.hom n ≫ E'.g = E.g)
    (hyc : (yonedaClass.{w} E).hom = inv (DerivedCategory.Q.map E.complexπ) ≫
      DerivedCategory.Q.map E.complexι ≫
        (DerivedCategory.Q.commShiftIso ((n + 1 + 1 : ℕ) : ℤ)).hom.app
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A))
    (hyc' : (yonedaClass.{w} E').hom = inv (DerivedCategory.Q.map E'.complexπ) ≫
      DerivedCategory.Q.map E'.complexι ≫
        (DerivedCategory.Q.commShiftIso ((n + 1 : ℕ) : ℤ)).hom.app
          ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj C)) :
    yonedaClass.{w} E =
      (-(((n + 1 : ℕ) : ℤ).negOnePow)) • (yonedaClass.{w} E').comp hS.extClass rfl := by
  have := isIso_Q_map_descShortComplex E p h hS
  have key := roof_comp (n + 1) (A₀ := (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj A)
    (mappingCone.descShortComplex (coneSES E p h)) (coneMor₃ E p h) hS.extClass.hom
    (Q_map_descShortComplex_comp_extClass_hom E p h hS) E.complexπ E'.complexπ
    (cutComplexHom E E' p h φ w₁) (cutComplexHom_comp_complexπ E E' p h φ w₁ w₂) E.complexι
    E'.complexι (coneπ E p h)
    ((coneπ_desc E p h).trans (cutComplexHom_comp_complexι E E' p h φ w₁).symm) _
    (coneπ_mor₃ E p h)
  have key2 : ((yonedaClass.{w} E').comp hS.extClass rfl).hom =
      (-(((n + 1 : ℕ) : ℤ).negOnePow)) • (yonedaClass.{w} E).hom := by
    rw [Ext.comp_hom, hyc', hyc]
    exact key
  apply Ext.ext
  rw [units_smul_ext_hom, key2, smul_smul, Int.units_mul_self, one_smul]

/-- For a Yoneda extension of degree `n + 2` cut into a short exact sequence
`0 → A → Z_{n + 1} → C → 0` and a degree `n + 1` extension `E'` of `B` by `C`, the class
`f s⁻¹` is `(-1)^n` times the composite of the two classes. -/
lemma yonedaClass_succ {n : ℕ} (E : YonedaExtension B A (n + 1)) {C : 𝒜}
    (E' : YonedaExtension B C n) (p : E.Z.left ⟶ C) (h : E.f ≫ p = 0)
    (hS : (ShortComplex.mk E.f p h).ShortExact) (φ : E.Z.δ₀ ≅ E'.Z)
    (w₁ : E.Z.map' 0 1 ≫ app' φ.hom 0 = p ≫ E'.f) (w₂ : app' φ.hom n ≫ E'.g = E.g) :
    yonedaClass.{w} E =
      (-(((n + 1 : ℕ) : ℤ).negOnePow)) • (yonedaClass.{w} E').comp hS.extClass rfl :=
  letI := HasDerivedCategory.standard 𝒜
  yonedaClass_succ_of E E' p h hS φ w₁ w₂ (yonedaClass_hom E) (yonedaClass_hom E')

/-- **The class `f s⁻¹` is the class map up to sign**: for a degree `n + 1` Yoneda extension `E`,
`δ(E) = f s⁻¹` is `(-1)^{(n + 1)(n + 2)/2}` times `CategoryTheory.Abelian.extClassMap n E`. -/
theorem yonedaClass_eq_units_smul_extClassMap {n : ℕ} (E : YonedaExtension B A n) :
    yonedaClass.{w} E = ((((n + 2).choose 2 : ℕ) : ℤ).negOnePow) • extClassMap.{w} n E := by
  induction n generalizing A with
  | zero =>
    have h := comp_g_eq_zero E
    have hS : (ShortComplex.mk E.f E.g h).ShortExact :=
      { exact := (ShortComplex.exact_iff_exact_toComposableArrows _).2 E.exact_g }
    have e0 : extClassMap.{w} 0 E = hS.extClass := isExtClassMap_extClassMap.1 B A E h hS
    rw [yonedaClass_zero E h hS, e0]
    simp
  | succ n ih =>
    obtain ⟨C, E', p, h, hS, φ, w₁, w₂⟩ := exists_cut E
    rw [yonedaClass_succ E E' p h hS φ w₁ w₂, ih E', extClassMap_succ_of_cut E E' p h hS φ w₁ w₂,
      units_smul_ext_comp, smul_smul]
    congr 1
    have hc : (n + 1 + 2).choose 2 = (n + 2) + (n + 2).choose 2 := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.choose_succ_succ, Nat.choose_one_right]
    rw [hc]
    push_cast
    simp only [Int.negOnePow_add, Int.negOnePow_one, Int.negOnePow_even 2 even_two]
    simp

/-- **Every element of `Ext^{n + 1}` is the class `f s⁻¹` of a Yoneda extension.** -/
@[stacks 06XU "every element of `Ext^i_𝒜(B, A)`, `i ≥ 1`, is the class `δ(E) = f s⁻¹` of a \
degree `i` Yoneda extension of `B` by `A`; through `yonedaClass_eq_units_smul_extClassMap` from \
`surjective_extClassMap`"]
theorem surjective_yonedaClass (B A : 𝒜) (n : ℕ) :
    Function.Surjective (fun E : YonedaExtension B A n => yonedaClass.{w} E) := by
  intro ξ
  obtain ⟨E, hE⟩ := surjective_extClassMap B A n ((((n + 2).choose 2 : ℕ) : ℤ).negOnePow • ξ)
  refine ⟨E, ?_⟩
  dsimp only at hE ⊢
  rw [yonedaClass_eq_units_smul_extClassMap, hE, smul_smul, Int.units_mul_self, one_smul]

/-- **Two Yoneda extensions of the same degree are equivalent if and only if they have the same
class `f s⁻¹`.** -/
@[stacks 06XU "two Yoneda extensions of the same degree are equivalent if and only if their \
classes `δ(E) = f s⁻¹` agree; through `yonedaClass_eq_units_smul_extClassMap` from \
`extClassMap_eq_of_equivalent` and `equivalent_of_extClassMap_eq`"]
theorem equivalent_iff_yonedaClass_eq {n : ℕ} (E E' : YonedaExtension B A n) :
    E.Equivalent E' ↔ yonedaClass.{w} E = yonedaClass.{w} E' := by
  rw [yonedaClass_eq_units_smul_extClassMap, yonedaClass_eq_units_smul_extClassMap,
    smul_left_cancel_iff]
  exact ⟨extClassMap_eq_of_equivalent, equivalent_of_extClassMap_eq E E'⟩

end YonedaClass

end YonedaExtension

end Abelian

end CategoryTheory
