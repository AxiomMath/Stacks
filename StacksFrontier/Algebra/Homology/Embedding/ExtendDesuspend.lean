module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendUpNatIso
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap

/-!
# The translate by `-1` of an `ℕ`-indexed cochain complex

A cochain complex `K` indexed by `ℕ` has no translation functor, `ℕ` carrying no shift. Its
translate by `-1`, `K[-1]` in the sign convention of Stacks Tag 011G, is still an `ℕ`-indexed
complex: it is `0` in degree `0` and `K^p` in degree `p + 1`, with differential `-d`. It is
functorial in `K`, and its extension by zero to `ℤ` is the translate by `-1` of the extension of
`K`, compatibly with additive functors.

## Main definitions

* `CochainComplex.desuspend`: `K[-1]` over `ℕ`.
* `CochainComplex.desuspendMap`: its functoriality.
* `CochainComplex.desuspendExtendIso`: `(K[-1]).extend ≅ (K.extend)⟦-1⟧`.
* `CochainComplex.desuspendLift`: the translate `ν[-1] : L[-1] ⟶ F(K[-1])` of a morphism
  `ν : L ⟶ F(K)`, for an additive functor `F`.

## Main results

* `CochainComplex.desuspendExtendIso_naturality`: the identification is natural in `K`.
* `CochainComplex.desuspendLift_extend`: translating by `-1` commutes with applying an additive
  functor, compatibly with the extensions to `ℤ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The terms of `K[-1]`: `0` in degree `0` and `K^p` in degree `p + 1`. -/
def desuspendX (K : CochainComplex C ℕ) : ℕ → C
  | 0 => 0
  | p + 1 => K.X p

/-- The differential of `K[-1]`: `-d`, the sign of the translation of Stacks Tag 011G. -/
def desuspendD (K : CochainComplex C ℕ) : ∀ n : ℕ, desuspendX K n ⟶ desuspendX K (n + 1)
  | 0 => 0
  | p + 1 => -K.d p (p + 1)

/-- The differential of `K[-1]` squares to zero. -/
theorem desuspendD_comp (K : CochainComplex C ℕ) (n : ℕ) :
    desuspendD K n ≫ desuspendD K (n + 1) = 0 := by
  cases n with
  | zero => exact zero_comp
  | succ p =>
    change (-K.d p (p + 1)) ≫ (-K.d (p + 1) (p + 1 + 1)) = 0
    rw [Preadditive.neg_comp_neg]
    exact K.d_comp_d _ _ _

/-- **The translate `K[-1]` of an `ℕ`-indexed cochain complex**: `K^{n-1}` in degree `n ≥ 1`,
`0` in degree `0`, with the differential negated. -/
def desuspend (K : CochainComplex C ℕ) : CochainComplex C ℕ :=
  CochainComplex.of (desuspendX K) (desuspendD K) (desuspendD_comp K)

/-- The differential of `K[-1]` from degree `n` to degree `n + 1` is `desuspendD K n`. -/
theorem desuspend_d (K : CochainComplex C ℕ) (n : ℕ) :
    (desuspend K).d n (n + 1) = desuspendD K n :=
  CochainComplex.of_d (desuspendX K) (desuspendD K) n

/-- The term of `K[-1]` in degree `p + 1` is `K^p`. -/
theorem desuspend_X_succ (K : CochainComplex C ℕ) (p : ℕ) : (desuspend K).X (p + 1) = K.X p :=
  rfl

/-- The components of `φ[-1]`: `0` in degree `0`, `φ^p` in degree `p + 1`. -/
def desuspendMapF {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    ∀ n : ℕ, (desuspend K).X n ⟶ (desuspend L).X n
  | 0 => 0
  | p + 1 => φ.f p

/-- **The translate `φ[-1]` of a map of `ℕ`-indexed cochain complexes.** -/
def desuspendMap {K L : CochainComplex C ℕ} (φ : K ⟶ L) : desuspend K ⟶ desuspend L :=
  CochainComplex.ofHom (desuspendMapF φ) fun n => by
    rw [desuspend_d, desuspend_d]
    cases n with
    | zero =>
      simp only [desuspendMapF, desuspendD]
      exact (zero_comp).trans (zero_comp).symm
    | succ p =>
      change φ.f p ≫ (-L.d p (p + 1)) = (-K.d p (p + 1)) ≫ φ.f (p + 1)
      rw [Preadditive.comp_neg, Preadditive.neg_comp, φ.comm]

/-- The component of `φ[-1]` in degree `p + 1` is `φ^p`. -/
theorem desuspendMap_f_succ {K L : CochainComplex C ℕ} (φ : K ⟶ L) (p : ℕ) :
    (desuspendMap φ).f (p + 1) = φ.f p :=
  rfl

/-- The component of `φ[-1]` in degree `0` is zero. -/
theorem desuspendMap_f_zero {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (desuspendMap φ).f 0 = 0 :=
  rfl

omit [HasZeroObject C] in
private theorem iso_inv_comp_neg_one_smul {A B D : C} (e : A ≅ B) (g : B ⟶ D) :
    e.inv ≫ ((-1 : ℤˣ) • (e.hom ≫ g)) = -g := by
  simp [Units.smul_def]

omit [Preadditive C] [HasZeroObject C] in
private theorem comp_iso_cancel {P Q R T A B : C} (x : P ⟶ Q) (a : A ≅ Q) (g : Q ⟶ R)
    (b : B ≅ R) (c : R ⟶ T) :
    x ≫ (g ≫ b.inv) ≫ b.hom ≫ c = (x ≫ a.inv) ≫ a.hom ≫ g ≫ c := by
  simp

/-- Index `k` of `K` sits in degree `k + 1 + -1` of the extension by zero to `ℤ`. -/
private theorem embeddingUpNat_f_eq_add_neg_one (k : ℕ) :
    ComplexShape.embeddingUpNat.f k = ((k + 1 : ℕ) : ℤ) + -1 := by
  simp only [ComplexShape.embeddingUpNat_f]; lia

/-- The degreewise comparison of `K[-1]`, extended by zero, with `(K.extend)⟦-1⟧`. -/
def desuspendXIso (K : CochainComplex C ℕ) : ∀ (n : ℕ) (p : ℤ), (n : ℤ) = p →
    ((desuspend K).X n ≅ ((K.extend ComplexShape.embeddingUpNat)⟦(-1 : ℤ)⟧).X p)
  | 0, p, hp => (isZero_zero _).iso
      (HomologicalComplex.isZero_extend_X_of_neg _ (by simp only; lia))
  | k + 1, p, hp => (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f k = p + -1 by
        simp only [ComplexShape.embeddingUpNat_f]; lia)).symm

/-- **`K[-1]`, built over `ℕ` and extended by zero, is the translate by `-1` of the extension of
`K` by zero.** -/
def desuspendExtendIso (K : CochainComplex C ℕ) :
    (desuspend K).extend ComplexShape.embeddingUpNat ≅
      (K.extend ComplexShape.embeddingUpNat)⟦(-1 : ℤ)⟧ :=
  HomologicalComplex.extendUpNatIso _ _
    (fun p hp => HomologicalComplex.isZero_extend_X_of_neg _ (by simp only; lia))
    (desuspendXIso K) fun n p q hp hq => by
      cases n with
      | zero => exact (isZero_zero _).eq_of_src _ _
      | succ k =>
        subst hp hq
        have h1 : ComplexShape.embeddingUpNat.f k = ((k + 1 : ℕ) : ℤ) + -1 := by
          simp only [ComplexShape.embeddingUpNat_f]; lia
        have h2 : ComplexShape.embeddingUpNat.f (k + 1) = ((k + 1 + 1 : ℕ) : ℤ) + -1 := by
          simp only [ComplexShape.embeddingUpNat_f]; lia
        rw [desuspend_d, CochainComplex.shiftFunctor_obj_d',
          HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat h1 h2]
        change (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat h1).inv ≫ _ =
          (-K.d k (k + 1)) ≫ (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat h2).inv
        rw [Int.negOnePow_neg, Int.negOnePow_one]
        exact (iso_inv_comp_neg_one_smul _ _).trans (Preadditive.neg_comp _ _).symm

/-- **The identification `(K[-1]).extend ≅ (K.extend)⟦-1⟧` is natural in `K`.** -/
theorem desuspendExtendIso_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    HomologicalComplex.extendMap (desuspendMap φ) ComplexShape.embeddingUpNat ≫
        (desuspendExtendIso L).hom =
      (desuspendExtendIso K).hom ≫
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)⟦(-1 : ℤ)⟧' := by
  ext p
  by_cases hp : 0 ≤ p
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg hp⟩
    cases n with
    | zero =>
      exact (HomologicalComplex.isZero_extend_X_of_neg _ (by simp only; lia)).eq_of_tgt _ _
    | succ k =>
      have h1 := embeddingUpNat_f_eq_add_neg_one k
      simp only [HomologicalComplex.comp_f, desuspendExtendIso,
        HomologicalComplex.extendUpNatIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
        HomologicalComplex.extendUpNatXIso_natCast, Iso.trans_hom,
        CochainComplex.shiftFunctor_map_f']
      rw [HomologicalComplex.extendMap_f (desuspendMap φ) ComplexShape.embeddingUpNat
          (i := k + 1) (i' := ((k + 1 : ℕ) : ℤ)) rfl,
        HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat h1]
      simp only [desuspendXIso, desuspendMap_f_succ, Iso.symm_hom, Category.assoc]
      exact comp_iso_cancel _ _ _ _ _
  · exact (HomologicalComplex.isZero_extend_X_of_neg _ (not_le.mp hp)).eq_of_src _ _

/-! ### Translating by `-1` and applying an additive functor -/

section Functor

variable {C₂ : Type*} [Category* C₂] [Preadditive C₂] [HasZeroObject C₂] (F : C ⥤ C₂)
  [F.Additive]

/-- The components of the translate by `-1` of a morphism `ν : L ⟶ F(K)` into the image of a
complex under an additive functor, read as a morphism `L[-1] ⟶ F(K[-1])`. -/
def desuspendLiftF {L : CochainComplex C₂ ℕ} {K : CochainComplex C ℕ}
    (ν : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :
    ∀ n : ℕ, (desuspend L).X n ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (desuspend K)).X n
  | 0 => 0
  | p + 1 => ν.f p

/-- **The translate `ν[-1] : L[-1] ⟶ F(K[-1])`** of a morphism `ν : L ⟶ F(K)`. -/
def desuspendLift {L : CochainComplex C₂ ℕ} {K : CochainComplex C ℕ}
    (ν : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :
    desuspend L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (desuspend K) :=
  CochainComplex.ofHom (desuspendLiftF F ν) fun n => by
    change desuspendLiftF F ν n ≫ F.map ((desuspend K).d n (n + 1)) =
      (desuspend L).d n (n + 1) ≫ desuspendLiftF F ν (n + 1)
    rw [desuspend_d, desuspend_d]
    cases n with
    | zero =>
      simp only [desuspendLiftF, desuspendD]
      exact (zero_comp).trans (zero_comp).symm
    | succ p =>
      change ν.f p ≫ F.map (-K.d p (p + 1)) = (-L.d p (p + 1)) ≫ ν.f (p + 1)
      rw [F.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (ν.comm p (p + 1))

/-- The component of `ν[-1]` in degree `p + 1` is `ν^p`. -/
theorem desuspendLift_f_succ {L : CochainComplex C₂ ℕ} {K : CochainComplex C ℕ}
    (ν : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (p : ℕ) :
    (desuspendLift F ν).f (p + 1) = ν.f p :=
  rfl

omit [Preadditive C] [HasZeroObject C] [Preadditive C₂] [HasZeroObject C₂] [F.Additive] in
private theorem desuspendLift_extend_aux {P Q Q' R' : C₂} {U V' W' : C} (a : P ⟶ Q)
    (e : Q' ≅ Q) (n : Q ⟶ F.obj U) (b : R' ≅ F.obj U) (c : V' ≅ U) (d : U ⟶ W') :
    a ≫ (n ≫ b.inv) ≫ b.hom ≫ F.map c.inv ≫ F.map (c.hom ≫ d) ≫ 𝟙 (F.obj W') =
      (a ≫ e.inv) ≫ e.hom ≫ n ≫ F.map d := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
  rw [← F.map_comp, Iso.inv_hom_id_assoc]

/-- **Translating by `-1` commutes with applying an additive functor**, compatibly with the
identifications of `HomologicalComplex.mapHomologicalComplexExtendIso` and
`CochainComplex.desuspendExtendIso`. -/
theorem desuspendLift_extend {L : CochainComplex C₂ ℕ} {K : CochainComplex C ℕ}
    (ν : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :
    HomologicalComplex.extendMap (desuspendLift F ν) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso F (desuspend K)
          ComplexShape.embeddingUpNat).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (desuspendExtendIso K).hom ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).hom.app
          (K.extend ComplexShape.embeddingUpNat) =
      (desuspendExtendIso L).hom ≫
        (HomologicalComplex.extendMap ν ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.mapHomologicalComplexExtendIso F K
            ComplexShape.embeddingUpNat).hom)⟦(-1 : ℤ)⟧' := by
  ext q
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg hq⟩
    cases n with
    | zero =>
      refine IsZero.eq_of_src ?_ _ _
      exact IsZero.of_iso (isZero_zero _)
        ((desuspend L).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl)
    | succ k =>
      have h1 := embeddingUpNat_f_eq_add_neg_one k
      have h0 : ComplexShape.embeddingUpNat.f (k + 1) = ((k + 1 : ℕ) : ℤ) := rfl
      simp only [HomologicalComplex.comp_f, desuspendExtendIso,
        HomologicalComplex.extendUpNatIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
        HomologicalComplex.extendUpNatXIso_natCast, Iso.trans_hom,
        CochainComplex.shiftFunctor_map_f', Functor.mapHomologicalComplex_map_f,
        Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
      rw [HomologicalComplex.extendMap_f (desuspendLift F ν) ComplexShape.embeddingUpNat
          (i := k + 1) (i' := ((k + 1 : ℕ) : ℤ)) h0,
        HomologicalComplex.extendMap_f ν ComplexShape.embeddingUpNat h1,
        HomologicalComplex.mapHomologicalComplexExtendIso_hom_f F (desuspend K)
          ComplexShape.embeddingUpNat (i := k + 1) (i' := ((k + 1 : ℕ) : ℤ)) h0,
        HomologicalComplex.mapHomologicalComplexExtendIso_hom_f F K ComplexShape.embeddingUpNat h1]
      simp only [desuspendXIso, desuspendLift_f_succ, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_assoc]
      exact desuspendLift_extend_aux F _ _ _ _ _ _
  · exact (HomologicalComplex.isZero_extend_X_of_neg _ (not_le.mp hq)).eq_of_src _ _

/-- The comparison of `HomologicalComplex.mapHomologicalComplexExtendIso` is natural in the
complex, in the direction of its `hom`. -/
theorem mapHomologicalComplexExtendIso_hom_naturality {K K' : CochainComplex C ℕ} (φ : K ⟶ K') :
    (HomologicalComplex.mapHomologicalComplexExtendIso F K ComplexShape.embeddingUpNat).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) =
      HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso F K'
          ComplexShape.embeddingUpNat).hom := by
  rw [← cancel_mono (HomologicalComplex.mapHomologicalComplexExtendIso F K'
      ComplexShape.embeddingUpNat).inv, Category.assoc,
    HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality, Iso.hom_inv_id_assoc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A square of maps of `ℕ`-indexed complexes into a translate by `-1`, read on `ℤ`**: if
`Ψ ≫ F(r) = r₁ ≫ ν[-1]`, then the same holds after extending by zero, with the translates by `-1`
of the extensions and the commutation of `F` with the translation. -/
theorem extend_comp_desuspendExtendIso {M K : CochainComplex C ℕ} {M₁ L : CochainComplex C₂ ℕ}
    (Ψ : M₁ ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M) (r : M ⟶ desuspend K)
    (r₁ : M₁ ⟶ desuspend L) (ν : L ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
    (h : Ψ ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map r = r₁ ≫ desuspendLift F ν) :
    (HomologicalComplex.extendMap Ψ ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso F M ComplexShape.embeddingUpNat).hom) ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat ≫
            (desuspendExtendIso K).hom) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1 : ℤ)).hom.app
          (K.extend ComplexShape.embeddingUpNat) =
      (HomologicalComplex.extendMap r₁ ComplexShape.embeddingUpNat ≫ (desuspendExtendIso L).hom) ≫
        (HomologicalComplex.extendMap ν ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.mapHomologicalComplexExtendIso F K
            ComplexShape.embeddingUpNat).hom)⟦(-1 : ℤ)⟧' := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc
      (HomologicalComplex.mapHomologicalComplexExtendIso F M ComplexShape.embeddingUpNat).hom,
    mapHomologicalComplexExtendIso_hom_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (HomologicalComplex.extendMap Ψ ComplexShape.embeddingUpNat),
    ← HomologicalComplex.extendMap_comp, h, HomologicalComplex.extendMap_comp]
  simp only [Category.assoc]
  rw [desuspendLift_extend]

end Functor

end CochainComplex
