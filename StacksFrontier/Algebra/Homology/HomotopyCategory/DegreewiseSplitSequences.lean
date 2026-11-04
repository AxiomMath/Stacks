module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.Algebra.Homology.DoubleMappingCone
public import StacksFrontier.Algebra.Homology.HomotopyCategory.PlusTriangleOfDegreewiseSplit
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.StupidTruncationSupplement

/-!
# Two degreewise split short exact sequences of cochain complexes

A short exact sequence of cochain complexes `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` which is split in every degree
gives a distinguished triangle of the homotopy category
(`CochainComplex.trianglehPlusOfDegreewiseSplit`), and a morphism of such sequences which is
compatible with given splittings gives a morphism of triangles. This file provides the two
sequences used in dévissage arguments along stupid truncations, together with their splittings,
and a criterion for the compatibility of a morphism with splittings.

* For a cochain complex `K` and an integer `p`, the sequence
  `0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ) ⟶ 0` of
  `StacksDraft.StupidTruncation.stupidTruncGEShortComplex` is split in every degree: in degree `p`
  its first term vanishes, in every other degree its last term does.
* For an object `X` and degrees `i₀`, `i₁ = i₀ + 1`, the sequence
  `0 ⟶ (single i₁).obj X ⟶ double (𝟙 X) ⟶ (single i₀).obj X ⟶ 0`, whose middle term is the
  two-term complex `X --𝟙--> X` in degrees `i₀` and `i₁`, is split in every degree, and its
  middle term is contractible. Its connecting morphism therefore identifies `X[-i₀]` with
  `X[-i₁][1]` in the homotopy and derived categories.

A morphism `ψ` from the image under an additive functor `F` of a split short complex `S` to a
split short complex `S'` commutes with the sections and with the retractions of the two
splittings as soon as `S.X₃` or `S'.X₁` is zero
(`CategoryTheory.ShortComplex.Splitting.map_s_comp_of_isZero` and
`CategoryTheory.ShortComplex.Splitting.map_r_comp_of_isZero`). In both sequences above, in every
degree either the last term or the first term vanishes, so every morphism between such sequences
is compatible with the splittings.

## Main definitions

* `StacksDraft.StupidTruncation.stupidTruncGEShortComplexSplitting`: the splitting of the stupid
  truncation sequence in each degree.
* `CochainComplex.doubleShortComplex`, `CochainComplex.doubleShortComplexSplitting`,
  `CochainComplex.doubleShortComplexMap`: the sequence `single i₁ ⟶ double 𝟙 ⟶ single i₀`, its
  splittings in each degree and its functoriality.

## Main results

* `CochainComplex.isZero_plusHomotopyObj_double_id`: the complex `double (𝟙 X)` is zero in the
  bounded below homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

/-! ### Compatibility of a morphism with splittings -/

namespace CategoryTheory.ShortComplex.Splitting

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] {S : ShortComplex C} {S' : ShortComplex D} (σ : S.Splitting)
  (σ' : S'.Splitting) {τ₁ : F.obj S.X₁ ⟶ S'.X₁} {τ₂ : F.obj S.X₂ ⟶ S'.X₂}
  {τ₃ : F.obj S.X₃ ⟶ S'.X₃}

/-- **A morphism of split short complexes commutes with the sections** when the last term of the
source or the first term of the target vanishes. -/
theorem map_s_comp_of_isZero (h₂₃ : F.map S.g ≫ τ₃ = τ₂ ≫ S'.g)
    (h : IsZero S.X₃ ∨ IsZero S'.X₁) : F.map σ.s ≫ τ₂ = τ₃ ≫ σ'.s := by
  rcases h with h | h
  · exact (F.map_isZero h).eq_of_src _ _
  · have e : S'.g ≫ σ'.s = 𝟙 _ := by
      have := σ'.id
      rwa [h.eq_of_tgt σ'.r 0, zero_comp, zero_add] at this
    calc F.map σ.s ≫ τ₂ = F.map σ.s ≫ τ₂ ≫ S'.g ≫ σ'.s := by rw [e, comp_id]
      _ = F.map σ.s ≫ F.map S.g ≫ τ₃ ≫ σ'.s := by rw [reassoc_of% h₂₃]
      _ = τ₃ ≫ σ'.s := by rw [← F.map_comp_assoc, σ.s_g, F.map_id, id_comp]

omit [F.Additive] in
/-- **A morphism of split short complexes commutes with the retractions** when the last term of
the source or the first term of the target vanishes. -/
theorem map_r_comp_of_isZero (h₁₂ : F.map S.f ≫ τ₂ = τ₁ ≫ S'.f)
    (h : IsZero S.X₃ ∨ IsZero S'.X₁) : F.map σ.r ≫ τ₁ = τ₂ ≫ σ'.r := by
  rcases h with h | h
  · have e : σ.r ≫ S.f = 𝟙 _ := by
      have := σ.id
      rwa [h.eq_of_src σ.s 0, comp_zero, add_zero] at this
    calc F.map σ.r ≫ τ₁ = F.map σ.r ≫ τ₁ ≫ S'.f ≫ σ'.r := by rw [σ'.f_r, comp_id]
      _ = F.map σ.r ≫ F.map S.f ≫ τ₂ ≫ σ'.r := by rw [reassoc_of% h₁₂]
      _ = τ₂ ≫ σ'.r := by rw [← F.map_comp_assoc, e, F.map_id, id_comp]
  · exact h.eq_of_tgt _ _

end CategoryTheory.ShortComplex.Splitting

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (F : C ⥤ D)
  [F.Additive] {S : ShortComplex (CochainComplex C ℤ)} {S' : ShortComplex (CochainComplex D ℤ)}
  (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
  (σ' : ∀ n, (S'.map (HomologicalComplex.eval D (ComplexShape.up ℤ) n)).Splitting)
  (ψ : S.map (F.mapHomologicalComplex _) ⟶ S')

include σ σ' in
/-- **A morphism of degreewise split sequences of complexes commutes with the sections** in every
degree in which the last term of the source or the first term of the target vanishes. -/
theorem splitting_map_s_comp_of_isZero (n : ℤ) (h : IsZero (S.X₃.X n) ∨ IsZero (S'.X₁.X n)) :
    F.map (σ n).s ≫ ψ.τ₂.f n = ψ.τ₃.f n ≫ (σ' n).s :=
  ShortComplex.Splitting.map_s_comp_of_isZero F (σ n) (σ' n)
    ((congrArg (fun φ => φ.f n) ψ.comm₂₃).symm) h

include σ σ' in
/-- **A morphism of degreewise split sequences of complexes commutes with the retractions** in
every degree in which the last term of the source or the first term of the target vanishes. -/
theorem splitting_map_r_comp_of_isZero (n : ℤ) (h : IsZero (S.X₃.X n) ∨ IsZero (S'.X₁.X n)) :
    F.map (σ n).r ≫ ψ.τ₁.f n = ψ.τ₂.f n ≫ (σ' n).r :=
  ShortComplex.Splitting.map_r_comp_of_isZero F (σ n) (σ' n)
    ((congrArg (fun φ => φ.f n) ψ.comm₁₂).symm) h

end CochainComplex


/-! ### The stupid truncation sequence is split in every degree -/

namespace StacksDraft.StupidTruncation

open HomologicalComplex

section StupidTrunc

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- **The splitting of the stupid truncation sequence in degree `m`**: in degree `p` the first
term of `0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ) ⟶ 0` vanishes and the projection is an
isomorphism; in every other degree the last term vanishes and the inclusion is an
isomorphism. -/
def stupidTruncGEShortComplexSplitting (p m : ℤ) :
    ((stupidTruncGEShortComplex K p).map (eval C (ComplexShape.up ℤ) m)).Splitting :=
  if hm : m = p then
    ShortComplex.Splitting.ofIsZeroOfIsIso _
      (by
        subst hm
        exact CochainComplex.isZero_of_isStrictlyGE
          (K.stupidTrunc (ComplexShape.embeddingUpIntGE (m + 1))) (m + 1) m (by omega))
      (by
        subst hm
        change IsIso ((stupidTruncGEπ K m).f m)
        rw [stupidTruncGEπ_f]
        infer_instance)
  else
    ShortComplex.Splitting.ofIsIsoOfIsZero _
      (by
        change IsIso ((stupidTruncGEMapLE K (show p ≤ p + 1 by omega)).f m)
        by_cases hpm : p < m
        · rw [stupidTruncGEMapLE_f K _ m (by omega)]
          infer_instance
        · exact IsZero.isIso
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (ComplexShape.embeddingUpIntGE (p + 1))) (p + 1) m (by omega))
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)) p m (by omega)) _)
      (isZero_single_obj_X (ComplexShape.up ℤ) p (K.X p) m hm)

variable {K} in
/-- In every degree, the last term of the stupid truncation sequence of `K` or the first term of
the one of `L` vanishes. -/
lemma isZero_stupidTruncGEShortComplex_X₃_or_X₁ {D : Type*} [Category* D] [Abelian D]
    (L : CochainComplex D ℤ) (p m : ℤ) :
    IsZero ((stupidTruncGEShortComplex K p).X₃.X m) ∨
      IsZero ((stupidTruncGEShortComplex L p).X₁.X m) := by
  by_cases hm : m ≤ p
  · exact Or.inr (CochainComplex.isZero_of_isStrictlyGE
      (L.stupidTrunc (ComplexShape.embeddingUpIntGE (p + 1))) (p + 1) m (by omega))
  · exact Or.inl (isZero_single_obj_X (ComplexShape.up ℤ) p (K.X p) m (by omega))

/-- A stupid truncation of a complex vanishing in degrees `< a` vanishes in degrees `< a`. -/
lemma isStrictlyGE_stupidTruncGE (a p : ℤ) [K.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  by_cases hpn : p ≤ n
  · exact (CochainComplex.isZero_of_isStrictlyGE K a n hn).of_iso (stupidTruncGEXIso K p n hpn)
  · exact CochainComplex.isZero_of_isStrictlyGE _ p n (by omega)

end StupidTrunc

end StacksDraft.StupidTruncation

namespace CochainComplex

open HomologicalComplex

/-! ### The sequence `single i₁ ⟶ double 𝟙 ⟶ single i₀` -/

section Double

variable {C : Type*} [Category* C] [Abelian C] (X : C) {i₀ i₁ : ℤ}
  (hi : (ComplexShape.up ℤ).Rel i₀ i₁)

include hi in
/-- Two degrees related in `ComplexShape.up ℤ`, i.e. with `i₁ = i₀ + 1`, are distinct. -/
lemma ne_of_rel_up : i₀ ≠ i₁ := by
  have h : i₀ + 1 = i₁ := hi
  omega

/-- **The sequence `0 ⟶ (single i₁).obj X ⟶ double (𝟙 X) ⟶ (single i₀).obj X ⟶ 0`**, for
`i₁ = i₀ + 1`: the inclusion of the top term of the two-term complex `X --𝟙--> X` and the
projection onto its bottom term. -/
abbrev doubleShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (mkHomFromSingle (doubleXIso₁ (𝟙 X) hi (ne_of_rel_up hi)).inv
      (fun _ _ => by rw [double_d_eq_zero₀ _ _ _ _ (ne_of_rel_up hi).symm, comp_zero]))
    (mkHomFromDouble hi (ne_of_rel_up hi) (singleObjXSelf (ComplexShape.up ℤ) i₀ X).inv 0
      (by simp) (by simp))
    (by
      apply from_single_hom_ext
      simp)

/-- In degree `i₁`, the first map of `doubleShortComplex X hi` is the composite of the
identifications of both terms with `X`. -/
@[simp]
lemma doubleShortComplex_f_f₁ :
    (doubleShortComplex X hi).f.f i₁ = (singleObjXSelf (ComplexShape.up ℤ) i₁ X).hom ≫
      (doubleXIso₁ (𝟙 X) hi (ne_of_rel_up hi)).inv := by
  simp [doubleShortComplex]

/-- In degree `i₀`, the second map of `doubleShortComplex X hi` is the composite of the
identifications of both terms with `X`. -/
@[simp]
lemma doubleShortComplex_g_f₀ :
    (doubleShortComplex X hi).g.f i₀ = (doubleXIso₀ (𝟙 X) hi).hom ≫
      (singleObjXSelf (ComplexShape.up ℤ) i₀ X).inv := by
  simp [doubleShortComplex]

/-- **The splitting of the sequence `single i₁ ⟶ double 𝟙 ⟶ single i₀` in degree `k`**: in
degree `i₁` its last term vanishes and the inclusion is an isomorphism; in every other degree its
first term vanishes and the projection is an isomorphism. -/
def doubleShortComplexSplitting (k : ℤ) :
    ((doubleShortComplex X hi).map (eval C (ComplexShape.up ℤ) k)).Splitting :=
  if hk : k = i₁ then
    ShortComplex.Splitting.ofIsIsoOfIsZero _
      (by
        subst hk
        change IsIso ((doubleShortComplex X hi).f.f k)
        rw [doubleShortComplex_f_f₁]
        exact Iso.isIso_hom (singleObjXSelf (ComplexShape.up ℤ) k X ≪≫
          (doubleXIso₁ (𝟙 X) hi (ne_of_rel_up hi)).symm))
      (by
        subst hk
        exact isZero_single_obj_X (ComplexShape.up ℤ) i₀ X k (ne_of_rel_up hi).symm)
  else
    ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_single_obj_X (ComplexShape.up ℤ) i₁ X k hk)
      (by
        change IsIso ((doubleShortComplex X hi).g.f k)
        by_cases hk₀ : k = i₀
        · subst hk₀
          rw [doubleShortComplex_g_f₀]
          exact Iso.isIso_hom ((doubleXIso₀ (𝟙 X) hi) ≪≫
            (singleObjXSelf (ComplexShape.up ℤ) k X).symm)
        · exact IsZero.isIso (isZero_double_X (𝟙 X) hi k hk₀ hk)
            (isZero_single_obj_X (ComplexShape.up ℤ) i₀ X k hk₀) _)

variable {X} in
/-- In every degree, the last term of the sequence `single i₁ ⟶ double 𝟙 ⟶ single i₀` of `X` or
the first term of the one of `Y` vanishes. -/
lemma isZero_doubleShortComplex_X₃_or_X₁ {D : Type*} [Category* D] [Abelian D] (Y : D)
    (k : ℤ) :
    IsZero ((doubleShortComplex X hi).X₃.X k) ∨ IsZero ((doubleShortComplex Y hi).X₁.X k) := by
  by_cases hk : k = i₁
  · subst hk
    exact Or.inl (isZero_single_obj_X _ _ _ _ (ne_of_rel_up hi).symm)
  · exact Or.inr (isZero_single_obj_X _ _ _ _ hk)

/-- The two-term complex `double (𝟙 X)` in degrees `i₀`, `i₁` vanishes in degrees `< a` for
`a ≤ i₀`. -/
lemma isStrictlyGE_double (a : ℤ) (ha : a ≤ i₀) :
    CochainComplex.IsStrictlyGE (double (𝟙 X) hi) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have h : i₀ + 1 = i₁ := hi
  exact isZero_double_X _ _ _ (by omega) (by omega)

/-- **The two-term complex `X --𝟙--> X` is contractible**: it is zero in the homotopy
category. -/
lemma isZero_quotient_obj_double_id :
    IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (double (𝟙 X) hi)) := by
  have h : IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (mappingCone ((single C (ComplexShape.up ℤ) i₁).map (𝟙 X)))) := by
    rw [CategoryTheory.Functor.map_id]
    exact (HomotopyCategory.isZero_quotient_obj_iff _).2 ⟨mappingCone.homotopyToZeroOfId _⟩
  exact h.of_iso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
    (doubleIsoMappingCone (𝟙 X) hi))

/-- **The two-term complex `X --𝟙--> X` is zero in the bounded below homotopy category.** -/
lemma isZero_plusHomotopyObj_double_id (a : ℤ)
    [CochainComplex.IsStrictlyGE (double (𝟙 X) hi) a] :
    IsZero (plusHomotopyObj a (double (𝟙 X) hi)) := by
  have h := isZero_quotient_obj_double_id X hi
  refine (IsZero.iff_id_eq_zero _).2 ((HomotopyCategory.Plus.ι C).map_injective ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

variable {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] {X} {Y : D}
  (φ : F.obj X ⟶ Y)

/-- The map `F(double (𝟙 X)) ⟶ double (𝟙 Y)` induced by a map `φ : F X ⟶ Y`: through the
identification `HomologicalComplex.doubleMapFunctorIso` of `F(double (𝟙 X))` with
`double (F.map (𝟙 X))`, it is `φ` in both degrees. -/
def doubleIdMap :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (double (𝟙 X) hi) ⟶ double (𝟙 Y) hi :=
  (doubleMapFunctorIso F (𝟙 X) hi (ne_of_rel_up hi)).inv ≫
    mkHomFromDouble hi (ne_of_rel_up hi) (φ ≫ (doubleXIso₀ (𝟙 Y) hi).inv)
      (φ ≫ (doubleXIso₁ (𝟙 Y) hi (ne_of_rel_up hi)).inv)
      (by simp [double_d _ hi (ne_of_rel_up hi)])
      (fun k _ => by rw [double_d_eq_zero₀ _ hi _ _ (ne_of_rel_up hi).symm, comp_zero])

/-- In degree `i₀`, the inverse of `doubleMapFunctorIso F (𝟙 X)` is `F` applied to the
identification of `(double (𝟙 X)).X i₀` with `X`, followed by the identification of `F X` with
`(double (F.map (𝟙 X))).X i₀`. -/
lemma doubleMapFunctorIso_inv_f₀ :
    (doubleMapFunctorIso F (𝟙 X) hi (ne_of_rel_up hi)).inv.f i₀ =
      F.map (doubleXIso₀ (𝟙 X) hi).hom ≫ (doubleXIso₀ (F.map (𝟙 X)) hi).inv := by
  rw [← cancel_epi ((doubleMapFunctorIso F (𝟙 X) hi (ne_of_rel_up hi)).hom.f i₀),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  simp [doubleMapFunctorIso, doubleMapFunctorHom]

/-- In degree `i₁`, the inverse of `doubleMapFunctorIso F (𝟙 X)` is `F` applied to the
identification of `(double (𝟙 X)).X i₁` with `X`, followed by the identification of `F X` with
`(double (F.map (𝟙 X))).X i₁`. -/
lemma doubleMapFunctorIso_inv_f₁ :
    (doubleMapFunctorIso F (𝟙 X) hi (ne_of_rel_up hi)).inv.f i₁ =
      F.map (doubleXIso₁ (𝟙 X) hi (ne_of_rel_up hi)).hom ≫
        (doubleXIso₁ (F.map (𝟙 X)) hi (ne_of_rel_up hi)).inv := by
  rw [← cancel_epi ((doubleMapFunctorIso F (𝟙 X) hi (ne_of_rel_up hi)).hom.f i₁),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  simp [doubleMapFunctorIso, doubleMapFunctorHom]

/-- In degree `i₀`, `doubleIdMap hi F φ` is `φ` up to the identifications of both terms with
`F X` and `Y`. -/
@[simp]
lemma doubleIdMap_f₀ : (doubleIdMap hi F φ).f i₀ =
    (F.map (doubleXIso₀ (𝟙 X) hi).hom ≫ φ) ≫ (doubleXIso₀ (𝟙 Y) hi).inv := by
  rw [doubleIdMap, HomologicalComplex.comp_f, doubleMapFunctorIso_inv_f₀, mkHomFromDouble_f₀]
  simp

/-- In degree `i₁`, `doubleIdMap hi F φ` is `φ` up to the identifications of both terms with
`F X` and `Y`. -/
@[simp]
lemma doubleIdMap_f₁ : (doubleIdMap hi F φ).f i₁ =
    (F.map (doubleXIso₁ (𝟙 X) hi (ne_of_rel_up hi)).hom ≫ φ) ≫
      (doubleXIso₁ (𝟙 Y) hi (ne_of_rel_up hi)).inv := by
  rw [doubleIdMap, HomologicalComplex.comp_f, doubleMapFunctorIso_inv_f₁, mkHomFromDouble_f₁]
  simp

/-- **The functoriality of the sequence `single i₁ ⟶ double 𝟙 ⟶ single i₀`**: the morphism from
the image under `F` of the sequence of `X` to the sequence of `Y` induced by `φ : F X ⟶ Y`. -/
def doubleShortComplexMap :
    (doubleShortComplex X hi).map (F.mapHomologicalComplex _) ⟶ doubleShortComplex Y hi where
  τ₁ := (F.mapCochainComplexSingleFunctor i₁).hom.app X ≫
    (single D (ComplexShape.up ℤ) i₁).map φ
  τ₂ := doubleIdMap hi F φ
  τ₃ := (F.mapCochainComplexSingleFunctor i₀).hom.app X ≫
    (single D (ComplexShape.up ℤ) i₀).map φ
  comm₁₂ := by
    refine to_double_hom_ext (hi₀₁ := hi) ?_ ?_
    · exact (F.map_isZero (isZero_single_obj_X _ _ _ _ (ne_of_rel_up hi))).eq_of_src _ _
    · simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Functor.mapCochainComplexSingleFunctor, singleMapHomologicalComplex_hom_app_self,
        single_map_f_self, mkHomFromSingle_f, doubleIdMap_f₁,
        Functor.map_comp, assoc,
        Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  comm₂₃ := by
    apply to_single_hom_ext
    simp only [ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapCochainComplexSingleFunctor, singleMapHomologicalComplex_hom_app_self,
      single_map_f_self, mkHomFromDouble_f₀, doubleIdMap_f₀,
      Functor.map_comp, assoc,
      Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]

/-- The middle component of `doubleShortComplexMap hi F φ` is `doubleIdMap hi F φ`. -/
@[simp]
lemma doubleShortComplexMap_τ₂ : (doubleShortComplexMap hi F φ).τ₂ = doubleIdMap hi F φ := rfl

end Double

end CochainComplex
