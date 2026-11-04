module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Glueing an object along three restriction functors with left adjoints

Let `D_X`, `D_U`, `D_V`, `D_P` be categories, with restriction functors `r_U : D_X ⥤ D_U`,
`r_V : D_X ⥤ D_V`, `r_P : D_X ⥤ D_P`, `r_{UP} : D_U ⥤ D_P`, `r_{VP} : D_V ⥤ D_P`, identifications
`r_U ⋙ r_{UP} ≅ r_P` and `r_V ⋙ r_{VP} ≅ r_P`, and left adjoints `s_U ⊣ r_U`, `s_V ⊣ r_V`,
`s_P ⊣ r_P`.  This is the shape of an elementary distinguished square `(U ⊆ X, V ⟶ X)` with
intersection `P = U ×_X V`, the left adjoints being the extensions by zero.

Given objects `A` of `D_U`, `B` of `D_V` and an isomorphism `c : A|_P ⟶ B|_P`, this file builds,
in a pretriangulated `D_X`, a candidate glueing `F` of `A` and `B`: the third vertex of a
distinguished triangle on

`s_P(B|_P) ⟶ s_U A ⊞ s_V B`,

whose components are the canonical maps `glueMapOfRestriction` of the two factorisations of
`r_P`, the first one precomposed with `s_P(c⁻¹)`.  The transposes of the two components of the
second map of the triangle are comparisons `A ⟶ F|_U` and `B ⟶ F|_V`, and they are compatible
with `c` over `P` (`glueCandidate_compat`).  Whether they are isomorphisms is a question about
the particular categories; for the derived categories of modules on an elementary distinguished
square of algebraic spaces it is answered on stalks.

The file also records two facts about distinguished triangles whose middle vertex is a binary
biproduct, which are what such a stalk computation uses.

## Main definitions

* `CategoryTheory.glueMapOfRestriction`: the map `s_P(A|_P) ⟶ s_U A` transposed to the image of
  the unit `A ⟶ (s_U A)|_U` under `r_{UP}`, read through `r_U ⋙ r_{UP} ≅ r_P`.
* `CategoryTheory.GlueCandidate`: a distinguished triangle on the map above together with the two
  transposed comparisons.

## Main results

* `CategoryTheory.homEquiv_glueMapOfRestriction_comp`: the transpose of a composite with
  `glueMapOfRestriction` is the restriction to `P` of the transpose.
* `CategoryTheory.GlueCandidate.compat`: the two comparisons agree over `P` up to `c`.
* `CategoryTheory.Pretriangulated.isIso_comp_mor₂_of_isIso_mor₁_comp`: in a distinguished
  triangle `X ⟶ Y₁ ⊞ Y₂ ⟶ Z ⟶ X⟦1⟧` whose component `X ⟶ Y₂` is invertible, the map `Y₁ ⟶ Z` is
  invertible.
* `CategoryTheory.Pretriangulated.isIso_comp_mor₂_of_isZero`: if `X` and `Y₁` vanish, the map
  `Y₂ ⟶ Z` is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A distinguished triangle on a biproduct with one invertible component.**  Let
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` be distinguished, and let `Y` be a binary biproduct of `Y₁` and `Y₂`,
presented by inclusions `i₁`, `i₂` and projections `p₁`, `p₂`.  If the component
`X ⟶ Y ⟶ Y₂` of the first map is invertible, then `Y₁ ⟶ Y ⟶ Z` is invertible. -/
theorem isIso_comp_mor₂_of_isIso_mor₁_comp {T : Triangle C} (hT : T ∈ distTriang C)
    {Y₁ Y₂ : C} (i₁ : Y₁ ⟶ T.obj₂) (i₂ : Y₂ ⟶ T.obj₂) (p₁ : T.obj₂ ⟶ Y₁) (p₂ : T.obj₂ ⟶ Y₂)
    (h₁₁ : i₁ ≫ p₁ = 𝟙 _) (h₂₂ : i₂ ≫ p₂ = 𝟙 _) (h₁₂ : i₁ ≫ p₂ = 0)
    (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 _) [IsIso (T.mor₁ ≫ p₂)] :
    IsIso (i₁ ≫ T.mor₂) := by
  set e := T.mor₁ ≫ p₂ with he
  have hmor₁ : T.mor₁ = (T.mor₁ ≫ p₁) ≫ i₁ + e ≫ i₂ := by
    rw [he, Category.assoc, Category.assoc, ← Preadditive.comp_add, htot, Category.comp_id]
  have hrel : i₂ ≫ T.mor₂ = -(inv e ≫ (T.mor₁ ≫ p₁) ≫ i₁ ≫ T.mor₂) := by
    have h0 := comp_distTriang_mor_zero₁₂ T hT
    rw [hmor₁, Preadditive.add_comp, Category.assoc, Category.assoc] at h0
    rw [eq_neg_iff_add_eq_zero, ← cancel_epi e, Preadditive.comp_add, comp_zero,
      IsIso.hom_inv_id_assoc, add_comm]
    simpa only [Category.assoc] using h0
  refine isIso_of_yoneda_map_bijective _ fun W => ⟨fun g g' hgg => ?_, fun z => ?_⟩
  · -- injectivity: a map to `Y₁` killed by `Y₁ ⟶ Z` vanishes
    have hz : ((g - g') ≫ i₁) ≫ T.mor₂ = 0 := by
      simp only [Preadditive.sub_comp, Category.assoc] at hgg ⊢
      exact sub_eq_zero.2 hgg
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ T hT _ hz
    have hh0 : h = 0 := by
      rw [← cancel_mono e, zero_comp, he, ← Category.assoc, ← hh, Category.assoc, h₁₂,
        comp_zero]
    rw [hh0, zero_comp] at hh
    have := congrArg (· ≫ p₁) hh
    simp only [Category.assoc, h₁₁, Category.comp_id, zero_comp] at this
    exact sub_eq_zero.1 this
  · -- surjectivity: every map to `Z` factors through `Y₁ ⟶ Z`
    have hm₃ : T.mor₃ = 0 := by
      rw [← cancel_mono ((shiftFunctor C (1 : ℤ)).map e), zero_comp, he, Functor.map_comp,
        ← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]
    have hδ : z ≫ T.mor₃ = 0 := by rw [hm₃, comp_zero]
    obtain ⟨y, rfl⟩ := Triangle.coyoneda_exact₃ T hT z hδ
    refine ⟨y ≫ p₁ - y ≫ p₂ ≫ inv e ≫ T.mor₁ ≫ p₁, ?_⟩
    dsimp only
    conv_rhs => rw [← Category.id_comp T.mor₂, ← htot]
    simp only [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_add,
      Category.assoc, hrel, Preadditive.comp_neg]
    abel

/-- **A distinguished triangle on a biproduct with two vanishing terms.**  Let
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` be distinguished with `X` zero, and let `Y` be a binary biproduct of `Y₁` and
`Y₂` with `Y₁` zero.  Then `Y₂ ⟶ Y ⟶ Z` is invertible. -/
theorem isIso_comp_mor₂_of_isZero {T : Triangle C} (hT : T ∈ distTriang C)
    {Y₁ Y₂ : C} (i₁ : Y₁ ⟶ T.obj₂) (i₂ : Y₂ ⟶ T.obj₂) (p₁ : T.obj₂ ⟶ Y₁) (p₂ : T.obj₂ ⟶ Y₂)
    (h₂₂ : i₂ ≫ p₂ = 𝟙 _) (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 _)
    (hX : IsZero T.obj₁) (hY₁ : IsZero Y₁) : IsIso (i₂ ≫ T.mor₂) := by
  have : IsIso T.mor₂ := (Triangle.isZero₁_iff_isIso₂ T hT).1 hX
  have : IsIso i₂ := ⟨p₂, h₂₂, by rw [← htot, hY₁.eq_of_tgt p₁ 0, zero_comp, zero_add]⟩
  infer_instance

end Pretriangulated

section Glue

variable {DX : Type u₁} {DU : Type u₂} {DV : Type u₃} {DP : Type u₄}
  [Category.{v₁} DX] [Category.{v₂} DU] [Category.{v₃} DV] [Category.{v₄} DP]
  {rU : DX ⥤ DU} {rV : DX ⥤ DV} {rP : DX ⥤ DP} {rUP : DU ⥤ DP} {rVP : DV ⥤ DP}
  {shU : DU ⥤ DX} {shV : DV ⥤ DX} {shP : DP ⥤ DX}

/-- **The canonical map `s_P(A|_P) ⟶ s_U A`** attached to a factorisation `r_U ⋙ r_{UP} ≅ r_P`
of a restriction functor: the transpose under `s_P ⊣ r_P` of the image under `r_{UP}` of the
unit `A ⟶ (s_U A)|_U`, read through the factorisation. -/
def glueMapOfRestriction (adjP : shP ⊣ rP) (adjU : shU ⊣ rU) (cmp : rU ⋙ rUP ≅ rP)
    (A : DU) : shP.obj (rUP.obj A) ⟶ shU.obj A :=
  (adjP.homEquiv _ _).symm (rUP.map (adjU.unit.app A) ≫ cmp.hom.app (shU.obj A))

/-- **The transpose of a composite with `glueMapOfRestriction`.**  For `g : s_U A ⟶ E`, the
transpose under `s_P ⊣ r_P` of `s_P(A|_P) ⟶ s_U A ⟶ E` is the restriction to `P` of the transpose
`A ⟶ E|_U` of `g`, read through the factorisation. -/
theorem homEquiv_glueMapOfRestriction_comp (adjP : shP ⊣ rP) (adjU : shU ⊣ rU)
    (cmp : rU ⋙ rUP ≅ rP) {A : DU} {E : DX} (g : shU.obj A ⟶ E) :
    adjP.homEquiv _ _ (glueMapOfRestriction adjP adjU cmp A ≫ g) =
      rUP.map (adjU.homEquiv _ _ g) ≫ cmp.hom.app E := by
  rw [glueMapOfRestriction, ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (cmp.hom.naturality g).symm

variable [Preadditive DX] [HasZeroObject DX] [HasShift DX ℤ]
  [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX] [HasBinaryBiproducts DX]

/-- **A candidate glueing of `A` and `B` along `c : A|_P ≅ B|_P`**: an object `F` with a
distinguished triangle

`s_P(B|_P) ⟶ s_U A ⊞ s_V B ⟶ F ⟶ s_P(B|_P)⟦1⟧`

whose first map has the components `s_P(c⁻¹) ≫ glueMapOfRestriction` and
`-glueMapOfRestriction`.  Such a triangle exists in any pretriangulated category
(`CategoryTheory.GlueCandidate.ofDistinguished`); it is unique up to non-unique isomorphism. -/
structure GlueCandidate (adjP : shP ⊣ rP) (adjU : shU ⊣ rU) (adjV : shV ⊣ rV)
    (cmpU : rU ⋙ rUP ≅ rP) (cmpV : rV ⋙ rVP ≅ rP) {A : DU} {B : DV}
    (c : rUP.obj A ≅ rVP.obj B) where
  /-- The glued object. -/
  obj : DX
  /-- The second map of the triangle. -/
  mor₂ : shU.obj A ⊞ shV.obj B ⟶ obj
  /-- The third map of the triangle. -/
  mor₃ : obj ⟶ (shP.obj (rVP.obj B))⟦(1 : ℤ)⟧
  /-- The triangle is distinguished. -/
  distinguished : Triangle.mk
    (biprod.lift (shP.map c.inv ≫ glueMapOfRestriction adjP adjU cmpU A)
      (-glueMapOfRestriction adjP adjV cmpV B)) mor₂ mor₃ ∈ distTriang DX

namespace GlueCandidate

variable {adjP : shP ⊣ rP} {adjU : shU ⊣ rU} {adjV : shV ⊣ rV}
  {cmpU : rU ⋙ rUP ≅ rP} {cmpV : rV ⋙ rVP ≅ rP} {A : DU} {B : DV} {c : rUP.obj A ≅ rVP.obj B}

variable (adjP adjU adjV cmpU cmpV c) in
/-- A candidate glueing exists in every pretriangulated category: complete the first map to a
distinguished triangle. -/
def ofDistinguished : GlueCandidate adjP adjU adjV cmpU cmpV c :=
  let h := distinguished_cocone_triangle
    (biprod.lift (shP.map c.inv ≫ glueMapOfRestriction adjP adjU cmpU A)
      (-glueMapOfRestriction adjP adjV cmpV B))
  { obj := h.choose
    mor₂ := h.choose_spec.choose
    mor₃ := h.choose_spec.choose_spec.choose
    distinguished := h.choose_spec.choose_spec.choose_spec }

variable (G : GlueCandidate adjP adjU adjV cmpU cmpV c)

/-- The comparison `A ⟶ F|_U`: the transpose of `s_U A ⟶ s_U A ⊞ s_V B ⟶ F`. -/
def toOpen : A ⟶ rU.obj G.obj := adjU.homEquiv _ _ (biprod.inl ≫ G.mor₂)

/-- The comparison `B ⟶ F|_V`: the transpose of `s_V B ⟶ s_U A ⊞ s_V B ⟶ F`. -/
def toEtale : B ⟶ rV.obj G.obj := adjV.homEquiv _ _ (biprod.inr ≫ G.mor₂)

/-- **The two comparisons of a candidate glueing agree over `P` up to `c`**:
`c⁻¹ ≫ (A ⟶ F|_U)|_P = (B ⟶ F|_V)|_P`, read through the two factorisations of `r_P`. -/
theorem compat :
    c.inv ≫ rUP.map G.toOpen ≫ cmpU.hom.app G.obj = rVP.map G.toEtale ≫ cmpV.hom.app G.obj := by
  have h0 := comp_distTriang_mor_zero₁₂ _ G.distinguished
  dsimp only [Triangle.mk_mor₁, Triangle.mk_mor₂] at h0
  have h1 : (shP.map c.inv ≫ glueMapOfRestriction adjP adjU cmpU A) ≫ biprod.inl ≫ G.mor₂ =
      glueMapOfRestriction adjP adjV cmpV B ≫ biprod.inr ≫ G.mor₂ := by
    rw [biprod.lift_eq, Preadditive.add_comp] at h0
    simp only [Category.assoc, Preadditive.neg_comp, ← sub_eq_add_neg, sub_eq_zero] at h0
    simpa only [Category.assoc] using h0
  have h2 := congrArg (adjP.homEquiv _ _) h1
  rw [Category.assoc, Adjunction.homEquiv_naturality_left, homEquiv_glueMapOfRestriction_comp,
    homEquiv_glueMapOfRestriction_comp] at h2
  simpa only [toOpen, toEtale, Category.assoc] using h2

end GlueCandidate

end Glue

end CategoryTheory
