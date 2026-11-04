module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Glueing objects and morphisms along an excision square, through extensions by zero

Consider pretriangulated categories `C`, `C_U`, `C_V`, `C_P` with exact restriction functors
`a_U : C ⥤ C_U`, `a_V : C ⥤ C_V`, `b_V : C_V ⥤ C_P` and a restriction functor `b_U : C_U ⥤ C_P`,
an identification `κ : a_U ⋙ b_U ≅ a_V ⋙ b_V` of the two restrictions to `P`, and *left* adjoints
`s_U ⊣ a_U`, `s_V ⊣ a_V`, `s_P ⊣ b_V`.  Think of an elementary distinguished square
`(U ⊆ W, j : V ⟶ W)` of algebraic spaces with `P = U ×_W V`, of `C = D(𝒪_W)` and so on, of the
restrictions and of the extensions by zero.  Assume:

* `s_U ⊣ a_U` and `s_P ⊣ b_V` have invertible units (`U ⊆ W` and `P ⊆ V` are open immersions);
* base change: the mate `γ : b_U ⋙ s_P ⟶ s_U ⋙ a_V` of `κ` is invertible, where "mate" is
  expressed by the unit identity `hγ` below;
* excision: the objects `N` of `C_V` with `b_V N = 0` satisfy `a_U (s_V N) = 0`, and the unit
  `N ⟶ a_V (s_V N)` is invertible at them;
* for the glueing of morphisms, an object of `C` restricting to zero on `U` and on `V` is zero.

Then:

* an object `A` of `C_U` and an object `B` of `C_V` with an isomorphism `c : b_U A ≅ b_V B` are the
  restrictions of one object `E` of `C`, by isomorphisms `f : a_U E ≅ A`, `g : a_V E ≅ B` that are
  compatible with `c` over `P`;
* morphisms `φ_U : a_U F ⟶ a_U E` and `φ_V : a_V F ⟶ a_V E` that agree over `P` are the
  restrictions of one morphism `F ⟶ E`.

These are the two assertions of [Stacks, Tag 08HB] in the abstract, in the form that uses the
extensions by zero and the base change of [Stacks, Tag 08HA] rather than the direct images; the
dual statement with right adjoints and without the compatibility of the glueing isomorphisms is
`CategoryTheory.Pretriangulated.exists_glue_of_excision`.

## The constructions

*Objects.* Let `s_P(b_V B) ⟶ B ⟶ B_T ⟶ s_P(b_V B)⟦1⟧` be a triangle on the counit of
`s_P ⊣ b_V`; then `b_V B_T = 0`.  Through `s_P(b_V B) ≅ s_P(b_U A) ≅ a_V(s_U A)` the third map is
a morphism `B_T ⟶ (a_V(s_U A))⟦1⟧`, whose transpose `s_V B_T ⟶ (s_U A)⟦1⟧` has a fibre `E`.  On
`U` the term `s_V B_T` dies, so `a_U E ≅ a_U(s_U A) ≅ A`; on `V` the defining triangle of `E`
becomes the triangle of `B`, since `B_T ≅ a_V(s_V B_T)` by excision.

*Morphisms.* Let `s_U(a_U F) ⟶ F ⟶ Y ⟶ s_U(a_U F)⟦1⟧` be a triangle on the counit of
`s_U ⊣ a_U`.  The transpose `ψ_U : s_U(a_U F) ⟶ E` of `φ_U` extends along the counit because
everything restricting to zero on `U` is recovered from its restriction to `V`, where `ψ_U` is
`φ_V` precomposed with the counit — this is where the agreement over `P` and the base change
enter.  The extension is then corrected on `V` by a morphism out of `Y`.

## Main results

* `CategoryTheory.Pretriangulated.isIso_of_isIso_map_of_isZero`: a morphism restricting to
  isomorphisms on `U` and on `V` is an isomorphism.
* `CategoryTheory.Pretriangulated.exists_glue_of_shriekExcision`: the glueing of objects, with
  the compatibility of the glueing isomorphisms over `P`.
* `CategoryTheory.Pretriangulated.exists_hom_of_shriekExcision`: the glueing of morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C CU CV CP : Type*} [Category* C] [Category* CU] [Category* CV] [Category* CP]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [Preadditive CU] [HasZeroObject CU] [HasShift CU ℤ] [∀ n : ℤ, (shiftFunctor CU n).Additive]
  [Pretriangulated CU]
  [Preadditive CV] [HasZeroObject CV] [HasShift CV ℤ] [∀ n : ℤ, (shiftFunctor CV n).Additive]
  [Pretriangulated CV]
  [Preadditive CP] [HasZeroObject CP] [HasShift CP ℤ] [∀ n : ℤ, (shiftFunctor CP n).Additive]
  [Pretriangulated CP]

/-- **A morphism restricting to isomorphisms on `U` and on `V` is an isomorphism**, as soon as
an object restricting to zero on `U` and on `V` is zero: its cone restricts to zero on both. -/
theorem isIso_of_isIso_map_of_isZero {aU : C ⥤ CU} {aV : C ⥤ CV}
    [aU.CommShift ℤ] [aU.IsTriangulated] [aV.CommShift ℤ] [aV.IsTriangulated]
    (hloc : ∀ N : C, IsZero (aU.obj N) → IsZero (aV.obj N) → IsZero N)
    {X Y : C} (φ : X ⟶ Y) (hU : IsIso (aU.map φ)) (hV : IsIso (aV.map φ)) : IsIso φ := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle φ
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hloc Z
    (Triangle.isZero₃_of_isIso₁ _ (aU.map_distinguished _ hT) hU)
    (Triangle.isZero₃_of_isIso₁ _ (aV.map_distinguished _ hT) hV))

section Shriek

/-- The right adjoint of the counit at `Z` is invertible when the unit at `G Z` is. -/
private theorem isIso_map_counit_app_of_isIso_unit_app {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) (Z : B) [IsIso (adj.unit.app (G.obj Z))] :
    IsIso (G.map (adj.counit.app Z)) := by
  rw [IsIso.eq_inv_of_hom_inv_id (adj.right_triangle_components Z)]
  infer_instance

/-- The unit followed by the transpose `G (ε ≫ x)` of `ε ≫ x` is `G x`. -/
private theorem unit_app_comp_map_counit_app_comp {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {Z E : B} (x : Z ⟶ E) :
    adj.unit.app (G.obj Z) ≫ G.map (adj.counit.app Z ≫ x) = G.map x := by
  simp

/-- The unit followed by `G` of the transpose of `f` is `f`. -/
private theorem unit_app_comp_map_homEquiv_symm {A B : Type*} [Category* A] [Category* B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {X : A} {Y : B} (f : X ⟶ G.obj Y) :
    adj.unit.app X ≫ G.map ((adj.homEquiv _ _).symm f) = f := by
  have h := (adj.homEquiv _ _).apply_symm_apply f
  rwa [Adjunction.homEquiv_unit] at h

variable {aU : C ⥤ CU} {aV : C ⥤ CV} {bU : CU ⥤ CP} {bV : CV ⥤ CP}
  [aU.CommShift ℤ] [aU.IsTriangulated] [aV.CommShift ℤ] [aV.IsTriangulated]
  [bV.CommShift ℤ] [bV.IsTriangulated]
  {sU : CU ⥤ C} {sV : CV ⥤ C} {sP : CP ⥤ CV}
  (adjU : sU ⊣ aU) (adjV : sV ⊣ aV) (adjP : sP ⊣ bV)
  (κ : aU ⋙ bU ≅ aV ⋙ bV) (γ : bU ⋙ sP ⟶ sU ⋙ aV)

omit [HasZeroObject CP] [HasShift CP ℤ] [∀ n : ℤ, (shiftFunctor CP n).Additive] [Pretriangulated CP]
  [bV.CommShift ℤ] [bV.IsTriangulated] in
include κ in
/-- **An object restricting to zero on `U` is recovered from its restriction to `V`**: under the
excision hypotheses, the counit `s_V(a_V Z) ⟶ Z` is invertible at an object `Z` of `C` with
`a_U Z = 0`.  Both sides restrict to zero on `U`, and on `V` a triangle identity exhibits the
restricted counit as a one-sided inverse of the unit at `a_V Z`, which is invertible by excision
since `b_V(a_V Z) ≅ b_U(a_U Z) = 0`. -/
theorem isIso_counit_app_of_isZero_of_shriekExcision [bU.PreservesZeroMorphisms]
    (hUV : ∀ N : CV, IsZero (bV.obj N) → IsZero (aU.obj (sV.obj N)))
    (hexc : ∀ N : CV, IsZero (bV.obj N) → IsIso (adjV.unit.app N))
    (hloc : ∀ N : C, IsZero (aU.obj N) → IsZero (aV.obj N) → IsZero N)
    (Z : C) (hZ : IsZero (aU.obj Z)) : IsIso (adjV.counit.app Z) := by
  have hb : IsZero (bV.obj (aV.obj Z)) := (bU.map_isZero hZ).of_iso (κ.app Z).symm
  refine isIso_of_isIso_map_of_isZero hloc _ ⟨⟨0, (hUV _ hb).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩ ?_
  have := hexc _ hb
  exact isIso_map_counit_app_of_isIso_unit_app adjV Z

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive CU] [HasZeroObject CU] [HasShift CU ℤ]
  [∀ n : ℤ, (shiftFunctor CU n).Additive] [Pretriangulated CU] [aU.CommShift ℤ]
  [aU.IsTriangulated] in
/-- The restriction to `U` of the counit of `s_U ⊣ a_U` is invertible when the unit is. -/
theorem isIso_map_counit_app_of_isIso_unit [IsIso adjU.unit] (F : C) :
    IsIso (aU.map (adjU.counit.app F)) := by
  exact isIso_map_counit_app_of_isIso_unit_app adjU F

/-- **Glueing objects along an excision square, compatibly over the intersection.**  Under the
hypotheses of the module docstring, an object `A` of `C_U`, an object `B` of `C_V` and an
isomorphism `c : b_U A ≅ b_V B` are glued by an object `E` of `C` and isomorphisms
`f : a_U E ≅ A`, `g : a_V E ≅ B` such that, over `P`, `c ∘ b_U f = b_V g ∘ κ_E`.

The hypothesis `hγ` says that `γ` is the mate of `κ` under `s_U ⊣ a_U` and `s_P ⊣ b_V`: the
transpose of `γ_A` is `b_U` of the unit at `A` followed by `κ`. -/
theorem exists_glue_of_shriekExcision [IsIso adjU.unit] [IsIso adjP.unit] [∀ A, IsIso (γ.app A)]
    (hγ : ∀ A : CU, adjP.unit.app (bU.obj A) ≫ bV.map (γ.app A) =
      bU.map (adjU.unit.app A) ≫ κ.hom.app (sU.obj A))
    (hUV : ∀ N : CV, IsZero (bV.obj N) → IsZero (aU.obj (sV.obj N)))
    (hexc : ∀ N : CV, IsZero (bV.obj N) → IsIso (adjV.unit.app N))
    (A : CU) (B : CV) (c : bU.obj A ≅ bV.obj B) :
    ∃ (E : C) (f : aU.obj E ≅ A) (g : aV.obj E ≅ B),
      bU.map f.hom ≫ c.hom = κ.hom.app E ≫ bV.map g.hom := by
  obtain ⟨BT, g₀, h₀, hT₀⟩ := distinguished_cocone_triangle (adjP.counit.app B)
  have hεP : IsIso (bV.map (adjP.counit.app B)) := by
    exact isIso_map_counit_app_of_isIso_unit_app adjP B
  have hBT : IsZero (bV.obj BT) := Triangle.isZero₃_of_isIso₁ _ (bV.map_distinguished _ hT₀) hεP
  let e₃ : sP.obj (bV.obj B) ≅ aV.obj (sU.obj A) := sP.mapIso c.symm ≪≫ asIso (γ.app A)
  let d' : sV.obj BT ⟶ (sU.obj A)⟦(1 : ℤ)⟧ := (adjV.homEquiv _ _).symm
    (h₀ ≫ e₃.hom⟦(1 : ℤ)⟧' ≫ (aV.commShiftIso (1 : ℤ)).inv.app (sU.obj A))
  have hd' : adjV.unit.app BT ≫ aV.map d' =
      h₀ ≫ e₃.hom⟦(1 : ℤ)⟧' ≫ (aV.commShiftIso (1 : ℤ)).inv.app (sU.obj A) :=
    unit_app_comp_map_homEquiv_symm adjV _
  obtain ⟨E, ι, π, hE⟩ := distinguished_cocone_triangle₂ d'
  have hιU : IsIso (aU.map ι) :=
    (Triangle.isZero₃_iff_isIso₁ _ (aU.map_distinguished _ hE)).1 (hUV BT hBT)
  let f : aU.obj E ≅ A := (asIso (aU.map ι)).symm ≪≫ (asIso (adjU.unit.app A)).symm
  have hTV := aV.map_distinguished _ hE
  have hcomm : h₀ ≫ e₃.hom⟦(1 : ℤ)⟧' =
      adjV.unit.app BT ≫ aV.map d' ≫ (aV.commShiftIso (1 : ℤ)).hom.app (sU.obj A) := by
    rw [reassoc_of% hd']
    simp
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b : B ⟶ aV.obj E, adjP.counit.app B ≫ b = e₃.hom ≫ aV.map ι ∧
      g₀ ≫ adjV.unit.app BT = b ≫ aV.map π :=
    complete_distinguished_triangle_morphism₂ _ _ hT₀ hTV e₃.hom (adjV.unit.app BT) hcomm
  have hbiso : IsIso b := by
    let φ : Triangle.mk (adjP.counit.app B) g₀ h₀ ⟶ aV.mapTriangle.obj (Triangle.mk ι π d') :=
      { hom₁ := e₃.hom
        hom₂ := b
        hom₃ := adjV.unit.app BT
        comm₁ := hb₁
        comm₂ := hb₂
        comm₃ := hcomm }
    exact isIso₂_of_isIso₁₃ φ hT₀ hTV ⟨⟨e₃.inv, e₃.hom_inv_id, e₃.inv_hom_id⟩⟩ (hexc BT hBT)
  refine ⟨E, f, (asIso b).symm, ?_⟩
  have h1 : bV.map b = adjP.unit.app (bV.obj B) ≫ bV.map (adjP.counit.app B ≫ b) :=
    (unit_app_comp_map_counit_app_comp adjP b).symm
  have h2 : c.hom ≫ adjP.unit.app (bV.obj B) ≫ bV.map (sP.map c.inv) =
      adjP.unit.app (bU.obj A) := by
    have := adjP.unit.naturality c.hom
    dsimp at this
    rw [reassoc_of% this, ← Functor.map_comp, ← Functor.map_comp, c.hom_inv_id,
      Functor.map_id, Functor.map_id, comp_id]
  have h3 : bU.map (aU.map ι) ≫ κ.hom.app E = κ.hom.app (sU.obj A) ≫ bV.map (aV.map ι) :=
    κ.hom.naturality ι
  have h4 : bV.map (adjP.counit.app B ≫ b) =
      bV.map (sP.map c.inv) ≫ bV.map (γ.app A) ≫ bV.map (aV.map ι) := by
    rw [hb₁]
    simp [e₃]
  have hcb : c.hom ≫ bV.map b = bU.map f.inv ≫ κ.hom.app E := by
    rw [h1, h4, reassoc_of% h2, reassoc_of% (hγ A), ← h3]
    simp [f]
  rw [← cancel_mono (bV.map b)]
  simp [hcb]

omit [HasZeroObject CP] [HasShift CP ℤ] [∀ n : ℤ, (shiftFunctor CP n).Additive] [Pretriangulated CP]
  [bV.CommShift ℤ] [bV.IsTriangulated] in
/-- **Glueing morphisms along an excision square.**  Under the hypotheses of the module
docstring, including that an object restricting to zero on `U` and on `V` is zero, morphisms
`φ_U : a_U F ⟶ a_U E` and `φ_V : a_V F ⟶ a_V E` that agree over `P` through `κ` are the
restrictions of one morphism `F ⟶ E`. -/
theorem exists_hom_of_shriekExcision [bU.PreservesZeroMorphisms] [IsIso adjU.unit] [∀ A, IsIso
    (γ.app A)]
    (hγ : ∀ A : CU, adjP.unit.app (bU.obj A) ≫ bV.map (γ.app A) =
      bU.map (adjU.unit.app A) ≫ κ.hom.app (sU.obj A))
    (hUV : ∀ N : CV, IsZero (bV.obj N) → IsZero (aU.obj (sV.obj N)))
    (hexc : ∀ N : CV, IsZero (bV.obj N) → IsIso (adjV.unit.app N))
    (hloc : ∀ N : C, IsZero (aU.obj N) → IsZero (aV.obj N) → IsZero N)
    {F E : C} (φU : aU.obj F ⟶ aU.obj E) (φV : aV.obj F ⟶ aV.obj E)
    (hagree : bU.map φU ≫ κ.hom.app E = κ.hom.app F ≫ bV.map φV) :
    ∃ φ : F ⟶ E, aU.map φ = φU ∧ aV.map φ = φV := by
  have hεU : IsIso (aU.map (adjU.counit.app F)) := isIso_map_counit_app_of_isIso_unit adjU F
  let ψU : sU.obj (aU.obj F) ⟶ E := (adjU.homEquiv _ _).symm φU
  have hψU : adjU.unit.app (aU.obj F) ≫ aU.map ψU = φU := unit_app_comp_map_homEquiv_symm adjU φU
  have hL : adjP.unit.app (bU.obj (aU.obj F)) ≫ bV.map (γ.app (aU.obj F)) ≫
      bV.map (aV.map ψU) = bU.map φU ≫ κ.hom.app E := by
    have h1 : bU.map (aU.map ψU) ≫ κ.hom.app E =
        κ.hom.app (sU.obj (aU.obj F)) ≫ bV.map (aV.map ψU) := κ.hom.naturality ψU
    rw [reassoc_of% (hγ (aU.obj F)), ← h1, ← Functor.map_comp_assoc, hψU]
  have hR : adjP.unit.app (bU.obj (aU.obj F)) ≫ bV.map (γ.app (aU.obj F)) ≫
      bV.map (aV.map (adjU.counit.app F)) ≫ bV.map φV = bU.map φU ≫ κ.hom.app E := by
    have h2 : bU.map (aU.map (adjU.counit.app F)) ≫ κ.hom.app F =
        κ.hom.app (sU.obj (aU.obj F)) ≫ bV.map (aV.map (adjU.counit.app F)) :=
      κ.hom.naturality (adjU.counit.app F)
    rw [reassoc_of% (hγ (aU.obj F)), ← reassoc_of% h2, ← Functor.map_comp_assoc,
      adjU.right_triangle_components, Functor.map_id, id_comp, hagree]
  have key : aV.map ψU = aV.map (adjU.counit.app F) ≫ φV := by
    apply (cancel_epi (γ.app (aU.obj F))).1
    apply (adjP.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [hL, hR]
  have hvan : ∀ {Z : C} (_ : IsZero (aU.obj Z)) (x : Z ⟶ E), aV.map x = 0 → x = 0 := by
    intro Z hZ x hx
    have := isIso_counit_app_of_isZero_of_shriekExcision adjV κ hUV hexc hloc Z hZ
    have h' : adjV.counit.app Z ≫ x = 0 := (adjV.homEquiv _ _).injective (by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, unit_app_comp_map_counit_app_comp,
        hx, Functor.map_zero, comp_zero])
    exact (cancel_epi (adjV.counit.app Z)).1 (h'.trans comp_zero.symm)
  obtain ⟨X, f₁, h₁, hT₁⟩ := distinguished_cocone_triangle₁ (adjU.counit.app F)
  have hXU : IsZero (aU.obj X) := Triangle.isZero₁_of_isIso₂ _ (aU.map_distinguished _ hT₁) hεU
  have hf₁ : f₁ ≫ adjU.counit.app F = 0 := comp_distTriang_mor_zero₁₂ _ hT₁
  have hf₁ψ : f₁ ≫ ψU = 0 := hvan hXU _ (by
    rw [Functor.map_comp, key, ← Functor.map_comp_assoc, hf₁, Functor.map_zero, zero_comp])
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : F ⟶ E, ψU = adjU.counit.app F ≫ φ₀ :=
    Triangle.yoneda_exact₂ _ hT₁ ψU hf₁ψ
  have hφ₀U : aU.map φ₀ = φU := by
    rw [← hψU, hφ₀, ← unit_app_comp_map_counit_app_comp adjU φ₀, ← hφ₀, hψU]
  obtain ⟨Y, g, h, hT⟩ : ∃ (Y : C) (g : F ⟶ Y) (h : Y ⟶ (sU.obj (aU.obj F))⟦(1 : ℤ)⟧),
      Triangle.mk (adjU.counit.app F) g h ∈ distTriang C :=
    distinguished_cocone_triangle _
  have hYU : IsZero (aU.obj Y) := Triangle.isZero₃_of_isIso₁ _ (aU.map_distinguished _ hT) hεU
  have hD : aV.map (adjU.counit.app F) ≫ (aV.map φ₀ - φV) = 0 := by
    rw [Preadditive.comp_sub, ← Functor.map_comp, ← hφ₀, key, sub_self]
  obtain ⟨D', hD'⟩ : ∃ D' : aV.obj Y ⟶ aV.obj E, aV.map φ₀ - φV = aV.map g ≫ D' :=
    Triangle.yoneda_exact₂ _ (aV.map_distinguished _ hT) _ hD
  have := isIso_counit_app_of_isZero_of_shriekExcision adjV κ hUV hexc hloc Y hYU
  let θ : Y ⟶ E := inv (adjV.counit.app Y) ≫ (adjV.homEquiv _ _).symm D'
  have hθV : aV.map θ = D' := by
    have h1 : aV.map (inv (adjV.counit.app Y)) = adjV.unit.app (aV.obj Y) := by
      rw [Functor.map_inv]
      exact IsIso.inv_eq_of_inv_hom_id (adjV.right_triangle_components Y)
    rw [Functor.map_comp, h1]
    exact unit_app_comp_map_homEquiv_symm adjV D'
  refine ⟨φ₀ - g ≫ θ, ?_, ?_⟩
  · rw [Functor.map_sub, Functor.map_comp, hφ₀U, hYU.eq_of_src (aU.map θ) 0, comp_zero, sub_zero]
  · rw [Functor.map_sub, Functor.map_comp, hθV, ← hD', sub_sub_cancel]

end Shriek

end CategoryTheory.Pretriangulated
