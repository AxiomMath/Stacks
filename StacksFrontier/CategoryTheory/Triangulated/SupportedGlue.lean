module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Glueing objects along an open part and an étale neighbourhood of its complement

This file isolates the formal half of the first assertion of [Stacks, Tag 08HB]. Let `D_X` be a
pretriangulated category — `D(𝒪_X)` for an algebraic space `X` — with two "restrictions"
`r_U : D_X ⥤ D_U` (to an open subspace) and `r_V : D_X ⥤ D_V` (along an étale morphism
`V ⟶ X`), and two further restrictions `r_{UP} : D_U ⥤ D_P`, `r_{VP} : D_V ⥤ D_P` to
`P = U ×_X V`, with an identification `e : r_U ⋙ r_{UP} ≅ r_V ⋙ r_{VP}` of the two iterated
restrictions. The restrictions `r_U`, `r_V` and `r_{VP}` have right adjoints `R_U`, `R_V`, `R_P`
(the derived direct images), and the counits of `r_U ⊣ R_U` and `r_{VP} ⊣ R_P` are invertible
(`U ⟶ X` and `P ⟶ V` are open immersions).

Unlike `CategoryTheory.Pretriangulated.exists_glue`, the counit of `r_V ⊣ R_V` is *not*
invertible: `V ⟶ X` is only étale. What replaces it is a class `Sup` of objects of `D_V` —
those supported on the inverse image of `|X| \ |U|` — with four properties:

* `h₁`: an object vanishing on `P` is in `Sup`;
* `h₂`: for `K` in `Sup`, `(R_V K)|_U = 0`;
* `h₃`: for `K` in `Sup`, the counit `(R_V K)|_V ⟶ K` is invertible (Stacks 08GG (2)(b));
* `h₄`: for `K` in `Sup`, every morphism `K ⟶ ((R_U A)|_V)[n]` vanishes (by `j_{V!} ⊣ r_V`, since
  `(j_{V!}K)|_U = 0`).

## Main definitions

* `CategoryTheory.Pretriangulated.glueBaseChange`: the base change map
  `(R_U A)|_V ⟶ R_P(A|_P)`, the transpose of `(R_U A)|_V|_P ≅ (R_U A)|_U|_P ⟶ A|_P`.

## Main results

* `CategoryTheory.Pretriangulated.isIso_glueBaseChange`: the base change map is invertible.
* `CategoryTheory.Pretriangulated.exists_glue_of_supported`: **glueing**. For `A` in `D_U`, `B`
  in `D_V` and an isomorphism `c : A|_P ≅ B|_P` there are an object `F` of `D_X` and
  isomorphisms `f : F|_U ≅ A`, `g : F|_V ≅ B` with `c = g|_P ∘ f⁻¹|_P`.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Pretriangulated

open Category Limits Preadditive

variable {DX : Type u₁} [Category.{v₁} DX] [Preadditive DX] [HasZeroObject DX] [HasShift DX ℤ]
  [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX]
  {DU : Type u₂} [Category.{v₂} DU] [Preadditive DU] [HasZeroObject DU] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DU n).Additive] [Pretriangulated DU]
  {DV : Type u₃} [Category.{v₃} DV] [Preadditive DV] [HasZeroObject DV] [HasShift DV ℤ]
  [∀ n : ℤ, (shiftFunctor DV n).Additive] [Pretriangulated DV]
  {DP : Type u₄} [Category.{v₄} DP] [Preadditive DP] [HasZeroObject DP] [HasShift DP ℤ]
  [∀ n : ℤ, (shiftFunctor DP n).Additive] [Pretriangulated DP]
  {rU : DX ⥤ DU} {rV : DX ⥤ DV} {rUP : DU ⥤ DP} {rVP : DV ⥤ DP}
  {RU : DU ⥤ DX} {RV : DV ⥤ DX} {RP : DP ⥤ DV}

/-- The image under `L` of the transpose of `g` followed by the counit is `g`. -/
private theorem map_homEquiv_comp_counit {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D} (g : L.obj X ⟶ Y) :
    L.map (adj.homEquiv _ _ g) ≫ adj.counit.app Y = g :=
  (adj.homEquiv_counit _ _ _).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)

/-- The base change map `(R_U A)|_V ⟶ R_P(A|_P)`: the transpose under `r_{VP} ⊣ R_P` of
`(R_U A)|_V|_P ≅ (R_U A)|_U|_P ⟶ A|_P`. -/
noncomputable def glueBaseChange (adjU : rU ⊣ RU) (adjP : rVP ⊣ RP)
    (e : rU ⋙ rUP ≅ rV ⋙ rVP) (A : DU) : rV.obj (RU.obj A) ⟶ RP.obj (rUP.obj A) :=
  adjP.homEquiv _ _ (e.inv.app (RU.obj A) ≫ rUP.map (adjU.counit.app A))

omit [Preadditive DX] [HasZeroObject DX] [HasShift DX ℤ]
  [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX]
  [Preadditive DU] [HasZeroObject DU] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DU n).Additive] [Pretriangulated DU]
  [Preadditive DV] [HasZeroObject DV] [HasShift DV ℤ]
  [∀ n : ℤ, (shiftFunctor DV n).Additive] [Pretriangulated DV]
  [Preadditive DP] [HasZeroObject DP] [HasShift DP ℤ]
  [∀ n : ℤ, (shiftFunctor DP n).Additive] [Pretriangulated DP] in
/-- The base change map followed by the counit of `r_{VP} ⊣ R_P` is
`(R_U A)|_V|_P ≅ (R_U A)|_U|_P ⟶ A|_P`. -/
theorem glueBaseChange_comp_counit (adjU : rU ⊣ RU) (adjP : rVP ⊣ RP)
    (e : rU ⋙ rUP ≅ rV ⋙ rVP) (A : DU) :
    rVP.map (glueBaseChange adjU adjP e A) ≫ adjP.counit.app (rUP.obj A) =
      e.inv.app (RU.obj A) ≫ rUP.map (adjU.counit.app A) :=
  map_homEquiv_comp_counit adjP _

/-- A morphism into the image under a right adjoint out of an object killed by the left adjoint
vanishes. -/
theorem eq_zero_of_isZero_leftAdjoint_obj {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X : C} {Y : D} (hX : IsZero (L.obj X)) (g : X ⟶ R.obj Y) : g = 0 :=
  (adj.homEquiv _ _).symm.injective (hX.eq_of_src _ _)

omit [Preadditive DX] [HasZeroObject DX] [HasShift DX ℤ]
  [∀ n : ℤ, (shiftFunctor DX n).Additive] [Pretriangulated DX]
  [Preadditive DU] [HasZeroObject DU] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DU n).Additive] [Pretriangulated DU] in
/-- **The base change map is invertible**, when the counits of `r_U ⊣ R_U` and `r_{VP} ⊣ R_P`
are invertible and `Sup` satisfies `h₁` and `h₄` of the module docstring. -/
theorem isIso_glueBaseChange (adjU : rU ⊣ RU) (adjP : rVP ⊣ RP)
    [rVP.CommShift ℤ] [rVP.IsTriangulated] [IsIso adjU.counit] [IsIso adjP.counit]
    (e : rU ⋙ rUP ≅ rV ⋙ rVP) (Sup : DV → Prop) (h₁ : ∀ K, IsZero (rVP.obj K) → Sup K)
    (h₄ : ∀ K, Sup K → ∀ (A' : DU) (n : ℤ) (g : K ⟶ (rV.obj (RU.obj A'))⟦n⟧), g = 0)
    (A : DU) : IsIso (glueBaseChange adjU adjP e A) := by
  obtain ⟨D, d, δ, hT⟩ := distinguished_cocone_triangle (glueBaseChange adjU adjP e A)
  have : IsIso (rVP.map (glueBaseChange adjU adjP e A) ≫ adjP.counit.app (rUP.obj A)) := by
    rw [glueBaseChange_comp_counit]
    infer_instance
  have hθ : IsIso (rVP.map (glueBaseChange adjU adjP e A)) :=
    IsIso.of_isIso_comp_right _ (adjP.counit.app (rUP.obj A))
  have hD : IsZero (rVP.obj D) := Triangle.isZero₃_of_isIso₁ _ (rVP.map_distinguished _ hT) hθ
  have hid : 𝟙 D = 0 := by
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₃ _ hT (𝟙 D) (by simpa using h₄ D (h₁ D hD) A 1 δ)
    rw [hh, eq_zero_of_isZero_leftAdjoint_obj adjP hD h, zero_comp]
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 ((IsZero.iff_id_eq_zero D).2 hid)

/-- **Glueing along an open part and an étale neighbourhood of its complement** (the formal
half of the first assertion of [Stacks, Tag 08HB]). In the situation of the module docstring,
for `A` in `D_U`, `B` in `D_V` and an isomorphism `c : A|_P ≅ B|_P` there are an object `F` of
`D_X` and isomorphisms `f : F|_U ≅ A`, `g : F|_V ≅ B` such that `c = g|_P ∘ f⁻¹|_P`, the two
restrictions of `F` to `P` being identified by `e`. -/
theorem exists_glue_of_supported (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjP : rVP ⊣ RP)
    [rU.CommShift ℤ] [rU.IsTriangulated] [rV.CommShift ℤ] [rV.IsTriangulated]
    [rVP.CommShift ℤ] [rVP.IsTriangulated] [IsIso adjU.counit] [IsIso adjP.counit]
    (e : rU ⋙ rUP ≅ rV ⋙ rVP) (Sup : DV → Prop) (h₁ : ∀ K, IsZero (rVP.obj K) → Sup K)
    (h₂ : ∀ K, Sup K → IsZero (rU.obj (RV.obj K)))
    (h₃ : ∀ K, Sup K → IsIso (adjV.counit.app K))
    (h₄ : ∀ K, Sup K → ∀ (A' : DU) (n : ℤ) (g : K ⟶ (rV.obj (RU.obj A'))⟦n⟧), g = 0)
    (A : DU) (B : DV) (c : rUP.obj A ≅ rVP.obj B) :
    ∃ (F : DX) (f : rU.obj F ≅ A) (g : rV.obj F ≅ B),
      c.hom = rUP.map f.inv ≫ e.hom.app F ≫ rVP.map g.hom := by
  have := isIso_glueBaseChange adjU adjP e Sup h₁ h₄ A
  let θ := glueBaseChange adjU adjP e A
  have hη : rVP.map (adjP.unit.app B) = inv (adjP.counit.app (rVP.obj B)) :=
    IsIso.eq_inv_of_inv_hom_id (adjP.left_triangle_components B)
  let u : B ⟶ rV.obj (RU.obj A) := adjP.unit.app B ≫ RP.map c.inv ≫ inv θ
  have hu : IsIso (rVP.map u) := by
    simp only [u, Functor.map_comp, hη]
    infer_instance
  obtain ⟨C, w, δ, hT⟩ := distinguished_cocone_triangle u
  have hC : Sup C := h₁ C (Triangle.isZero₃_of_isIso₁ _ (rVP.map_distinguished _ hT) hu)
  let φ : RU.obj A ⟶ RV.obj C := adjV.homEquiv _ _ w
  obtain ⟨F, i, δ', hF⟩ := distinguished_cocone_triangle₁ φ
  have hi : IsIso (rU.map i) :=
    (Triangle.isZero₃_iff_isIso₁ _ (rU.map_distinguished _ hF)).1 (h₂ C hC)
  let f : rU.obj F ≅ A := asIso (rU.map i) ≪≫ asIso (adjU.counit.app A)
  let κ : rV.obj (RV.obj C) ≅ C := @asIso _ _ _ _ (adjV.counit.app C) (h₃ C hC)
  have hw : rV.map φ ≫ κ.hom = w :=
    map_homEquiv_comp_counit adjV w
  have hw' : w ≫ κ.inv = 𝟙 _ ≫ rV.map φ := by
    rw [id_comp, ← hw, assoc, Iso.hom_inv_id, comp_id]
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ (Triangle.mk u w δ)
    (rV.mapTriangle.obj (Triangle.mk i φ δ')) hT (rV.map_distinguished _ hF) (𝟙 _) κ.inv hw'
  let ψ : Triangle.mk u w δ ⟶ rV.mapTriangle.obj (Triangle.mk i φ δ') :=
    { hom₁ := a, hom₂ := 𝟙 _, hom₃ := κ.inv
      comm₁ := ha₁
      comm₂ := hw'
      comm₃ := ha₃ }
  have ha : IsIso a :=
    isIso₁_of_isIso₂₃ ψ hT (rV.map_distinguished _ hF) (by change IsIso (𝟙 _); infer_instance)
      (by change IsIso κ.inv; infer_instance)
  let a' : B ⟶ rV.obj F := a
  have : IsIso a' := ha
  have ha₁' : a' ≫ rV.map i = u := ((comp_id u).symm.trans ha₁).symm
  let g : rV.obj F ≅ B := (asIso a').symm
  refine ⟨F, f, g, ?_⟩
  have : IsIso (rVP.map a' ≫ rVP.map (rV.map i)) := by rwa [← Functor.map_comp, ha₁']
  have := IsIso.of_isIso_comp_left (rVP.map a') (rVP.map (rV.map i))
  have hθ' : inv (adjP.counit.app (rUP.obj A)) ≫ rVP.map (inv θ) =
      inv (rUP.map (adjU.counit.app A)) ≫ e.hom.app (RU.obj A) := by
    rw [Functor.map_inv, ← IsIso.inv_comp]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [glueBaseChange_comp_counit]
    simp
  have hnc : inv (adjP.counit.app (rVP.obj B)) ≫ rVP.map (RP.map c.inv) =
      c.inv ≫ inv (adjP.counit.app (rUP.obj A)) := by
    rw [IsIso.inv_comp_eq, ← assoc, IsIso.eq_comp_inv]
    exact adjP.counit.naturality c.inv
  have hcu : c.hom ≫ rVP.map u =
      inv (rUP.map (adjU.counit.app A)) ≫ e.hom.app (RU.obj A) := by
    simp only [u, Functor.map_comp, hη]
    rw [← assoc (inv _), hnc, assoc, Iso.hom_inv_id_assoc, hθ']
  have h1 : c.hom ≫ rVP.map a' = rUP.map f.inv ≫ e.hom.app F := by
    rw [← cancel_mono (rVP.map (rV.map i)), assoc, ← Functor.map_comp, ha₁', hcu]
    have hnat := e.hom.naturality i
    simp only [Functor.comp_map] at hnat
    rw [assoc, ← hnat]
    simp only [f, Iso.trans_inv, asIso_inv, Functor.map_comp, assoc, Functor.map_inv,
      IsIso.inv_hom_id_assoc]
  have hg : rVP.map g.hom = inv (rVP.map a') := by
    simp only [g, Iso.symm_hom, asIso_inv, Functor.map_inv]
  rw [hg, ← assoc, ← h1, assoc, IsIso.hom_inv_id, comp_id]

end CategoryTheory.Pretriangulated
