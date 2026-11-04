module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The formal part of glueing across a square of restriction functors

This file isolates the purely categorical half of the glueing of modules across an elementary
distinguished square (see
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Glue`).  We are given
categories `C_W`, `C_U`, `C_V`, `C_P` with "restriction" functors

`r_U : C_W ⥤ C_U`, `r_V : C_W ⥤ C_V`, `r_1 : C_U ⥤ C_P`, `r_2 : C_V ⥤ C_P`, `r_P : C_W ⥤ C_P`

and identifications `e_U : r_U ⋙ r_1 ≅ r_P`, `e_V : r_V ⋙ r_2 ≅ r_P`, together with left
adjoints `L_U ⊣ r_U`, `L_V ⊣ r_V` and `L_2 ⊣ r_2`.  For objects `G_U` of `C_U` and `H` of `C_V`
and an isomorphism `θ : r_2 H ≅ r_1 G_U`, the *glued object* is the pushout `G` of

* `a : L_V L_2 r_2 H ⟶ L_U G_U`, the double adjoint of
  `r_2 H ≅ r_1 G_U ⟶ r_1 r_U L_U G_U ≅ r_P L_U G_U ≅ r_2 r_V L_U G_U`, and
* `b = L_V(ε_H) : L_V L_2 r_2 H ⟶ L_V H`,

with comparison maps `α_U : G_U ⟶ r_U G` and `α_V : H ⟶ r_V G` obtained from the units and the
two coprojections.  Formally:

* `CategoryTheory.GlueSquare.r₂_map_glueαV`: the restriction of `α_V` along `r_2` is `θ`
  followed by the restriction of `α_U` along `r_1`, read through `e_U` and `e_V`;
* `CategoryTheory.GlueSquare.glueαU_comp_map_glueDesc` and
  `CategoryTheory.GlueSquare.glueαV_comp_map_glueDesc`: given an object `F` of `C_W` and maps
  `ψ_U : G_U ⟶ r_U F`, `ψ_V : H ⟶ r_V F` compatible with `θ`, the induced map `ψ : G ⟶ F`
  restricts to `ψ_U` and `ψ_V`.

Nothing here says that `α_U` and `α_V` are invertible: that is geometry, proved for the square of
restrictions of an elementary distinguished square on geometric stalks.

## Implementation notes

Keeping the functors abstract is not only a matter of generality.  For the concrete restriction
functors of algebraic spaces, equations between morphisms whose objects are spelled once as
`(F ⋙ G).obj X` and once as `G.obj (F.obj X)` are expensive for the kernel to check, because it
unfolds the restriction functors before `CategoryTheory.Functor.comp`; for abstract functors the
same identifications are immediate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vW vU vV vP uW uU uV uP

namespace CategoryTheory.GlueSquare

variable {CW : Type uW} [Category.{vW} CW] {CU : Type uU} [Category.{vU} CU]
  {CV : Type uV} [Category.{vV} CV] {CP : Type uP} [Category.{vP} CP]
  (rU : CW ⥤ CU) (rV : CW ⥤ CV) (r₁ : CU ⥤ CP) (r₂ : CV ⥤ CP) (rP : CW ⥤ CP)
  (eU : rU ⋙ r₁ ≅ rP) (eV : rV ⋙ r₂ ≅ rP)
  {LU : CU ⥤ CW} {LV : CV ⥤ CW} {L₂ : CP ⥤ CV}
  (adjU : LU ⊣ rU) (adjV : LV ⊣ rV) (adj₂ : L₂ ⊣ r₂)
  (GU : CU) (H : CV) (θ : r₂.obj H ≅ r₁.obj GU)

/-- The map `r_2 H ⟶ r_2 r_V L_U G_U` whose double adjoint is the first map of the glueing
pushout: `θ`, then the unit of `L_U ⊣ r_U` restricted along `r_1`, then the two identifications
of restrictions. -/
def glueLeftAux : r₂.obj H ⟶ r₂.obj (rV.obj (LU.obj GU)) :=
  θ.hom ≫ r₁.map (adjU.unit.app GU) ≫ eU.hom.app (LU.obj GU) ≫ eV.inv.app (LU.obj GU)

/-- The first map `L_V L_2 r_2 H ⟶ L_U G_U` of the glueing pushout. -/
def glueLeft : LV.obj (L₂.obj (r₂.obj H)) ⟶ LU.obj GU :=
  (adjV.homEquiv _ _).symm
    ((adj₂.homEquiv _ _).symm (glueLeftAux rU rV r₁ r₂ rP eU eV adjU GU H θ))

/-- The second map `L_V L_2 r_2 H ⟶ L_V H` of the glueing pushout: `L_V` of the counit of
`L_2 ⊣ r_2`. -/
def glueRight : LV.obj (L₂.obj (r₂.obj H)) ⟶ LV.obj H :=
  LV.map (adj₂.counit.app H)

/-- The double adjoint of a map out of `L_V L_2 r_2 H` followed by a map out of `L_U G_U`. -/
theorem homEquiv_homEquiv_glueLeft_comp {T : CW} (g : LU.obj GU ⟶ T) :
    adj₂.homEquiv _ _
        (adjV.homEquiv _ _ (glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ ≫ g)) =
      θ.hom ≫ r₁.map (adjU.unit.app GU ≫ rU.map g) ≫ eU.hom.app T ≫ eV.inv.app T := by
  rw [glueLeft, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, glueLeftAux]
  simp only [Category.assoc, Functor.map_comp]
  have h₁ := eU.hom.naturality g
  have h₂ := eV.inv.naturality g
  simp only [Functor.comp_map] at h₁ h₂
  rw [← h₂, reassoc_of% h₁]

/-- The double adjoint of a map out of `L_V L_2 r_2 H` through `L_V H`. -/
theorem homEquiv_homEquiv_glueRight_comp {T : CW} (g : LV.obj H ⟶ T) :
    adj₂.homEquiv _ _ (adjV.homEquiv _ _ (glueRight r₂ adj₂ H ≫ g)) =
      r₂.map (adjV.homEquiv _ _ g) := by
  rw [glueRight, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit adj₂, Adjunction.right_triangle_components, Category.id_comp]

variable [HasPushout (glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ)
  (glueRight r₂ adj₂ H)]

/-- **The glued object**: the pushout of `CategoryTheory.GlueSquare.glueLeft` and
`CategoryTheory.GlueSquare.glueRight`. -/
abbrev glueObj : CW :=
  pushout (glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ) (glueRight r₂ adj₂ H)

/-- The comparison `α_U : G_U ⟶ r_U G`: the unit of `L_U ⊣ r_U` followed by the restriction of
the first coprojection. -/
def glueαU : GU ⟶ rU.obj (glueObj rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ) :=
  adjU.unit.app GU ≫ rU.map (pushout.inl (glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ)
    (glueRight r₂ adj₂ H))

/-- The comparison `α_V : H ⟶ r_V G`: the unit of `L_V ⊣ r_V` followed by the restriction of
the second coprojection. -/
def glueαV : H ⟶ rV.obj (glueObj rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ) :=
  adjV.unit.app H ≫ rV.map (pushout.inr (glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ)
    (glueRight r₂ adj₂ H))

/-- **The restriction of `α_V` to the intersection is `θ` followed by the restriction of
`α_U`**, read through the identifications `e_U` and `e_V`: this is the commutativity of the
glueing pushout, transported along the two adjunctions. -/
theorem r₂_map_glueαV :
    r₂.map (glueαV rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ) =
      θ.hom ≫ r₁.map (glueαU rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ) ≫
        eU.hom.app _ ≫ eV.inv.app _ := by
  have h := congrArg (fun k => adj₂.homEquiv _ _ (adjV.homEquiv _ _ k))
    (pushout.condition (f := glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ)
      (g := glueRight r₂ adj₂ H))
  rw [homEquiv_homEquiv_glueLeft_comp, homEquiv_homEquiv_glueRight_comp,
    Adjunction.homEquiv_unit] at h
  rw [glueαV, glueαU, h]

section Desc

variable (F : CW) (ψU : GU ⟶ rU.obj F) (ψV : H ⟶ rV.obj F)
  (hθ : θ.hom ≫ r₁.map ψU ≫ eU.hom.app F = r₂.map ψV ≫ eV.hom.app F)

omit [HasPushout (glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ) (glueRight r₂ adj₂ H)] in
include hθ in
/-- The adjoints of two maps `ψ_U : G_U ⟶ r_U F` and `ψ_V : H ⟶ r_V F` compatible with `θ`
agree on the source of the glueing pushout. -/
theorem glueLeft_comp_eq :
    glueLeft rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ ≫ (adjU.homEquiv _ _).symm ψU =
      glueRight r₂ adj₂ H ≫ (adjV.homEquiv _ _).symm ψV := by
  apply (adjV.homEquiv _ _).injective
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_homEquiv_glueLeft_comp, homEquiv_homEquiv_glueRight_comp, Equiv.apply_symm_apply,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, reassoc_of% hθ, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The map `ψ : G ⟶ F` out of the glued object induced by two maps compatible with `θ`. -/
def glueDesc : glueObj rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ ⟶ F :=
  pushout.desc ((adjU.homEquiv _ _).symm ψU) ((adjV.homEquiv _ _).symm ψV)
    (glueLeft_comp_eq rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ F ψU ψV hθ)

/-- **`α_U` followed by the restriction of `ψ` is `ψ_U`.** -/
theorem glueαU_comp_map_glueDesc :
    glueαU rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ ≫
        rU.map (glueDesc rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ F ψU ψV hθ) = ψU := by
  rw [glueαU, Category.assoc, ← Functor.map_comp, glueDesc, pushout.inl_desc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

/-- **`α_V` followed by the restriction of `ψ` is `ψ_V`.** -/
theorem glueαV_comp_map_glueDesc :
    glueαV rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ ≫
        rV.map (glueDesc rU rV r₁ r₂ rP eU eV adjU adjV adj₂ GU H θ F ψU ψV hθ) = ψV := by
  rw [glueαV, Category.assoc, ← Functor.map_comp, glueDesc, pushout.inr_desc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

end Desc

end CategoryTheory.GlueSquare

end
