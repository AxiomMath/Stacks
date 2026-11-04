module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedStagesElementarySquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelSquareGlueing

/-!
# Cubes of derived pullbacks on the spaces-étale models

A commutative cube of algebraic spaces — a top square `(W, U, V, P)`, a bottom square
`(W', U', V', P')` and vertical morphisms `g_• : •' ⟶ •` with commuting sides — gives six squares
of derived pullbacks on the models
(`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackSquareIso`). They are compatible: the
pullback along `g_P` of the top square, followed by the sides through `V`, is the sides through `U`
followed by the bottom square. In the language of `CategoryTheory.RestrictionSquare.Coherent`:
the squares of the sides are coherent comparisons of the restrictions of the top square with those
of the bottom one. This is the compatibility of the identifications over `P` with pullback that
both the transport of glueing along isomorphisms and the passage from a stage to the limit in
Stacks 09RJ use.

## Main results

* `AlgebraicGeometry.Space.coherent_spacesEtaleModelDerivedPullbackSquareIso`.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A square of derived pullbacks followed by the composition isomorphism of its lower path is
the composition isomorphism of its upper path. -/
theorem spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp {W W' Y Y' : AlgebraicSpaces B S hS}
    (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W) (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)
    (Z : DerivedCategory (spacesEtaleModelRingedTopos B S hS W).Modules) :
    (spacesEtaleModelDerivedPullbackSquareIso B S hS g h j j' comm).hom.app Z ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS j' g rfl Z).hom =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS h j comm Z).hom := by
  rw [spacesEtaleModelDerivedPullbackSquareIso_hom_app, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- `spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp` after a further derived pullback. -/
private theorem spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp_map
    {X W W' Y Y' : AlgebraicSpaces B S hS} (x : X ⟶ Y')
    (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W) (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)
    (Z : DerivedCategory (spacesEtaleModelRingedTopos B S hS W).Modules) :
    (derivedPullback.{u} (spacesEtaleModelHom B S hS x)).map
        ((spacesEtaleModelDerivedPullbackSquareIso B S hS g h j j' comm).hom.app Z) ≫
      (derivedPullback.{u} (spacesEtaleModelHom B S hS x)).map
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS j' g rfl Z).hom =
      (derivedPullback.{u} (spacesEtaleModelHom B S hS x)).map
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS h j comm Z).hom := by
  rw [← Functor.map_comp, spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp]

/-- The composition isomorphism `Lx^* Lp^* ≅ Lr^*` after `Lx^*` of `La^* Lb^* ≅ Lp^*` depends only
on `a`, `b`, `x` and `r`. -/
theorem spacesEtaleModelDerivedPullbackCompIsoOfEq_map_comp {X Y Z T : AlgebraicSpaces B S hS}
    (x : X ⟶ Y) (a : Y ⟶ Z) (b : Z ⟶ T) {p : Y ⟶ T} {r : X ⟶ T} (hp : a ≫ b = p)
    (hr : x ≫ p = r) (hr' : x ≫ a ≫ b = r)
    (F : DerivedCategory (spacesEtaleModelRingedTopos B S hS T).Modules) :
    (derivedPullback.{u} (spacesEtaleModelHom B S hS x)).map
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS a b hp F).hom ≫
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS x p hr F).hom =
    (derivedPullback.{u} (spacesEtaleModelHom B S hS x)).map
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS a b rfl F).hom ≫
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS x (a ≫ b) hr' F).hom := by
  subst hp
  rfl

variable {B S hS} {W U V P W' U' V' P' : AlgebraicSpaces B S hS}
  (jU : U ⟶ W) (jV : V ⟶ W) (jUP : P ⟶ U) (jVP : P ⟶ V) (cT : jUP ≫ jU = jVP ≫ jV)
  (jU' : U' ⟶ W') (jV' : V' ⟶ W') (jUP' : P' ⟶ U') (jVP' : P' ⟶ V') (cB : jUP' ≫ jU' = jVP' ≫ jV')
  (gW : W' ⟶ W) (gU : U' ⟶ U) (gV : V' ⟶ V) (gP : P' ⟶ P)
  (sU : gU ≫ jU = jU' ≫ gW) (sV : gV ≫ jV = jV' ≫ gW) (sUP : gP ≫ jUP = jUP' ≫ gU)
  (sVP : gP ≫ jVP = jVP' ≫ gV)

/-- Perfectness on the models transports along derived pullback and isomorphisms. -/
private theorem isPerfect_spacesEtaleModel_of_iso_derivedPullback {X Y : AlgebraicSpaces B S hS}
    (k : X ⟶ Y) {K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules}
    {L : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules}
    (e : (derivedPullback.{u} (spacesEtaleModelHom B S hS k)).obj K ≅ L)
    (hK : (spacesEtaleModelRingedSite B S hS Y).IsPerfect K) :
    (spacesEtaleModelRingedSite B S hS X).IsPerfect L :=
  let ⟨E, hE, ⟨i⟩⟩ := isPerfect_derivedPullback_spacesEtaleModelHom k K hK
  ⟨E, hE, ⟨i ≪≫ e⟩⟩

/-- **The squares of derived pullbacks of a commutative cube are compatible**: the squares of the
sides are coherent comparisons, in the sense of `CategoryTheory.RestrictionSquare.Coherent`,
between the square of the top face and the square of the bottom face. -/
theorem coherent_spacesEtaleModelDerivedPullbackSquareIso :
    RestrictionSquare.Coherent (eX := derivedPullback.{u} (spacesEtaleModelHom B S hS gW))
      (spacesEtaleModelDerivedPullbackSquareIso B S hS jV jUP jU jVP cT)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS jV' jUP' jU' jVP' cB)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS gW gU jU jU' sU)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS gW gV jV jV' sV)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS gU gP jUP jUP' sUP)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS gV gP jVP jVP' sVP) := by
  intro F
  have hr₁ : (jVP' ≫ jV') ≫ gW = jVP' ≫ jV' ≫ gW := Category.assoc _ _ _
  have hrV : (jVP' ≫ gV) ≫ jV = jVP' ≫ jV' ≫ gW := by rw [Category.assoc, sV]
  have hr₃ : jUP' ≫ jU' ≫ gW = jVP' ≫ jV' ≫ gW := by rw [← Category.assoc, cB, Category.assoc]
  have hrU : (jUP' ≫ gU) ≫ jU = jVP' ≫ jV' ≫ gW := by rw [Category.assoc, sU, hr₃]
  have hrP : gP ≫ jVP ≫ jV = jVP' ≫ jV' ≫ gW := by
    rw [← Category.assoc, sVP, Category.assoc, sV]
  have hrP' : gP ≫ jUP ≫ jU = jVP' ≫ jV' ≫ gW := by
    rw [← Category.assoc, sUP, Category.assoc, sU, hr₃]
  have L1 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp_map B S hS jVP' gW gV jV jV' sV F
  have L2 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS jVP' gV jV rfl sV hrV rfl F
  have L3 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp B S hS gV gP jVP jVP' sVP
    ((derivedPullback.{u} (spacesEtaleModelHom B S hS jV)).obj F)
  have L4 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS gP jVP jV sVP rfl hrV hrP F
  have L5 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp B S hS jV jUP jU jVP cT F
  have L6 := spacesEtaleModelDerivedPullbackCompIsoOfEq_map_comp B S hS gP jUP jU cT hrP hrP' F
  have R1 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS jVP' jV' gW rfl rfl hr₁ rfl F
  have R2 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp B S hS jV' jUP' jU' jVP' cB
    ((derivedPullback.{u} (spacesEtaleModelHom B S hS gW)).obj F)
  have R3 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS jUP' jU' gW cB rfl hr₁ hr₃ F
  have R4 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp_map B S hS jUP' gW gU jU jU' sU F
  have R5 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS jUP' gU jU rfl sU hrU hr₃ F
  have R6 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp B S hS gU gP jUP jUP' sUP
    ((derivedPullback.{u} (spacesEtaleModelHom B S hS jU)).obj F)
  have R7 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS gP jUP jU sUP rfl hrU hrP' F
  rw [← Iso.cancel_iso_hom_right _ _ ((derivedPullback.{u} (spacesEtaleModelHom B S hS jVP')).mapIso
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS jV' gW rfl F) ≪≫
      spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS jVP' (jV' ≫ gW) rfl F)]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% L1, L2, reassoc_of% L3, ← L4, ← Functor.map_comp_assoc, L5, L6, R1,
    reassoc_of% R2, ← R3, reassoc_of% R4, R5, reassoc_of% R6, ← R7]

/-- **The prism of derived pullbacks between two stages and the limit.** For a square
`tP ≫ j₁ = j' ≫ tU` between two stages, its pullback to the limit through the square of the later
stage and the comparisons `Lπ'^* Lt^* ≅ Lπ₁^*` is the square of the earlier stage. -/
theorem spacesEtaleModelDerivedPullbackSquareIso_prism {P' P₁ U' U₁ LP LU : AlgebraicSpaces B S hS}
    (tP : P' ⟶ P₁) (tU : U' ⟶ U₁) (j₁ : P₁ ⟶ U₁) (j' : P' ⟶ U') (jL : LP ⟶ LU)
    (πP' : LP ⟶ P') (πP₁ : LP ⟶ P₁) (πU' : LU ⟶ U') (πU₁ : LU ⟶ U₁)
    (e₀ : tP ≫ j₁ = j' ≫ tU) (e' : πP' ≫ j' = jL ≫ πU') (e₁ : πP₁ ≫ j₁ = jL ≫ πU₁)
    (eP : πP' ≫ tP = πP₁) (eU : πU' ≫ tU = πU₁)
    (A : DerivedCategory (spacesEtaleModelRingedTopos B S hS U₁).Modules) :
    (derivedPullback.{u} (spacesEtaleModelHom B S hS πP')).map
        ((spacesEtaleModelDerivedPullbackSquareIso B S hS tU tP j₁ j' e₀).hom.app A) ≫
      (spacesEtaleModelDerivedPullbackSquareIso B S hS πU' πP' j' jL e').hom.app
        ((derivedPullback.{u} (spacesEtaleModelHom B S hS tU)).obj A) ≫
      (derivedPullback.{u} (spacesEtaleModelHom B S hS jL)).map
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πU' tU eU A).hom =
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πP' tP eP
        ((derivedPullback.{u} (spacesEtaleModelHom B S hS j₁)).obj A)).hom ≫
      (spacesEtaleModelDerivedPullbackSquareIso B S hS πU₁ πP₁ j₁ jL e₁).hom.app A := by
  rw [← Iso.cancel_iso_hom_right _ _
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS jL πU₁ rfl A)]
  have hr : (jL ≫ πU') ≫ tU = jL ≫ πU₁ := by rw [Category.assoc, eU]
  have hr₁ : πP' ≫ tP ≫ j₁ = jL ≫ πU₁ := by rw [← Category.assoc, eP, e₁]
  have hr₂ : πP' ≫ j' ≫ tU = jL ≫ πU₁ := by rw [← Category.assoc, e', hr]
  have L1 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS jL πU' tU rfl eU hr rfl A
  have L2 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp B S hS πU' πP' j' jL e'
    ((derivedPullback.{u} (spacesEtaleModelHom B S hS tU)).obj A)
  have L3 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS πP' j' tU e' rfl hr hr₂ A
  have L4 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp_map B S hS πP' tU tP j₁ j' e₀ A
  have L5 := spacesEtaleModelDerivedPullbackCompIsoOfEq_map_comp B S hS πP' tP j₁ e₀ hr₂ hr₁ A
  have R1 := spacesEtaleModelDerivedPullbackSquareIso_hom_app_comp B S hS πU₁ πP₁ j₁ jL e₁ A
  have R2 := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS πP' tP j₁ eP rfl e₁ hr₁ A
  simp only [Category.assoc]
  rw [L1, reassoc_of% L2, ← L3, reassoc_of% L4, L5, R1, ← R2]

section IsoSquare

variable (B S hS) in
/-- **Derived pullback along an isomorphism of algebraic spaces is an equivalence** on the models,
with inverse the derived pullback along the inverse. -/
def spacesEtaleModelDerivedPullbackEquivalence {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y)
    [IsIso k] :
    DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules ≌
      DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules :=
  CategoryTheory.Equivalence.mk (derivedPullback.{u} (spacesEtaleModelHom B S hS k))
    (derivedPullback.{u} (spacesEtaleModelHom B S hS (inv k)))
    (spacesEtaleModelDerivedPullbackCompIso B S hS (inv k) k ≪≫
      spacesEtaleModelDerivedPullbackCongr B S hS (IsIso.inv_hom_id k) ≪≫
        spacesEtaleModelDerivedPullbackIdIso B S hS Y).symm
    (spacesEtaleModelDerivedPullbackCompIso B S hS k (inv k) ≪≫
      spacesEtaleModelDerivedPullbackCongr B S hS (IsIso.hom_inv_id k) ≪≫
        spacesEtaleModelDerivedPullbackIdIso B S hS X)

/-- Derived pullback along an isomorphism of algebraic spaces is an equivalence on the models. -/
instance isEquivalence_derivedPullback_spacesEtaleModelHom {X Y : AlgebraicSpaces B S hS}
    (k : X ⟶ Y) [IsIso k] : (derivedPullback.{u} (spacesEtaleModelHom B S hS k)).IsEquivalence :=
  (spacesEtaleModelDerivedPullbackEquivalence B S hS k).isEquivalence_functor

variable {Wo : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor Wo.1} {fV : Ve ⟶ Wo.1}
  (hsq : IsElementaryDistinguishedSquare B S hS Wo.2 Uo fV)
  {U₁ V₁ P₁ : AlgebraicSpaces B S hS} (iU : U₁ ⟶ Wo) (iV : V₁ ⟶ Wo) (iUP : P₁ ⟶ U₁)
  (iVP : P₁ ⟶ V₁) (cS : iUP ≫ iU = iVP ≫ iV)
  (τU : edsOpen B S hS hsq ⟶ U₁) (τV : edsEtale B S hS hsq ⟶ V₁) (τP : edsInter B S hS hsq ⟶ P₁)
  [IsIso τU] [IsIso τV] [IsIso τP]
  (hU : τU ≫ iU = edsOpenHom B S hS hsq) (hV : τV ≫ iV = edsEtaleHom B S hS hsq)
  (hUP : τP ≫ iUP = edsFst B S hS hsq ≫ τU) (hVP : τP ≫ iVP = edsSnd B S hS hsq ≫ τV)

omit [IsIso τU] [IsIso τV] [IsIso τP] in
include hU hV hUP hVP in
/-- The cube between a square isomorphic to an elementary distinguished square and that square. -/
theorem coherent_spacesEtaleModel_isoEds :
    RestrictionSquare.Coherent (eX := derivedPullback.{u} (spacesEtaleModelHom B S hS (𝟙 Wo)))
      (spacesEtaleModelDerivedPullbackSquareIso B S hS iV iUP iU iVP cS)
      (spacesEtaleModelEdsSquareIso B S hS hsq)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS (𝟙 Wo) τU iU (edsOpenHom B S hS hsq)
        (by rw [hU, Category.comp_id]))
      (spacesEtaleModelDerivedPullbackSquareIso B S hS (𝟙 Wo) τV iV (edsEtaleHom B S hS hsq)
        (by rw [hV, Category.comp_id]))
      (spacesEtaleModelDerivedPullbackSquareIso B S hS τU τP iUP (edsFst B S hS hsq) hUP)
      (spacesEtaleModelDerivedPullbackSquareIso B S hS τV τP iVP (edsSnd B S hS hsq) hVP) :=
  coherent_spacesEtaleModelDerivedPullbackSquareIso iU iV iUP iVP cS (edsOpenHom B S hS hsq)
    (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsSnd B S hS hsq)
    (isPullback_edsInter B S hS hsq).w (𝟙 Wo) τU τV τP _ _ hUP hVP

include hU hV hUP hVP in
/-- **Stacks 08HB, glueing of morphisms, on the models, for a square isomorphic to an elementary
distinguished square**, given the compatibility of the comparisons of Stacks 03G1 with
composition. -/
theorem homsGlue_spacesEtaleModel_isoEds (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.HomsGlue _ _ _ _
      (spacesEtaleModelDerivedPullbackSquareIso B S hS iV iUP iU iVP cS) :=
  (homsGlue_spacesEtaleModel_eds hsq hT).transport
    (coherent_spacesEtaleModel_isoEds hsq iU iV iUP iVP cS τU τV τP hU hV hUP hVP)

include hU hV hUP hVP in
/-- **Stacks 08HB, glueing of objects, on the models, for a square isomorphic to an elementary
distinguished square**, given the compatibility of the comparisons of Stacks 03G1 with
composition. -/
theorem objectsGlue_spacesEtaleModel_isoEds (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.ObjectsGlue _ _ _ _
      (spacesEtaleModelDerivedPullbackSquareIso B S hS iV iUP iU iVP cS) :=
  (objectsGlue_spacesEtaleModel_eds hsq hT).transport
    (coherent_spacesEtaleModel_isoEds hsq iU iV iUP iVP cS τU τV τP hU hV hUP hVP)

omit [IsIso τU] [IsIso τV] in
include hU hV in
/-- The derived pullbacks to the two members of a square isomorphic to an elementary distinguished
square jointly reflect isomorphisms. -/
theorem reflectsIso_spacesEtaleModel_isoEds :
    RestrictionSquare.ReflectsIso (derivedPullback.{u} (spacesEtaleModelHom B S hS iU))
      (derivedPullback.{u} (spacesEtaleModelHom B S hS iV)) :=
  (reflectsIso_spacesEtaleModel_eds B S hS hsq).transport
    (spacesEtaleModelDerivedPullbackSquareIso B S hS (𝟙 Wo) τU iU (edsOpenHom B S hS hsq)
      (by rw [hU, Category.comp_id]))
    (spacesEtaleModelDerivedPullbackSquareIso B S hS (𝟙 Wo) τV iV (edsEtaleHom B S hS hsq)
      (by rw [hV, Category.comp_id]))

omit [IsIso τU] [IsIso τV] in
include hU hV in
/-- Perfectness on the models is checked on the two members of a square isomorphic to an
elementary distinguished square. -/
theorem isPerfect_of_isPerfect_spacesEtaleModel_isoEds
    (F : DerivedCategory (spacesEtaleModelRingedTopos B S hS Wo).Modules)
    (hFU : (spacesEtaleModelRingedSite B S hS U₁).IsPerfect
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS iU)).obj F))
    (hFV : (spacesEtaleModelRingedSite B S hS V₁).IsPerfect
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS iV)).obj F)) :
    (spacesEtaleModelRingedSite B S hS Wo).IsPerfect F :=
  isPerfect_of_isPerfect_spacesEtaleModel_eds B S hS hsq F
    (isPerfect_spacesEtaleModel_of_iso_derivedPullback τU
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS τU iU hU F) hFU)
    (isPerfect_spacesEtaleModel_of_iso_derivedPullback τV
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS τV iV hV F) hFV)

end IsoSquare

section BaseChangeOver

variable {X₀ W₀ V₀ T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {w : W₀ ⟶ X₀} {U : Subfunctor W₀}
  {f : V₀ ⟶ W₀} {hW₀ : IsAlgebraicSpace B S hS W₀}
  (hsq : IsElementaryDistinguishedSquare B S hS hW₀ U f) (p : T ⟶ X₀)
  (hWp : IsAlgebraicSpace B S hS (pullback p w))
  (hUp : IsAlgebraicSpace B S hS (pullback p (U.ι ≫ w)))
  (hVp : IsAlgebraicSpace B S hS (pullback p (f ≫ w)))
  (hPp : IsAlgebraicSpace B S hS (pullback p (pullback.fst U.ι f ≫ U.ι ≫ w)))

include hsq in
/-- **Stacks 08HB, glueing of objects, on the models, for the base change over `T ⟶ X₀` of an
elementary distinguished square over `X₀`**, given the compatibility of the comparisons of
Stacks 03G1 with composition. -/
theorem objectsGlue_spacesEtaleModel_baseChangeOver
    (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.ObjectsGlue _ _ _ _
      (spacesEtaleModelDerivedPullbackSquareIso B S hS
        (baseChangeOverEtaleHom B S hS w f p hVp hWp)
        (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
        (baseChangeOverOpenHom B S hS w U p hUp hWp)
        (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
        (baseChangeOverInterFstHom_comp_openHom B S hS w U f p hWp hUp hVp hPp)) :=
  objectsGlue_spacesEtaleModel_isoEds
    (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp)
    _ _ _ _ _ (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom
    (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom
    (baseChangeOverEdsInterIso B S hS hsq p hWp hPp).hom
    (baseChangeOverEdsOpenIso_hom_comp B S hS hsq p hWp hUp)
    (baseChangeOverEdsEtaleIso_hom_comp B S hS hsq p hWp hVp)
    (baseChangeOverEdsInterIso_hom_comp_fst B S hS hsq p hWp hUp hPp)
    (baseChangeOverEdsInterIso_hom_comp_snd B S hS hsq p hWp hVp hPp) hT

include hsq in
/-- **Stacks 08HB, glueing of morphisms, on the models, for the base change over `T ⟶ X₀` of an
elementary distinguished square over `X₀`**, given the compatibility of the comparisons of
Stacks 03G1 with composition. -/
theorem homsGlue_spacesEtaleModel_baseChangeOver
    (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) :
    RestrictionSquare.HomsGlue _ _ _ _
      (spacesEtaleModelDerivedPullbackSquareIso B S hS
        (baseChangeOverEtaleHom B S hS w f p hVp hWp)
        (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
        (baseChangeOverOpenHom B S hS w U p hUp hWp)
        (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
        (baseChangeOverInterFstHom_comp_openHom B S hS w U f p hWp hUp hVp hPp)) :=
  homsGlue_spacesEtaleModel_isoEds
    (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp)
    _ _ _ _ _ (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom
    (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom
    (baseChangeOverEdsInterIso B S hS hsq p hWp hPp).hom
    (baseChangeOverEdsOpenIso_hom_comp B S hS hsq p hWp hUp)
    (baseChangeOverEdsEtaleIso_hom_comp B S hS hsq p hWp hVp)
    (baseChangeOverEdsInterIso_hom_comp_fst B S hS hsq p hWp hUp hPp)
    (baseChangeOverEdsInterIso_hom_comp_snd B S hS hsq p hWp hVp hPp) hT

include hsq in
/-- The derived pullbacks to the two members of the base change over `T ⟶ X₀` of an elementary
distinguished square jointly reflect isomorphisms. -/
theorem reflectsIso_spacesEtaleModel_baseChangeOver :
    RestrictionSquare.ReflectsIso
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverOpenHom B S hS w U p hUp hWp)))
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverEtaleHom B S hS w f p hVp hWp))) :=
  reflectsIso_spacesEtaleModel_isoEds
    (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp)
    (iU := baseChangeOverOpenHom B S hS w U p hUp hWp)
    (iV := baseChangeOverEtaleHom B S hS w f p hVp hWp)
    (τU := (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom)
    (τV := (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom)
    (baseChangeOverEdsOpenIso_hom_comp B S hS hsq p hWp hUp)
    (baseChangeOverEdsEtaleIso_hom_comp B S hS hsq p hWp hVp)

include hsq in
/-- Perfectness on the models is checked on the two members of the base change over `T ⟶ X₀` of an
elementary distinguished square. -/
theorem isPerfect_of_isPerfect_spacesEtaleModel_baseChangeOver
    (F : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p w, hWp⟩).Modules)
    (hFU : (spacesEtaleModelRingedSite B S hS ⟨pullback p (U.ι ≫ w), hUp⟩).IsPerfect
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverOpenHom B S hS w U p hUp hWp))).obj F))
    (hFV : (spacesEtaleModelRingedSite B S hS ⟨pullback p (f ≫ w), hVp⟩).IsPerfect
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverEtaleHom B S hS w f p hVp hWp))).obj F)) :
    (spacesEtaleModelRingedSite B S hS ⟨pullback p w, hWp⟩).IsPerfect F :=
  isPerfect_of_isPerfect_spacesEtaleModel_isoEds
    (isElementaryDistinguishedSquare_baseChangeOver B S hS hsq p hWp)
    (iU := baseChangeOverOpenHom B S hS w U p hUp hWp)
    (iV := baseChangeOverEtaleHom B S hS w f p hVp hWp)
    (τU := (baseChangeOverEdsOpenIso B S hS hsq p hWp hUp).hom)
    (τV := (baseChangeOverEdsEtaleIso B S hS hsq p hWp hVp).hom)
    (baseChangeOverEdsOpenIso_hom_comp B S hS hsq p hWp hUp)
    (baseChangeOverEdsEtaleIso_hom_comp B S hS hsq p hWp hVp) F hFU hFV

/-- The isomorphism over `T ×_{X₀} P₀` between the pullbacks of the restrictions to
`T₁ ×_{X₀} P₀` of `A` and `Bo`, given identifications `αU`, `αV` of their pullbacks to `T` with
the restrictions of `E`: the comparison of `αU` and `αV` through the square of `T`. -/
def spacesEtaleModelBaseChangeOverInterIso {T₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p₁ : T₁ ⟶ X₀)
    (a₁ : T ⟶ T₁) (ha₁ : a₁ ≫ p₁ = p)
    (hUp₁ : IsAlgebraicSpace B S hS (pullback p₁ (U.ι ≫ w)))
    (hVp₁ : IsAlgebraicSpace B S hS (pullback p₁ (f ≫ w)))
    (hPp₁ : IsAlgebraicSpace B S hS (pullback p₁ (pullback.fst U.ι f ≫ U.ι ≫ w)))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p w, hWp⟩).Modules)
    (A : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p₁ (U.ι ≫ w), hUp₁⟩).Modules)
    (Bo : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p₁ (f ≫ w), hVp₁⟩).Modules)
    (αU : (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hUp hUp₁))).obj A ≅
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverOpenHom B S hS w U p hUp hWp))).obj E)
    (αV : (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hVp hVp₁))).obj Bo ≅
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverEtaleHom B S hS w f p hVp hWp))).obj E) :
    (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁))).obj
        ((derivedPullback.{u} (spacesEtaleModelHom B S hS
          (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁))).obj A) ≅
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁))).obj
        ((derivedPullback.{u} (spacesEtaleModelHom B S hS
          (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁))).obj Bo) :=
  (spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hUp hUp₁)
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁)
      (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁)
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p p₁ a₁ ha₁ hUp hUp₁ hPp hPp₁)).app A ≪≫
    (derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp))).mapIso αU ≪≫
    (spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverEtaleHom B S hS w f p hVp hWp)
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverOpenHom B S hS w U p hUp hWp)
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverInterFstHom_comp_openHom B S hS w U f p hWp hUp hVp hPp)).app E ≪≫
    (derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp))).mapIso αV.symm ≪≫
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hVp hVp₁)
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁)
      (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁)
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p p₁ a₁ ha₁ hVp hVp₁ hPp hPp₁)).app
        Bo).symm

include hsq in
/-- **The step of Stacks 09RJ across an elementary distinguished square, between stages.** Let
`T ⟶ T' ⟶ T₁` be morphisms over `X₀` (a limit, a later and an earlier stage). Let `E` be an object
on `T ×_{X₀} W₀`, and `A`, `Bo` perfect objects on `T₁ ×_{X₀} U` and `T₁ ×_{X₀} V₀` whose
pullbacks to `T` are identified with the restrictions of `E` by `αU`, `αV`. If an isomorphism `ψ`
between the pullbacks to `T'` of the restrictions of `A` and `Bo` to `T₁ ×_{X₀} P₀` pulls back to
`T` to the comparison of `αU` and `αV` through the square of `T`, then `E` is the pullback of a
perfect object on `T' ×_{X₀} W₀`. -/
theorem exists_isPerfect_iso_spacesEtaleModel_baseChangeOver
    (hT : SpacesEtaleModelEtaleTransportCoherent B S hS) {T' T₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p' : T' ⟶ X₀) (p₁ : T₁ ⟶ X₀) (a : T ⟶ T') (a' : T' ⟶ T₁) (a₁ : T ⟶ T₁)
    (ha : a ≫ p' = p) (ha' : a' ≫ p₁ = p') (ha₁ : a₁ ≫ p₁ = p) (hcomp : a ≫ a' = a₁)
    (hWp' : IsAlgebraicSpace B S hS (pullback p' w))
    (hUp' : IsAlgebraicSpace B S hS (pullback p' (U.ι ≫ w)))
    (hVp' : IsAlgebraicSpace B S hS (pullback p' (f ≫ w)))
    (hPp' : IsAlgebraicSpace B S hS (pullback p' (pullback.fst U.ι f ≫ U.ι ≫ w)))
    (hUp₁ : IsAlgebraicSpace B S hS (pullback p₁ (U.ι ≫ w)))
    (hVp₁ : IsAlgebraicSpace B S hS (pullback p₁ (f ≫ w)))
    (hPp₁ : IsAlgebraicSpace B S hS (pullback p₁ (pullback.fst U.ι f ≫ U.ι ≫ w)))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p w, hWp⟩).Modules)
    (A : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p₁ (U.ι ≫ w), hUp₁⟩).Modules)
    (Bo : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p₁ (f ≫ w), hVp₁⟩).Modules)
    (hA : (spacesEtaleModelRingedSite B S hS ⟨pullback p₁ (U.ι ≫ w), hUp₁⟩).IsPerfect A)
    (hBo : (spacesEtaleModelRingedSite B S hS ⟨pullback p₁ (f ≫ w), hVp₁⟩).IsPerfect Bo)
    (αU : (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hUp hUp₁))).obj A ≅
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverOpenHom B S hS w U p hUp hWp))).obj E)
    (αV : (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hVp hVp₁))).obj Bo ≅
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverEtaleHom B S hS w f p hVp hWp))).obj E)
    (ψ : (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁))).obj
          ((derivedPullback.{u} (spacesEtaleModelHom B S hS
            (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁))).obj A) ≅
      (derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁))).obj
          ((derivedPullback.{u} (spacesEtaleModelHom B S hS
            (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁))).obj Bo))
    (hψ : (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
          (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
          (baseChangeOverMapHom_comp B S hS p p' p₁ a a' a₁ ha ha' ha₁ hcomp _ hPp hPp' hPp₁)
          ((derivedPullback.{u} (spacesEtaleModelHom B S hS
            (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁))).obj A)).inv ≫
        (derivedPullback.{u} (spacesEtaleModelHom B S hS
          (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp'))).map ψ.hom ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
          (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
          (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
          (baseChangeOverMapHom_comp B S hS p p' p₁ a a' a₁ ha ha' ha₁ hcomp _ hPp hPp' hPp₁)
          ((derivedPullback.{u} (spacesEtaleModelHom B S hS
            (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁))).obj Bo)).hom =
      (spacesEtaleModelBaseChangeOverInterIso p hWp hUp hVp hPp p₁ a₁ ha₁ hUp₁ hVp₁ hPp₁ E A Bo αU
        αV).hom) :
    ∃ F : DerivedCategory (spacesEtaleModelRingedTopos B S hS ⟨pullback p' w, hWp'⟩).Modules,
      (spacesEtaleModelRingedSite B S hS ⟨pullback p' w, hWp'⟩).IsPerfect F ∧
        Nonempty ((derivedPullback.{u} (spacesEtaleModelHom B S hS
          (baseChangeOverMapHom B S hS p p' a ha w hWp hWp'))).obj F ≅ E) := by
  have eU := baseChangeOverMapHom_comp B S hS p p' p₁ a a' a₁ ha ha' ha₁ hcomp _ hUp hUp' hUp₁
  have eV := baseChangeOverMapHom_comp B S hS p p' p₁ a a' a₁ ha ha' ha₁ hcomp _ hVp hVp' hVp₁
  have eP := baseChangeOverMapHom_comp B S hS p p' p₁ a a' a₁ ha ha' ha₁ hcomp _ hPp hPp' hPp₁
  have hc := RestrictionSquare.compat_of_stageTransition
    (derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)))
    (derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)))
    (derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')))
    αU αV
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hUp hUp')
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁) eU A)
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hVp hVp')
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁) eV Bo)
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverEtaleHom B S hS w f p hVp hWp)
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverOpenHom B S hS w U p hUp hWp)
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverInterFstHom_comp_openHom B S hS w U f p hWp hUp hVp hPp)).hom.app E)
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hUp hUp₁)
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁)
      (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁)
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p p₁ a₁ ha₁ hUp hUp₁ hPp hPp₁)).app A)
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hVp hVp₁)
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁)
      (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁)
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p p₁ a₁ ha₁ hVp hVp₁ hPp hPp₁)).app Bo)
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁) eP
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁))).obj A))
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁) eP
      ((derivedPullback.{u} (spacesEtaleModelHom B S hS
        (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁))).obj Bo))
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁)
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
      (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁)
      (baseChangeOverInterFstHom B S hS w U f p' hPp' hUp')
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p' p₁ a' ha' hUp' hUp₁ hPp' hPp₁)).app A)
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁)
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
      (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁)
      (baseChangeOverInterSndHom B S hS w U f p' hPp' hVp')
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p' p₁ a' ha' hVp' hVp₁ hPp' hPp₁)).app Bo)
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hUp hUp')
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverInterFstHom B S hS w U f p' hPp' hUp')
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p p' a ha hUp hUp' hPp hPp')).app
        ((derivedPullback.{u} (spacesEtaleModelHom B S hS
          (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁))).obj A))
    ((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hVp hVp')
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverInterSndHom B S hS w U f p' hPp' hVp')
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p p' a ha hVp hVp' hPp hPp')).app
        ((derivedPullback.{u} (spacesEtaleModelHom B S hS
          (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁))).obj Bo)) ψ
    (spacesEtaleModelDerivedPullbackSquareIso_prism
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁)
      (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁)
      (baseChangeOverInterFstHom B S hS w U f p' hPp' hUp')
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁)
      (baseChangeOverMapHom B S hS p p' a ha _ hUp hUp')
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hUp hUp₁)
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p' p₁ a' ha' hUp' hUp₁ hPp' hPp₁)
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p p' a ha hUp hUp' hPp hPp')
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p p₁ a₁ ha₁ hUp hUp₁ hPp hPp₁) eP eU A)
    (spacesEtaleModelDerivedPullbackSquareIso_prism
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁)
      (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁)
      (baseChangeOverInterSndHom B S hS w U f p' hPp' hVp')
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hPp hPp₁)
      (baseChangeOverMapHom B S hS p p' a ha _ hVp hVp')
      (baseChangeOverMapHom B S hS p p₁ a₁ ha₁ _ hVp hVp₁)
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p' p₁ a' ha' hVp' hVp₁ hPp' hPp₁)
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p p' a ha hVp hVp' hPp hPp')
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p p₁ a₁ ha₁ hVp hVp₁ hPp hPp₁) eP eV Bo)
    hψ
  obtain ⟨F, fU, fV, ⟨e⟩⟩ := RestrictionSquare.exists_iso_of_objectsGlue_of_homsGlue
    (objectsGlue_spacesEtaleModel_baseChangeOver hsq p' hWp' hUp' hVp' hPp' hT)
    (homsGlue_spacesEtaleModel_baseChangeOver hsq p hWp hUp hVp hPp hT)
    (reflectsIso_spacesEtaleModel_baseChangeOver hsq p hWp hUp hVp)
    (coherent_spacesEtaleModelDerivedPullbackSquareIso
      (baseChangeOverOpenHom B S hS w U p' hUp' hWp')
      (baseChangeOverEtaleHom B S hS w f p' hVp' hWp')
      (baseChangeOverInterFstHom B S hS w U f p' hPp' hUp')
      (baseChangeOverInterSndHom B S hS w U f p' hPp' hVp')
      (baseChangeOverInterFstHom_comp_openHom B S hS w U f p' hWp' hUp' hVp' hPp')
      (baseChangeOverOpenHom B S hS w U p hUp hWp)
      (baseChangeOverEtaleHom B S hS w f p hVp hWp)
      (baseChangeOverInterFstHom B S hS w U f p hPp hUp)
      (baseChangeOverInterSndHom B S hS w U f p hPp hVp)
      (baseChangeOverInterFstHom_comp_openHom B S hS w U f p hWp hUp hVp hPp)
      (baseChangeOverMapHom B S hS p p' a ha w hWp hWp')
      (baseChangeOverMapHom B S hS p p' a ha _ hUp hUp')
      (baseChangeOverMapHom B S hS p p' a ha _ hVp hVp')
      (baseChangeOverMapHom B S hS p p' a ha _ hPp hPp')
      (baseChangeOverMapHom_comp_openHom B S hS w U p p' a ha hWp hWp' hUp hUp')
      (baseChangeOverMapHom_comp_etaleHom B S hS w f p p' a ha hWp hWp' hVp hVp')
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p p' a ha hUp hUp' hPp hPp')
      (baseChangeOverMapHom_comp_interSndHom B S hS w U f p p' a ha hVp hVp' hPp hPp'))
    E
    ((derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁))).obj A)
    ((derivedPullback.{u} (spacesEtaleModelHom B S hS
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁))).obj Bo)
    ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hUp hUp')
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁) eU A) ≪≫ αU)
    ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
      (baseChangeOverMapHom B S hS p p' a ha _ hVp hVp')
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁) eV Bo) ≪≫ αV)
    (((spacesEtaleModelDerivedPullbackSquareIso B S hS
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hUp' hUp₁)
      (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
      (baseChangeOverInterFstHom B S hS w U f p₁ hPp₁ hUp₁)
      (baseChangeOverInterFstHom B S hS w U f p' hPp' hUp')
      (baseChangeOverMapHom_comp_interFstHom B S hS w U f p' p₁ a' ha' hUp' hUp₁ hPp' hPp₁)).app
        A).symm ≪≫ ψ ≪≫
      ((spacesEtaleModelDerivedPullbackSquareIso B S hS
        (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hVp' hVp₁)
        (baseChangeOverMapHom B S hS p' p₁ a' ha' _ hPp' hPp₁)
        (baseChangeOverInterSndHom B S hS w U f p₁ hPp₁ hVp₁)
        (baseChangeOverInterSndHom B S hS w U f p' hPp' hVp')
        (baseChangeOverMapHom_comp_interSndHom B S hS w U f p' p₁ a' ha' hVp' hVp₁ hPp'
          hPp₁)).app Bo)) hc
  exact ⟨F, isPerfect_of_isPerfect_spacesEtaleModel_baseChangeOver hsq p' hWp' hUp' hVp' F
    (isPerfect_spacesEtaleModel_of_iso_derivedPullback _ fU.symm hA)
    (isPerfect_spacesEtaleModel_of_iso_derivedPullback _ fV.symm hBo), ⟨e⟩⟩

end BaseChangeOver

end AlgebraicGeometry.Space

end
