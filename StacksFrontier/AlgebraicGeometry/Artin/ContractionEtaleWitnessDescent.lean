module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleCompletionCover
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessComparison
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification

/-!
# Étale descent of the compatibility condition of Artin's contraction functor

In the situation of Stacks 0GH8 a triple `(Z, u', x̂)` over `V` is compatible when there is a
witness `V' ⟶ V`, `x̂'`, `x'`
(`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness`). This file proves that
compatibility descends along an étale covering `{V_i ⟶ V}` of the locally Noetherian site,
for a pair `(u', x̂)` with `x̂` adic: if the restriction of `(u', x̂)` to every `V_i` is
compatible, so is `(u', x̂)`.

This is the place where the source's hint for Stacks 0GHG, that "morphisms may be defined étale
locally", carries the argument; the witness over `V` is assembled as follows.

1. *The dilatation.* As `x̂` is adic and `V_{/Z}` is locally Noetherian, the base change of the
   formal modification `g` along `x̂` is a formal modification of `V_{/Z}` (Stacks 0GDN), so the
   existence half of the main theorem on dilatations (Stacks 0GDU) produces a proper
   `p : V' ⟶ V` which is an isomorphism over `V ∖ Z` and whose completion along `Z` is that
   base change. The data `V' ⟶ V`, `V ∖ Z ⟶ V'` and `x̂'` without the morphism `x'` are
   recorded as `AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness`.
2. *The morphism `x'` locally.* Over `V_i` the base change `V_i ×_V V'` and the given witness
   over `V_i` are two dilatations of the same formal modification, so the uniqueness half of
   Stacks 0GDU gives a morphism between them compatible with everything
   (`AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness.exists_hom`); composing
   the witness's `x'_i` with it gives a morphism `V_i ×_V V' ⟶ X'` with the two required
   restrictions.
3. *Glueing.* On the overlaps `V_{ij} ×_V V'` the two morphisms so obtained have the same
   restriction to the complement of the inverse image of `Z` and to the completion along it, so
   they agree by the uniqueness statement of Stacks 0GI1
   (`AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness.hom_ext`). As `X'` is an fppf
   sheaf and the `V_i ×_V V'` cover `V'`, they glue to `x' : V' ⟶ X'`.
4. *The two conditions on `x'`* are equalities of morphisms out of `V ∖ Z` and out of
   `V'_{/Z}`; they hold after restriction to the members of the covering families
   `{V_i ∖ Z_i}` and `{(V_i ×_V V')_{/Z}}`, hence hold.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness`: a compatibility witness
  without its morphism `x'`.
* `AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness.pullback`: its base change.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness.exists_hom`: two such data
  over a locally Noetherian base are comparable (Stacks 0GDU, uniqueness).
* `AlgebraicGeometry.Artin.ContractionSituation.DilatationWitness.hom_ext`: a morphism out of
  `V'` is determined by its restrictions to `V ∖ Z` and to `V'_{/Z}` (Stacks 0GI1).
* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_dilatationWitness`: the datum exists
  for an adic `x̂` over a locally Noetherian base (Stacks 0GDN and 0GDU, existence).
* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_of_isEtaleCovering`:
  the compatibility condition descends along étale coverings of the locally Noetherian site.

## References

* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin

attribute [local instance] Space.pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of fppf sheaves times out at the default budget
/-- Pullbacks of fppf sheaves (in `Type (u + 1)`, where completions live), found once: instance
search for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_ContractionEtaleWitnessDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) := by
  infer_instance

local instance (priority := high) hasLimit_cospan_sheaf_ContractionEtaleWitnessDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site times out at the default
-- budget
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_ContractionEtaleWitnessDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := by
  infer_instance

local instance (priority := high) hasLimit_cospan_presheaf_ContractionEtaleWitnessDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS}

/-- In the situation of Stacks 0GH8, the part of a compatibility witness that does not involve
the morphism `x'`: a proper morphism `p : V' ⟶ V` of algebraic spaces which is an isomorphism
over `V ∖ Z` (recorded as `isPullback_j`) and whose completion along `Z` is the pullback of the
formal modification `g` along `x̂` (recorded as `isPullback_xhat'`). By the main theorem on
dilatations (Stacks 0GDU) such a datum exists over a locally Noetherian `V` as soon as `x̂` is
adic, and it is unique up to unique isomorphism. -/
structure DilatationWitness (c : ContractionSituation B S hS) (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V)))
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W) where
  /-- The algebraic space `V'` over `S`. -/
  V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `V'` is an algebraic space over `S`. -/
  isAlgebraicSpace_V' : IsAlgebraicSpace B S hS V'
  /-- The morphism `p : V' ⟶ V`. -/
  p : V' ⟶ yoneda.obj V
  /-- `p` is proper. -/
  isProper_p : Space.IsProper B S hS p
  /-- The morphism `j : V ∖ Z ⟶ V'`. -/
  j : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ V'
  /-- `p` is an isomorphism over `V ∖ Z`, with `j` as the identification. -/
  isPullback_j : IsPullback (𝟙 _) j
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι p
  /-- The morphism `x̂' : V'_{/Z} ⟶ X'_{/T'}`. -/
  xhat' : Space.completionSheaf B S hS V' (Space.pointsMap B S hS V' p ⁻¹' Z) ⟶
    Space.completionSheaf B S hS c.X' c.T'
  /-- The completion of `p` along `Z` is the pullback of `g` along `x̂`. -/
  isPullback_xhat' : IsPullback
    (Space.completionSheafRestrict B S hS p (Space.pointsMap B S hS V' p ⁻¹' Z) Z
      fun _ hz => hz) xhat' xhat c.g

/-- The datum of a compatibility witness that does not involve `x'`. -/
def CompatibilityWitness.toDilatationWitness {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (ω : CompatibilityWitness c V Z u xhat) : DilatationWitness c V Z xhat where
  V' := ω.V'
  isAlgebraicSpace_V' := ω.isAlgebraicSpace_V'
  p := ω.p
  isProper_p := ω.isProper_p
  j := ω.j
  isPullback_j := ω.isPullback_j
  xhat' := ω.xhat'
  isPullback_xhat' := ω.isPullback_xhat'

/-- A datum `V' ⟶ V`, `j`, `x̂'` together with a morphism `x' : V' ⟶ X'` restricting to `u'`
over `V ∖ Z` and to `x̂'` over `V'_{/Z}` is a compatibility witness. -/
def CompatibilityWitness.ofDilatationWitness {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (D : DilatationWitness c V Z xhat) (x' : D.V' ⟶ c.X') (hu : D.j ≫ x' = u ≫ c.U'.ι)
    (hx : Space.completionSheafInclusion B S hS D.V' (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) ≫
        Space.sheafifiedULiftMap B S hS x' =
      D.xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T') :
    CompatibilityWitness c V Z u xhat where
  V' := D.V'
  isAlgebraicSpace_V' := D.isAlgebraicSpace_V'
  p := D.p
  isProper_p := D.isProper_p
  j := D.j
  isPullback_j := D.isPullback_j
  xhat' := D.xhat'
  isPullback_xhat' := D.isPullback_xhat'
  x' := x'
  restrict_x' := hu
  completion_x' := hx

namespace DilatationWitness

variable {V : BigFppfOver B S hS} {Z : Set (Space.points B S hS (yoneda.obj V))}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}

/-- `j` is a section of `p` over `V ∖ Z`. -/
@[reassoc]
theorem j_p (D : DilatationWitness c V Z xhat) :
    D.j ≫ D.p = (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι := by
  have hw := D.isPullback_j.w
  rw [Category.id_comp] at hw
  exact hw.symm

/-- A morphism into `V ∖ Z` which agrees with a morphism into `V'` over `V` is followed by `j`
to that morphism. -/
private theorem comp_j_eq_of_comp_p (D : DilatationWitness c V Z xhat)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : A ⟶ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor) (b : A ⟶ D.V')
    (h : a ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι = b ≫ D.p) :
    a ≫ D.j = b := by
  have h1 := D.isPullback_j.lift_fst _ _ h
  have h2 := D.isPullback_j.lift_snd _ _ h
  rw [Category.comp_id] at h1
  rwa [h1] at h2

/-! ### Base change -/

section Pullback

variable {V₂ : BigFppfOver B S hS} (D : DilatationWitness c V Z xhat) (φ : V₂ ⟶ V)

/-- The inverse image of `Z` in the base change `V₂ ×_V V'`, read along either projection. -/
theorem preimage_pullback_fst_eq :
    Space.pointsMap B S hS (Limits.pullback (yoneda.map φ) D.p)
        (Limits.pullback.fst (yoneda.map φ) D.p) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z) =
      Space.pointsMap B S hS (Limits.pullback (yoneda.map φ) D.p)
        (Limits.pullback.snd (yoneda.map φ) D.p) ⁻¹' (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) :=
  Space.preimage_pointsMap_eq_of_comm B S hS Limits.pullback.condition Z

/-- The restriction of `j` to `V₂ ∖ Z₂`, followed by `p`, is the inclusion composed with `φ`. -/
theorem pullback_lift_cond :
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V₂)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ).ι ≫ yoneda.map φ =
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ
          (fun _ hz => hz) ≫ D.j) ≫ D.p := by
  rw [Category.assoc, D.j_p]
  exact (Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _).symm

/-- **The base change of a dilatation datum**, the construction of the proof of Stacks 0GHA:
for `φ : V₂ ⟶ V`, the fibre product `V₂ ×_V V'` with its first projection, the morphism
`V₂ ∖ Z₂ ⟶ V₂ ×_V V'` induced by `j`, and the composition of `x̂'` with
`(V₂ ×_V V')_{/Z₂} ⟶ V'_{/Z}`. -/
noncomputable def pullback :
    DilatationWitness c V₂ (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)
      (Space.completionSheafRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z) Z (fun _ hz => hz) ≫
          xhat) :=
  have hpb : IsPullback (Limits.pullback.fst (yoneda.map φ) D.p)
      (Limits.pullback.snd (yoneda.map φ) D.p) (yoneda.map φ) D.p :=
    IsPullback.of_hasPullback _ _
  have halg : IsAlgebraicSpace B S hS (Limits.pullback (yoneda.map φ) D.p) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS V₂)
      D.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS V)
  have hproper : Space.IsProper B S hS (Limits.pullback.fst (yoneda.map φ) D.p) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (Limits.pullback.fst (yoneda.map φ) D.p) :
          (⟨Limits.pullback (yoneda.map φ) D.p, halg⟩ : AlgebraicSpaces B S hS) ⟶
            schemeSpace V₂)
        (ObjectProperty.homMk (Limits.pullback.snd (yoneda.map φ) D.p) :
          (⟨Limits.pullback (yoneda.map φ) D.p, halg⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.V', D.isAlgebraicSpace_V'⟩)
        (schemeSpaceMap φ :
          (schemeSpace V₂ : AlgebraicSpaces B S hS) ⟶
            schemeSpace V)
        (ObjectProperty.homMk D.p :
          (⟨D.V', D.isAlgebraicSpace_V'⟩ : AlgebraicSpaces B S hS) ⟶
            schemeSpace V) :=
      IsPullback.of_map_of_faithful
        (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS F)) hpb
    exact (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq.flip D.isProper_p
  have hr : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
      (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫
        (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V₂)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ).ι ≫ yoneda.map φ :=
    Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _
  { V' := Limits.pullback (yoneda.map φ) D.p
    isAlgebraicSpace_V' := halg
    p := Limits.pullback.fst (yoneda.map φ) D.p
    isProper_p := hproper
    j := Limits.pullback.lift _ _ (D.pullback_lift_cond φ)
    isPullback_j := by
      refine (IsPullback.of_right ?_ ?_ hpb.flip).flip
      · have hid : IsPullback
            (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
              (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ
              (fun _ hz => hz)) (𝟙 _) (𝟙 _)
            (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
              (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ
              (fun _ hz => hz)) :=
          IsPullback.of_id_snd
        have hcomposite := hid.paste_horiz D.isPullback_j.flip
        rw [hr] at hcomposite
        rwa [← Limits.pullback.lift_snd _ _ (D.pullback_lift_cond φ)] at hcomposite
      · rw [Limits.pullback.lift_fst, Category.id_comp]
    xhat' := Space.completionSheafRestrict B S hS (Limits.pullback.snd (yoneda.map φ) D.p) _ _
      (D.preimage_pullback_fst_eq φ).subset ≫ D.xhat'
    isPullback_xhat' :=
      (Space.isPullback_completionSheafRestrict B S hS (Limits.pullback.fst (yoneda.map φ) D.p)
        (Limits.pullback.snd (yoneda.map φ) D.p) (yoneda.map φ) D.p hpb Z _ _ _ rfl rfl rfl
        (fun _ hz => hz) (D.preimage_pullback_fst_eq φ).subset (fun _ hz => hz)
        (fun _ hz => hz)).paste_vert D.isPullback_xhat' }

/-- The second projection `V₂ ×_V V' ⟶ V'` of the base change. -/
noncomputable def pullbackSnd : (D.pullback φ).V' ⟶ D.V' :=
  Limits.pullback.snd (yoneda.map φ) D.p

/-- The base change square commutes. -/
theorem pullback_condition :
    (D.pullback φ).p ≫ yoneda.map φ = D.pullbackSnd φ ≫ D.p :=
  Limits.pullback.condition

/-- The base change square is cartesian. -/
theorem isPullback_pullbackSnd :
    IsPullback (D.pullbackSnd φ) (D.pullback φ).p D.p (yoneda.map φ) :=
  (IsPullback.of_hasPullback (yoneda.map φ) D.p).flip

/-- The morphism into the base change induced by two compatible morphisms. -/
noncomputable def pullbackLift {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Y ⟶ yoneda.obj V₂)
    (b : Y ⟶ D.V') (h : a ≫ yoneda.map φ = b ≫ D.p) : Y ⟶ (D.pullback φ).V' :=
  Limits.pullback.lift a b h

/-- The morphism `pullbackLift φ a b h` followed by the first projection `p` is `a`. -/
@[reassoc (attr := simp)]
theorem pullbackLift_p {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Y ⟶ yoneda.obj V₂)
    (b : Y ⟶ D.V') (h : a ≫ yoneda.map φ = b ≫ D.p) :
    D.pullbackLift φ a b h ≫ (D.pullback φ).p = a :=
  Limits.pullback.lift_fst _ _ _

/-- The morphism `pullbackLift φ a b h` followed by the second projection `pullbackSnd φ` is
`b`. -/
@[reassoc (attr := simp)]
theorem pullbackLift_snd {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Y ⟶ yoneda.obj V₂)
    (b : Y ⟶ D.V') (h : a ≫ yoneda.map φ = b ≫ D.p) :
    D.pullbackLift φ a b h ≫ D.pullbackSnd φ = b :=
  Limits.pullback.lift_snd _ _ _

/-- Morphisms into the base change are determined by their two projections. -/
theorem pullback_hom_ext {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k k' : Y ⟶ (D.pullback φ).V'}
    (h₁ : k ≫ (D.pullback φ).p = k' ≫ (D.pullback φ).p)
    (h₂ : k ≫ D.pullbackSnd φ = k' ≫ D.pullbackSnd φ) : k = k' :=
  Limits.pullback.hom_ext h₁ h₂

/-- The inverse image of `Z₂` in `V₂ ×_V V'` is the inverse image of `p⁻¹ Z` along the second
projection. -/
theorem preimage_pullback_p_eq :
    Space.pointsMap B S hS (D.pullback φ).V' (D.pullback φ).p ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z) =
      Space.pointsMap B S hS (D.pullback φ).V' (D.pullbackSnd φ) ⁻¹'
        (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) :=
  D.preimage_pullback_fst_eq φ

/-- The morphism `j` of the base change, followed by the second projection, is the restriction
of `j`. -/
@[reassoc]
theorem pullback_j_snd :
    (D.pullback φ).j ≫ D.pullbackSnd φ =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z)ᶜ Zᶜ
          (fun _ hz => hz) ≫ D.j :=
  Limits.pullback.lift_snd _ _ _

/-- The morphism `x̂'` of the base change is the restriction of `x̂'`. -/
theorem pullback_xhat' :
    (D.pullback φ).xhat' = Space.completionSheafRestrict B S hS (D.pullbackSnd φ) _ _
      (D.preimage_pullback_p_eq φ).subset ≫ D.xhat' := rfl

end Pullback

/-! ### Uniqueness -/

/-- **Two dilatation data are comparable**, the uniqueness half of Stacks 0GDU: over a locally
Noetherian `V`, for two data `D` and `D'` of the same `Z` and `x̂` there is a morphism
`ψ : V'₁ ⟶ V'₂` over `V` compatible with the two morphisms `j` and with the two morphisms
`x̂'`. -/
theorem exists_hom (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    (hZ : IsClosed Z) (D D' : DilatationWitness c V Z xhat) :
    ∃ ψ : Over.mk D.p ⟶ Over.mk D'.p, D.j ≫ ψ.left = D'.j ∧
      Space.completionOverMap B S hS Z ψ ≫ D'.xhat' = D.xhat' := by
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN := Space.isLocallyNoetherian_yoneda B S hS V hV
  let e : ∀ w : DilatationWitness c V Z xhat,
      (Space.completionOverFunctor B S hS Z).obj (Over.mk w.p) ≅
        Over.mk (Limits.pullback.fst xhat c.g) := fun w =>
    Over.isoMk w.isPullback_xhat'.isoPullback (by
      change _ ≫ Limits.pullback.fst xhat c.g = Space.completionSheafMap B S hS w.p Z
      rw [IsPullback.isoPullback_hom_fst]
      exact Space.completionSheafRestrict_self B S hS w.p Z _)
  have hU : ∀ w : DilatationWitness c V Z xhat, IsIso
      (Limits.pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) := by
    intro w
    have h := w.isPullback_j.flip.isoPullback_hom_snd
    rw [← Iso.eq_inv_comp, Category.comp_id] at h
    rw [h]
    infer_instance
  obtain ⟨ψ, ⟨hψ, -⟩, -⟩ := FormalSpace.existsUnique_completionOverFunctor_map_comp_eq_of_isProper
    hVsp hVN Z hZ (Limits.pullback.fst xhat c.g) D.isAlgebraicSpace_V' D'.isAlgebraicSpace_V'
    D.isProper_p D'.isProper_p (hU D) (hU D') (e D) (e D')
  have hp : ψ.left ≫ D'.p = D.p := Over.w ψ
  refine ⟨ψ, ?_, ?_⟩
  · have hw : 𝟙 _ ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι =
        (D.j ≫ ψ.left) ≫ D'.p := by
      rw [Category.assoc, hp, ← D.isPullback_j.w]
    exact (D'.comp_j_eq_of_comp_p _ _ hw).symm.trans (Category.id_comp _)
  · have h1 := congrArg CommaMorphism.left hψ
    have h2 := congrArg (· ≫ Limits.pullback.snd xhat c.g) h1
    simp only [Over.comp_left, Category.assoc] at h2
    exact (congrArg (Space.completionOverMap B S hS Z ψ ≫ ·)
      D'.isPullback_xhat'.isoPullback_hom_snd.symm).trans
        (h2.trans D.isPullback_xhat'.isoPullback_hom_snd)

/-- **A morphism out of `V'` is determined by its restrictions to `V ∖ Z` and to `V'_{/Z}`**,
the uniqueness statement of Stacks 0GI1 for the dilatation `V'` of a locally Noetherian `V`:
`V'` is locally Noetherian, being locally of finite type over `V`, and the restriction of a
morphism to `V' ∖ p⁻¹Z` is its restriction to `V ∖ Z` through the identification `j`. -/
theorem hom_ext (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    (hZ : IsClosed Z) (D : DilatationWitness c V Z xhat)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (a b : D.V' ⟶ Y)
    (hj : D.j ≫ a = D.j ≫ b)
    (hc : Space.completionSheafInclusion B S hS D.V' (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) ≫
        Space.sheafifiedULiftMap B S hS a =
      Space.completionSheafInclusion B S hS D.V' (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) ≫
        Space.sheafifiedULiftMap B S hS b) :
    a = b := by
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN := Space.isLocallyNoetherian_yoneda B S hS V hV
  have hN := Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    D.isAlgebraicSpace_V' hVsp D.p D.isProper_p.2.1.1
    (FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hVsp hVN)
  refine Space.eq_of_eq_on_compl_of_eq_on_completion B S hS D.isAlgebraicSpace_V'
    hY hN (hZ.preimage (Space.continuous_pointsMap B S hS D.p)) _ _ ?_ ?_
  · let r := Space.openSubspaceOfPointsRestrict B S hS D.p
      (Space.pointsMap B S hS D.V' D.p ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz)
    have hr : r ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι =
        (Space.openSubspaceOfPoints B S hS D.V' (Space.pointsMap B S hS D.V' D.p ⁻¹' Z)ᶜ).ι ≫
          D.p :=
      Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _
    rw [← D.comp_j_eq_of_comp_p _ _ hr, Category.assoc, Category.assoc, hj]
  · exact Space.completionSubfunctor_ι_whiskerRight_eq B S hS hY _ _ _ hc

end DilatationWitness

/-! ### Existence -/

/-- **Dilatation data exist for an adic `x̂` over a locally Noetherian base.** As `V_{/Z}` is a
locally Noetherian formal algebraic space (Stacks 0AQ1) and `x̂` is adic, the base change of the
formal modification `g` along `x̂` is a formal modification of `V_{/Z}` (Stacks 0GDN), and the
existence half of the main theorem on dilatations (Stacks 0GDU) algebraizes it. -/
theorem nonempty_dilatationWitness (c : ContractionSituation B S hS) {V : BigFppfOver B S hS}
    (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
    (hadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xhat.hom) :
    Nonempty (DilatationWitness c V Z xhat) := by
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN := Space.isLocallyNoetherian_yoneda B S hS V hV
  have hFM := FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism B S hS c.g xhat
    (FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hVsp hVN Z hZ)
    hadic c.isFormalModification_g
  obtain ⟨V', hV', p, hp, hU, ⟨e⟩⟩ :=
    FormalSpace.exists_isProper_completion_iso_of_isFormalModification hVsp hVN Z hZ hFM
  have he : e.inv.left ≫ Space.completionSheafMap B S hS p Z =
      Limits.pullback.snd c.g xhat := Over.w e.inv
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  refine ⟨{ V' := V'
            isAlgebraicSpace_V' := hV'
            p := p
            isProper_p := hp
            j := inv (Limits.pullback.snd p (Space.openSubspaceOfPoints B S hS
              (yoneda.obj V) Zᶜ).ι) ≫ Limits.pullback.fst p (Space.openSubspaceOfPoints B S hS
              (yoneda.obj V) Zᶜ).ι
            isPullback_j := ?_
            xhat' := e.hom.left ≫ Limits.pullback.fst c.g xhat
            isPullback_xhat' := ?_ }⟩
  · refine (IsPullback.of_hasPullback p
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι).flip.of_iso
      (asIso (Limits.pullback.snd p (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · refine (IsPullback.of_hasPullback c.g xhat).flip.of_iso
      ((Over.forget _).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans he.symm
    · change _ ≫ 𝟙 _ = e.inv.left ≫ e.hom.left ≫ _
      rw [Category.comp_id, ← Category.assoc, hei, Category.id_comp]
    · simp
    · simp

/-! ### Descent -/

section Descent

variable {V : BigFppfOver B S hS} {Z : Set (Space.points B S hS (yoneda.obj V))}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}

/-- A set mapping into the inverse image of `Z` in `V₁ ×_V V'` along `m` maps into the inverse
image of `p⁻¹ Z` along `m ≫ pullbackSnd φ`. -/
private theorem DilatationWitness.subset_preimage_comp_pullbackSnd
    (D : DilatationWitness c V Z xhat) {V₁ : BigFppfOver B S hS} (φ : V₁ ⟶ V)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : Q ⟶ (D.pullback φ).V')
    {A : Set (Space.points B S hS Q)}
    (s₁ : A ⊆ Space.pointsMap B S hS Q m ⁻¹' (Space.pointsMap B S hS (D.pullback φ).V'
      (D.pullback φ).p ⁻¹' (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map φ) ⁻¹' Z))) :
    A ⊆ Space.pointsMap B S hS Q (m ≫ D.pullbackSnd φ) ⁻¹'
      (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) :=
  fun x hx => by
    rw [Set.mem_preimage, Space.pointsMap_comp]
    exact (D.preimage_pullback_p_eq φ).subset (s₁ hx)

/-- The completion of `m ≫ y` along a set `A` is the restriction of `x̂'` along
`m ≫ pullbackSnd φ`, when `y` is compatible with `x̂'` over the base change `V₁ ×_V V'`. -/
private theorem DilatationWitness.inclusion_comp_sheafifiedULiftMap_comp
    (D : DilatationWitness c V Z xhat) {V₁ : BigFppfOver B S hS} (φ : V₁ ⟶ V)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : Q ⟶ (D.pullback φ).V') (y : (D.pullback φ).V' ⟶ c.X')
    (hc : Space.completionSheafInclusion B S hS (D.pullback φ).V'
        (Space.pointsMap B S hS (D.pullback φ).V' (D.pullback φ).p ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map φ) ⁻¹' Z)) ≫
        Space.sheafifiedULiftMap B S hS y =
      (D.pullback φ).xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T')
    (A : Set (Space.points B S hS Q))
    (s₁ : A ⊆ Space.pointsMap B S hS Q m ⁻¹' (Space.pointsMap B S hS (D.pullback φ).V'
      (D.pullback φ).p ⁻¹' (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map φ) ⁻¹' Z))) :
    Space.completionSheafInclusion B S hS Q A ≫ Space.sheafifiedULiftMap B S hS (m ≫ y) =
      Space.completionSheafRestrict B S hS (m ≫ D.pullbackSnd φ) A _
        (D.subset_preimage_comp_pullbackSnd φ m s₁) ≫
        D.xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T' := by
  rw [Space.sheafifiedULiftMap_comp]
  simp only [← Category.assoc]
  rw [← Space.completionSheafRestrict_comp_inclusion B S hS _ _ _ s₁]
  simp only [Category.assoc]
  rw [hc, pullback_xhat']
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (D.xhat' ≫ _),
    ← Space.completionSheafRestrict_comp B S hS m _ _ _ _ s₁ (D.preimage_pullback_p_eq φ).subset
      (D.subset_preimage_comp_pullbackSnd φ m s₁)]

/-- **Local morphisms agree on overlaps**, the step of the descent of the compatibility
condition that uses Stacks 0GI1. Let `D` be a dilatation datum over `V`, let `V₁ ⟶ V` and
`V₂ ⟶ V` be two morphisms with a common refinement `O`, `O` locally Noetherian, and let
`y_k : V_k ×_V V' ⟶ X'` restrict to `u'` over `V_k ∖ Z_k` and to `x̂'` over the completion. Then
the two morphisms `O ×_V V' ⟶ X'` they induce agree: both restrict to `u'` and to `x̂'`. -/
theorem DilatationWitness.eq_of_overlap {V₁ V₂ O : BigFppfOver B S hS} (f₁ : V₁ ⟶ V)
    (f₂ : V₂ ⟶ V) (o₁ : O ⟶ V₁) (o₂ : O ⟶ V₂) (ho : o₁ ≫ f₁ = o₂ ≫ f₂)
    (hO : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj O)) (hZ : IsClosed Z)
    (D : DilatationWitness c V Z xhat)
    (y₁ : (D.pullback f₁).V' ⟶ c.X') (y₂ : (D.pullback f₂).V' ⟶ c.X')
    (hy₁ : (D.pullback f₁).j ≫ y₁ =
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map f₁)
        (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z)ᶜ Zᶜ
          (fun _ hz => hz) ≫ u) ≫ c.U'.ι)
    (hy₂ : (D.pullback f₂).j ≫ y₂ =
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map f₂)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)ᶜ Zᶜ
          (fun _ hz => hz) ≫ u) ≫ c.U'.ι)
    (hc₁ : Space.completionSheafInclusion B S hS (D.pullback f₁).V'
        (Space.pointsMap B S hS (D.pullback f₁).V' (D.pullback f₁).p ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z)) ≫
        Space.sheafifiedULiftMap B S hS y₁ =
      (D.pullback f₁).xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T')
    (hc₂ : Space.completionSheafInclusion B S hS (D.pullback f₂).V'
        (Space.pointsMap B S hS (D.pullback f₂).V' (D.pullback f₂).p ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)) ≫
        Space.sheafifiedULiftMap B S hS y₂ =
      (D.pullback f₂).xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T')
    (r : ((D.pullback f₁).pullback o₁).V' ⟶ (D.pullback f₂).V')
    (hrp : r ≫ (D.pullback f₂).p = ((D.pullback f₁).pullback o₁).p ≫ yoneda.map o₂)
    (hrq : r ≫ D.pullbackSnd f₂ = (D.pullback f₁).pullbackSnd o₁ ≫ D.pullbackSnd f₁) :
    (D.pullback f₁).pullbackSnd o₁ ≫ y₁ = r ≫ y₂ := by
  have hoY : yoneda.map o₁ ≫ yoneda.map f₁ = yoneda.map o₂ ≫ yoneda.map f₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, ho]
  have hZ₁₂ : Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z) =
      Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₂) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z) :=
    Space.preimage_pointsMap_eq_of_comm B S hS hoY Z
  refine DilatationWitness.hom_ext hO
    ((hZ.preimage (Space.continuous_pointsMap B S hS _)).preimage
      (Space.continuous_pointsMap B S hS _)) ((D.pullback f₁).pullback o₁)
    c.isAlgebraicSpace_X' _ _ ?_ ?_
  · have hsub₂ : (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z))ᶜ ⊆
        Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₂) ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)ᶜ := by
      rw [hZ₁₂]; exact fun _ hz => hz
    have hs₁ : (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z))ᶜ ⊆
        Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁ ≫ yoneda.map f₁) ⁻¹' Zᶜ := by
      intro x hx
      rw [Set.mem_preimage, Space.pointsMap_comp]
      exact hx
    have hs₂ : (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z))ᶜ ⊆
        Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₂ ≫ yoneda.map f₂) ⁻¹' Zᶜ :=
      hoY ▸ hs₁
    have hres : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map o₁)
          (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z))ᶜ
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z)ᶜ (fun _ hz => hz) ≫
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map f₁)
          (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z)ᶜ Zᶜ
          (fun _ hz => hz) =
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map o₂)
          (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z))ᶜ
          (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)ᶜ hsub₂ ≫
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map f₂)
          (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)ᶜ Zᶜ
          (fun _ hz => hz) :=
      Space.openSubspaceOfPointsRestrict_congr B S hS hoY _ Zᶜ hs₁ hs₂
    have hjr₁ := (D.pullback f₁).pullback_j_snd o₁
    have hjr₂ : ((D.pullback f₁).pullback o₁).j ≫ r =
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map o₂)
          (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z))ᶜ
          (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)ᶜ hsub₂ ≫
          (D.pullback f₂).j := by
      refine D.pullback_hom_ext f₂ ?_ ?_
      · rw [Category.assoc, hrp, ← Category.assoc, j_p, Category.assoc, j_p]
        exact (Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _).symm
      · rw [Category.assoc, hrq, ← Category.assoc, hjr₁, Category.assoc,
          D.pullback_j_snd f₁, Category.assoc, D.pullback_j_snd f₂, ← Category.assoc,
          ← Category.assoc, hres]
    rw [← Category.assoc, hjr₁, ← Category.assoc, hjr₂, Category.assoc, Category.assoc, hy₁, hy₂]
    simp only [← Category.assoc]
    rw [hres]
  · have s₁ := ((D.pullback f₁).preimage_pullback_p_eq o₁).subset
    have s₂ := (D.preimage_pullback_p_eq f₁).subset
    have s₂' := (D.preimage_pullback_p_eq f₂).subset
    have s₁' : Space.pointsMap B S hS ((D.pullback f₁).pullback o₁).V'
          ((D.pullback f₁).pullback o₁).p ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₁) ⁻¹'
              (Space.pointsMap B S hS (yoneda.obj V₁) (yoneda.map f₁) ⁻¹' Z)) ⊆
        Space.pointsMap B S hS ((D.pullback f₁).pullback o₁).V' r ⁻¹'
          (Space.pointsMap B S hS (D.pullback f₂).V' (D.pullback f₂).p ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)) := by
      intro x hx
      have e1 := congrFun (Space.pointsMap_comp B S hS _ r (D.pullback f₂).p) x
      rw [hrp, Space.pointsMap_comp, Function.comp_apply, Function.comp_apply] at e1
      have hx' : x ∈ Space.pointsMap B S hS ((D.pullback f₁).pullback o₁).V'
          ((D.pullback f₁).pullback o₁).p ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj O) (yoneda.map o₂) ⁻¹'
              (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z)) := by
        rw [← hZ₁₂]; exact hx
      change Space.pointsMap B S hS _ (D.pullback f₂).p (Space.pointsMap B S hS _ r x) ∈
        Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f₂) ⁻¹' Z
      rw [← e1]
      exact hx'
    rw [DilatationWitness.inclusion_comp_sheafifiedULiftMap_comp D f₁ _ y₁ hc₁ _ s₁,
      DilatationWitness.inclusion_comp_sheafifiedULiftMap_comp D f₂ r y₂ hc₂ _ s₁',
      Space.completionSheafRestrict_congr B S hS hrq.symm _ _ _ _]

/-- **The compatibility condition descends along a covering family with locally Noetherian
overlaps.** Let `V` be locally Noetherian, let `{f_i : V_i ⟶ V}` generate a covering sieve of
the big fppf site with each `V_i` locally Noetherian, and let `O_{ij}` with `o₁ : O_{ij} ⟶ V_i`,
`o₂ : O_{ij} ⟶ V_j` be locally Noetherian objects through which every pair of morphisms agreeing
over `V` factors (the fibre products `V_i ×_V V_j`). Let `Z ⊆ |V|` be closed, `u' : V ∖ Z ⟶ U'`,
and let `x̂ : V_{/Z} ⟶ W` be adic. If the restriction of `(u', x̂)` to every `V_i` is compatible,
then `(u', x̂)` is compatible.

The dilatation `V' ⟶ V` of the base change of `g` along `x̂` exists by Stacks 0GDU
(`nonempty_dilatationWitness`); over each `V_i` it is comparable with the given witness
(`DilatationWitness.exists_hom`), which defines `x'` over `V_i ×_V V'`; these agree on overlaps
by Stacks 0GI1 (`DilatationWitness.eq_of_overlap`), glue because `X'` is an fppf sheaf, and the
glued `x'` restricts correctly because it does so on the members of covering families. -/
theorem nonempty_compatibilityWitness_of_cover (c : ContractionSituation B S hS)
    {V : BigFppfOver B S hS} (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {I : Type*} (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (hVi : ∀ i, IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (Vi i)))
    (O : I → I → BigFppfOver B S hS) (o₁ : ∀ i j, O i j ⟶ Vi i) (o₂ : ∀ i j, O i j ⟶ Vi j)
    (ho : ∀ i j, o₁ i j ≫ f i = o₂ i j ≫ f j)
    (hO : ∀ i j, IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (O i j)))
    (hlift : ∀ i j (Y : BigFppfOver B S hS) (a : Y ⟶ Vi i) (b : Y ⟶ Vi j),
      a ≫ f i = b ≫ f j → ∃ l : Y ⟶ O i j, l ≫ o₁ i j = a ∧ l ≫ o₂ i j = b)
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
    (hadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xhat.hom)
    (h : ∀ i, Nonempty (CompatibilityWitness c (Vi i)
      (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) _ Zᶜ
        (fun _ hz => hz) ≫ u)
      (Space.completionSheafRestrict B S hS (yoneda.map (f i)) _ Z
        (fun _ hz => hz) ≫ xhat))) :
    Nonempty (CompatibilityWitness c V Z u xhat) := by
  obtain ⟨D⟩ := nonempty_dilatationWitness c hV hZ xhat hadic
  have hZi : ∀ i, IsClosed (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z) :=
    fun i => hZ.preimage (Space.continuous_pointsMap B S hS _)
  have hy : ∀ i, ∃ y : (D.pullback (f i)).V' ⟶ c.X',
      (D.pullback (f i)).j ≫ y =
        (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (f i))
          (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)ᶜ Zᶜ
            (fun _ hz => hz) ≫ u) ≫ c.U'.ι ∧
      Space.completionSheafInclusion B S hS (D.pullback (f i)).V'
          (Space.pointsMap B S hS (D.pullback (f i)).V' (D.pullback (f i)).p ⁻¹'
            (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)) ≫
          Space.sheafifiedULiftMap B S hS y =
        (D.pullback (f i)).xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T' := by
    intro i
    obtain ⟨ω⟩ := h i
    obtain ⟨ψ, hψj, hψx⟩ :=
      DilatationWitness.exists_hom (hVi i) (hZi i) (D.pullback (f i)) ω.toDilatationWitness
    let ψl : (D.pullback (f i)).V' ⟶ ω.V' := ψ.left
    refine ⟨ψl ≫ ω.x', ?_, ?_⟩
    · have h1 : (D.pullback (f i)).j ≫ ψl = ω.j := hψj
      rw [← Category.assoc, h1]
      exact ω.restrict_x'
    · have h1 : Space.completionSheafInclusion B S hS (D.pullback (f i)).V'
            (Space.pointsMap B S hS (D.pullback (f i)).V' (D.pullback (f i)).p ⁻¹'
              (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)) ≫
            Space.sheafifiedULiftMap B S hS ψl =
          Space.completionOverMap B S hS _ ψ ≫ Space.completionSheafInclusion B S hS
            ω.V' (Space.pointsMap B S hS ω.V' ω.p ⁻¹'
              (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)) :=
        (Space.completionOverMap_comp_inclusion B S hS _ ψ).symm
      have h2 : Space.completionOverMap B S hS _ ψ ≫ ω.xhat' = (D.pullback (f i)).xhat' := hψx
      rw [Space.sheafifiedULiftMap_comp, ← Category.assoc, h1]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ω.completion_x').trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h2)))
  choose y hyj hyc using hy
  have hcover : ∀ (T : BigFppfOver B S hS) (x : D.V'.obj (op T)),
      (Space.familyImage fun i => D.pullbackSnd (f i)).sieveOfSection x ∈
        BigFppfOver.topology B S hS T :=
    fun T x => Space.familyImage_cover _ f hf D.p (fun i => D.pullbackSnd (f i))
      (fun i => (D.pullback (f i)).p) (fun i => D.isPullback_pullbackSnd (f i)) T x
  obtain ⟨x', hx', -⟩ := Space.glueHom (BigFppfOver.topology B S hS)
    (fun i => D.pullbackSnd (f i)) hcover c.isAlgebraicSpace_X'.isSheaf y (by
      rintro ⟨T⟩ i j a b hab
      let a' : yoneda.obj T ⟶ (D.pullback (f i)).V' := yonedaEquiv.symm a
      let b' : yoneda.obj T ⟶ (D.pullback (f j)).V' := yonedaEquiv.symm b
      have hab' : a' ≫ D.pullbackSnd (f i) = b' ≫ D.pullbackSnd (f j) :=
        yonedaEquiv.injective (by
          rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact hab)
      have hα : yoneda.preimage (a' ≫ (D.pullback (f i)).p) ≫ f i =
          yoneda.preimage (b' ≫ (D.pullback (f j)).p) ≫ f j := yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
          Category.assoc, Category.assoc, D.pullback_condition (f i), D.pullback_condition (f j),
          ← Category.assoc, hab', Category.assoc])
      obtain ⟨l, hl₁, hl₂⟩ := hlift i j T _ _ hα
      have hcond : (((D.pullback (f i)).pullback (o₁ i j)).p ≫ yoneda.map (o₂ i j)) ≫
          yoneda.map (f j) = ((D.pullback (f i)).pullbackSnd (o₁ i j) ≫
            D.pullbackSnd (f i)) ≫ D.p := by
        have hY : yoneda.map (o₂ i j) ≫ yoneda.map (f j) =
            yoneda.map (o₁ i j) ≫ yoneda.map (f i) := by
          rw [← Functor.map_comp, ← Functor.map_comp, ho]
        rw [Category.assoc, hY,
          reassoc_of% ((D.pullback (f i)).pullback_condition (o₁ i j)),
          D.pullback_condition (f i), Category.assoc]
      obtain ⟨r, hrp, hrq⟩ : ∃ r : ((D.pullback (f i)).pullback (o₁ i j)).V' ⟶
          (D.pullback (f j)).V', r ≫ (D.pullback (f j)).p =
            ((D.pullback (f i)).pullback (o₁ i j)).p ≫ yoneda.map (o₂ i j) ∧
          r ≫ D.pullbackSnd (f j) =
            (D.pullback (f i)).pullbackSnd (o₁ i j) ≫ D.pullbackSnd (f i) :=
        ⟨_, D.pullbackLift_p (f j) _ _ hcond, D.pullbackLift_snd (f j) _ _ hcond⟩
      have key := DilatationWitness.eq_of_overlap (f i) (f j) (o₁ i j) (o₂ i j) (ho i j)
        (hO i j) hZ D (y i) (y j) (hyj i) (hyj j) (hyc i) (hyc j) r hrp hrq
      have hlz : yoneda.map l ≫ yoneda.map (o₁ i j) = a' ≫ (D.pullback (f i)).p := by
        rw [← Functor.map_comp, hl₁, Functor.map_preimage]
      let z : yoneda.obj T ⟶ ((D.pullback (f i)).pullback (o₁ i j)).V' :=
        (D.pullback (f i)).pullbackLift (o₁ i j) (yoneda.map l) a' hlz
      have hz₁ : z ≫ (D.pullback (f i)).pullbackSnd (o₁ i j) = a' :=
        (D.pullback (f i)).pullbackLift_snd _ _ _ _
      have hz₂ : z ≫ r = b' := by
        refine D.pullback_hom_ext (f j) ?_ ?_
        · rw [Category.assoc, hrp, ← Category.assoc, DilatationWitness.pullbackLift_p,
            ← Functor.map_comp, hl₂,
            Functor.map_preimage]
        · rw [Category.assoc, hrq, ← Category.assoc, hz₁, hab']
      calc (y i).app (op T) a = yonedaEquiv (a' ≫ y i) := by
            rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
        _ = yonedaEquiv (z ≫ (D.pullback (f i)).pullbackSnd (o₁ i j) ≫ y i) := by
            rw [← Category.assoc, hz₁]
        _ = yonedaEquiv (z ≫ r ≫ y j) := by rw [key]
        _ = (y j).app (op T) b := by
            rw [← Category.assoc, hz₂, yonedaEquiv_comp, Equiv.apply_symm_apply])
  have hR : D.j ≫ x' = u ≫ c.U'.ι := by
    refine Space.hom_ext_openSubspaceOfPoints B S hS Vi f hf Zᶜ
      (fun i => (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)ᶜ)
      (fun _ => Set.preimage_compl.symm) c.isAlgebraicSpace_X'.isSheaf _ _ fun i => ?_
    rw [← Category.assoc, ← D.pullback_j_snd (f i), Category.assoc, hx' i, hyj i,
      Category.assoc]
  have hC : Space.completionSheafInclusion B S hS D.V' (Space.pointsMap B S hS D.V' D.p ⁻¹' Z) ≫
      Space.sheafifiedULiftMap B S hS x' =
      D.xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T' := by
    refine Space.hom_ext_completionSheaf_of_cover B S hS (fun i => D.pullbackSnd (f i)) hcover _
      (fun i => Space.pointsMap B S hS (D.pullback (f i)).V' (D.pullback (f i)).p ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z))
      (fun i => D.preimage_pullback_p_eq (f i)) _ _ fun i => ?_
    rw [← Category.assoc, Space.completionSheafRestrict_comp_inclusion, Category.assoc,
      ← Space.sheafifiedULiftMap_comp, hx' i, hyc i, DilatationWitness.pullback_xhat',
      Category.assoc]
  exact ⟨CompatibilityWitness.ofDilatationWitness D x' hR hC⟩

/-- **The compatibility condition descends along étale coverings of the locally Noetherian
site.** Let `{V_i ⟶ V}` be an étale covering of the locally Noetherian site over `S`, let
`Z ⊆ |V|` be closed, `u' : V ∖ Z ⟶ U'`, and let `x̂ : V_{/Z} ⟶ W` be adic. If the restriction of
`(u', x̂)` to every `V_i` is compatible, then `(u', x̂)` is compatible. This is
`nonempty_compatibilityWitness_of_cover` with the overlaps `V_i ×_V V_j`, which lie in the
locally Noetherian site because `V_i ⟶ V` is étale. -/
theorem nonempty_compatibilityWitness_of_isEtaleCovering (c : ContractionSituation B S hS)
    {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E)
    {Z : Set (Space.points B S hS (yoneda.obj E.1.obj))} (hZ : IsClosed Z)
    (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj E.1.obj) Zᶜ).toFunctor ⟶
      c.U'.toFunctor)
    (xhat : Space.completionSheaf B S hS (yoneda.obj E.1.obj) Z ⟶ c.W)
    (hadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xhat.hom)
    (h : ∀ i, Nonempty (CompatibilityWitness c (E.2.X i).obj
      (Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj) (yoneda.map (E.2.f i).hom) ⁻¹' Z)
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (E.2.f i).hom) _ Zᶜ
        (fun _ hz => hz) ≫ u)
      (Space.completionSheafRestrict B S hS (yoneda.map (E.2.f i).hom) _ Z
        (fun _ hz => hz) ≫ xhat))) :
    Nonempty (CompatibilityWitness c E.1.obj Z u xhat) := by
  have hetale : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (E.2.f i).hom) := fun i =>
    LocallyNoetherianOver.etale_of_isEtaleCovering B S hS hE i
  exact nonempty_compatibilityWitness_of_cover c E.1.property (fun i => (E.2.X i).obj)
    (fun i => (E.2.f i).hom)
    (LocallyNoetherianOver.ofArrows_mem_topology_of_isCovering B S hS
      (LocallyNoetherianOver.isCovering_of_isEtaleCovering B S hS hE))
    (fun i => (E.2.X i).property)
    (fun i j => (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
    (fun i j => (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j => (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j => congrArg (fun k => k.hom)
      (LocallyNoetherianOver.overlapFst_comp_f B S hS (E.2.f i) (E.2.f j) (hetale i)))
    (fun i j => (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).property)
    (fun i j Y a b hab =>
      LocallyNoetherianOver.exists_lift_overlap B S hS (E.2.f i) (E.2.f j) (hetale i) Y a b hab)
    hZ u xhat hadic h

end Descent


end ContractionSituation

end AlgebraicGeometry.Artin

end
