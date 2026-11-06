module

public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContraction

/-!
# The statement of Stacks 0E89 for families of curves

Let `f : X ⟶ S` and `gᵢ : Yᵢ ⟶ S`, `i = 1, 2`, be families of curves over a scheme `S` of the
site and `cᵢ : X ⟶ Yᵢ` morphisms over `S`. Stacks 0E89 says that an isomorphism of the fibres of
`Y₁` and `Y₂` at a point `s ∈ S`, compatible with the fibres of the `cᵢ`, extends to an open
neighbourhood of `s` when the fibre `c₁,ₛ` has `𝒪 = c₁,ₛ,*𝒪` and `R¹c₁,ₛ,*𝒪 = 0`.

This file states it as a proposition about `AlgebraicGeometry.CurveFamily`: the fibres are taken
at the residue field of `s`, presented by schemes of the site, and the conclusion is an isomorphism
of the base changes along an open immersion compatible with the base changes of the `cᵢ`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.residueFieldValuedPoint`: the residue field of a point of the
  base as a field-valued point.
* `AlgebraicGeometry.CurveFamily.ExtendsFibreIsoNearPoint`: the statement of Stacks 0E89.

## Main results

* `AlgebraicGeometry.CurveFamily.isPullback_yoneda_of_isPullback_schemeSpace`: a cartesian square
  of algebraic spaces presenting a fibre is a cartesian square of presheaves.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. (Not `private`: the exposed definitions below
cannot use private instances.) -/
local instance (priority := high) hasPullbacks_presheaf_extendsFibreIsoNearPoint
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_extendsFibreIsoNearPoint
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

variable (B hZ) in
/-- The residue field `Spec κ(s) ⟶ Q` of a point `s` of a scheme of the site, as a field-valued
point of the algebraic space represented by `Q`. -/
def residueFieldValuedPoint (Q : BigFppfOver B integerBase hZ) (s : Q.left.1) :
    Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj where
  carrier := Q.left.1.residueField s
  contained := B.residueField_spec_contains Q.left.property s
  toBase := Q.left.1.fromSpecResidueField s ≫ Q.hom.1
  value := Space.residueFieldMap B integerBase hZ Q s _

/-- A presentation of a fibre by a cartesian square of algebraic spaces is one of presheaves. -/
theorem isPullback_yoneda_of_isPullback_schemeSpace {F : AlgebraicSpaces B integerBase hZ}
    {Q : BigFppfOver B integerBase hZ} (f : F ⟶ schemeSpace Q)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj)
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : schemeSpace V ⟶ F}
    (hsq : IsPullback q (schemeSpaceMap v) f (schemeSpaceMap p.value)) :
    IsPullback q.hom (yoneda.map v) f.hom (yonedaEquiv.symm p.value) := by
  have hp : yonedaEquiv.symm p.value = yoneda.map p.value :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map p.value).symm
  rw [hp]
  exact AlgebraicSpaces.isPullback_hom B integerBase hZ hsq

variable (B hZ) in
/-- **The statement of Stacks 0E89** for families of curves. Let `f : X ⟶ S` and `gᵢ : Yᵢ ⟶ S`,
`i = 1, 2`, be families of curves over a scheme `S` of the site and `cᵢ : X ⟶ Yᵢ` morphisms over
`S`. Let `s ∈ S`, let `V_X`, `V₁`, `V₂` present the fibres over `κ(s)`, with `aᵢ : V_X ⟶ Vᵢ` the
fibres of the `cᵢ`, and let `φ : V₁ ≅ V₂` be an isomorphism over `κ(s)` with `a₁ ≫ φ = a₂`. If
`𝒪_{V₁} = a₁,*𝒪_{V_X}` and `R¹a₁,*𝒪_{V_X} = 0`, there are an open neighbourhood `j : W ⟶ S` of
`s` and an isomorphism `Y₁,W ≅ Y₂,W` over `W` compatible with `c₁` and `c₂`. -/
def ExtendsFibreIsoNearPoint : Prop :=
  ∀ (X Y₁ Y₂ : CurveFamily B hZ) (hb₁ : Y₁.base = X.base) (hb₂ : Y₂.base = X.base)
    (c₁ : X.total ⟶ Y₁.total) (c₂ : X.total ⟶ Y₂.total)
    (hc₁ : c₁ ≫ Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) = X.toBase)
    (hc₂ : c₂ ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) = X.toBase)
    (s : X.base.left.1) (VX V₁ V₂ : BigFppfOver B integerBase hZ)
    (vX : VX ⟶ (residueFieldValuedPoint B hZ X.base s).siteObject)
    (v₁ : V₁ ⟶ (residueFieldValuedPoint B hZ X.base s).siteObject)
    (v₂ : V₂ ⟶ (residueFieldValuedPoint B hZ X.base s).siteObject)
    (qX : schemeSpace VX ⟶ X.total) (q₁ : schemeSpace V₁ ⟶ Y₁.total)
    (q₂ : schemeSpace V₂ ⟶ Y₂.total),
    IsPullback qX (schemeSpaceMap vX) X.toBase
      (schemeSpaceMap (residueFieldValuedPoint B hZ X.base s).value) →
    IsPullback q₁ (schemeSpaceMap v₁) (Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁))
      (schemeSpaceMap (residueFieldValuedPoint B hZ X.base s).value) →
    IsPullback q₂ (schemeSpaceMap v₂) (Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂))
      (schemeSpaceMap (residueFieldValuedPoint B hZ X.base s).value) →
    ∀ (a₁ : VX ⟶ V₁) (a₂ : VX ⟶ V₂), a₁ ≫ v₁ = vX → a₂ ≫ v₂ = vX →
    qX ≫ c₁ = schemeSpaceMap a₁ ≫ q₁ → qX ≫ c₂ = schemeSpaceMap a₂ ≫ q₂ →
    ∀ (φ : V₁ ≅ V₂), φ.hom ≫ v₂ = v₁ → a₁ ≫ φ.hom = a₂ →
    IsIso (SheafOfModules.unitToPushforwardObjUnit ((𝒯).map a₁).toRingCatSheafHom) →
    IsZero (((Scheme.Modules.pushforward ((𝒯).map a₁)).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯).obj VX).ringCatSheaf)) →
    ∃ (W : BigFppfOver B integerBase hZ) (j : W ⟶ X.base),
      IsOpenImmersion ((𝒯).map j) ∧ s ∈ Set.range ((𝒯).map j) ∧
      ∃ ψ : AlgebraicSpaces.fiberProduct B integerBase hZ
          (Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁)) (schemeSpaceMap j) ≅
        AlgebraicSpaces.fiberProduct B integerBase hZ
          (Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂)) (schemeSpaceMap j),
        ψ.hom ≫ ObjectProperty.homMk (pullback.snd _ _) = ObjectProperty.homMk (pullback.snd _ _) ∧
        Space.structureContractionBaseChange B integerBase hZ c₁ hc₁ (schemeSpaceMap j) ≫ ψ.hom =
          Space.structureContractionBaseChange B integerBase hZ c₂ hc₂ (schemeSpaceMap j)

end CurveFamily

end AlgebraicGeometry

end
