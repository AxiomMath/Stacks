module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.SeparatedComplex
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAlgebraUnitSection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.SingleUnitComposition

/-!
# Transporting the map `ξ` of a relative dualizing complex along a diagonal square

Let `D` be a diagonal open of `f : X ⟶ S` and `D'` one of `f' : X' ⟶ S'`. A *diagonal square*
from `D'` to `D` is a pair `(g' : X' ⟶ X, w : W' ⟶ W)` with `w ≫ pr₁|_W = pr₁|_{W'} ≫ g'`.
Together with an identification `eΔ : Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}` it transports a map
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` to a map `Δ'_*𝒪_{X'} ⟶ L pr₁^*(L(g')^*K)|_{W'}`
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.xiTransport`); this is the derived base change of `ξ`
of the proof of Stacks 0E2Y.

This file proves that transport is natural in `K` and functorial under pasting of diagonal
squares, the identifications `eΔ` being composed along. The identifications are normalised by
their compatibility with the unit maps `𝒪_W ⟶ Δ_*𝒪_X`
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.IsUnitNormalized`): a normalised identification is
unique, since every endomorphism of `Δ'_*𝒪_{X'}` is a scalar of `Γ(X', 𝒪_{X'})`, and normalised
identifications compose to normalised ones, by the coherence of `Lf^*𝒪 ≅ 𝒪` with composition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}

/-! ### Transport of `ξ` -/

/-- **Transport of `ξ` along a diagonal square** `(g', w)` with `w ≫ pr₁|_W = pr₁|_{W'} ≫ g'`,
read through an identification `eΔ : Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}`. -/
def xiTransport (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X) (w : D'.W ⟶ D.W)
    (hw : w ≫ D.proj = D'.proj ≫ g') (eΔ : (pull w).obj D.diagonalObject ≅ D'.diagonalObject)
    (K : Std X) (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) :
    (D'.diagonalObject : Std D'.W) ⟶ (pull D'.proj).obj ((pull g').obj K) :=
  eΔ.inv ≫ (pull w).map ξ ≫ (D.projPullIso D' g' w hw K).hom

/-- **Transport is natural in `K`.** -/
theorem xiTransport_comp_map (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X)
    (w : D'.W ⟶ D.W) (hw : w ≫ D.proj = D'.proj ≫ g')
    (eΔ : (pull w).obj D.diagonalObject ≅ D'.diagonalObject) {K L : Std X}
    (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) (φ : K ⟶ L) :
    D.xiTransport D' g' w hw eΔ L (ξ ≫ (pull D.proj).map φ) =
      D.xiTransport D' g' w hw eΔ K ξ ≫ (pull D'.proj).map ((pull g').map φ) :=
  Stacks.DerivedPullback.conj_map_comp _ _ _ _ _ _ _
    (D.projPullIso_hom_naturality D' g' w hw φ)

/-- The identification `L(w₃₂ ≫ w₂₁)^*Δ₁ ≅ Δ₃` obtained by composing identifications along two
stacked diagonal squares. -/
def diagonalPullComp {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂}
    {f₃ : X₃ ⟶ S₃} (D₁ : DiagonalOpen f₁) (D₂ : DiagonalOpen f₂) (D₃ : DiagonalOpen f₃)
    (w₂₁ : D₂.W ⟶ D₁.W) (w₃₂ : D₃.W ⟶ D₂.W) (w₃₁ : D₃.W ⟶ D₁.W) (hw : w₃₂ ≫ w₂₁ = w₃₁)
    (e₂₁ : (pull w₂₁).obj D₁.diagonalObject ≅ D₂.diagonalObject)
    (e₃₂ : (pull w₃₂).obj D₂.diagonalObject ≅ D₃.diagonalObject) :
    (pull w₃₁).obj D₁.diagonalObject ≅ D₃.diagonalObject :=
  ((Stacks.DerivedPullback.schemeFactorIso w₃₂ w₂₁ w₃₁ hw).app D₁.diagonalObject).symm ≪≫
    (pull w₃₂).mapIso e₂₁ ≪≫ e₃₂

/-- The chase behind `xiTransport_xiTransport`, with every object and morphism a variable. -/
theorem transport_paste_chase {C₁ C₂ C₃ E : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category E] (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) (G₃ : C₁ ⥤ C₃) (κ : G₁ ⋙ G₂ ≅ G₃) (H : E ⥤ C₃)
    {Δ₁ L₁ : C₁} {Δ₂ L₂ : C₂} {Δ₃ : C₃} {E₁ E₂ : E} (e₂₁ : G₁.obj Δ₁ ≅ Δ₂)
    (e₃₂ : G₂.obj Δ₂ ≅ Δ₃) (P₂₁ : G₁.obj L₁ ≅ L₂) (P₃₂ : G₂.obj L₂ ≅ H.obj E₁)
    (P₃₁ : G₃.obj L₁ ≅ H.obj E₂) (J : E₁ ≅ E₂)
    (hP : (κ.app L₁).symm ≪≫ G₂.mapIso P₂₁ ≪≫ P₃₂ ≪≫ H.mapIso J = P₃₁) (ξ : Δ₁ ⟶ L₁) :
    (e₃₂.inv ≫ G₂.map (e₂₁.inv ≫ G₁.map ξ ≫ P₂₁.hom) ≫ P₃₂.hom) ≫ H.map J.hom =
      ((κ.app Δ₁).symm ≪≫ G₂.mapIso e₂₁ ≪≫ e₃₂).inv ≫ G₃.map ξ ≫ P₃₁.hom := by
  subst hP
  have hn := κ.hom.naturality ξ
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]

/-- **Transport is functorial under pasting of diagonal squares**: transporting along
`(g₂₁, w₂₁)` and then along `(g₃₂, w₃₂)` is transporting along the composite square, with the
composite identification `diagonalPullComp`, up to the composition isomorphism of derived
pullback along `g₃₂ ≫ g₂₁ = g₃₁`. -/
theorem xiTransport_xiTransport {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁}
    {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃} (D₁ : DiagonalOpen f₁) (D₂ : DiagonalOpen f₂)
    (D₃ : DiagonalOpen f₃) (g₂₁ : X₂ ⟶ X₁) (g₃₂ : X₃ ⟶ X₂) (g₃₁ : X₃ ⟶ X₁)
    (hg : g₃₂ ≫ g₂₁ = g₃₁) (w₂₁ : D₂.W ⟶ D₁.W) (w₃₂ : D₃.W ⟶ D₂.W) (w₃₁ : D₃.W ⟶ D₁.W)
    (hw : w₃₂ ≫ w₂₁ = w₃₁) (h₂₁ : w₂₁ ≫ D₁.proj = D₂.proj ≫ g₂₁)
    (h₃₂ : w₃₂ ≫ D₂.proj = D₃.proj ≫ g₃₂) (h₃₁ : w₃₁ ≫ D₁.proj = D₃.proj ≫ g₃₁)
    (e₂₁ : (pull w₂₁).obj D₁.diagonalObject ≅ D₂.diagonalObject)
    (e₃₂ : (pull w₃₂).obj D₂.diagonalObject ≅ D₃.diagonalObject) (K : Std X₁)
    (ξ : (D₁.diagonalObject : Std D₁.W) ⟶ (pull D₁.proj).obj K) :
    D₂.xiTransport D₃ g₃₂ w₃₂ h₃₂ e₃₂ _ (D₁.xiTransport D₂ g₂₁ w₂₁ h₂₁ e₂₁ K ξ) ≫
        (pull D₃.proj).map ((Stacks.DerivedPullback.schemeFactorIso g₃₂ g₂₁ g₃₁ hg).hom.app K) =
      D₁.xiTransport D₃ g₃₁ w₃₁ h₃₁ (diagonalPullComp D₁ D₂ D₃ w₂₁ w₃₂ w₃₁ hw e₂₁ e₃₂) K ξ :=
  transport_paste_chase (pull w₂₁) (pull w₃₂) (pull w₃₁)
    (Stacks.DerivedPullback.schemeFactorIso w₃₂ w₂₁ w₃₁ hw) (pull D₃.proj) e₂₁ e₃₂
    (D₁.projPullIso D₂ g₂₁ w₂₁ h₂₁ K) (D₂.projPullIso D₃ g₃₂ w₃₂ h₃₂ ((pull g₂₁).obj K))
    (D₁.projPullIso D₃ g₃₁ w₃₁ h₃₁ K)
    ((Stacks.DerivedPullback.schemeFactorIso g₃₂ g₂₁ g₃₁ hg).app K)
    (D₁.projPullIso_paste D₂ D₃ g₂₁ g₃₂ g₃₁ hg w₂₁ w₃₂ w₃₁ hw h₂₁ h₃₂ h₃₁ K) ξ

/-! ### Normalising the identification of the diagonal objects -/

/-- The unit `𝒪_W ⟶ Δ_*𝒪_X` of the sheaf of algebras `Δ_*𝒪_X`, in `D(𝒪_W)`. -/
abbrev diagonalUnitMap (D : DiagonalOpen f) :
    Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite D.W.sheaf) ⟶
      D.diagonalObject :=
  Stacks.RelativeSpec.AlgebraSheaf.derivedUnit D.diagonalAlgebra

/-- `Lw^*𝒪_W ≅ 𝒪_{W'}`, the unit comparison of derived pullback. -/
abbrev unitPullIso {A B : Scheme.{u}} (w : A ⟶ B) :
    (pull w).obj (Stacks.DerivedTensor.RingedSite.unitObject
      (Stacks.SheafOfModules.ringedSite B.sheaf)) ≅
      Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite A.sheaf) :=
  Stacks.RingedSpace.derivedPullbackSingleUnitIso w.toLRSHom.toShHom

/-- **A normalised identification** `eΔ : Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}`: it carries `Lw^*` of the unit
`𝒪_W ⟶ Δ_*𝒪_X` to the unit `𝒪_{W'} ⟶ Δ'_*𝒪_{X'}`, through `Lw^*𝒪_W ≅ 𝒪_{W'}`. -/
def IsUnitNormalized (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (eΔ : (pull w).obj D.diagonalObject ≅ D'.diagonalObject) : Prop :=
  (pull w).map D.diagonalUnitMap ≫ eΔ.hom = (unitPullIso w).hom ≫ D'.diagonalUnitMap

/-- **A scalar fixing the unit is `1`.** If multiplication by `c ∈ Γ(X, 𝒪_X)` on `Δ_*𝒪_X` fixes
the unit `𝒪_W ⟶ Δ_*𝒪_X`, then `c = 1`. -/
theorem eq_one_of_diagonalUnitMap_comp_smul (D : DiagonalOpen f) (c : Γ(X, ⊤))
    (h : letI := D.proj.linearStructureSheafModules
      D.diagonalUnitMap ≫ (c • 𝟙 D.diagonalObject) = D.diagonalUnitMap) : c = 1 := by
  let := D.proj.linearStructureSheafModules
  let := HasDerivedCategory.standard (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf)
  rw [D.smul_id_diagonalObject c] at h
  have h' : Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra ≫
      D.diagonalScalar c = Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra := by
    apply (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0).map_injective
    exact ((DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0).map_comp _ _).trans h
  have e1 : ((Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra).val.app
      (op ⊤)).hom (1 : Γ(D.W, ⊤)) = (1 : D.diagonalAlgebra.right.obj.obj (op ⊤)) :=
    Stacks.RelativeSpec.AlgebraSheaf.structSection_one _ _
  have h1 : ((D.diagonalScalar c).val.app (op ⊤)).hom
      (((Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap D.diagonalAlgebra).val.app
        (op ⊤)).hom (1 : Γ(D.W, ⊤))) = _ :=
    congrArg (fun φ => (φ.val.app (op ⊤)).hom (1 : Γ(D.W, ⊤))) h'
  rw [e1] at h1
  exact (D.diagonalScalar_app_top_one c).symm.trans h1

/-- The chase behind `eq_of_isUnitNormalized`, with every object a variable. -/
theorem unit_comp_inv_hom_chase {C : Type*} [Category C] {L A T U : C} (Lu : L ⟶ A) (ν : L ≅ U)
    (u' : U ⟶ T) (e₁ e₂ : A ≅ T) (h₁ : Lu ≫ e₁.hom = ν.hom ≫ u')
    (h₂ : Lu ≫ e₂.hom = ν.hom ≫ u') : u' ≫ (e₁.inv ≫ e₂.hom) = u' := by
  have k : u' = ν.inv ≫ Lu ≫ e₁.hom := by rw [h₁, Iso.inv_hom_id_assoc]
  conv_lhs => rw [k]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, h₂, Iso.inv_hom_id_assoc]

/-- Two isomorphisms `e₁, e₂` with `e₁⁻¹ ≫ e₂ = 𝟙` are equal. -/
theorem iso_eq_of_inv_comp_hom_eq_id {C : Type*} [Category C] {A B : C} (e₁ e₂ : A ≅ B)
    (h : e₁.inv ≫ e₂.hom = 𝟙 B) : e₁ = e₂ := by
  ext
  simpa using ((Iso.inv_comp_eq e₁).1 h).symm

/-- **Normalised identifications are unique.** -/
theorem eq_of_isUnitNormalized (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    {e₁ e₂ : (pull w).obj D.diagonalObject ≅ D'.diagonalObject}
    (h₁ : IsUnitNormalized D D' w e₁) (h₂ : IsUnitNormalized D D' w e₂) : e₁ = e₂ := by
  let := D'.proj.linearStructureSheafModules
  obtain ⟨c, hc⟩ := D'.exists_eq_smul_id_diagonalObject (e₁.inv ≫ e₂.hom)
  have hu : D'.diagonalUnitMap ≫ (c • 𝟙 D'.diagonalObject) = D'.diagonalUnitMap := by
    rw [← hc]
    exact unit_comp_inv_hom_chase _ _ _ e₁ e₂ h₁ h₂
  obtain rfl := D'.eq_one_of_diagonalUnitMap_comp_smul c hu
  exact iso_eq_of_inv_comp_hom_eq_id e₁ e₂ (hc.trans (one_smul _ _))

/-- The chase behind `isUnitNormalized_diagonalPullComp`, with every object a variable. -/
theorem unit_paste_chase {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) (G₃ : C₁ ⥤ C₃) (κ : G₁ ⋙ G₂ ≅ G₃) {O₁ Δ₁ : C₁}
    {O₂ Δ₂ : C₂} {O₃ Δ₃ : C₃} (u₁ : O₁ ⟶ Δ₁) (u₂ : O₂ ⟶ Δ₂) (u₃ : O₃ ⟶ Δ₃)
    (ν₂₁ : G₁.obj O₁ ≅ O₂) (ν₃₂ : G₂.obj O₂ ≅ O₃) (ν₃₁ : G₃.obj O₁ ≅ O₃)
    (e₂₁ : G₁.obj Δ₁ ≅ Δ₂) (e₃₂ : G₂.obj Δ₂ ≅ Δ₃)
    (hc : κ.hom.app O₁ ≫ ν₃₁.hom = G₂.map ν₂₁.hom ≫ ν₃₂.hom)
    (h₂₁ : G₁.map u₁ ≫ e₂₁.hom = ν₂₁.hom ≫ u₂) (h₃₂ : G₂.map u₂ ≫ e₃₂.hom = ν₃₂.hom ≫ u₃) :
    G₃.map u₁ ≫ ((κ.app Δ₁).symm ≪≫ G₂.mapIso e₂₁ ≪≫ e₃₂).hom = ν₃₁.hom ≫ u₃ := by
  have hn := κ.inv.naturality u₁
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, h₂₁, Functor.map_comp_assoc, h₃₂,
    ← reassoc_of% hc, Iso.inv_hom_id_app_assoc]

/-- **Normalised identifications compose** to a normalised identification. -/
theorem isUnitNormalized_diagonalPullComp {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁}
    {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃} (D₁ : DiagonalOpen f₁) (D₂ : DiagonalOpen f₂)
    (D₃ : DiagonalOpen f₃) (w₂₁ : D₂.W ⟶ D₁.W) (w₃₂ : D₃.W ⟶ D₂.W) (w₃₁ : D₃.W ⟶ D₁.W)
    (hw : w₃₂ ≫ w₂₁ = w₃₁) {e₂₁ : (pull w₂₁).obj D₁.diagonalObject ≅ D₂.diagonalObject}
    {e₃₂ : (pull w₃₂).obj D₂.diagonalObject ≅ D₃.diagonalObject}
    (h₂₁ : IsUnitNormalized D₁ D₂ w₂₁ e₂₁) (h₃₂ : IsUnitNormalized D₂ D₃ w₃₂ e₃₂) :
    IsUnitNormalized D₁ D₃ w₃₁ (diagonalPullComp D₁ D₂ D₃ w₂₁ w₃₂ w₃₁ hw e₂₁ e₃₂) := by
  subst hw
  exact unit_paste_chase (pull w₂₁) (pull w₃₂) (pull (w₃₂ ≫ w₂₁))
    (Stacks.DerivedPullback.schemeFactorIso w₃₂ w₂₁ _ rfl) D₁.diagonalUnitMap
    D₂.diagonalUnitMap D₃.diagonalUnitMap (unitPullIso w₂₁) (unitPullIso w₃₂)
    (unitPullIso (w₃₂ ≫ w₂₁)) e₂₁ e₃₂
    (StacksDraft.UnitPullbackComposition.derivedPullbackCompIsoCanonical_hom_app_singleUnit
      w₃₂.toLRSHom.toShHom w₂₁.toLRSHom.toShHom) h₂₁ h₃₂

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
